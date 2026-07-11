use std::num::NonZeroU64;

use anyhow::{Context, Result, bail};
use cwdemangle::demangle;
use flagset::Flags;
use object::{
    Architecture, BinaryFormat, Endianness, Object, ObjectKind, ObjectSection, ObjectSymbol,
    RelocationEncoding, RelocationKind, RelocationTarget, SectionKind, SymbolFlags, SymbolKind,
    SymbolScope,
    write::{
        Comdat, Mangling, Object as WriteObject, Relocation, RelocationFlags, SectionId, Symbol,
        SymbolId, SymbolSection as WriteSymbolSection,
    },
    ComdatKind,
};

use crate::{
    analysis::cfa::SectionAddress,
    obj::{
        ObjArchitecture, ObjInfo, ObjKind, ObjReloc, ObjRelocKind, ObjSection, ObjSectionKind,
        ObjSplit, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags, ObjSymbolKind, PeMetadata,
        SectionIndex as ObjSectionIndex,
    },
};

/// Returns the parsed `ObjInfo` and, for PE executables, the ImageBase.
pub fn process_coff(data: &[u8], name: &str) -> Result<(ObjInfo, Option<u32>)> {
    let obj_file = object::File::parse(data).context("Failed to parse COFF/PE file")?;

    let architecture = match obj_file.architecture() {
        Architecture::I386 => ObjArchitecture::X86,
        Architecture::PowerPc => ObjArchitecture::PowerPc,
        arch => bail!("Unsupported architecture: {arch:?}"),
    };

    let kind = match obj_file.kind() {
        // A DLL is a fully-linked PE image (with an ImageBase and base
        // relocation table), so treat it the same as an executable.
        ObjectKind::Executable | ObjectKind::Dynamic => ObjKind::Executable,
        ObjectKind::Relocatable => ObjKind::Relocatable,
        kind => bail!("Unexpected COFF type: {kind:?}"),
    };

    let mut sections: Vec<ObjSection> = vec![];
    let mut section_indexes: Vec<Option<usize>> = vec![None]; // index 0 = null section

    for section in obj_file.sections() {
        if section.size() == 0 {
            section_indexes.push(None);
            continue;
        }
        let section_name = section.name().context("Section name")?;
        let section_kind = match section.kind() {
            SectionKind::Text => ObjSectionKind::Code,
            SectionKind::Data | SectionKind::OtherString => ObjSectionKind::Data,
            SectionKind::ReadOnlyData => ObjSectionKind::ReadOnlyData,
            SectionKind::UninitializedData => ObjSectionKind::Bss,
            _ => {
                section_indexes.push(None);
                continue;
            }
        };
        section_indexes.push(Some(sections.len()));
        let data = if section_kind == ObjSectionKind::Bss {
            vec![]
        } else {
            // Only read physical (on-disk) bytes. The gap between SizeOfRawData and
            // VirtualSize is implicitly zero-initialized BSS; split_obj handles it.
            section.uncompressed_data().context("Section data")?.to_vec()
        };
        sections.push(ObjSection {
            name: section_name.to_string(),
            kind: section_kind,
            address: section.address(),
            size: section.size(), // VirtualSize — covers full address range
            data,
            align: section.align().max(1),
            elf_index: section.index().0 as ObjSectionIndex,
            relocations: Default::default(),
            virtual_address: None,
            file_offset: section.file_range().map(|(v, _)| v).unwrap_or_default(),
            section_known: true,
            splits: Default::default(),
            sub_regions: Vec::new(),
        });
    }

    let mut symbols: Vec<ObjSymbol> = vec![];
    // Maps COFF symbol index → our ObjSymbol vector index.
    // Needed to resolve COFF relocation targets for .obj files.
    let mut coff_sym_map: std::collections::BTreeMap<usize, usize> = Default::default();
    let mut stack_address: Option<u32> = None;
    let mut stack_end: Option<u32> = None;
    let mut db_stack_addr: Option<u32> = None;
    let mut arena_lo: Option<u32> = None;
    let mut arena_hi: Option<u32> = None;
    let mut sda_base: Option<u32> = None;
    let mut sda2_base: Option<u32> = None;

    for symbol in obj_file.symbols() {
        let coff_idx = symbol.index().0;
        let symbol_name = match symbol.name() {
            Ok(n) if !n.is_empty() => n,
            _ => continue,
        };

        match symbol_name {
            "_stack_addr" => stack_address = Some(symbol.address() as u32),
            "_stack_end" => stack_end = Some(symbol.address() as u32),
            "_db_stack_addr" => db_stack_addr = Some(symbol.address() as u32),
            "__ArenaLo" => arena_lo = Some(symbol.address() as u32),
            "__ArenaHi" => arena_hi = Some(symbol.address() as u32),
            "_SDA_BASE_" => sda_base = Some(symbol.address() as u32),
            "_SDA2_BASE_" => sda2_base = Some(symbol.address() as u32),
            _ => {}
        }

        if matches!(symbol.kind(), SymbolKind::Section | SymbolKind::File) {
            continue;
        }

        let symbol_kind = match symbol.kind() {
            SymbolKind::Text => ObjSymbolKind::Function,
            SymbolKind::Data => ObjSymbolKind::Object,
            SymbolKind::Label | SymbolKind::Unknown => ObjSymbolKind::Unknown,
            _ => continue,
        };

        let section_index =
            symbol.section_index().and_then(|idx| section_indexes.get(idx.0).copied()).flatten();

        let mut flags = ObjSymbolFlagSet(ObjSymbolFlags::none());
        if symbol.is_global() {
            flags = ObjSymbolFlagSet(flags.0 | ObjSymbolFlags::Global);
        }
        if symbol.is_local() {
            flags = ObjSymbolFlagSet(flags.0 | ObjSymbolFlags::Local);
        }

        coff_sym_map.insert(coff_idx, symbols.len());
        symbols.push(ObjSymbol {
            name: symbol_name.to_string(),
            demangled_name: demangle(symbol_name, &Default::default()),
            address: symbol.address(),
            section: section_index.map(|s| s as ObjSectionIndex),
            size: symbol.size(),
            size_known: symbol.size() > 0,
            flags,
            kind: symbol_kind,
            ..Default::default()
        });
    }

    // For relocatable (.obj) files, read COFF section relocations so that
    // analyze_x86_functions can distinguish resolved vs unresolved operands.
    if kind == ObjKind::Relocatable {
        for section in obj_file.sections() {
            let sec_idx = match section_indexes.get(section.index().0).copied().flatten() {
                Some(idx) => idx,
                None => continue,
            };
            let sec_addr = sections[sec_idx].address;
            for (offset, reloc) in section.relocations() {
                let target_sym = match reloc.target() {
                    RelocationTarget::Symbol(idx) => match coff_sym_map.get(&idx.0) {
                        Some(&our_idx) => our_idx as u32,
                        None => continue,
                    },
                    _ => continue,
                };
                let reloc_kind = match reloc.kind() {
                    RelocationKind::Relative => ObjRelocKind::X86Rel32,
                    RelocationKind::Absolute => ObjRelocKind::X86Abs32,
                    _ => continue,
                };
                let addr = sec_addr + offset;
                sections[sec_idx].relocations.replace(
                    addr as u32,
                    ObjReloc {
                        kind: reloc_kind,
                        target_symbol: target_sym,
                        addend: reloc.addend(),
                        module: None,
                    },
                );
            }
        }
    }

    // Extract ImageBase from the PE optional header (x86 PE32 only)
    let image_base: Option<u32> = if kind == ObjKind::Executable {
        use object::{
            LittleEndian as LE,
            read::pe::{ImageNtHeaders, PeFile32},
        };
        PeFile32::parse(data).ok().map(|pe| pe.nt_headers().optional_header().image_base.get(LE))
    } else {
        None
    };

    let mut obj = ObjInfo::new(kind, architecture, name.to_string(), symbols, sections);
    obj.entry = NonZeroU64::new(obj_file.entry()).map(|n| n.get());
    obj.sda2_base = sda2_base;
    obj.sda_base = sda_base;
    obj.stack_address = stack_address;
    obj.stack_end = stack_end;
    obj.db_stack_addr = db_stack_addr;
    obj.arena_lo = arena_lo;
    obj.arena_hi = arena_hi;

    // Retain the base relocation table for reconstructing absolute relocations.
    // It is not kept as a section (the linker regenerates .reloc on output).
    if let Some(reloc_section) = obj_file.section_by_name(".reloc") {
        if let Ok(reloc_data) = reloc_section.uncompressed_data() {
            obj.pe_reloc_data = reloc_data.into_owned();
        }
    }

    // Capture original PE header metadata for the post-link patch. Only DLLs
    // need it (the base image has its own dedicated patch), and capturing the
    // base's large trailing data would bloat config.json.
    if kind == ObjKind::Executable {
        use object::{
            LittleEndian as LE,
            read::pe::{ImageNtHeaders, PeFile32},
        };
        if let Ok(pe) = PeFile32::parse(data) {
            let nt = pe.nt_headers();
            let opt = nt.optional_header();
            let is_dll = nt.file_header().characteristics.get(LE) & object::pe::IMAGE_FILE_DLL != 0;
            let data_directories = pe
                .data_directories()
                .iter()
                .map(|d| (d.virtual_address.get(LE), d.size.get(LE)))
                .collect();
            let reloc_virtual_size = pe
                .section_table()
                .iter()
                .find(|s| &s.name == b".reloc\0\0")
                .map(|s| s.virtual_size.get(LE))
                .unwrap_or(0);
            let trailing_off = pe
                .section_table()
                .iter()
                .map(|s| {
                    s.pointer_to_raw_data.get(LE) as usize + s.size_of_raw_data.get(LE) as usize
                })
                .max()
                .unwrap_or(0);
            if is_dll {
                obj.pe_metadata = Some(PeMetadata {
                    timestamp: nt.file_header().time_date_stamp.get(LE),
                    characteristics: nt.file_header().characteristics.get(LE),
                    dll_characteristics: opt.dll_characteristics.get(LE),
                    base_of_data: opt.base_of_data.get(LE),
                    size_of_code: opt.size_of_code.get(LE),
                    size_of_initialized_data: opt.size_of_initialized_data.get(LE),
                    size_of_image: opt.size_of_image.get(LE),
                    data_directories,
                    reloc_virtual_size,
                    trailing_data: data.get(trailing_off..).unwrap_or(&[]).to_vec(),
                });
            }
        }
    }

    Ok((obj, image_base))
}

pub fn write_coff(obj: &ObjInfo, export_all: bool) -> Result<Vec<u8>> {
    let mut out = WriteObject::new(BinaryFormat::Coff, Architecture::I386, Endianness::Little);
    // Disable object crate's auto leading-underscore mangling: it blindly
    // prepends '_' to every Text/Data symbol, which corrupts MSVC C++
    // mangled names ('?...') and fastcall names ('@...').  dtk's stored
    // symbol names already follow the MSVC convention literally (cdecl C
    // names include their leading '_' in symbols.txt; mangled names do not),
    // so we write them verbatim.
    out.set_mangling(Mangling::None);

    // Add sections and build section id map (indexed by ObjSectionIndex)
    let mut section_ids: Vec<Option<SectionId>> = vec![None; obj.sections.len() as usize];
    for (idx, section) in obj.sections.iter() {
        let kind = match section.kind {
            ObjSectionKind::Code => SectionKind::Text,
            ObjSectionKind::Data => SectionKind::Data,
            ObjSectionKind::ReadOnlyData => SectionKind::ReadOnlyData,
            ObjSectionKind::Bss => SectionKind::UninitializedData,
        };
        let sid = out.add_section(vec![], section.name.as_bytes().to_vec(), kind);
        if section.kind == ObjSectionKind::Bss {
            out.append_section_bss(sid, section.size, section.align.max(1));
        } else {
            // Zero out bytes at relocation sites; addend is carried by the relocation record
            let mut data = section.data.clone();
            for (addr, _) in section.relocations.iter() {
                let off = (addr as u64 - section.address) as usize;
                if off + 4 <= data.len() {
                    data[off..off + 4].fill(0);
                }
            }
            out.set_section_data(sid, data, section.align.max(1));
        }
        section_ids[idx as usize] = Some(sid);
    }

    // Add symbols and build symbol id map (indexed by SymbolIndex)
    let mut symbol_ids: Vec<SymbolId> = Vec::with_capacity(obj.symbols.count() as usize);
    // (leader SymbolId, SectionId) for each symbol flagged comdat, emitted as
    // selectany COMDAT groups after all symbols are added.
    let mut comdat_groups: Vec<(SymbolId, SectionId)> = Vec::new();
    // Dedup defined symbols that share an exact name within this object (e.g. a
    // `label` and a `function` emitted at the same vtable-slot address). Two
    // external definitions of one name in one object collide at link time;
    // emit the first and point later duplicates at the same SymbolId so any
    // relocations against them still resolve.
    let mut defined_by_name: std::collections::HashMap<Vec<u8>, SymbolId> =
        std::collections::HashMap::new();
    for (_, sym) in obj.symbols.iter() {
        let sym_section = match sym.section {
            Some(sec_idx) => match section_ids.get(sec_idx as usize).copied().flatten() {
                Some(sid) => WriteSymbolSection::Section(sid),
                None => WriteSymbolSection::Undefined,
            },
            None => WriteSymbolSection::Undefined,
        };
        let is_exported = sym.flags.0.contains(ObjSymbolFlags::Exported)
            || sym.flags.0.contains(ObjSymbolFlags::Global)
            || (export_all
                && !sym.flags.0.contains(ObjSymbolFlags::NoExport)
                && matches!(sym.kind, ObjSymbolKind::Function | ObjSymbolKind::Object));
        // Label (Unknown) symbols with a defined section are code labels that
        // may be referenced cross-object by DISP32 relocations.  Promote them
        // to Linkage scope so lld can resolve the cross-object reference.
        let is_defined_label = sym.kind == ObjSymbolKind::Unknown && sym.section.is_some();
        let scope = if sym.flags.0.contains(ObjSymbolFlags::Weak) || is_exported || is_defined_label
        {
            SymbolScope::Linkage
        } else {
            SymbolScope::Compilation
        };
        let kind = match sym.kind {
            ObjSymbolKind::Function => SymbolKind::Text,
            ObjSymbolKind::Object => SymbolKind::Data,
            ObjSymbolKind::Section => SymbolKind::Section,
            // COFF does not support Label-class defined symbols; lld rejects
            // them with "should not refer to special section 0".  Emit as Text
            // (function) so they are accepted as code labels.
            ObjSymbolKind::Unknown => SymbolKind::Text,
        };
        // Skip a duplicate *defined* symbol with an identical name already
        // emitted in this object; reuse the existing SymbolId for its index.
        if matches!(sym_section, WriteSymbolSection::Section(_))
            && !sym.flags.is_comdat()
            && !sym.name.is_empty()
        {
            if let Some(&existing) = defined_by_name.get(sym.name.as_bytes()) {
                symbol_ids.push(existing);
                continue;
            }
        }

        // The COMDAT section symbol (which carries the selection aux) must
        // precede the leader symbol in the symbol table, or lld defers the
        // leader, never resolves the pending comdat, and silently discards
        // the section ("comdat section without leader and unassociated").
        if sym.flags.is_comdat() {
            if let WriteSymbolSection::Section(section_id) = sym_section {
                out.section_symbol(section_id);
            }
        }
        let sid = out.add_symbol(Symbol {
            name: sym.name.as_bytes().to_vec(),
            value: sym.address,
            size: sym.size,
            kind,
            scope,
            weak: sym.flags.0.contains(ObjSymbolFlags::Weak),
            section: sym_section,
            flags: SymbolFlags::None,
        });
        if sym.flags.is_comdat() {
            if let WriteSymbolSection::Section(section_id) = sym_section {
                comdat_groups.push((sid, section_id));
            }
        }
        if matches!(sym_section, WriteSymbolSection::Section(_)) && !sym.name.is_empty() {
            defined_by_name.entry(sym.name.as_bytes().to_vec()).or_insert(sid);
        }
        symbol_ids.push(sid);
    }

    // Emit COMDAT groups (selectany) so duplicate definitions of these
    // symbols fold into this copy at link time instead of colliding.
    for (symbol, section_id) in comdat_groups {
        out.add_comdat(Comdat { kind: ComdatKind::Any, symbol, sections: vec![section_id] });
    }

    // Add relocations
    for (sec_idx, section) in obj.sections.iter() {
        let sid = match section_ids[sec_idx as usize] {
            Some(id) => id,
            None => continue,
        };
        for (addr, reloc) in section.relocations.iter() {
            let (kind, encoding, size) = match reloc.kind {
                ObjRelocKind::X86Abs32 => {
                    (RelocationKind::Absolute, RelocationEncoding::Generic, 32)
                }
                ObjRelocKind::X86Rel32 => {
                    (RelocationKind::Relative, RelocationEncoding::Generic, 32)
                }
                _ => continue,
            };
            let offset = (addr as u64).saturating_sub(section.address) as usize;
            // Skip relocations whose 4-byte field extends past the end of the
            // section data.  This can happen when a false-positive function split
            // cuts a boundary mid-instruction; the relocation belongs to the
            // correctly-sized split of the enclosing function.
            if offset + 4 > section.data.len() {
                log::warn!(
                    "Skipping relocation at {:#010X} in section {} (offset {} + 4 > {} bytes): \
                     split boundary may be mid-instruction",
                    addr,
                    section.name,
                    offset,
                    section.data.len()
                );
                continue;
            }
            let sym_id = symbol_ids[reloc.target_symbol as usize];
            // The object crate's coff_adjust_addend adds 4 to the addend for
            // IMAGE_REL_I386_REL32, storing it as the implicit addend in the
            // section data.  lld-link then computes sym_rva - P - 4 + A_implicit,
            // so the net effect with our addend A is: sym_rva - P - 4 + (A + 4) =
            // sym_rva - P + A.  For the CALL/JMP displacement to be correct
            // (sym_rva - P - 4 + A) we must subtract 4 here so the crate writes
            // A - 4 + 4 = A, and lld gets sym_rva - P - 4 + A. ✓
            let coff_addend =
                if reloc.kind == ObjRelocKind::X86Rel32 { reloc.addend - 4 } else { reloc.addend };
            out.add_relocation(
                sid,
                Relocation {
                    offset: offset as u64,
                    symbol: sym_id,
                    addend: coff_addend,
                    flags: RelocationFlags::Generic { kind, encoding, size },
                },
            )
            .with_context(|| {
                format!("Adding relocation at {:#010X} in section {}", addr, section.name)
            })?;
        }
    }

    out.write().map_err(|e| anyhow::anyhow!("{e:?}"))
}

const IMAGE_REL_BASED_HIGHLOW: u16 = 3;

/// Parse the PE `.reloc` section and add [`ObjRelocKind::X86Abs32`] relocations.
pub fn apply_base_relocations(obj: &mut ObjInfo, image_base: u32) -> Result<()> {
    let reloc_data = {
        if obj.pe_reloc_data.is_empty() {
            // A /FIXED image strips the .reloc table, so there are no base
            // relocations to import. Recover abs32 relocations by scanning data
            // for pointer words instead — otherwise verbatim data carries no
            // cross-references and /OPT:REF dead-strips sections the original
            // link kept (e.g. RTTI descriptors and the type_info they point at).
            log::debug!("No .reloc data; reconstructing abs32 relocations by data scan");
            return reconstruct_abs32_relocations_by_scan(obj);
        }
        obj.pe_reloc_data.clone()
    };

    let mut block_off = 0usize;
    let mut count = 0u32;
    while block_off + 8 <= reloc_data.len() {
        let page_rva = u32::from_le_bytes(reloc_data[block_off..block_off + 4].try_into().unwrap());
        let block_size =
            u32::from_le_bytes(reloc_data[block_off + 4..block_off + 8].try_into().unwrap());
        if block_size < 8 {
            break;
        }
        let num_entries = (block_size - 8) / 2;
        for i in 0..num_entries as usize {
            let e = block_off + 8 + i * 2;
            if e + 2 > reloc_data.len() {
                break;
            }
            let type_offset = u16::from_le_bytes(reloc_data[e..e + 2].try_into().unwrap());
            if type_offset >> 12 != IMAGE_REL_BASED_HIGHLOW {
                continue;
            }
            let reloc_va = image_base.wrapping_add(page_rva + (type_offset & 0x0FFF) as u32);

            let Ok((src_idx, _)) = obj.sections.at_address(reloc_va) else { continue };
            let src_sec = &obj.sections[src_idx];
            if src_sec.kind == ObjSectionKind::Bss || src_sec.relocations.at(reloc_va).is_some() {
                continue;
            }
            // Skip IAT slots: the linker regenerates the import address table and
            // its base relocations from the import directory.
            if obj.symbols.at_section_address(src_idx, reloc_va).any(|(_, s)| s.name.starts_with("__imp_")) {
                continue;
            }
            let off = (reloc_va as u64 - src_sec.address) as usize;
            if off + 4 > src_sec.data.len() {
                continue;
            }
            let target_va = u32::from_le_bytes(src_sec.data[off..off + 4].try_into().unwrap());
            if target_va == 0 {
                continue;
            }
            let Ok((tgt_idx, _)) = obj.sections.at_address(target_va) else { continue };
            let tgt_addr = SectionAddress::new(tgt_idx, target_va);
            let (target_symbol, addend) =
                match obj.symbols.for_relocation(tgt_addr, ObjRelocKind::X86Abs32)? {
                    Some((sym_idx, sym)) => (sym_idx, target_va as i64 - sym.address as i64),
                    None => {
                        let sym_idx = obj.symbols.add_direct(ObjSymbol {
                            name: format!("lbl_{:08X}", target_va),
                            address: target_va as u64,
                            section: Some(tgt_idx),
                            ..Default::default()
                        })?;
                        (sym_idx, 0)
                    }
                };
            let src_sec = &mut obj.sections[src_idx];
            src_sec
                .relocations
                .insert(
                    reloc_va,
                    ObjReloc { kind: ObjRelocKind::X86Abs32, target_symbol, addend, module: None },
                )
                .ok();
            count += 1;
        }
        block_off += block_size as usize;
    }
    log::info!("Applied {count} abs32 relocations from .reloc section");
    Ok(())
}

/// Reconstruct abs32 relocations for a `/FIXED` image (whose `.reloc` table has
/// been stripped) by scanning data sections for 4-byte-aligned pointer words.
///
/// This is the COFF analogue of the DOL/PPC `Tracker::process_data` pass: every
/// data word that points into a section is treated as a pointer and recovered as
/// an abs32 relocation, scope-agnostically. The linked bytes are unchanged (an
/// abs32 reloc resolves to the same absolute value the raw word already holds),
/// but the recovered references let `/OPT:REF` keep the same sections the
/// original link kept. Linkage validity — cross-unit references to file-local
/// (static) symbols, which can't be named across units — is handled afterwards
/// by the reconciliation pass in `cmd/coff.rs`, exactly as for rel32; dropped
/// relocs simply revert to the raw fixed-address word.
fn reconstruct_abs32_relocations_by_scan(obj: &mut ObjInfo) -> Result<()> {
    // First pass: collect candidate pointer words (immutable borrow of sections).
    let mut candidates: Vec<(ObjSectionIndex, u32, u32)> = Vec::new();
    for (src_idx, sec) in obj.sections.iter() {
        if matches!(sec.kind, ObjSectionKind::Bss | ObjSectionKind::Code) {
            continue;
        }
        let base = sec.address as u32;
        let mut off = (base.wrapping_neg() & 3) as usize; // align first word to 4
        while off + 4 <= sec.data.len() {
            let target_va = u32::from_le_bytes(sec.data[off..off + 4].try_into().unwrap());
            if target_va != 0 {
                if let Ok((tsec_idx, tsec)) = obj.sections.at_address(target_va) {
                    // References to code are normally aligned, so an unaligned in-range
                    // hit is usually an integer that merely looks like a pointer — unless
                    // a real symbol is defined at exactly that address. x86 CRT routines
                    // (e.g. __purecall) can sit at an unaligned code address and are
                    // referenced only by vtable data words; keep those.
                    let unaligned_code = tsec.kind == ObjSectionKind::Code && target_va & 3 != 0;
                    if !unaligned_code
                        || obj.symbols.at_section_address(tsec_idx, target_va).next().is_some()
                    {
                        candidates.push((src_idx, base + off as u32, target_va));
                    }
                }
            }
            off += 4;
        }
    }

    // Second pass: resolve each word to an *existing* symbol and insert the
    // relocation. No scope filter. Unlike the .reloc path we do NOT synthesize
    // labels for unknown targets: a data scan produces far more false positives
    // (integers that merely look in-range), and a spurious label gets auto-sized
    // to the next symbol, bisecting a split. Words with no existing symbol are
    // left as the raw fixed-address value — correct bytes, just not symbolic.
    let mut count = 0u32;
    for (src_idx, reloc_va, target_va) in candidates {
        if obj.sections[src_idx].relocations.at(reloc_va).is_some() {
            continue;
        }
        // Respect `noreloc` symbols (and config block_relocations): data whose
        // contents merely look like in-image pointers must stay raw bytes.
        if obj.blocked_relocation_sources.contains(SectionAddress::new(src_idx, reloc_va)) {
            continue;
        }
        // Skip IAT slots: the linker regenerates the import address table.
        if obj
            .symbols
            .at_section_address(src_idx, reloc_va)
            .any(|(_, s)| s.name.starts_with("__imp_"))
        {
            continue;
        }
        let Ok((tgt_idx, _)) = obj.sections.at_address(target_va) else { continue };
        let tgt_addr = SectionAddress::new(tgt_idx, target_va);
        let (target_symbol, addend) =
            match obj.symbols.for_relocation(tgt_addr, ObjRelocKind::X86Abs32)? {
                Some((sym_idx, sym)) => (sym_idx, target_va as i64 - sym.address as i64),
                None => continue,
            };
        obj.sections[src_idx]
            .relocations
            .insert(
                reloc_va,
                ObjReloc {
                    kind: ObjRelocKind::X86Abs32,
                    target_symbol,
                    addend,
                    module: None,
                },
            )
            .ok();
        count += 1;
    }
    log::info!("Reconstructed {count} abs32 relocations by data scan (FIXED image)");
    Ok(())
}

/// Create one `ObjSplit` per `Function`-kind symbol in code sections so that
/// each function becomes its own compilation unit, mirroring what the DOL
/// pipeline does via Tracker + CFA.
///
/// Only creates splits that don't already exist (user-defined splits in
/// `splits.txt` take precedence).
pub fn create_function_splits(obj: &mut ObjInfo) -> Result<()> {
    let code_sections: Vec<ObjSectionIndex> = obj
        .sections
        .iter()
        .filter(|(_, s)| s.kind == ObjSectionKind::Code)
        .map(|(idx, _)| idx)
        .collect();

    // Track which unit names are already in use (across all sections) to
    // ensure each split gets a unique unit name.  A duplicate name (e.g. two
    // LOCAL static functions with the same name) would cause split_obj to put
    // both ranges into the same object file, producing two .text sections.
    let mut unit_name_to_addr: std::collections::HashMap<String, u32> =
        std::collections::HashMap::new();
    // Pre-populate with splits already present (from splits.txt / user config).
    for (_sec_idx, section) in obj.sections.iter() {
        for (addr, split) in section.splits.iter() {
            unit_name_to_addr.insert(split.unit.clone(), addr);
        }
    }

    let mut total = 0u32;
    for sec_idx in code_sections {
        let section_end = {
            let s = &obj.sections[sec_idx];
            (s.address + s.size) as u32
        };

        // Collect (address, name) for every Function symbol in this section,
        // sorted by address.
        let fn_symbols: Vec<(u32, String)> = {
            let mut v: Vec<(u32, String)> = obj
                .symbols
                .for_section(sec_idx)
                .filter(|(_, sym)| sym.kind == ObjSymbolKind::Function)
                .map(|(_, sym)| (sym.address as u32, sym.name.clone()))
                .collect();
            v.sort_by_key(|(addr, _)| *addr);
            v
        };

        for (i, (addr, name)) in fn_symbols.iter().enumerate() {
            // Skip if a split already exists at this address.
            if obj.sections[sec_idx].splits.for_address(*addr).is_some() {
                continue;
            }
            let end = fn_symbols.get(i + 1).map(|(next_addr, _)| *next_addr).unwrap_or(section_end);

            // Ensure unit name is unique.  Duplicate function names (e.g. a
            // LOCAL static that appears twice due to COMDAT folding) would
            // otherwise merge two disjoint address ranges into one object.
            let unit = if name.is_empty() {
                // Unnamed function symbol (common in stripped DLLs): derive a
                // unique unit name from the address so the split object gets a
                // valid file name.
                let generated = format!("fn_{:#010x}", addr);
                unit_name_to_addr.insert(generated.clone(), *addr);
                generated
            } else {
                match unit_name_to_addr.entry(name.clone()) {
                std::collections::hash_map::Entry::Vacant(e) => {
                    e.insert(*addr);
                    name.clone()
                }
                std::collections::hash_map::Entry::Occupied(e) if *e.get() == *addr => {
                    // Same address — already handled (split exists check above
                    // should have caught this, but be safe).
                    name.clone()
                }
                std::collections::hash_map::Entry::Occupied(_) => {
                    // Duplicate: generate an address-unique unit name.
                    let generated = format!("fn_{:#010x}", addr);
                    log::warn!(
                        "Duplicate split unit name '{}' at {:#010X}; using '{}'",
                        name,
                        addr,
                        generated
                    );
                    unit_name_to_addr.insert(generated.clone(), *addr);
                    generated
                }
                }
            };

            obj.sections[sec_idx].splits.push(
                *addr,
                ObjSplit {
                    unit,
                    end,
                    align: Some(1), // x86 functions have no guaranteed alignment
                    common: false,
                    autogenerated: true,
                    skip: false,
                    rename: None,
                },
            );
            total += 1;
        }
    }

    log::info!("Created {total} function splits");
    Ok(())
}
