use std::num::NonZeroU64;

use anyhow::{Context, Result, bail};
use cwdemangle::demangle;
use flagset::Flags;
use object::{
    Architecture, BinaryFormat, ComdatKind, Endianness, Object, ObjectKind, ObjectSection,
    ObjectSymbol, RelocationEncoding, RelocationKind, RelocationTarget, SectionKind, SymbolFlags,
    SymbolKind, SymbolScope,
    write::{
        Comdat, Mangling, Object as WriteObject, Relocation, RelocationFlags, SectionId, Symbol,
        SymbolId, SymbolSection as WriteSymbolSection,
    },
};

use crate::{
    analysis::cfa::SectionAddress,
    obj::{
        ObjArchitecture, ObjInfo, ObjKind, ObjReloc, ObjRelocKind, ObjSection, ObjSectionKind,
        ObjSplit, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags, ObjSymbolKind, PeMetadata,
        SectionIndex as ObjSectionIndex,
    },
};

/// Extract exestr comment strings from the given `(file_offset, size, unit)`
/// ranges of the PE header padding onto `ObjInfo::pe_comment_directives`. Each
/// range may hold several NUL-separated runs; each non-empty run is kept
/// verbatim (a run truncated in the source is emitted as-is) and tagged with the
/// range's owning unit. Ranges come from `type:comment` entries in the splits
/// file (see `read_comment_regions`).
pub fn extract_comment_directives(
    data: &[u8],
    regions: &[(u32, u32, Option<String>)],
    obj: &mut ObjInfo,
    name: &str,
) -> Result<()> {
    for (offset, size, unit) in regions {
        let (start, end) = (*offset as usize, *offset as usize + *size as usize);
        let Some(region) = data.get(start..end) else {
            bail!("Comment region {offset:#x}..+{size:#x} is out of bounds for '{name}'");
        };
        for run in region.split(|&b| b == 0) {
            if !run.is_empty() {
                obj.pe_comment_directives.push((unit.clone(), run.to_vec()));
            }
        }
    }
    Ok(())
}

/// Encode exestr comment payloads as whitespace-separated `-?comment:"..."`
/// linker directives for a `.drectve` section.
fn encode_drectve<'a>(payloads: impl Iterator<Item = &'a [u8]>) -> Vec<u8> {
    let mut data = Vec::new();
    for (i, payload) in payloads.enumerate() {
        if i > 0 {
            data.push(b' ');
        }
        data.extend_from_slice(b"-?comment:\"");
        data.extend_from_slice(payload);
        data.push(b'"');
    }
    data
}

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

/// A contiguous byte range of an input section emitted as its own COFF
/// section (MSVC /Gy-style function-level sections). `start`/`end` are
/// section-relative offsets.
struct SectionChunk {
    start: u64,
    end: u64,
    id: SectionId,
}

/// Find the chunk containing `offset`. An offset at or past the end of the
/// last chunk clamps to the last chunk (defensive; split_obj filters symbols
/// at the section end address).
fn chunk_for(chunks: &[SectionChunk], offset: u64) -> Option<&SectionChunk> {
    let idx = chunks.partition_point(|c| c.start <= offset);
    if idx == 0 { None } else { Some(&chunks[idx - 1]) }
}

pub fn write_coff(obj: &ObjInfo, export_all: bool, function_sections: bool) -> Result<Vec<u8>> {
    let mut out = WriteObject::new(BinaryFormat::Coff, Architecture::I386, Endianness::Little);
    // Disable object crate's auto leading-underscore mangling: it blindly
    // prepends '_' to every Text/Data symbol, which corrupts MSVC C++
    // mangled names ('?...') and fastcall names ('@...').  dtk's stored
    // symbol names already follow the MSVC convention literally (cdecl C
    // names include their leading '_' in symbols.txt; mangled names do not),
    // so we write them verbatim.
    out.set_mangling(Mangling::None);

    // Add sections and build chunk table (indexed by ObjSectionIndex).
    // With function_sections enabled, each code section is cut at function
    // symbol boundaries so every function gets its own `.text` section (MSVC
    // /Gy style). COFF allows multiple sections with the same name, and
    // lld-link concatenates them in section-table order, so the emitted byte
    // stream is unchanged: inter-function padding and trailing jump tables
    // stay attached to the preceding function's chunk, and non-first chunks
    // use alignment 1 so the linker inserts nothing between them.
    let mut section_chunks: Vec<Vec<SectionChunk>> = Vec::new();
    section_chunks.resize_with(obj.sections.len() as usize, Vec::new);
    for (idx, section) in obj.sections.iter() {
        let kind = match section.kind {
            ObjSectionKind::Code => SectionKind::Text,
            ObjSectionKind::Data => SectionKind::Data,
            ObjSectionKind::ReadOnlyData => SectionKind::ReadOnlyData,
            ObjSectionKind::Bss => SectionKind::UninitializedData,
        };
        if section.kind == ObjSectionKind::Bss {
            let sid = out.add_section(vec![], section.name.as_bytes().to_vec(), kind);
            out.append_section_bss(sid, section.size, section.align.max(1));
            section_chunks[idx as usize].push(SectionChunk {
                start: 0,
                end: section.size,
                id: sid,
            });
            continue;
        }
        // Section-relative offsets where a new chunk begins. Labels (Unknown)
        // and Object symbols (e.g. jump tables) do not cut.
        let mut starts = vec![0u64];
        if function_sections && section.kind == ObjSectionKind::Code {
            let mut cuts: Vec<u64> = obj
                .symbols
                .for_section(idx)
                .filter(|(_, s)| s.kind == ObjSymbolKind::Function)
                .map(|(_, s)| s.address.saturating_sub(section.address))
                .filter(|&a| a > 0 && a < section.size)
                .collect();
            cuts.sort_unstable();
            cuts.dedup();
            starts.extend(cuts);
        }
        for (i, &start) in starts.iter().enumerate() {
            let end = starts.get(i + 1).copied().unwrap_or(section.size);
            let sid = out.add_section(vec![], section.name.as_bytes().to_vec(), kind);
            let data_end = (end as usize).min(section.data.len());
            let mut data = section.data[(start as usize).min(data_end)..data_end].to_vec();
            // Zero out bytes at relocation sites; addend is carried by the relocation record
            for (addr, _) in section.relocations.iter() {
                let off = (addr as u64).saturating_sub(section.address);
                if off >= start && off < end {
                    let rel = (off - start) as usize;
                    if rel + 4 <= data.len() {
                        data[rel..rel + 4].fill(0);
                    }
                }
            }
            let align = if start == 0 { section.align.max(1) } else { 1 };
            out.set_section_data(sid, data, align);
            section_chunks[idx as usize].push(SectionChunk { start, end, id: sid });
        }
    }

    // Add symbols and build symbol id map (indexed by SymbolIndex)
    let mut symbol_ids: Vec<SymbolId> = Vec::with_capacity(obj.symbols.count() as usize);
    // (leader SymbolId, SectionId, selection) for each symbol that leads a
    // COMDAT, emitted as COMDAT groups after all symbols are added.
    let mut comdat_groups: Vec<(SymbolId, SectionId, ComdatKind)> = Vec::new();
    // Dedup defined symbols that share an exact name within this object (e.g. a
    // `label` and a `function` emitted at the same vtable-slot address). Two
    // external definitions of one name in one object collide at link time;
    // emit the first and point later duplicates at the same SymbolId so any
    // relocations against them still resolve.
    let mut defined_by_name: std::collections::HashMap<Vec<u8>, SymbolId> =
        std::collections::HashMap::new();
    for (_, sym) in obj.symbols.iter() {
        // Resolve the symbol's chunk and chunk-relative value. Function
        // symbols that start a chunk land at value 0 in their own section;
        // mid-function labels get chunk-relative values.
        let (sym_section, sym_value) = match sym.section {
            Some(sec_idx) => {
                let sec_addr = obj.sections.get(sec_idx).map_or(0, |s| s.address);
                let offset = sym.address.saturating_sub(sec_addr);
                match section_chunks
                    .get(sec_idx as usize)
                    .and_then(|chunks| chunk_for(chunks, offset))
                {
                    Some(chunk) => (WriteSymbolSection::Section(chunk.id), offset - chunk.start),
                    None => (WriteSymbolSection::Undefined, sym.address),
                }
            }
            None => (WriteSymbolSection::Undefined, sym.address),
        };
        // scope:local in symbols.txt is honored even with export_all: the
        // globalize pass in split_obj has already cleared the Local flag on
        // any local symbol referenced cross-unit, so remaining locals are
        // genuinely unit-private and emit as IMAGE_SYM_CLASS_STATIC.
        let is_local = sym.flags.0.contains(ObjSymbolFlags::Local);
        let is_exported = sym.flags.0.contains(ObjSymbolFlags::Exported)
            || sym.flags.0.contains(ObjSymbolFlags::Global)
            || (export_all
                && !sym.flags.0.contains(ObjSymbolFlags::NoExport)
                && !is_local
                && matches!(sym.kind, ObjSymbolKind::Function | ObjSymbolKind::Object));
        // Label (Unknown) symbols with a defined section are code labels that
        // may be referenced cross-object by DISP32 relocations.  Promote them
        // to Linkage scope so lld can resolve the cross-object reference.
        let is_defined_label =
            sym.kind == ObjSymbolKind::Unknown && sym.section.is_some() && !is_local;
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
        // MSVC compiles every function into its own COMDAT, so an object that
        // mixes COMDAT and plain sections is a shape cl.exe never emits. lld
        // lays plain sections out in section order but COMDATs in symbol-table
        // order, so a lone COMDAT among plain sections drifts to the end of the
        // object; matching cl.exe and making each function section a COMDAT
        // keeps one order for the whole object. `nocomdat` opts a symbol out.
        // The selection differs: an explicit `comdat` is selectany, so a
        // duplicate definition folds into this copy, whereas a function is
        // NODUPLICATES like /Gy output.
        let comdat_kind = if sym.flags.is_no_comdat() {
            None
        } else if sym.flags.is_comdat() {
            Some(ComdatKind::Any)
        } else if function_sections
            && sym_value == 0
            && sym.kind == ObjSymbolKind::Function
            && sym.section.and_then(|i| obj.sections.get(i)).map(|s| s.kind)
                == Some(ObjSectionKind::Code)
        {
            Some(ComdatKind::NoDuplicates)
        } else {
            None
        };

        // Skip a duplicate *defined* symbol with an identical name already
        // emitted in this object; reuse the existing SymbolId for its index.
        if matches!(sym_section, WriteSymbolSection::Section(_))
            && comdat_kind.is_none()
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
        if comdat_kind.is_some() {
            if let WriteSymbolSection::Section(section_id) = sym_section {
                out.section_symbol(section_id);
            }
        }
        let sid = out.add_symbol(Symbol {
            name: sym.name.as_bytes().to_vec(),
            value: sym_value,
            size: sym.size,
            kind,
            scope,
            weak: sym.flags.0.contains(ObjSymbolFlags::Weak),
            section: sym_section,
            flags: SymbolFlags::None,
        });
        if let Some(kind) = comdat_kind {
            if let WriteSymbolSection::Section(section_id) = sym_section {
                comdat_groups.push((sid, section_id, kind));
            }
        }
        if matches!(sym_section, WriteSymbolSection::Section(_)) && !sym.name.is_empty() {
            defined_by_name.entry(sym.name.as_bytes().to_vec()).or_insert(sid);
        }
        symbol_ids.push(sid);
    }

    // Emit the COMDAT groups now that every leader has a SymbolId.
    for (symbol, section_id, kind) in comdat_groups {
        out.add_comdat(Comdat { kind, symbol, sections: vec![section_id] });
    }

    // Add relocations
    for (sec_idx, section) in obj.sections.iter() {
        let chunks = &section_chunks[sec_idx as usize];
        if chunks.is_empty() {
            continue;
        }
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
            let offset = (addr as u64).saturating_sub(section.address);
            let Some(chunk) = chunk_for(chunks, offset) else { continue };
            let chunk_off = (offset - chunk.start) as usize;
            let chunk_len = ((chunk.end.min(section.data.len() as u64)) - chunk.start) as usize;
            // Skip relocations whose 4-byte field extends past the end of the
            // chunk data.  This can happen when a false-positive function split
            // cuts a boundary mid-instruction; the relocation belongs to the
            // correctly-sized split of the enclosing function.
            if chunk_off + 4 > chunk_len {
                log::warn!(
                    "Skipping relocation at {:#010X} in section {} (offset {} + 4 > {} bytes): \
                     split boundary may be mid-instruction",
                    addr,
                    section.name,
                    chunk_off,
                    chunk_len
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
                chunk.id,
                Relocation {
                    offset: chunk_off as u64,
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

    // Emit this unit's exestr comments as a `.drectve` section
    // (IMAGE_SCN_LNK_INFO | IMAGE_SCN_LNK_REMOVE), which a comment-aware linker
    // re-embeds and others ignore.
    if !obj.pe_comment_directives.is_empty() {
        let data = encode_drectve(obj.pe_comment_directives.iter().map(|(_, p)| p.as_slice()));
        let sid = out.add_section(vec![], b".drectve".to_vec(), SectionKind::Linker);
        out.set_section_data(sid, data, 1);
    }

    out.write().map_err(|e| anyhow::anyhow!("{e:?}"))
}

/// Build a COFF object whose sole content is a `.drectve` section carrying one
/// `-?comment:"..."` directive per payload (used for comments not attributed to
/// any unit). Returns `None` if there are no directives.
pub fn write_coff_comments(directives: &[&[u8]]) -> Result<Option<Vec<u8>>> {
    if directives.is_empty() {
        return Ok(None);
    }
    let mut out = WriteObject::new(BinaryFormat::Coff, Architecture::I386, Endianness::Little);
    out.set_mangling(Mangling::None);
    let sid = out.add_section(vec![], b".drectve".to_vec(), SectionKind::Linker);
    out.set_section_data(sid, encode_drectve(directives.iter().copied()), 1);
    out.write().map(Some).map_err(|e| anyhow::anyhow!("{e:?}"))
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
            if obj
                .symbols
                .at_section_address(src_idx, reloc_va)
                .any(|(_, s)| s.name.starts_with("__imp_"))
            {
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
                ObjReloc { kind: ObjRelocKind::X86Abs32, target_symbol, addend, module: None },
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

#[cfg(test)]
mod tests {
    use object::ObjectSymbol;

    use super::*;
    use crate::obj::{ObjRelocations, ObjSplits};

    fn section(
        name: &str,
        kind: ObjSectionKind,
        elf_index: ObjSectionIndex,
        data: Vec<u8>,
        relocations: Vec<(u32, ObjReloc)>,
    ) -> ObjSection {
        ObjSection {
            name: name.to_string(),
            kind,
            address: 0,
            size: data.len() as u64,
            data,
            align: 16,
            elf_index,
            relocations: ObjRelocations::new(relocations).unwrap(),
            virtual_address: None,
            file_offset: 0,
            section_known: true,
            splits: ObjSplits::default(),
            sub_regions: vec![],
        }
    }

    fn symbol(
        name: &str,
        address: u64,
        section: Option<ObjSectionIndex>,
        size: u64,
        kind: ObjSymbolKind,
        flags: ObjSymbolFlagSet,
    ) -> ObjSymbol {
        ObjSymbol {
            name: name.to_string(),
            address,
            section,
            size,
            size_known: true,
            flags,
            kind,
            ..Default::default()
        }
    }

    /// .text: fnA = 8 bytes (Rel32 at +2), 2 bytes 0xCC padding, fnB = 6 bytes
    /// (Abs32 at +1, i.e. section offset 11); label mid-fnB at +12. Plus .data
    /// with one Local object symbol.
    fn test_obj() -> ObjInfo {
        let mut text: Vec<u8> = (1..=16u8).collect();
        text[8] = 0xCC;
        text[9] = 0xCC;
        let text_sec = section(
            ".text",
            ObjSectionKind::Code,
            0,
            text,
            vec![
                (
                    2,
                    ObjReloc {
                        kind: ObjRelocKind::X86Rel32,
                        target_symbol: 1,
                        addend: 0,
                        module: None,
                    },
                ),
                (
                    11,
                    ObjReloc {
                        kind: ObjRelocKind::X86Abs32,
                        target_symbol: 3,
                        addend: 0,
                        module: None,
                    },
                ),
            ],
        );
        let data_sec = section(".data", ObjSectionKind::Data, 1, vec![1, 2, 3, 4], vec![]);
        let symbols = vec![
            symbol(
                "fnA",
                0,
                Some(0),
                8,
                ObjSymbolKind::Function,
                ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
            ),
            symbol(
                "fnB",
                10,
                Some(0),
                6,
                ObjSymbolKind::Function,
                ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
            ),
            symbol("lbl_12", 12, Some(0), 0, ObjSymbolKind::Unknown, Default::default()),
            symbol(
                "dat",
                0,
                Some(1),
                4,
                ObjSymbolKind::Object,
                ObjSymbolFlagSet(ObjSymbolFlags::Local.into()),
            ),
        ];
        ObjInfo::new(
            ObjKind::Relocatable,
            ObjArchitecture::X86,
            "test".to_string(),
            symbols,
            vec![text_sec, data_sec],
        )
    }

    #[test]
    fn test_function_sections_are_comdat() {
        // Every function section is a COMDAT, the way cl.exe emits them, so an
        // object never mixes COMDAT and plain sections. `nocomdat` opts out.
        // Read IMAGE_SCN_LNK_COMDAT straight out of the section headers: the
        // object crate is in the dependency graph twice here, so its comdat
        // trait is awkward to name, and the raw flag is what lld reads anyway.
        const LNK_COMDAT: u32 = 0x0000_1000;
        fn comdat_flags(out: &[u8]) -> Vec<(String, bool)> {
            let count = u16::from_le_bytes([out[2], out[3]]) as usize;
            (0..count)
                .map(|i| {
                    let o = 20 + i * 40;
                    let name =
                        String::from_utf8_lossy(&out[o..o + 8]).trim_end_matches('\0').to_string();
                    let chars = u32::from_le_bytes(out[o + 36..o + 40].try_into().unwrap());
                    (name, chars & LNK_COMDAT != 0)
                })
                .collect()
        }

        let mut obj = test_obj();
        let out = write_coff(&obj, true, true).unwrap();
        let secs = comdat_flags(&out);
        assert_eq!(
            secs,
            vec![
                (".text".to_string(), true),
                (".text".to_string(), true),
                (".data".to_string(), false),
            ],
            "function sections are COMDATs, data stays plain"
        );

        // nocomdat leaves that one function's section out of a COMDAT.
        let idx = obj.symbols.iter().find(|(_, s)| s.name == "fnB").unwrap().0;
        obj.symbols.flags(idx).0 |= ObjSymbolFlags::NoComdat;
        let out = write_coff(&obj, true, true).unwrap();
        assert_eq!(
            comdat_flags(&out).iter().filter(|(_, c)| *c).count(),
            1,
            "nocomdat keeps fnB out"
        );
    }

    #[test]
    fn test_function_sections() {
        let obj = test_obj();
        let out = write_coff(&obj, true, true).unwrap();
        let file = object::File::parse(&*out).unwrap();

        // fnA chunk [0,10) with padding attached, fnB chunk [10,16), .data
        let sections: Vec<_> = file.sections().collect();
        assert_eq!(sections.len(), 3);
        assert_eq!(sections[0].name().unwrap(), ".text");
        assert_eq!(sections[1].name().unwrap(), ".text");
        assert_eq!(sections[2].name().unwrap(), ".data");
        assert_eq!(sections[0].size(), 10);
        assert_eq!(sections[1].size(), 6);

        let d0 = sections[0].data().unwrap();
        assert_eq!(&d0[8..10], &[0xCC, 0xCC], "padding attached to preceding function");
        assert_eq!(&d0[6..8], &[7, 8], "non-reloc bytes preserved");
        let d1 = sections[1].data().unwrap();
        assert_eq!(d1[0], 11, "fnB data starts at section offset 10");
        assert_eq!(&d1[1..5], &[0, 0, 0, 0], "Abs32 reloc site zeroed chunk-relative");

        // Relocations rebased into their chunks
        let relocs0: Vec<_> = sections[0].relocations().collect();
        assert_eq!(relocs0.len(), 1);
        assert_eq!(relocs0[0].0, 2);
        let relocs1: Vec<_> = sections[1].relocations().collect();
        assert_eq!(relocs1.len(), 1);
        assert_eq!(relocs1[0].0, 1);

        // Symbols land in their chunks with chunk-relative values
        let find = |name: &str| file.symbols().find(|s| s.name() == Ok(name)).unwrap();
        let fna = find("fnA");
        assert_eq!(fna.section_index(), Some(sections[0].index()));
        assert_eq!(fna.address(), 0);
        let fnb = find("fnB");
        assert_eq!(fnb.section_index(), Some(sections[1].index()));
        assert_eq!(fnb.address(), 0);
        let lbl = find("lbl_12");
        assert_eq!(lbl.section_index(), Some(sections[1].index()));
        assert_eq!(lbl.address(), 2);
    }

    #[test]
    fn test_no_function_sections() {
        let obj = test_obj();
        let out = write_coff(&obj, true, false).unwrap();
        let file = object::File::parse(&*out).unwrap();
        let sections: Vec<_> = file.sections().collect();
        assert_eq!(sections.len(), 2);
        assert_eq!(sections[0].name().unwrap(), ".text");
        assert_eq!(sections[0].size(), 16);
        let relocs: Vec<_> = sections[0].relocations().collect();
        assert_eq!(relocs.len(), 2);
        assert_eq!(relocs[0].0, 2);
        assert_eq!(relocs[1].0, 11);
        let fnb = file.symbols().find(|s| s.name() == Ok("fnB")).unwrap();
        assert_eq!(fnb.address(), 10);
    }

    #[test]
    fn test_scope_local_static() {
        let obj = test_obj();
        let out = write_coff(&obj, true, true).unwrap();
        let file = object::File::parse(&*out).unwrap();
        let find = |name: &str| file.symbols().find(|s| s.name() == Ok(name)).unwrap();
        // scope:local honored despite export_all
        assert!(find("dat").is_local(), "Local flag must emit IMAGE_SYM_CLASS_STATIC");
        // globalized/global symbols stay external
        assert!(find("fnA").is_global());
        assert!(find("fnB").is_global());
    }

    #[test]
    fn test_multi_range_unit_chunks_per_section() {
        // Two same-named code sections (non-contiguous unit): chunked
        // independently, no index collisions.
        let text_a = section(".text", ObjSectionKind::Code, 0, vec![0x90; 8], vec![]);
        let text_b = section(".text", ObjSectionKind::Code, 1, vec![0x90; 8], vec![]);
        let symbols = vec![
            symbol(
                "fn1",
                0,
                Some(0),
                8,
                ObjSymbolKind::Function,
                ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
            ),
            symbol(
                "fn2",
                0,
                Some(1),
                4,
                ObjSymbolKind::Function,
                ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
            ),
            symbol(
                "fn3",
                4,
                Some(1),
                4,
                ObjSymbolKind::Function,
                ObjSymbolFlagSet(ObjSymbolFlags::Global.into()),
            ),
        ];
        let obj = ObjInfo::new(
            ObjKind::Relocatable,
            ObjArchitecture::X86,
            "test".to_string(),
            symbols,
            vec![text_a, text_b],
        );
        let out = write_coff(&obj, true, true).unwrap();
        let file = object::File::parse(&*out).unwrap();
        let sections: Vec<_> = file.sections().collect();
        // section A: 1 chunk; section B: 2 chunks
        assert_eq!(sections.len(), 3);
        assert!(sections.iter().all(|s| s.name() == Ok(".text")));
        assert_eq!(sections[0].size(), 8);
        assert_eq!(sections[1].size(), 4);
        assert_eq!(sections[2].size(), 4);
        let find = |name: &str| file.symbols().find(|s| s.name() == Ok(name)).unwrap();
        assert_eq!(find("fn1").section_index(), Some(sections[0].index()));
        assert_eq!(find("fn2").section_index(), Some(sections[1].index()));
        let fn3 = find("fn3");
        assert_eq!(fn3.section_index(), Some(sections[2].index()));
        assert_eq!(fn3.address(), 0);
    }

    #[test]
    fn test_extract_comment_directives() {
        // Runs inside the region: "abc" \0 "def"; a trailing NUL yields no empty
        // run. Bytes outside the declared region must be ignored.
        let mut data = Vec::new();
        let region_off = data.len() as u32;
        data.extend_from_slice(b"abc\0def\0");
        data.extend_from_slice(b"JUNK_OUTSIDE"); // outside the declared size
        let region_size = 8u32; // covers "abc\0def\0" only

        let (mut obj, _) =
            process_coff(&write_coff(&test_obj(), true, false).unwrap(), "test").unwrap();
        obj.pe_comment_directives.clear();
        let unit = Some("amaths".to_string());
        extract_comment_directives(
            &data,
            &[(region_off, region_size, unit.clone())],
            &mut obj,
            "t",
        )
        .unwrap();
        assert_eq!(
            obj.pe_comment_directives,
            vec![(unit.clone(), b"abc".to_vec()), (unit, b"def".to_vec()),]
        );
    }

    #[test]
    fn test_write_coff_comments() {
        assert!(write_coff_comments(&[]).unwrap().is_none());

        let out =
            write_coff_comments(&[b"Intel(R) foo".as_slice(), b"bar".as_slice()]).unwrap().unwrap();
        let file = object::File::parse(&*out).unwrap();
        let sections: Vec<_> = file.sections().collect();
        assert_eq!(sections.len(), 1);
        assert_eq!(sections[0].name().unwrap(), ".drectve");
        assert_eq!(sections[0].kind(), object::SectionKind::Linker);
        assert_eq!(sections[0].data().unwrap(), br#"-?comment:"Intel(R) foo" -?comment:"bar""#);
    }
}
