use anyhow::Result;
use flagset::Flags as _;
use object::{
    LittleEndian as LE,
    pe::ImageNtHeaders32,
    read::pe::{ImageNtHeaders, ImageThunkData, PeFile32},
};

use crate::obj::{
    ObjInfo, ObjSectionKind, ObjSymbol, ObjSymbolFlagSet, ObjSymbolFlags, ObjSymbolKind,
};

/// Run all PE-metadata–derived symbol detection on `obj` while the raw PE
/// bytes are still available.  Adds:
///   - A proper name for the entry-point function (WinMainCRTStartup etc.)
///   - `__imp__Name` object symbols for every IAT slot
///   - Import-thunk function symbols for every JMP-through-IAT stub in .text
///   - Export symbols for every PE export directory entry
///   - CRT init/term table boundaries and the constructor/destructor pointers
pub fn detect_pe_symbols(obj: &mut ObjInfo, data: &[u8]) -> Result<()> {
    let Ok(pe) = PeFile32::parse(data) else {
        return Ok(()); // Not a PE32 — nothing to do
    };

    label_entry_point(obj, &pe)?;
    detect_imports(obj, &pe, data)?;
    detect_exports(obj, &pe)?;
    detect_crt_init(obj)?;

    Ok(())
}

// ── Entry point ──────────────────────────────────────────────────────────────

fn label_entry_point(obj: &mut ObjInfo, pe: &PeFile32) -> Result<()> {
    let entry_va = pe.nt_headers().optional_header().address_of_entry_point.get(LE);
    let image_base = pe.nt_headers().optional_header().image_base.get(LE);
    let entry_abs = image_base.wrapping_add(entry_va) as u64;

    // Choose the standard MSVC CRT startup name. Names carry the i386 cdecl/
    // stdcall decoration (leading '_', '@N' suffix) so they match both the
    // bundled signatures and the symbol the linker resolves for /ENTRY.
    let characteristics = pe.nt_headers().file_header().characteristics.get(LE);
    let is_dll = characteristics & object::pe::IMAGE_FILE_DLL != 0;
    let subsystem = pe.nt_headers().optional_header().subsystem.get(LE);
    let entry_name = if is_dll {
        "__DllMainCRTStartup@12"
    } else {
        match subsystem {
            2 => "_WinMainCRTStartup", // IMAGE_SUBSYSTEM_WINDOWS_GUI
            3 => "_mainCRTStartup",    // IMAGE_SUBSYSTEM_WINDOWS_CUI
            _ => "_CRTStartup",
        }
    };

    let Some((sec_idx, _)) =
        obj.sections.iter().find(|(_, s)| entry_abs >= s.address && entry_abs < s.address + s.size)
    else {
        return Ok(());
    };

    // Only add if no symbol already exists at this address.
    if obj.symbols.at_section_address(sec_idx, entry_abs as u32).next().is_none() {
        obj.symbols.add_direct(ObjSymbol {
            name: entry_name.to_string(),
            address: entry_abs,
            section: Some(sec_idx),
            kind: ObjSymbolKind::Function,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::none()),
            ..Default::default()
        })?;
        log::debug!("PE: entry point labelled {entry_name} @ {entry_abs:#010X}");
    }
    Ok(())
}

// ── Import table ─────────────────────────────────────────────────────────────

fn detect_imports(obj: &mut ObjInfo, pe: &PeFile32, _data: &[u8]) -> Result<()> {
    let image_base = pe.nt_headers().optional_header().image_base.get(LE) as u64;

    let Ok(Some(import_table)) = pe.import_table() else {
        return Ok(());
    };

    let mut iat_symbols: Vec<(u64, String)> = Vec::new(); // (abs_va, imp_name)

    let mut desc_iter = import_table.descriptors()?;
    while let Ok(Some(desc)) = desc_iter.next() {
        let first_thunk_rva = desc.first_thunk.get(LE);
        if first_thunk_rva == 0 {
            continue;
        }

        // Prefer the OriginalFirstThunk (INT) for names; fall back to FirstThunk.
        let lookup_rva = {
            let oft = desc.original_first_thunk.get(LE);
            if oft != 0 { oft } else { first_thunk_rva }
        };

        let Ok(mut thunk_iter) = import_table.thunks(lookup_rva) else {
            continue;
        };
        let mut iat_off = 0u32;

        while let Ok(Some(thunk)) = thunk_iter.next::<ImageNtHeaders32>() {
            let iat_va = image_base + first_thunk_rva as u64 + iat_off as u64;
            let raw = thunk.raw() as u32;
            let sym_name = if raw & 0x8000_0000 != 0 {
                // Ordinal import — name it by ordinal
                let ordinal = raw & 0x7FFF_FFFF;
                let dll_name = import_table
                    .name(desc.name.get(LE))
                    .ok()
                    .and_then(|n| std::str::from_utf8(n).ok())
                    .unwrap_or("unknown")
                    .trim_end_matches('\0')
                    .to_ascii_uppercase();
                let dll_stem = dll_name.trim_end_matches(".DLL");
                format!("__imp__{}_{}", dll_stem, ordinal)
            } else {
                // Named import
                match import_table.hint_name(raw & 0x7FFF_FFFF) {
                    Ok((_hint, name)) => {
                        let n =
                            std::str::from_utf8(name).unwrap_or("unknown").trim_end_matches('\0');
                        // MSVC IAT name convention: '__imp_' + decorated name.
                        // Cdecl/stdcall C names already carry a leading '_' (so
                        // the result is '__imp__Foo'); C++ mangled ('?...') and
                        // fastcall ('@...') names do not, yielding '__imp_?foo'
                        // or '__imp_@foo@8' with a single underscore.
                        if n.starts_with('?') || n.starts_with('@') {
                            format!("__imp_{}", n)
                        } else {
                            format!("__imp__{}", n)
                        }
                    }
                    Err(_) => {
                        iat_off += 4;
                        continue;
                    }
                }
            };

            iat_symbols.push((iat_va, sym_name));
            iat_off += 4;
        }
    }

    // Add IAT slot symbols (type:object, size 4).
    let mut imp_count = 0u32;
    let mut thunk_count = 0u32;
    for (iat_va, name) in &iat_symbols {
        let Some((sec_idx, _)) =
            obj.sections.iter().find(|(_, s)| *iat_va >= s.address && *iat_va < s.address + s.size)
        else {
            continue;
        };
        if obj.symbols.at_section_address(sec_idx, *iat_va as u32).next().is_some() {
            continue;
        }
        obj.symbols.add_direct(ObjSymbol {
            name: name.clone(),
            address: *iat_va,
            section: Some(sec_idx),
            size: 4,
            size_known: true,
            kind: ObjSymbolKind::Object,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::none()),
            ..Default::default()
        })?;
        imp_count += 1;
    }

    // Find JMP-through-IAT thunk stubs in .text.
    // Pattern: FF 25 <iat_va_le32>  (JMP DWORD PTR [__imp__Foo])
    let iat_map: std::collections::HashMap<u32, &str> =
        iat_symbols.iter().map(|(va, n)| (*va as u32, n.as_str())).collect();

    // Pre-build a set of already-used symbol names so duplicate thunks don't collide.
    let mut used_names: std::collections::HashSet<String> =
        obj.symbols.iter().map(|(_, s)| s.name.clone()).collect();

    for (sec_idx, sec) in obj.sections.iter().filter(|(_, s)| s.kind == ObjSectionKind::Code) {
        let base = sec.address as u32;
        let d = &sec.data;

        // The byte scan below cannot tell a linker-emitted import thunk from a
        // `jmp dword ptr [__imp__Foo]` tail call sitting in the middle of a real
        // function — both are the same six bytes. Collect the candidate offsets
        // first so each one can be judged by what precedes it.
        let candidates: std::collections::BTreeSet<usize> = (0..d.len().saturating_sub(5))
            .filter(|&i| {
                d[i] == 0xFF
                    && d[i + 1] == 0x25
                    && iat_map.contains_key(&u32::from_le_bytes(
                        d[i + 2..i + 6].try_into().unwrap(),
                    ))
            })
            .collect();

        // A real thunk either sits in a run — the linker emits them packed six
        // bytes apart, so a neighbour on either side is enough — or stands alone
        // and is reached only after whatever ended the previous function: NOP or
        // INT3 padding, or the RET itself when the linker left no gap. A tail
        // call is preceded by the instruction that set up its arguments
        // (`mov ecx, <this>` and friends), so it matches neither.
        //
        // Zero bytes are deliberately not treated as padding: an immediate
        // operand ending in 0x00 is exactly what precedes a typical tail call.
        let is_thunk = |i: usize| -> bool {
            let in_run = (i >= 6 && candidates.contains(&(i - 6))) || candidates.contains(&(i + 6));
            let after_gap = matches!(i.checked_sub(1).map(|p| d[p]), Some(0x90 | 0xCC | 0xC3));
            in_run || after_gap
        };

        let mut i = 0usize;
        while i + 6 <= d.len() {
            if d[i] == 0xFF && d[i + 1] == 0x25 {
                let target = u32::from_le_bytes(d[i + 2..i + 6].try_into().unwrap());
                if let Some(imp_name) = iat_map.get(&target) {
                    let thunk_va = base + i as u32;
                    if obj.symbols.at_section_address(sec_idx, thunk_va).next().is_some()
                        || !is_thunk(i)
                    {
                        i += 1;
                        continue;
                    }
                    // Derive thunk name from IAT symbol:
                    //   "__imp__SetWindowPos" → "_SetWindowPos"   (cdecl: drop one '_')
                    //   "__imp_?foo@@YAXXZ"   → "?foo@@YAXXZ"     (MSVC C++: drop '__imp_')
                    //   "__imp_@foo@8"        → "@foo@8"          (fastcall: drop '__imp_')
                    let preferred = if let Some(rest) = imp_name.strip_prefix("__imp_") {
                        // `rest` is the decorated thunk name as MSVC writes it:
                        // for cdecl it still starts with '_' (the original C prefix);
                        // for '?'/'@' it is the bare mangled name.
                        rest.to_string()
                    } else {
                        imp_name.to_string()
                    };
                    // If the preferred name is already taken (e.g. two thunks for the same
                    // import), fall back to a generated name so there's no duplicate symbol.
                    let thunk_name = if used_names.contains(&preferred) {
                        log::warn!(
                            "PE thunk {thunk_va:#010X}: name '{preferred}' already in use, \
                             using generated name"
                        );
                        format!("fn_{thunk_va:#010x}")
                    } else {
                        preferred
                    };
                    used_names.insert(thunk_name.clone());
                    obj.symbols.add_direct(ObjSymbol {
                        name: thunk_name,
                        address: thunk_va as u64,
                        section: Some(sec_idx),
                        size: 6,
                        size_known: true,
                        kind: ObjSymbolKind::Function,
                        flags: ObjSymbolFlagSet(ObjSymbolFlags::none()),
                        ..Default::default()
                    })?;
                    thunk_count += 1;
                }
            }
            i += 1;
        }
    }

    log::info!("PE imports: {imp_count} IAT symbols, {thunk_count} thunk stubs");
    Ok(())
}

// ── Export table ─────────────────────────────────────────────────────────────

fn detect_exports(obj: &mut ObjInfo, pe: &PeFile32) -> Result<()> {
    let Ok(Some(export_table)) = pe.export_table() else {
        return Ok(());
    };
    let image_base = pe.nt_headers().optional_header().image_base.get(LE) as u64;

    use object::read::pe::ExportTarget;

    let mut count = 0u32;
    for export in export_table.exports()?.iter() {
        let Some(name_bytes) = export.name else { continue };
        let Ok(name) = std::str::from_utf8(name_bytes) else { continue };
        let name = name.trim_end_matches('\0');
        if name.is_empty() {
            continue;
        }

        let abs_va = match export.target {
            ExportTarget::Address(rva) => image_base + rva as u64,
            _ => continue, // skip forwarders
        };

        let Some((sec_idx, _)) =
            obj.sections.iter().find(|(_, s)| abs_va >= s.address && abs_va < s.address + s.size)
        else {
            continue;
        };

        if obj.symbols.at_section_address(sec_idx, abs_va as u32).next().is_some() {
            continue;
        }

        let kind = if obj.sections[sec_idx].kind == ObjSectionKind::Code {
            ObjSymbolKind::Function
        } else {
            ObjSymbolKind::Object
        };

        obj.symbols.add_direct(ObjSymbol {
            name: name.to_string(),
            address: abs_va,
            section: Some(sec_idx),
            kind,
            flags: ObjSymbolFlagSet(ObjSymbolFlags::none()),
            ..Default::default()
        })?;
        count += 1;
    }

    if count > 0 {
        log::info!("PE exports: {count} symbols");
    }
    Ok(())
}

// ── CRT init / term tables ────────────────────────────────────────────────────
//
// MSVC links C initializers (`_initterm(__xi_a, __xi_z)`) and C++ constructors
// (`_initterm(__xc_a, __xc_z)`) from the CRT startup.  In the linked PE the
// tables look like:
//
//   __xi_a / __xc_a:  dd 0          ← null sentinel at start
//                     dd fn_ptr...  ← one non-null code pointer per TU
//   __xi_z / __xc_z:  dd 0          ← null sentinel at end
//
// Detection strategy:
//   Scan every non-code, non-BSS section for runs of the form:
//     null, (null | code-ptr)+, null
//   with at least one non-null code pointer and at most 4096 entries total.
//   The null sentinels at both ends are the MSVC-specific distinguishing
//   feature that separates these from ordinary function-pointer arrays
//   (vtables, dispatch tables, etc.).

fn detect_crt_init(obj: &mut ObjInfo) -> Result<()> {
    // Collect code section VA ranges for pointer validation.
    let code_ranges: Vec<(u64, u64)> = obj
        .sections
        .iter()
        .filter(|(_, s)| s.kind == ObjSectionKind::Code)
        .map(|(_, s)| (s.address, s.address + s.size))
        .collect();

    let is_code_va = |va: u32| -> bool {
        let va = va as u64;
        code_ranges.iter().any(|&(lo, hi)| va >= lo && va < hi)
    };

    // Snapshot data sections.
    let data_secs: Vec<(usize, u64, Vec<u8>)> = obj
        .sections
        .iter()
        .filter(|(_, s)| {
            !matches!(s.kind, ObjSectionKind::Code | ObjSectionKind::Bss) && !s.data.is_empty()
        })
        .map(|(idx, s)| (idx as usize, s.address, s.data.clone()))
        .collect();

    const MAX_TABLE_ENTRIES: usize = 4096;

    let mut table_count = 0u32;
    let mut fn_count = 0u32;

    for (_sec_idx, base, data) in &data_secs {
        let base = *base as u32;
        let mut i = 0usize;

        while i + 8 <= data.len() {
            // CRT init tables begin with a null sentinel.
            let first = u32::from_le_bytes(data[i..i + 4].try_into().unwrap());
            if first != 0 {
                i += 4;
                continue;
            }

            // Extend the run while every entry is null or a code pointer.
            let run_start = i;
            let mut has_nonnull = false;
            let mut j = i + 4;
            while j + 4 <= data.len() && (j - run_start) / 4 < MAX_TABLE_ENTRIES {
                let v = u32::from_le_bytes(data[j..j + 4].try_into().unwrap());
                if v == 0 {
                    // A null entry is fine — keep extending; we'll verify
                    // the trailing sentinel below.
                    j += 4;
                    continue;
                }
                if !is_code_va(v) {
                    break;
                }
                has_nonnull = true;
                j += 4;
            }

            // The run must end with a null sentinel (the __xi_z / __xc_z slot).
            // `j` already points one past the last consumed byte.  The last
            // entry in [run_start..j) is at j-4.
            let run_len = (j - run_start) / 4;
            let last_entry = if run_len >= 2 {
                u32::from_le_bytes(data[j - 4..j].try_into().unwrap())
            } else {
                1 // non-zero → will fail check below
            };

            if run_len >= 3 && has_nonnull && last_entry == 0 {
                let table_va = base + run_start as u32;
                table_count += 1;
                // Count non-null entries for the log message.
                for k in (run_start..j).step_by(4) {
                    let fn_va = u32::from_le_bytes(data[k..k + 4].try_into().unwrap());
                    if fn_va != 0 {
                        fn_count += 1;
                    }
                }
                log::debug!(
                    "PE CRT: table @ {:#010X}, {} entries ({} non-null)",
                    table_va,
                    run_len,
                    fn_count,
                );
                // Do NOT add Function symbols here — they will be discovered
                // naturally by the x86 phase-2 data sweep, which preserves the
                // call-graph–derived link order and avoids cyclic dependencies.
            }

            i = j.max(i + 4);
        }
    }

    if table_count > 0 {
        log::info!(
            "PE CRT: {table_count} init/term table(s) found, {fn_count} constructor/destructor \
             function(s) labelled"
        );
    }
    Ok(())
}
