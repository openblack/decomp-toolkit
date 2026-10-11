//! Regenerate a PE image's import tables with the linker.
//!
//! The original import directory is read back into a short-import library (one
//! member per imported function, carrying the original hint and imported name)
//! and an order file recording how link.exe laid the tables out, which a
//! vc6-aware lld-link (`/vc6imports:`) reproduces.

use std::{collections::HashMap, fmt::Write as _};

use anyhow::{Result, bail};
use object::{LittleEndian as LE, read::pe::PeFile32};

use crate::obj::ObjInfo;

/// A function imported through the import directory.
#[derive(Debug, Clone)]
pub struct PeImport {
    /// Virtual address of the function's IAT slot.
    pub slot: u32,
    /// Imported by name (with its hint) or by ordinal.
    pub name: PeImportName,
    /// Virtual address of the hint/name entry, if imported by name.
    pub hint_name: Option<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PeImportName {
    Name { hint: u16, name: String },
    Ordinal(u16),
}

/// One import descriptor: a DLL and the functions imported from it.
#[derive(Debug, Clone)]
pub struct PeImportDll {
    pub name: String,
    /// Virtual address of the DLL name string.
    pub name_address: u32,
    /// Virtual address of the DLL's lookup table.
    pub lookup: u32,
    pub functions: Vec<PeImport>,
}

/// The import directory, descriptors in their original order.
#[derive(Debug, Clone, Default)]
pub struct PeImports {
    pub dlls: Vec<PeImportDll>,
}

pub fn parse_imports(pe: &PeFile32, image_base: u32) -> Option<PeImports> {
    let directory = pe.data_directories().get(object::pe::IMAGE_DIRECTORY_ENTRY_IMPORT)?;
    if directory.virtual_address.get(LE) == 0 {
        return None;
    }
    let sections = pe.section_table();
    let data = pe.data();
    let read = |rva: u32, len: usize| -> Option<&[u8]> {
        let (offset, size) = sections.pe_file_range_at(rva)?;
        (len <= size as usize).then(|| data.get(offset as usize..offset as usize + len)).flatten()
    };
    let u32_at = |rva: u32| read(rva, 4).map(|b| u32::from_le_bytes(b.try_into().unwrap()));
    let c_string = |rva: u32| -> Option<String> {
        let (offset, size) = sections.pe_file_range_at(rva)?;
        let bytes = data.get(offset as usize..offset as usize + size as usize)?;
        let end = bytes.iter().position(|&b| b == 0)?;
        Some(String::from_utf8_lossy(&bytes[..end]).into_owned())
    };

    let mut dlls = Vec::new();
    let mut descriptor = directory.virtual_address.get(LE);
    loop {
        let lookup = u32_at(descriptor)?;
        let name = u32_at(descriptor + 12)?;
        let iat = u32_at(descriptor + 16)?;
        if lookup == 0 && name == 0 && iat == 0 {
            break;
        }
        let mut functions = Vec::new();
        let table = if lookup != 0 { lookup } else { iat };
        let mut index = 0;
        loop {
            let entry = u32_at(table + index * 4)?;
            if entry == 0 {
                break;
            }
            let slot = image_base.wrapping_add(iat + index * 4);
            if entry & 0x8000_0000 != 0 {
                let ordinal = (entry & 0xFFFF) as u16;
                functions.push(PeImport { slot, name: PeImportName::Ordinal(ordinal), hint_name: None });
            } else {
                let hint = u16::from_le_bytes(read(entry, 2)?.try_into().unwrap());
                let name = c_string(entry + 2)?;
                functions.push(PeImport {
                    slot,
                    name: PeImportName::Name { hint, name },
                    hint_name: Some(image_base.wrapping_add(entry)),
                });
            }
            index += 1;
        }
        dlls.push(PeImportDll {
            name: c_string(name)?,
            name_address: image_base.wrapping_add(name),
            lookup: image_base.wrapping_add(table),
            functions,
        });
        descriptor += 20;
    }
    Some(PeImports { dlls })
}

/// The symbol each import's IAT slot is known by (`__imp_` + the member's
/// symbol name), from the image's symbols.
pub fn slot_symbols(obj: &ObjInfo, imports: &PeImports) -> Result<HashMap<u32, String>> {
    let mut names = HashMap::new();
    let mut missing = Vec::new();
    for function in imports.dlls.iter().flat_map(|d| &d.functions) {
        let name = obj.sections.at_address(function.slot).ok().and_then(|(section_index, _)| {
            obj.symbols
                .at_section_address(section_index, function.slot)
                .find(|(_, s)| s.name.starts_with("__imp_"))
                .map(|(_, s)| s.name.clone())
        });
        match name {
            Some(name) => {
                names.insert(function.slot, name);
            }
            None => missing.push(function.slot),
        }
    }
    if let Some(slot) = missing.first() {
        bail!("{} IAT slot(s) have no __imp_ symbol, e.g. {slot:#010X}", missing.len());
    }
    Ok(names)
}

/// A short-format import object (`IMPORT_OBJECT_HEADER` + strings). Every
/// import is DATA, so the linker only defines `__imp_<symbol>`: the image's
/// own `jmp [__imp_X]` stubs come from the split objects.
fn import_object(symbol: &str, dll: &str, name: &PeImportName) -> Vec<u8> {
    const IMPORT_OBJECT_DATA: u16 = 1;
    const IMPORT_OBJECT_ORDINAL: u16 = 0;
    const IMPORT_OBJECT_NAME_EXPORTAS: u16 = 4;
    let mut strings = Vec::new();
    strings.extend_from_slice(symbol.as_bytes());
    strings.push(0);
    strings.extend_from_slice(dll.as_bytes());
    strings.push(0);
    let (hint, name_type) = match name {
        PeImportName::Name { hint, name } => {
            strings.extend_from_slice(name.as_bytes());
            strings.push(0);
            (*hint, IMPORT_OBJECT_NAME_EXPORTAS)
        }
        PeImportName::Ordinal(ordinal) => (*ordinal, IMPORT_OBJECT_ORDINAL),
    };
    let mut out = Vec::with_capacity(20 + strings.len());
    out.extend_from_slice(&0u16.to_le_bytes()); // Sig1
    out.extend_from_slice(&0xFFFFu16.to_le_bytes()); // Sig2
    out.extend_from_slice(&0u16.to_le_bytes()); // Version
    out.extend_from_slice(&object::pe::IMAGE_FILE_MACHINE_I386.to_le_bytes());
    out.extend_from_slice(&0u32.to_le_bytes()); // TimeDateStamp
    out.extend_from_slice(&(strings.len() as u32).to_le_bytes());
    out.extend_from_slice(&hint.to_le_bytes());
    out.extend_from_slice(&(IMPORT_OBJECT_DATA | name_type << 2).to_le_bytes());
    out.extend_from_slice(&strings);
    out
}

fn archive_member_header(out: &mut Vec<u8>, name: &str, size: usize) {
    out.extend_from_slice(format!("{name:<16}{:<12}{:<6}{:<6}{:<8}{size:<10}`\n", 0, 0, 0, 644).as_bytes());
}

/// A COFF archive of short-format import objects, one per imported function.
pub fn write_import_library(imports: &PeImports, symbols: &HashMap<u32, String>) -> Vec<u8> {
    let mut members = Vec::new();
    for dll in &imports.dlls {
        for function in &dll.functions {
            let imp = &symbols[&function.slot];
            let symbol = imp.strip_prefix("__imp_").unwrap_or(imp);
            members.push((imp.clone(), import_object(symbol, &dll.name, &function.name)));
        }
    }

    // First linker member: big-endian member count, member offsets, then the
    // NUL-terminated symbol names in the same order.
    let mut names = Vec::new();
    for (imp, _) in &members {
        names.extend_from_slice(imp.as_bytes());
        names.push(0);
    }
    let symtab_size = 4 + 4 * members.len() + names.len();
    let mut offset = 8 + 60 + symtab_size + symtab_size % 2;
    let mut offsets = Vec::with_capacity(members.len());
    for (_, data) in &members {
        offsets.push(offset as u32);
        offset += 60 + data.len() + data.len() % 2;
    }

    let mut out = b"!<arch>\n".to_vec();
    archive_member_header(&mut out, "/", symtab_size);
    out.extend_from_slice(&(members.len() as u32).to_be_bytes());
    for offset in &offsets {
        out.extend_from_slice(&offset.to_be_bytes());
    }
    out.extend_from_slice(&names);
    if symtab_size % 2 != 0 {
        out.push(b'\n');
    }
    for (_, data) in &members {
        archive_member_header(&mut out, "import/", data.len());
        out.extend_from_slice(data);
        if data.len() % 2 != 0 {
            out.push(b'\n');
        }
    }
    out
}

/// The layout link.exe gave the tables, for lld-link's `/vc6imports:`:
/// - `descriptor <dll>`: import descriptors, in order;
/// - `slot <__imp_symbol>`: IAT (and lookup table) entries, in order, a DLL's
///   entries together;
/// - `hintname <__imp_symbol>` / `dllname <dll>`: the hint/name area, in
///   address order;
/// - `pad <dll> <lookups> <addresses>`: zero padding after the DLL's lookup
///   table and IAT entries. An incremental link leaves it when the tables run
///   on into each other; past the end of the IAT it is whatever the splits'
///   `.idata$5` section (`iat_section_end`) covers beyond the last entry.
pub fn write_import_order(
    imports: &PeImports,
    symbols: &HashMap<u32, String>,
    iat_section_end: Option<u32>,
) -> Result<String> {
    let mut out = String::new();
    for dll in &imports.dlls {
        let _ = writeln!(out, "descriptor {}", dll.name);
    }
    let mut slots: Vec<&PeImport> = imports.dlls.iter().flat_map(|d| &d.functions).collect();
    slots.sort_by_key(|f| f.slot);
    for function in slots {
        let _ = writeln!(out, "slot {}", symbols[&function.slot]);
    }
    let mut names: Vec<(u32, String)> = Vec::new();
    for dll in &imports.dlls {
        names.push((dll.name_address, format!("dllname {}", dll.name)));
        for function in &dll.functions {
            if let Some(address) = function.hint_name {
                names.push((address, format!("hintname {}", symbols[&function.slot])));
            }
        }
    }
    names.sort_by_key(|(address, _)| *address);
    let names_start = names.first().map(|(address, _)| *address);
    for (_, line) in names {
        let _ = writeln!(out, "{line}");
    }

    // Each DLL's lookup table and IAT entries end with a null entry. Whatever
    // lies between that and the next DLL's entries (or, after the last DLL,
    // the IAT and the hint/name area) is padding.
    const MAX_PAD: u32 = 0x1000;
    let mut groups: Vec<(&PeImportDll, u32, u32)> = imports
        .dlls
        .iter()
        .filter_map(|d| {
            let count = d.functions.len() as u32 + 1;
            d.functions.first().map(|f| (d, d.lookup + 4 * count, f.slot + 4 * count))
        })
        .collect();
    groups.sort_by_key(|(_, _, iat_end)| *iat_end);
    let iat_start = groups.iter().filter_map(|(d, _, _)| d.functions.first()).map(|f| f.slot).min();
    for (i, &(dll, lookups_end, iat_end)) in groups.iter().enumerate() {
        let (next_lookup, next_slot) = match groups.get(i + 1) {
            Some((next, _, _)) => (Some(next.lookup), next.functions.first().map(|f| f.slot)),
            None => (iat_start, names_start),
        };
        let gap = |end: u32, next: Option<u32>| match next {
            Some(next) if next > end && next - end < MAX_PAD => next - end,
            _ => 0,
        };
        let (lookups_pad, mut iat_pad) = (gap(lookups_end, next_lookup), gap(iat_end, next_slot));
        if i + 1 == groups.len() && iat_pad == 0 {
            iat_pad = gap(iat_end, iat_section_end);
        }
        if lookups_pad != 0 || iat_pad != 0 {
            if i + 1 < groups.len() && lookups_pad != iat_pad {
                bail!("{}: lookup table and IAT padding differ ({lookups_pad:#x}, {iat_pad:#x})", dll.name);
            }
            let _ = writeln!(out, "pad {} {lookups_pad} {iat_pad}", dll.name);
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn import(slot: u32, hint: u16, name: &str, hint_name: u32) -> PeImport {
        PeImport {
            slot,
            name: PeImportName::Name { hint, name: name.to_string() },
            hint_name: Some(hint_name),
        }
    }

    /// KERNEL32 then USER32 in the descriptors, but USER32's slots first; one
    /// ordinal import.
    fn imports() -> (PeImports, HashMap<u32, String>) {
        let imports = PeImports {
            dlls: vec![
                PeImportDll {
                    name: "KERNEL32.dll".to_string(),
                    name_address: 0x3010,
                    lookup: 0x2008,
                    functions: vec![
                        import(0x1008, 7, "CloseHandle", 0x3000),
                        PeImport { slot: 0x100C, name: PeImportName::Ordinal(42), hint_name: None },
                    ],
                },
                PeImportDll {
                    name: "USER32.dll".to_string(),
                    name_address: 0x3030,
                    lookup: 0x2000,
                    functions: vec![import(0x1000, 3, "MessageBoxA", 0x3020)],
                },
            ],
        };
        let symbols = HashMap::from([
            (0x1008, "__imp__CloseHandle@4".to_string()),
            (0x100C, "__imp__Ordinal42".to_string()),
            (0x1000, "__imp__MessageBoxA@16".to_string()),
        ]);
        (imports, symbols)
    }

    #[test]
    fn writes_short_import_objects() {
        let name = PeImportName::Name { hint: 0x1234, name: "CloseHandle".to_string() };
        let object = import_object("_CloseHandle@4", "KERNEL32.dll", &name);
        assert_eq!(&object[..4], &[0, 0, 0xFF, 0xFF]);
        assert_eq!(u16::from_le_bytes([object[6], object[7]]), 0x14C);
        assert_eq!(u16::from_le_bytes([object[16], object[17]]), 0x1234);
        // IMPORT_OBJECT_DATA, IMPORT_OBJECT_NAME_EXPORTAS
        assert_eq!(u16::from_le_bytes([object[18], object[19]]), 1 | 4 << 2);
        assert_eq!(&object[20..], b"_CloseHandle@4\0KERNEL32.dll\0CloseHandle\0");
        assert_eq!(u32::from_le_bytes(object[12..16].try_into().unwrap()) as usize, object.len() - 20);

        let object = import_object("_Ordinal42", "KERNEL32.dll", &PeImportName::Ordinal(42));
        assert_eq!(u16::from_le_bytes([object[16], object[17]]), 42);
        assert_eq!(u16::from_le_bytes([object[18], object[19]]), 1); // IMPORT_OBJECT_ORDINAL
        assert_eq!(&object[20..], b"_Ordinal42\0KERNEL32.dll\0");
    }

    #[test]
    fn writes_an_import_library() {
        let (imports, symbols) = imports();
        let library = write_import_library(&imports, &symbols);
        let archive = object::read::archive::ArchiveFile::parse(library.as_slice()).unwrap();
        let members: Vec<_> = archive.members().map(|m| m.unwrap()).collect();
        assert_eq!(members.len(), 3);
        let symbols: Vec<_> = archive
            .symbols()
            .unwrap()
            .unwrap()
            .map(|s| {
                let s = s.unwrap();
                (std::str::from_utf8(s.name()).unwrap().to_string(), s.offset().0)
            })
            .collect();
        let names: Vec<_> = symbols.iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(names, ["__imp__CloseHandle@4", "__imp__Ordinal42", "__imp__MessageBoxA@16"]);
        // Each symbol points at its member's header.
        for ((_, offset), member) in symbols.iter().zip(&members) {
            let data = member.data(library.as_slice()).unwrap();
            let start = data.as_ptr() as usize - library.as_ptr() as usize;
            assert_eq!(*offset as usize + 60, start);
        }
    }

    #[test]
    fn writes_the_import_order() {
        let (imports, symbols) = imports();
        let order = write_import_order(&imports, &symbols, None).unwrap();
        assert_eq!(
            order,
            "descriptor KERNEL32.dll\ndescriptor USER32.dll\n\
             slot __imp__MessageBoxA@16\nslot __imp__CloseHandle@4\nslot __imp__Ordinal42\n\
             hintname __imp__CloseHandle@4\ndllname KERNEL32.dll\n\
             hintname __imp__MessageBoxA@16\ndllname USER32.dll\n"
        );
        // An IAT section running past the last entry pads it.
        let order = write_import_order(&imports, &symbols, Some(0x1020)).unwrap();
        assert!(order.ends_with("pad KERNEL32.dll 0 12\n"), "{order}");
    }

    #[test]
    fn writes_incremental_link_padding() {
        let (mut imports, symbols) = imports();
        // Leave 8 bytes after USER32's entries in both tables, as an
        // incremental link does.
        imports.dlls[0].lookup = 0x2010;
        imports.dlls[0].functions[0].slot = 0x1010;
        imports.dlls[0].functions[1].slot = 0x1014;
        let symbols = HashMap::from([
            (0x1010, symbols[&0x1008].clone()),
            (0x1014, symbols[&0x100C].clone()),
            (0x1000, symbols[&0x1000].clone()),
        ]);
        let order = write_import_order(&imports, &symbols, None).unwrap();
        assert!(order.ends_with("pad USER32.dll 8 8\n"), "{order}");
    }
}
