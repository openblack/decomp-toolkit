use std::collections::{BTreeMap, BTreeSet, VecDeque};

use anyhow::Result;
use flagset::Flags as _;
use iced_x86::{Code, Decoder, DecoderOptions, FlowControl, Instruction, Mnemonic, OpKind};

use crate::{
    analysis::cfa::SectionAddress,
    obj::{
        ObjInfo, ObjReloc, ObjRelocKind, ObjSectionKind, ObjSymbol, ObjSymbolFlagSet,
        ObjSymbolFlags, ObjSymbolKind, SectionIndex, SymbolIndex,
    },
};

/// Data produced by [`analyze_x86_functions`] that is needed by the deferred
/// size pass [`compute_x86_function_sizes`].  Keep opaque — callers just
/// thread it through.
pub struct X86FunctionSizeData {
    /// (section, fn_va) → raw (uncapped) instruction-end VA from phase-1 disassembly.
    fn_raw_ends: BTreeMap<(SectionIndex, u32), u32>,
    /// (section, fn_va) → VAs of jump tables referenced by indirect JMPs in that function.
    fn_tables: BTreeMap<(SectionIndex, u32), Vec<u32>>,
    /// Snapshot of code sections (idx, base, data).
    code_snap: Vec<(SectionIndex, u64, Vec<u8>)>,
}

/// Recursively disassemble all reachable code in `obj` starting from every
/// known function entry point, discovering new entries via CALL targets and
/// recording [`ObjRelocKind::X86Rel32`] relocations only for cross-function
/// references (CALLs and tail-call JMPs).
///
/// Within-function branches (Jcc, internal JMP) are followed for control-flow
/// coverage but produce no relocations and no label symbols — their relative
/// displacements are self-contained within the same output `.obj`.
///
/// A second pass scans all non-code sections for 4-byte-aligned pointer slots
/// whose values point into `.text`. Candidates are accepted only if they were
/// not already decoded as interior (non-entry) instruction addresses in phase 1,
/// and if they decode as a valid instruction.
///
/// Returns [`X86FunctionSizeData`] that must be passed to
/// [`compute_x86_function_sizes`] **after** all other symbol-discovery passes
/// (e.g. RTTI) have run, so that size caps account for every function entry.
pub fn analyze_x86_functions(obj: &mut ObjInfo) -> Result<X86FunctionSizeData> {
    // Snapshot code sections first so we can resolve VAs to (section, offset) pairs
    // during seeding.  COFF .obj relocatables set all section addresses to 0, so we
    // track (section_index, va) pairs throughout — not bare VAs — to avoid conflating
    // functions that live in different COMDAT sections at the same offset.
    let code_snap: Vec<(SectionIndex, u64, Vec<u8>)> = obj
        .sections
        .iter()
        .filter(|(_, s)| s.kind == ObjSectionKind::Code && !s.data.is_empty())
        .map(|(idx, s)| (idx, s.address, s.data.clone()))
        .collect();

    // Snapshot non-code, non-BSS sections for the function-pointer sweep.
    let data_snap: Vec<(u64, Vec<u8>)> = obj
        .sections
        .iter()
        .filter(|(_, s)| {
            s.kind != ObjSectionKind::Code && s.kind != ObjSectionKind::Bss && !s.data.is_empty()
        })
        .map(|(_, s)| (s.address, s.data.clone()))
        .collect();

    let find_code = |va: u32| -> Option<(SectionIndex, usize)> {
        code_snap.iter().find_map(|(idx, base, data)| {
            let off = (va as u64).checked_sub(*base)? as usize;
            if off < data.len() { Some((*idx, off)) } else { None }
        })
    };

    let snap_for_section = |sec_idx: SectionIndex| -> Option<(u64, &[u8])> {
        code_snap
            .iter()
            .find(|(idx, _, _)| *idx == sec_idx)
            .map(|(_, base, data)| (*base, data.as_slice()))
    };

    // `pending` stores (section_index, va) pairs.  Using the section index as part
    // of the key ensures that two functions in different sections at the same VA
    // (the common case for COFF COMDAT .obj files where every section starts at 0)
    // are treated as distinct worklist entries and both get disassembled.
    let mut pending: BTreeSet<(SectionIndex, u32)> = BTreeSet::new();

    let enqueue = |key: (SectionIndex, u32), pending: &mut BTreeSet<(SectionIndex, u32)>| {
        pending.insert(key);
    };

    // Seed worklist: PE entry point + any Function symbols already known.
    if let Some(entry_va) = obj.entry {
        if let Some((sec_idx, _)) = find_code(entry_va as u32) {
            enqueue((sec_idx, entry_va as u32), &mut pending);
        }
    }
    for (_, sym) in obj.symbols.iter() {
        if sym.kind == ObjSymbolKind::Function {
            if let Some(sec_idx) = sym.section {
                enqueue((sec_idx, sym.address as u32), &mut pending);
            }
        }
    }

    // Snapshot of pre-existing relocation addresses (from COFF .obj loading).
    // Keyed by (section, va) so that two sections at offset 0 don't share entries.
    // For Relocatable objects, displacement bytes at these sites are unresolved
    // placeholders — the computed branch targets must not be trusted.
    let coff_reloc_sites: BTreeSet<(SectionIndex, u32)> =
        if obj.kind == crate::obj::ObjKind::Relocatable {
            obj.sections
                .iter()
                .filter(|(_, s)| s.kind == ObjSectionKind::Code)
                .flat_map(|(sec_idx, s)| s.relocations.iter().map(move |(addr, _)| (sec_idx, addr)))
                .collect()
        } else {
            BTreeSet::new()
        };

    // Instruction spans decoded in phase 1: (section, start_va) → exclusive end VA.
    // Keyed by section so spans from one section don't shadow another section's
    // addresses at the same offset.
    let mut decoded_spans: BTreeMap<(SectionIndex, u32), u32> = BTreeMap::new();

    // Uncapped function sizes: (section, fn_va) → raw instruction-end VA.
    // Capping against the next function start is deferred to
    // compute_x86_function_sizes, which runs after RTTI adds its own entries.
    let mut fn_raw_ends: BTreeMap<(SectionIndex, u32), u32> = BTreeMap::new();
    // Jump-table VAs per function for the deferred size pass.
    let mut fn_tables: BTreeMap<(SectionIndex, u32), Vec<u32>> = BTreeMap::new();

    let mut fn_new_count = 0u32;
    let mut rel_count = 0u32;
    let mut data_scanned = false;

    loop {
        if let Some((fn_sec_idx, fn_va)) = pending.pop_first() {
            // A phase-2 candidate may have been enqueued before we knew its
            // address fell inside another function's instruction span.  Skip it
            // now that decoded_spans is more complete.
            if is_within_decoded_span(fn_sec_idx, fn_va, &decoded_spans) {
                continue;
            }

            // Likewise skip an address that falls strictly inside the body of a
            // size-known function (e.g. a data-section pointer into the middle of
            // a known function). Minting a sub-entry here would split that
            // function and conflict with its declared size.
            if inside_known_function(obj, fn_sec_idx, fn_va) {
                continue;
            }

            // Ensure a Function symbol exists at this entry.
            if obj
                .symbols
                .kind_at_section_address(fn_sec_idx, fn_va, ObjSymbolKind::Function)?
                .is_none()
            {
                obj.symbols.add_direct(ObjSymbol {
                    name: format!("fn_{:08X}", fn_va),
                    address: fn_va as u64,
                    section: Some(fn_sec_idx),
                    kind: ObjSymbolKind::Function,
                    flags: ObjSymbolFlagSet(ObjSymbolFlags::none()),
                    ..Default::default()
                })?;
                fn_new_count += 1;
            }

            // Hoist the section data lookup for this function so that all instruction
            // decoding uses fn_sec_idx's bytes — not whichever section find_code(pc)
            // happens to return first (which can be the wrong section when multiple
            // COMDAT sections share the same base VA of 0).
            let (fn_base, fn_data) = match snap_for_section(fn_sec_idx) {
                Some(v) => v,
                None => continue,
            };

            // Recursively disassemble the function body.
            let mut visited: BTreeSet<u32> = BTreeSet::new();
            let mut flow: VecDeque<u32> = VecDeque::new();
            // VAs of jump tables referenced by indirect JMPs in this function.
            // Used after the loop to extend the function's size over embedded tables.
            let mut potential_tables: Vec<u32> = Vec::new();
            flow.push_back(fn_va);

            while let Some(pc) = flow.pop_front() {
                if !visited.insert(pc) {
                    continue;
                }

                // Decode from this function's own section.  Using find_code(pc) would
                // return the wrong section for functions in COMDAT sections that share
                // the same base VA as another section (the COFF .obj case where every
                // section starts at 0).
                let off = match (pc as u64).checked_sub(fn_base).map(|o| o as usize) {
                    Some(o) if o < fn_data.len() => o,
                    _ => continue,
                };
                // sec_idx for this instruction is fn_sec_idx.
                let sec_idx = fn_sec_idx;

                let mut decoder =
                    Decoder::with_ip(32, &fn_data[off..], pc as u64, DecoderOptions::NONE);
                let mut instr = Instruction::default();
                decoder.decode_out(&mut instr);
                if instr.is_invalid() {
                    continue;
                }
                decoded_spans.insert((fn_sec_idx, pc), pc + instr.len() as u32);

                let next_pc = pc + instr.len() as u32;

                match instr.flow_control() {
                    FlowControl::Next => {
                        flow.push_back(next_pc);
                    }

                    FlowControl::ConditionalBranch => {
                        // Both edges continue within the function — no relocation needed.
                        flow.push_back(next_pc);
                        if instr.op0_kind() == OpKind::NearBranch32 {
                            let target = instr.near_branch32();
                            if find_code(target).is_some() {
                                flow.push_back(target);
                            }
                        }
                    }

                    FlowControl::Call => {
                        if instr.op0_kind() == OpKind::NearBranch32 {
                            // For COFF .obj files, the displacement may be an
                            // unresolved placeholder (external symbol). Skip if
                            // the operand sits on a COFF relocation site.
                            let operand_va = if instr.code() == Code::Call_rel32_32 {
                                pc + 1
                            } else {
                                next_pc - 4
                            };
                            let target = instr.near_branch32();
                            if coff_reloc_sites.contains(&(sec_idx, operand_va)) {
                                // Unresolved external — don't trust the displacement.
                                // Still continue to the next instruction.
                                flow.push_back(next_pc);
                                continue;
                            }
                            if let Some((tgt_sec, _)) = find_code(target) {
                                // A CALL whose target lands inside an already-known
                                // function's body is a reference into that function,
                                // not a new entry: don't mint a sub-function or trace
                                // it (the function is traced from its own entry), but
                                // still emit the relocation (resolves to the containing
                                // function + addend).
                                if !inside_known_function(obj, tgt_sec, target) {
                                    // Ensure the callee has a Function symbol now so the
                                    // relocation can reference it directly (no lbl_ needed).
                                    if obj
                                        .symbols
                                        .kind_at_section_address(
                                            tgt_sec,
                                            target,
                                            ObjSymbolKind::Function,
                                        )?
                                        .is_none()
                                    {
                                        obj.symbols.add_direct(ObjSymbol {
                                            name: format!("fn_{:08X}", target),
                                            address: target as u64,
                                            section: Some(tgt_sec),
                                            kind: ObjSymbolKind::Function,
                                            flags: ObjSymbolFlagSet(ObjSymbolFlags::none()),
                                            ..Default::default()
                                        })?;
                                        fn_new_count += 1;
                                    }
                                    enqueue((tgt_sec, target), &mut pending);
                                }
                                add_rel32(
                                    obj,
                                    sec_idx,
                                    operand_va,
                                    tgt_sec,
                                    target,
                                    &mut rel_count,
                                )?;
                            }
                        }
                        flow.push_back(next_pc);
                    }

                    FlowControl::UnconditionalBranch => {
                        if instr.op0_kind() == OpKind::NearBranch32 {
                            let target = instr.near_branch32();
                            // Only 5-byte near JMPs (e9 XX XX XX XX) have a 4-byte
                            // displacement field that needs a DISP32 relocation.
                            // Short JMPs (eb XX, Jmp_rel8_32) have a 1-byte displacement
                            // that is self-contained in the object data — no reloc needed.
                            let is_near32 = instr.code() == Code::Jmp_rel32_32;
                            if is_near32 {
                                let operand_va = next_pc - 4;
                                if coff_reloc_sites.contains(&(sec_idx, operand_va)) {
                                    // Unresolved external — don't follow.
                                    continue;
                                }
                                if let Some((tgt_sec, _)) = find_code(target) {
                                    // Tail call if target already has a Function symbol or is
                                    // pending as one; otherwise treat as within-function JMP.
                                    let is_tail_call = pending.contains(&(tgt_sec, target))
                                        || obj
                                            .symbols
                                            .kind_at_section_address(
                                                tgt_sec,
                                                target,
                                                ObjSymbolKind::Function,
                                            )?
                                            .is_some();
                                    if is_tail_call && inside_known_function(obj, tgt_sec, target)
                                    {
                                        // Tail JMP into the body of a known function:
                                        // emit the reference (resolves to the containing
                                        // function + addend) but don't mint a sub-entry
                                        // or follow it.
                                        add_rel32(
                                            obj,
                                            sec_idx,
                                            operand_va,
                                            tgt_sec,
                                            target,
                                            &mut rel_count,
                                        )?;
                                    } else if is_tail_call {
                                        if obj
                                            .symbols
                                            .kind_at_section_address(
                                                tgt_sec,
                                                target,
                                                ObjSymbolKind::Function,
                                            )?
                                            .is_none()
                                        {
                                            obj.symbols.add_direct(ObjSymbol {
                                                name: format!("fn_{:08X}", target),
                                                address: target as u64,
                                                section: Some(tgt_sec),
                                                kind: ObjSymbolKind::Function,
                                                flags: ObjSymbolFlagSet(ObjSymbolFlags::none()),
                                                ..Default::default()
                                            })?;
                                            fn_new_count += 1;
                                        }
                                        enqueue((tgt_sec, target), &mut pending);
                                        add_rel32(
                                            obj,
                                            sec_idx,
                                            operand_va,
                                            tgt_sec,
                                            target,
                                            &mut rel_count,
                                        )?;
                                    } else {
                                        // Within-function jump — follow without relocation.
                                        flow.push_back(target);
                                    }
                                }
                            } else {
                                // Short JMP (eb XX): no DISP32 reloc; still follow the
                                // target to ensure reachable code is analyzed.
                                if let Some((tgt_sec, _)) = find_code(target) {
                                    let is_tail_call = pending.contains(&(tgt_sec, target))
                                        || obj
                                            .symbols
                                            .kind_at_section_address(
                                                tgt_sec,
                                                target,
                                                ObjSymbolKind::Function,
                                            )?
                                            .is_some();
                                    if is_tail_call {
                                        // Enqueue the function for analysis but do NOT add a
                                        // DISP32 reloc — the 1-byte displacement is baked in.
                                        enqueue((tgt_sec, target), &mut pending);
                                    } else {
                                        flow.push_back(target);
                                    }
                                }
                            }
                        }
                        // Indirect JMP (switch dispatch): record any memory displacement
                        // that points into the same code section as a potential jump table.
                        // Both first-order (JMP [eax*4+table]) and second-order
                        // (MOVZX eax,[idx_table+eax]; JMP [eax*4+target_table]) emit a
                        // displacement here, so one pass covers both.
                        if instr.flow_control() == FlowControl::IndirectBranch
                            && instr.op0_kind() == OpKind::Memory
                            && instr.memory_displacement64() != 0
                        {
                            let disp = instr.memory_displacement64() as u32;
                            if find_code(disp).is_some() {
                                potential_tables.push(disp);
                            }
                        }
                    }

                    FlowControl::Return | FlowControl::Exception | FlowControl::Interrupt => {
                        // End of this path.
                    }

                    FlowControl::IndirectCall
                    | FlowControl::IndirectBranch
                    | FlowControl::XbeginXabortXend => {
                        flow.push_back(next_pc);
                    }
                }
            }

            // Record the raw end and jump tables for the post-pass size computation.
            let raw_end = visited
                .iter()
                .filter_map(|&pc| decoded_spans.get(&(fn_sec_idx, pc)).copied())
                .max()
                .unwrap_or(fn_va);
            if raw_end > fn_va {
                fn_raw_ends.insert((fn_sec_idx, fn_va), raw_end);
            }
            if !potential_tables.is_empty() {
                fn_tables.insert((fn_sec_idx, fn_va), potential_tables);
            }
        } else if !data_scanned {
            // Phase 2: scan non-code sections for 4-byte-aligned pointer slots
            // whose values point into .text (vtables, callback arrays, SEH tables).
            //
            // Acceptance criteria for a candidate target VA:
            //   1. Points into a code section.
            //   2. Not already queued (would be a no-op).
            //   3. Not within any decoded instruction span from phase 1. This
            //      rejects both known function-interior addresses and bytes that
            //      fall inside multi-byte instruction operands (e.g. the rel32
            //      field of a CALL), preventing false splits mid-instruction.
            //   4. Decodes as a valid instruction at that address.
            data_scanned = true;
            let mut ptr_count = 0u32;
            for (_, data) in &data_snap {
                let mut i = 0usize;
                while i + 4 <= data.len() {
                    let va = u32::from_le_bytes(data[i..i + 4].try_into().unwrap());
                    if let Some((sec_idx, _)) = find_code(va) {
                        if !pending.contains(&(sec_idx, va))
                            && !is_within_decoded_span(sec_idx, va, &decoded_spans)
                            && decode_valid(va, &code_snap)
                        {
                            enqueue((sec_idx, va), &mut pending);
                            ptr_count += 1;
                        }
                    }
                    i += 4;
                }
            }
            if ptr_count > 0 {
                log::debug!(
                    "x86 analysis: data-section sweep enqueued {ptr_count} function-pointer \
                     candidates"
                );
            }
            // Loop continues — pending may now be non-empty again.
        } else {
            break;
        }
    }

    // Phase 3: linear sweep of code bytes the flow-based disassembler never
    // entered (un-seeded function bodies, indirect-only blocks). These gaps
    // still contain CALL/JMP rel32 instructions whose displacements were left
    // raw — invisible to the linker's reference graph (`/OPT:REF`).
    //
    // Data-in-code (jump tables, embedded constants in .text) is the false-
    // positive hazard: linear-decoding non-instruction bytes yields garbage
    // that may look like a `call rel32`. Two guards make a bad relocation
    // astronomically unlikely:
    //   1. A relocation is emitted only when the branch target lands *exactly*
    //      on an already-known Function symbol. A coincidental garbage decode
    //      whose displacement happens to hit a real function entry is rare.
    //   2. No new symbols are minted here (unlike phases 1-2): the sweep only
    //      connects existing entries, never invents targets from garbage.
    // The byte-exact link check is the ultimate backstop — any wrong reloc
    // perturbs a displacement and breaks the rebuild.
    {
        let mut sweep_count = 0u32;
        // Snapshot existing function-entry VAs per section so the sweep does
        // not react to entries it would add (it adds none, but keep it pure).
        for (sec_idx, base, data) in &code_snap {
            let sec_idx = *sec_idx;
            let base = *base as u32;
            let sec_end = base + data.len() as u32;
            let mut pc = base;
            while pc < sec_end {
                // If pc is inside an already-decoded span, trust it and skip to
                // its end — those relocations were emitted in phase 1.
                if let Some((&(_s, start), &end)) = decoded_spans
                    .range((
                        std::ops::Bound::Included((sec_idx, 0u32)),
                        std::ops::Bound::Included((sec_idx, pc)),
                    ))
                    .next_back()
                {
                    if start <= pc && pc < end {
                        pc = end;
                        continue;
                    }
                }

                let off = (pc - base) as usize;
                let mut decoder =
                    Decoder::with_ip(32, &data[off..], pc as u64, DecoderOptions::NONE);
                let mut instr = Instruction::default();
                decoder.decode_out(&mut instr);
                if instr.is_invalid() {
                    // Likely data or a misaligned start — resync one byte.
                    pc += 1;
                    continue;
                }
                let ins_len = instr.len() as u32;
                // NOTE: deliberately do not record this span in `decoded_spans`.
                // That map drives function-size capping and the stale-symbol
                // downgrade pass; a speculative linear decode across a gap must
                // not influence either, or it shrinks/merges real functions and
                // explodes downstream diffing. The sweep only *reads* the map to
                // skip flow-decoded regions.

                // Only CALL/JMP with a 4-byte rel32 displacement field carry a
                // cross-unit reference that needs a relocation.
                let is_call = instr.code() == Code::Call_rel32_32;
                let is_jmp = instr.code() == Code::Jmp_rel32_32;
                if (is_call || is_jmp) && instr.op0_kind() == OpKind::NearBranch32 {
                    let target = instr.near_branch32();
                    let operand_va = pc + ins_len - 4; // rel32 is the last 4 bytes
                    if let Some((tgt_sec, _)) = find_code(target) {
                        let already = obj.sections[sec_idx].relocations.at(operand_va).is_some();
                        // Only symbolicate a call to a target that already has a
                        // Function symbol, and whose scope is *not* local. A static
                        // (local-scope) C function is owned by its translation unit
                        // and cannot satisfy a cross-unit external reference — forcing
                        // a symbolic reloc to one would leave the link undefined.
                        // Such call sites stay as raw fixed-address displacements,
                        // exactly as the original linker resolved them.
                        let emit = obj
                            .symbols
                            .kind_at_section_address(tgt_sec, target, ObjSymbolKind::Function)?
                            .is_some_and(|(_, sym)| !sym.flags.is_local());
                        // Never place a relocation whose 4-byte field starts exactly
                        // on an existing Function symbol: a real CALL/JMP operand is
                        // mid-instruction and never coincides with a function entry,
                        // so this only happens at a spurious mid-instruction symbol
                        // (the operand byte mislabeled as a function). The reloc's
                        // 4-byte field would overrun that tiny symbol, and downstream
                        // tools that scan per-symbol (objdiff) loop forever on it.
                        let on_symbol_start = obj
                            .symbols
                            .kind_at_section_address(sec_idx, operand_va, ObjSymbolKind::Function)?
                            .is_some();
                        if !already && emit && !on_symbol_start {
                            add_rel32(
                                obj,
                                sec_idx,
                                operand_va,
                                tgt_sec,
                                target,
                                &mut sweep_count,
                            )?;
                        }
                    }
                }
                pc += ins_len;
            }
        }
        if sweep_count > 0 {
            log::info!(
                "{}: x86 analysis: linear sweep recovered {sweep_count} cross-unit rel32 \
                 relocations",
                obj.name
            );
        }
    }

    // Final validation: downgrade any Function symbol whose address falls
    // strictly inside a decoded instruction span (start < va < end).  These
    // are false-positive entries (e.g. from a previous run's symbols.txt) that
    // point into the operand bytes of an instruction in unreachable or
    // indirect-only code — blocks the recursive disassembler never visited, so
    // the dequeue-time span check couldn't filter them earlier.
    // Downgrading to Unknown prevents create_function_splits from creating a
    // split boundary mid-instruction.
    let stale: Vec<(SymbolIndex, ObjSymbol)> = obj
        .symbols
        .iter()
        .filter_map(|(idx, sym)| {
            if sym.kind != ObjSymbolKind::Function {
                return None;
            }
            let sec = sym.section?;
            let va = sym.address as u32;
            // Search only within this symbol's section to avoid cross-section false positives.
            if let Some((&(_s, start), &end)) = decoded_spans
                .range((std::ops::Bound::Included((sec, 0)), std::ops::Bound::Included((sec, va))))
                .next_back()
            {
                if start < va && va < end {
                    let mut downgraded = sym.clone();
                    downgraded.kind = ObjSymbolKind::Unknown;
                    return Some((idx, downgraded));
                }
            }
            None
        })
        .collect();
    let removed = stale.len() as u32;
    for (idx, downgraded) in stale {
        obj.symbols.replace(idx, downgraded)?;
    }
    if removed > 0 {
        log::debug!(
            "x86 analysis: downgraded {removed} mid-instruction false-positive function symbols"
        );
    }

    log::info!(
        "{}: x86 analysis: {fn_new_count} functions discovered, {rel_count} rel32 relocations added",
        obj.name
    );
    Ok(X86FunctionSizeData { fn_raw_ends, fn_tables, code_snap })
}

/// Compute and set `size` / `size_known` on all x86 function symbols.
///
/// Must be called **after** all symbol-discovery passes (including RTTI) have
/// completed, so that size caps account for every function entry point.
/// Pass in the [`X86FunctionSizeData`] returned by [`analyze_x86_functions`].
pub fn compute_x86_function_sizes(obj: &mut ObjInfo, data: X86FunctionSizeData) -> Result<()> {
    let X86FunctionSizeData { fn_raw_ends, fn_tables, code_snap } = data;

    let find_code = |va: u32| -> Option<(SectionIndex, usize)> {
        code_snap.iter().find_map(|(idx, base, data)| {
            let off = (va as u64).checked_sub(*base)? as usize;
            if off < data.len() { Some((*idx, off)) } else { None }
        })
    };
    let snap_for_section = |sec_idx: SectionIndex| -> Option<(u64, &[u8])> {
        code_snap
            .iter()
            .find(|(idx, _, _)| *idx == sec_idx)
            .map(|(_, base, data)| (*base, data.as_slice()))
    };

    // Build sorted fn-entry lists per section (includes RTTI-added entries).
    let mut fn_entries_by_sec: BTreeMap<SectionIndex, Vec<u32>> = BTreeMap::new();
    for (_, sym) in obj.symbols.iter() {
        if sym.kind == ObjSymbolKind::Function {
            if let Some(sec) = sym.section {
                fn_entries_by_sec.entry(sec).or_default().push(sym.address as u32);
            }
        }
    }
    for entries in fn_entries_by_sec.values_mut() {
        entries.sort_unstable();
    }

    let mut size_updates: Vec<(SymbolIndex, ObjSymbol)> = Vec::new();

    // fn_raw_ends is now keyed by (section_index, fn_va) so functions in separate
    // sections at the same VA (COFF COMDAT) are handled independently.
    for (&(fn_sec_idx, fn_va), &raw_end) in &fn_raw_ends {
        let (sec_base, sec_data) = match snap_for_section(fn_sec_idx) {
            Some(v) => v,
            None => continue,
        };
        let sec_end = sec_base as u32 + sec_data.len() as u32;

        // Cap at the next known function entry in the same section (after RTTI).
        let next_fn = fn_entries_by_sec
            .get(&fn_sec_idx)
            .and_then(|entries| {
                let pos = entries.partition_point(|&e| e <= fn_va);
                entries.get(pos).copied()
            })
            .unwrap_or(sec_end);
        let cap = next_fn.min(sec_end);

        // 1. Skip NOP / INT3 padding.
        let mut fn_end = raw_end.min(cap);
        while fn_end < cap {
            let off = (fn_end as u64 - sec_base) as usize;
            let mut dec =
                Decoder::with_ip(32, &sec_data[off..], fn_end as u64, DecoderOptions::NONE);
            let mut pad = Instruction::default();
            dec.decode_out(&mut pad);
            if pad.is_invalid() {
                break;
            }
            if pad.mnemonic() == Mnemonic::Nop || pad.code() == Code::Int3 {
                fn_end += pad.len() as u32;
            } else {
                break;
            }
        }
        fn_end = fn_end.min(cap);

        // 2. Extend over embedded jump tables (capped).
        if let Some(tables) = fn_tables.get(&(fn_sec_idx, fn_va)) {
            for &table_va in tables {
                if table_va < raw_end || table_va >= cap {
                    continue;
                }
                let mut t = table_va;
                while t + 4 <= cap {
                    let off = (t as u64 - sec_base) as usize;
                    let entry = u32::from_le_bytes(sec_data[off..off + 4].try_into().unwrap());
                    if find_code(entry).is_some() {
                        t += 4;
                    } else {
                        break;
                    }
                }
                if t > fn_end {
                    fn_end = t;
                }
            }
        }
        fn_end = fn_end.min(cap);

        let fn_size = (fn_end - fn_va) as u64;
        if fn_size == 0 {
            continue;
        }

        if let Some((sym_idx, sym)) =
            obj.symbols.kind_at_section_address(fn_sec_idx, fn_va, ObjSymbolKind::Function)?
        {
            if !sym.size_known {
                size_updates
                    .push((sym_idx, ObjSymbol { size: fn_size, size_known: true, ..sym.clone() }));
            }
        }
    }

    let count = size_updates.len();
    for (idx, sym) in size_updates {
        obj.symbols.replace(idx, sym)?;
    }
    log::debug!("x86 analysis: set sizes on {count} function symbol(s)");
    Ok(())
}

/// Returns `true` if `va` in `sec_idx` falls within any span in `decoded_spans`.
/// Spans are stored as (section, start) → exclusive_end.  Searching is scoped to
/// `sec_idx` so that spans from one section never shadow another section's addresses.
fn is_within_decoded_span(
    sec_idx: SectionIndex,
    va: u32,
    decoded_spans: &BTreeMap<(SectionIndex, u32), u32>,
) -> bool {
    if let Some((&(_s, _start), &end)) = decoded_spans
        .range((std::ops::Bound::Included((sec_idx, 0)), std::ops::Bound::Included((sec_idx, va))))
        .next_back()
    {
        va < end
    } else {
        false
    }
}

/// Returns `true` if `va` falls strictly inside the body of a size-known
/// Function symbol (start < va < start+size). Used to avoid minting a spurious
/// sub-function entry at a CALL/JMP target that lands in the middle of an
/// already-known function — which would split that function and conflict with
/// its declared size. The reference itself is still emitted as a relocation
/// against the containing function (with an addend).
fn inside_known_function(obj: &ObjInfo, sec: SectionIndex, va: u32) -> bool {
    obj.symbols
        .for_section_range(sec, ..=va)
        .any(|(_, s)| {
            s.kind == ObjSymbolKind::Function
                && s.size_known
                && (s.address as u32) < va
                && va < (s.address as u32).wrapping_add(s.size as u32)
        })
}

/// Returns `true` if `va` decodes as a valid (non-invalid) instruction.
fn decode_valid(va: u32, code_snap: &[(SectionIndex, u64, Vec<u8>)]) -> bool {
    let Some((_, base, data)) = code_snap.iter().find(|(_, base, data)| {
        (va as u64).checked_sub(*base).is_some_and(|o| (o as usize) < data.len())
    }) else {
        return false;
    };
    let off = (va as u64 - base) as usize;
    let mut decoder = Decoder::with_ip(32, &data[off..], va as u64, DecoderOptions::NONE);
    let mut instr = Instruction::default();
    decoder.decode_out(&mut instr);
    !instr.is_invalid()
}

/// Insert a [`ObjRelocKind::X86Rel32`] relocation at `operand_va` pointing at
/// `target_va` in `tgt_sec`, reusing an existing symbol if one is present.
fn add_rel32(
    obj: &mut ObjInfo,
    src_sec: SectionIndex,
    operand_va: u32,
    tgt_sec: SectionIndex,
    target_va: u32,
    count: &mut u32,
) -> Result<()> {
    if obj.sections[src_sec].relocations.at(operand_va).is_some() {
        return Ok(());
    }
    let tgt_addr = SectionAddress::new(tgt_sec, target_va);
    let (target_symbol, addend) =
        match obj.symbols.for_relocation(tgt_addr, ObjRelocKind::X86Rel32)? {
            Some((sym_idx, sym)) => (sym_idx, target_va as i64 - sym.address as i64),
            None => {
                // If the target lands inside the body of a size-known function,
                // reference that function with an addend rather than minting a
                // spurious sub-entry (which would split the function and conflict
                // with its declared size).
                let containing = obj
                    .symbols
                    .for_section_range(tgt_sec, ..=target_va)
                    .filter(|(_, s)| {
                        s.kind == ObjSymbolKind::Function
                            && s.size_known
                            && (s.address as u32) < target_va
                            && target_va < (s.address as u32).wrapping_add(s.size as u32)
                    })
                    .next_back()
                    .map(|(idx, s)| (idx, s.address));
                if let Some((sym_idx, sym_addr)) = containing {
                    (sym_idx, target_va as i64 - sym_addr as i64)
                } else {
                    let sym_idx = obj.symbols.add_direct(ObjSymbol {
                        name: format!("fn_{:08X}", target_va),
                        address: target_va as u64,
                        section: Some(tgt_sec),
                        kind: ObjSymbolKind::Function,
                        flags: ObjSymbolFlagSet(ObjSymbolFlags::none()),
                        ..Default::default()
                    })?;
                    (sym_idx, 0)
                }
            }
        };
    obj.sections[src_sec]
        .relocations
        .insert(
            operand_va,
            ObjReloc { kind: ObjRelocKind::X86Rel32, target_symbol, addend, module: None },
        )
        .ok();
    *count += 1;
    Ok(())
}
