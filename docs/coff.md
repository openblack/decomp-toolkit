# COFF / PE support (prototype)

Notes on behavior specific to the `dtk coff` subcommand family (x86 PE
executables split into MSVC-style COFF objects).

## Object file layout

By default (`function_sections: true` in `config.yml`), each function in a
unit is emitted as its own `.text` section, mirroring MSVC `/Gy`
(function-level linking). This gives tooling (objdiff, `dumpbin`,
`llvm-readobj`) exact per-function section sizes instead of sizes inferred
from symbol gaps, which would include inter-function padding.

Details:

- COFF permits multiple sections with the same name in one object; lld-link
  concatenates them in section-table order, so relinked output is unchanged.
- Inter-function padding bytes (`int3`/`nop`) and trailing jump tables stay
  attached to the preceding function's section. Non-first sections have
  alignment 1, so the linker inserts no padding between them and the byte
  stream is preserved.
- Sections are not COMDAT: dtk deduplicates symbol names globally at split
  time, so COMDAT selection semantics are unnecessary.

Set `function_sections: false` to emit one section per split range instead.

## Symbol visibility

- `scope:local` in `symbols.txt` is honored even with `export_all: true`
  (the default): the symbol is emitted as `IMAGE_SYM_CLASS_STATIC`.
- If a `scope:local` symbol is referenced from another unit and
  `globalize_symbols` is enabled (the default), it is renamed to
  `<name>_<addr>` and promoted to external automatically.
- With `globalize_symbols: false`, a `scope:local` symbol referenced
  cross-unit will fail to link (undefined symbol) — same contract as the
  ELF pipeline.
- `noexport` still forces a symbol static regardless of scope.

## symbols.txt / splits.txt changes

Symbol names, scopes, and splits are baked into the emitted objects at
`dtk coff split` time. After editing `symbols.txt` or `splits.txt`, re-run
`dtk coff split` to regenerate the objects.

## Non-contiguous units

A unit may be listed in `splits.txt` with multiple, non-adjacent ranges of
the same section (e.g. two `.text` ranges). This is supported for diffing:
the unit's object receives one section per range.

Limitations:

- Link order is resolved from address adjacency; interleaved units create
  cycles that are broken heuristically. A warning names any unit with
  non-contiguous ranges.
- A relinked image cannot be byte-identical to the original in this case,
  since the linker emits one object's sections adjacently. Multi-section
  ranges (`.text` + `.data` + `.bss` for one unit) are unaffected — that is
  the normal case and fully supported.

## Known limitations

- objdiff may display function signatures as `void(void)`: COFF symbols
  carry no parameter or return type information (only the DTYPE_FUNCTION
  bit). Real signatures live in CodeView debug data, which dtk does not
  emit. This is cosmetic and does not affect diffing.
