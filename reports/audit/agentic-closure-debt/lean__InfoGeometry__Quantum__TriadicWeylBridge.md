# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:38.013440+00:00`
Root: `lean/InfoGeometry/Quantum/TriadicWeylBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **28**
- Hard: **0**
- Soft: **9**
- Advisory: **19**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/TriadicWeylBridge.lean` | `advisory` | 37 | 0 | 9 | 19 | 28 |

## Findings by file

### `lean/InfoGeometry/Quantum/TriadicWeylBridge.lean`
- module: `InfoGeometry.Quantum.TriadicWeylBridge`
- status: `advisory`
- debt_score: `37`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L18 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L20 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L64 [soft] `skeletal-proof` in `theorem isWeylCompatible_iff_comp_spectralEpsilon` — proof appears to close via minimal tactic one-liner
  - L72 [advisory] `local-hypothesis-injection` in `theorem isWeylCompatible_iff_comp_spectralEpsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L95 [advisory] `local-hypothesis-injection` in `theorem isWeylCompatible_iff_comp_spectralEpsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L125 [soft] `simp-law-injection` in `simp-declaration plusProjectorFlux_eq_zero_of_isWeylCompatible` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L130 [advisory] `local-hypothesis-injection` in `theorem isWeylCompatible_iff_comp_spectralEpsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L137 [soft] `simp-law-injection` in `simp-declaration minusProjectorFlux_eq_zero_of_isWeylCompatible` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L142 [advisory] `local-hypothesis-injection` in `theorem isWeylCompatible_iff_comp_spectralEpsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L149 [soft] `skeletal-proof` in `theorem isWeylCompatible_of_plusProjectorFlux_eq_zero` — proof appears to close via minimal tactic one-liner
  - L154 [advisory] `local-hypothesis-injection` in `theorem isWeylCompatible_of_plusProjectorFlux_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L166 [advisory] `local-hypothesis-injection` in `theorem isWeylCompatible_of_plusProjectorFlux_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L167 [advisory] `local-hypothesis-injection` in `theorem isWeylCompatible_of_plusProjectorFlux_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L169 [advisory] `local-hypothesis-injection` in `theorem isWeylCompatible_of_plusProjectorFlux_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L178 [soft] `skeletal-proof` in `theorem isWeylCompatible_of_minusProjectorFlux_eq_zero` — proof appears to close via minimal tactic one-liner
  - L183 [advisory] `local-hypothesis-injection` in `theorem isWeylCompatible_of_minusProjectorFlux_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L187 [advisory] `local-hypothesis-injection` in `theorem isWeylCompatible_of_minusProjectorFlux_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L188 [advisory] `local-hypothesis-injection` in `theorem isWeylCompatible_of_minusProjectorFlux_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L190 [advisory] `local-hypothesis-injection` in `theorem isWeylCompatible_of_minusProjectorFlux_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L259 [advisory] `local-hypothesis-injection` in `theorem dyadicKrein_isWeylCompatible_of_mem_plusSheet` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L283 [advisory] `local-hypothesis-injection` in `theorem dyadicKrein_isWeylCompatible_of_mem_minusSheet` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L287 [soft] `simp-law-injection` in `simp-declaration plusToMinusBlockMap_triadicGenerator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L294 [soft] `simp-law-injection` in `simp-declaration minusToPlusBlockMap_triadicGenerator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L303 [advisory] `bridge-shaped-declaration` in `theorem triadicGenerator_blockDiagonal_of_compatibility` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L325 [soft] `skeletal-proof` in `theorem eq_common_relative_form_of_scalarBlocks` — proof appears to close via minimal tactic one-liner
  - L334 [advisory] `local-hypothesis-injection` in `theorem eq_common_relative_form_of_scalarBlocks` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L368 [soft] `skeletal-proof` in `theorem eq_logarithmicGenerator_of_scalarSheetBlocks` — proof appears to close via minimal tactic one-liner

