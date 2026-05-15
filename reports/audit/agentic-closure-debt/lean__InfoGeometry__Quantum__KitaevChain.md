# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:35.446078+00:00`
Root: `lean/InfoGeometry/Quantum/KitaevChain.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **23**
- Hard: **0**
- Soft: **11**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/KitaevChain.lean` | `advisory` | 34 | 0 | 11 | 12 | 23 |

## Findings by file

### `lean/InfoGeometry/Quantum/KitaevChain.lean`
- module: `InfoGeometry.Quantum.KitaevChain`
- status: `advisory`
- debt_score: `34`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [soft] `law-field-locker` in `structure-field KitaevCell.pairing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field KitaevCocycle.U` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field KitaevCocycle.cocycle` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `skeletal-proof` in `theorem macroscopicVolume_eq_prod_pfaffians` — proof appears to close via minimal tactic one-liner
  - L63 [soft] `skeletal-proof` in `theorem macroscopicVolume_append` — proof appears to close via minimal tactic one-liner
  - L71 [soft] `skeletal-proof` in `theorem macroscopicVolume_singleton` — proof appears to close via minimal tactic one-liner
  - L83 [soft] `skeletal-proof` in `theorem topologicalIndex_append` — proof appears to close via minimal tactic one-liner
  - L106 [advisory] `existential-packaging` in `def HasDefect` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L128 [soft] `skeletal-proof` in `theorem hasDefect_singleton_iff_isCritical` — proof appears to close via minimal tactic one-liner
  - L142 [soft] `skeletal-proof` in `theorem topologicalIndex_eq_zero_iff` — proof appears to close via minimal tactic one-liner
  - L221 [advisory] `existential-packaging` in `lemma zero_exists_of_opposite_sign` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L237 [advisory] `existential-packaging` in `lemma zero_exists_of_opposite_sign_symm` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L237 [soft] `skeletal-proof` in `lemma zero_exists_of_opposite_sign_symm` — proof appears to close via minimal tactic one-liner
  - L250 [advisory] `local-hypothesis-injection` in `lemma zero_exists_of_opposite_sign_symm` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L253 [advisory] `existential-packaging` in `theorem index_change_forces_defect_crossing` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L271 [advisory] `local-hypothesis-injection` in `theorem index_change_forces_defect_crossing` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L279 [advisory] `local-hypothesis-injection` in `theorem index_change_forces_defect_crossing` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L286 [advisory] `existential-packaging` in `theorem kitaev_tiling_identity` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L294 [soft] `skeletal-proof` in `theorem macroscopicVolume_eq_one_of_pfaffian_one` — proof appears to close via minimal tactic one-liner
  - L307 [advisory] `local-hypothesis-injection` in `theorem macroscopicVolume_eq_one_of_pfaffian_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L308 [advisory] `local-hypothesis-injection` in `theorem macroscopicVolume_eq_one_of_pfaffian_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L312 [advisory] `local-hypothesis-injection` in `theorem macroscopicVolume_eq_one_of_pfaffian_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

