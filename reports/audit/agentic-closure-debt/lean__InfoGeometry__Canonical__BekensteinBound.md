# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:41.833430+00:00`
Root: `lean/InfoGeometry/Canonical/BekensteinBound.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **22**
- Hard: **0**
- Soft: **13**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BekensteinBound.lean` | `advisory` | 35 | 0 | 13 | 9 | 22 |

## Findings by file

### `lean/InfoGeometry/Canonical/BekensteinBound.lean`
- module: `InfoGeometry.Canonical.BekensteinBound`
- status: `advisory`
- debt_score: `35`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L21 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L28 [advisory] `local-hypothesis-injection` in `theorem trajectoryRNBarrier_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L30 [advisory] `local-hypothesis-injection` in `theorem trajectoryRNBarrier_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L51 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L149 [soft] `simp-law-injection` in `simp-declaration trajectoryRNGeneratorPotential_natCast` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L155 [soft] `skeletal-proof` in `theorem cocycleGeneratorLift_of_trajectoryRNGeneratorPotential` — proof appears to close via minimal tactic one-liner
  - L185 [soft] `skeletal-proof` in `theorem cocycleGeneratorLift_of_cocycleEntropyPotential_match` — proof appears to close via minimal tactic one-liner
  - L260 [advisory] `local-hypothesis-injection` in `theorem cocycleEntropyPotential_natMatch_of_cocycleGeneratorLift_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L277 [advisory] `local-hypothesis-injection` in `theorem cocycleEntropyPotential_natMatch_of_cocycleGeneratorLift_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L288 [advisory] `local-hypothesis-injection` in `theorem cocycleEntropyPotential_natMatch_of_cocycleGeneratorLift_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L291 [soft] `skeletal-proof` in `theorem cocycleEntropyPotential_zero_of_connesCocycle` — proof appears to close via minimal tactic one-liner
  - L630 [soft] `law-field-locker` in `structure-field CasiniIncrementBridge.cocycle_increment_eq_relEnt_drop` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L635 [soft] `law-field-locker` in `structure-field CasiniIncrementBridge.relEnt_drop_eq_phaseRN` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L639 [soft] `law-field-locker` in `structure-field CasiniIncrementBridge.relEnt_monotone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L656 [soft] `law-field-locker` in `structure-field MinimalCasiniIncrementBridge.cocycle_increment_eq_relEnt_drop` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L661 [soft] `law-field-locker` in `structure-field MinimalCasiniIncrementBridge.relEnt_drop_eq_phaseRN` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L869 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L886 [soft] `skeletal-proof` in `theorem topologicalBekensteinBound_of_tomitaGeneratorLift` — proof appears to close via minimal tactic one-liner
  - L961 [soft] `skeletal-proof` in `theorem topologicalBekensteinBound_of_tomitaConnesCocycle_natMatch` — proof appears to close via minimal tactic one-liner
  - L988 [soft] `skeletal-proof` in `theorem topologicalBekensteinBound_of_tomitaConnesCocycle_generatorLift_zero` — proof appears to close via minimal tactic one-liner
  - L1013 [soft] `skeletal-proof` in `theorem topologicalBekensteinBound_of_tomitaConnesCocycle_casiniIncrement` — proof appears to close via minimal tactic one-liner

