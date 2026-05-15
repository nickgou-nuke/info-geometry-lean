# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:00.233860+00:00`
Root: `lean/InfoGeometry/MaxEnt/JaynesInfoStatMech.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **25**
- Hard: **0**
- Soft: **12**
- Advisory: **13**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/MaxEnt/JaynesInfoStatMech.lean` | `advisory` | 37 | 0 | 12 | 13 | 25 |

## Findings by file

### `lean/InfoGeometry/MaxEnt/JaynesInfoStatMech.lean`
- module: `InfoGeometry.MaxEnt.JaynesInfoStatMech`
- status: `advisory`
- debt_score: `37`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L24 [soft] `law-field-locker` in `structure-field ProbDist.p` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L25 [soft] `law-field-locker` in `structure-field ProbDist.nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L26 [soft] `law-field-locker` in `structure-field ProbDist.sum_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field ConstraintFamily.f` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field ConstraintFamily.d` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [advisory] `existential-packaging` in `def IsFeasible` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L90 [advisory] `existential-packaging` in `def maxEntDist` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L94 [advisory] `local-hypothesis-injection` in `def maxEntDist` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L139 [advisory] `existential-packaging` in `def helmholtzFreeEnergy` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L226 [soft] `skeletal-proof` in `lemma gibbsProb_sum_one` — proof appears to close via minimal tactic one-liner
  - L244 [advisory] `existential-packaging` in `def densityMatrix` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L250 [soft] `simp-law-injection` in `simp-declaration densityMatrix_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L255 [soft] `simp-law-injection` in `simp-declaration densityMatrix_offdiag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L271 [advisory] `local-hypothesis-injection` in `lemma log_gibbsProb` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L276 [advisory] `existential-packaging` in `def logDensityMatrix` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L282 [soft] `simp-law-injection` in `simp-declaration logDensityMatrix_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L286 [soft] `skeletal-proof` in `lemma logDensityMatrix_diag_affine` — proof appears to close via minimal tactic one-liner
  - L297 [advisory] `existential-packaging` in `def gibbsStateDiag` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L318 [soft] `skeletal-proof` in `lemma gibbsEntropy_eq_beta_internal_plus_logPartition` — proof appears to close via minimal tactic one-liner
  - L384 [advisory] `existential-packaging` in `def modularConj` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L392 [soft] `skeletal-proof` in `lemma modularConj_diag_entry` — proof appears to close via minimal tactic one-liner
  - L401 [advisory] `existential-packaging` in `def modularShiftDiag` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L408 [advisory] `existential-packaging` in `lemma modularShiftDiag_eq` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L421 [advisory] `local-hypothesis-injection` in `theorem gibbsState_kmsLike_diag` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

