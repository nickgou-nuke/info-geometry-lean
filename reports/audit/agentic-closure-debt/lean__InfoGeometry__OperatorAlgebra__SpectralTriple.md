# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:22.442737+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/SpectralTriple.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **22**
- Hard: **0**
- Soft: **20**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/SpectralTriple.lean` | `advisory` | 42 | 0 | 20 | 2 | 22 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/SpectralTriple.lean`
- module: `InfoGeometry.OperatorAlgebra.SpectralTriple`
- status: `advisory`
- debt_score: `42`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L60 [soft] `law-field-locker` in `structure-field KOSigns.epsJ_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field KOSigns.epsD_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [soft] `law-field-locker` in `structure-field KOSigns.epsChi_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L81 [soft] `law-field-locker` in `structure-field PhaseAxis.K_square_neg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L100 [soft] `law-field-locker` in `structure-field RealStructure.J_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L105 [soft] `law-field-locker` in `structure-field RealStructure.J_phase_reversing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L145 [soft] `law-field-locker` in `structure-field ChiralGrading.chi_square_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L190 [soft] `law-field-locker` in `structure-field SpectralGenerator.selfAdjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L193 [soft] `law-field-locker` in `structure-field SpectralGenerator.compactResolventOrSummability` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L229 [soft] `law-field-locker` in `structure-field RepresentedAlgebra.rep` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L319 [soft] `law-field-locker` in `structure-field StateReadout.eval` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L320 [advisory] `existential-packaging` in `def ConnesDistanceAdmissibleValue` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L350 [soft] `law-field-locker` in `structure-field DixmierTraceDatum.dixmierTrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L351 [soft] `law-field-locker` in `structure-field DixmierTraceDatum.positive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L353 [soft] `law-field-locker` in `structure-field DixmierTraceDatum.traceLikeCyclicity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L355 [soft] `law-field-locker` in `structure-field DixmierTraceDatum.logarithmicDivergenceExtraction_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L368 [soft] `law-field-locker` in `structure-field ZetaRenormalizationDatum.zeta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L370 [soft] `law-field-locker` in `structure-field ZetaRenormalizationDatum.residueReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L371 [soft] `law-field-locker` in `structure-field ZetaRenormalizationDatum.finitePartReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L372 [soft] `law-field-locker` in `structure-field ZetaRenormalizationDatum.meromorphicContinuation_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L431 [soft] `law-field-locker` in `structure-field PhaseRealSpectralTriple.rep_phase_linear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

