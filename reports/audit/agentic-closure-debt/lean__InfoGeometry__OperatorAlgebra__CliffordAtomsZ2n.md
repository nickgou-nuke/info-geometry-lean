# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:07.574738+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/CliffordAtomsZ2n.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **43**
- Hard: **0**
- Soft: **38**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/CliffordAtomsZ2n.lean` | `advisory` | 81 | 0 | 38 | 5 | 43 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/CliffordAtomsZ2n.lean`
- module: `InfoGeometry.OperatorAlgebra.CliffordAtomsZ2n`
- status: `advisory`
- debt_score: `81`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [soft] `law-field-locker` in `structure-field SplitCliffordAtom.e_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field SplitCliffordAtom.f_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field SplitCliffordAtom.anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L54 [soft] `skeletal-proof` in `theorem h_sq` — proof appears to close via minimal tactic one-liner
  - L96 [soft] `law-field-locker` in `structure-field SplitCliffordAtomSystem.e` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L98 [soft] `law-field-locker` in `structure-field SplitCliffordAtomSystem.f` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L101 [soft] `law-field-locker` in `structure-field SplitCliffordAtomSystem.e_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L105 [soft] `law-field-locker` in `structure-field SplitCliffordAtomSystem.f_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L109 [soft] `law-field-locker` in `structure-field SplitCliffordAtomSystem.same_anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L113 [soft] `law-field-locker` in `structure-field SplitCliffordAtomSystem.H` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L116 [soft] `law-field-locker` in `structure-field SplitCliffordAtomSystem.H_def` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L120 [soft] `law-field-locker` in `structure-field SplitCliffordAtomSystem.H_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L124 [soft] `law-field-locker` in `structure-field SplitCliffordAtomSystem.H_comm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L132 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L166 [soft] `simp-law-injection` in `simp-declaration flip_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L168 [soft] `skeletal-proof` in `theorem flip_self` — proof appears to close via minimal tactic one-liner
  - L174 [soft] `simp-law-injection` in `simp-declaration flip_ne` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L176 [soft] `skeletal-proof` in `theorem flip_ne` — proof appears to close via minimal tactic one-liner
  - L212 [soft] `simp-law-injection` in `simp-declaration flipCharge_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L214 [soft] `skeletal-proof` in `theorem flipCharge_self` — proof appears to close via minimal tactic one-liner
  - L219 [soft] `skeletal-proof` in `theorem flipCharge_of_ne` — proof appears to close via minimal tactic one-liner
  - L261 [soft] `skeletal-proof` in `theorem sectorSign_flip_of_ne` — proof appears to close via minimal tactic one-liner
  - L325 [soft] `law-field-locker` in `structure-field CliffordEdgeAction.act` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L327 [soft] `law-field-locker` in `structure-field CliffordEdgeAction.act_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L331 [soft] `law-field-locker` in `structure-field CliffordEdgeAction.act_neg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L335 [soft] `law-field-locker` in `structure-field CliffordEdgeAction.act_smul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L339 [soft] `law-field-locker` in `structure-field CliffordEdgeAction.H_e_comm_of_ne` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L343 [soft] `law-field-locker` in `structure-field CliffordEdgeAction.H_e_anticomm_self` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L428 [soft] `law-field-locker` in `structure-field LocalToGlobalAnomalyDatum.localCharge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L430 [soft] `law-field-locker` in `structure-field LocalToGlobalAnomalyDatum.globalIndex` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L433 [soft] `law-field-locker` in `structure-field LocalToGlobalAnomalyDatum.reductionMod16` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L436 [soft] `law-field-locker` in `structure-field LocalToGlobalAnomalyDatum.compatibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L448 [soft] `law-field-locker` in `structure-field GlobalAnomalyClass.localSector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L456 [soft] `law-field-locker` in `structure-field GlobalAnomalyClass.reduction_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L460 [soft] `law-field-locker` in `structure-field GlobalAnomalyClass.assembly_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L468 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L490 [soft] `law-field-locker` in `structure-field DIIIIndexCalibration.dIIIIndex` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L492 [soft] `law-field-locker` in `structure-field DIIIIndexCalibration.calibration_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L503 [soft] `law-field-locker` in `structure-field DIIIInteractionCalibration.encode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L505 [soft] `law-field-locker` in `structure-field DIIIInteractionCalibration.stacking_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L513 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

