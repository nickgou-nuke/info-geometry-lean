# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:14.891475+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/HelicalDivisorStinespring.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **20**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/HelicalDivisorStinespring.lean` | `advisory` | 44 | 0 | 20 | 4 | 24 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/HelicalDivisorStinespring.lean`
- module: `InfoGeometry.OperatorAlgebra.HelicalDivisorStinespring`
- status: `advisory`
- debt_score: `44`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L53 [soft] `simp-law-injection` in `simp-declaration nextSheet_angle` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L58 [soft] `simp-law-injection` in `simp-declaration nextSheet_sheet` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L63 [soft] `simp-law-injection` in `simp-declaration prevSheet_angle` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L68 [soft] `simp-law-injection` in `simp-declaration prevSheet_sheet` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L103 [soft] `law-field-locker` in `structure-field SpectralDivisorCharge.multiplicity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [soft] `law-field-locker` in `structure-field SpectralDivisorCharge.chargeOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L105 [soft] `law-field-locker` in `structure-field SpectralDivisorCharge.divisor_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L151 [soft] `law-field-locker` in `structure-field HelicalPacket.component` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L152 [soft] `law-field-locker` in `structure-field HelicalPacket.packet_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L164 [soft] `simp-law-injection` in `simp-declaration project_eq_component` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L184 [soft] `law-field-locker` in `structure-field HelicalDivisorObstructionFlow.invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L186 [soft] `law-field-locker` in `structure-field HelicalDivisorObstructionFlow.flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L187 [soft] `law-field-locker` in `structure-field HelicalDivisorObstructionFlow.flat_invariant_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L189 [soft] `law-field-locker` in `structure-field HelicalDivisorObstructionFlow.flow_preserves_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L209 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L247 [soft] `law-field-locker` in `structure-field HelicalStinespringAccounting.hiddenSheetCharge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L249 [soft] `law-field-locker` in `structure-field HelicalStinespringAccounting.hidden_charge_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L252 [soft] `law-field-locker` in `structure-field HelicalStinespringAccounting.nonzero_charge_hidden_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L267 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L303 [soft] `law-field-locker` in `structure-field SpectralFunctionDivisorCalibration.spectralFunction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L307 [soft] `law-field-locker` in `structure-field SpectralFunctionDivisorCalibration.spectral_divisor_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L313 [soft] `law-field-locker` in `structure-field SpectralFunctionDivisorCalibration.interpretation_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L323 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

