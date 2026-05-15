# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:48.614346+00:00`
Root: `lean/InfoGeometry/Thermodynamics/SouriauTemperatureProjective.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **31**
- Hard: **0**
- Soft: **30**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Thermodynamics/SouriauTemperatureProjective.lean` | `advisory` | 61 | 0 | 30 | 1 | 31 |

## Findings by file

### `lean/InfoGeometry/Thermodynamics/SouriauTemperatureProjective.lean`
- module: `InfoGeometry.Thermodynamics.SouriauTemperatureProjective`
- status: `advisory`
- debt_score: `61`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L39 [soft] `law-field-locker` in `structure-field PositiveSouriauTemperature.im_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `simp-law-injection` in `simp-declaration toRealUpperHalfPlane_x` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L60 [soft] `skeletal-proof` in `theorem toRealUpperHalfPlane_x` — proof appears to close via minimal tactic one-liner
  - L64 [soft] `simp-law-injection` in `simp-declaration toRealUpperHalfPlane_y` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L66 [soft] `skeletal-proof` in `theorem toRealUpperHalfPlane_y` — proof appears to close via minimal tactic one-liner
  - L70 [soft] `simp-law-injection` in `simp-declaration ofRealUpperHalfPlane_temp_s` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [soft] `skeletal-proof` in `theorem ofRealUpperHalfPlane_temp_s` — proof appears to close via minimal tactic one-liner
  - L76 [soft] `simp-law-injection` in `simp-declaration toRealUpperHalfPlane_ofRealUpperHalfPlane` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L82 [soft] `simp-law-injection` in `simp-declaration ofRealUpperHalfPlane_toRealUpperHalfPlane` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L124 [soft] `simp-law-injection` in `simp-declaration smul_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L126 [soft] `skeletal-proof` in `theorem smul_def` — proof appears to close via minimal tactic one-liner
  - L132 [soft] `simp-law-injection` in `simp-declaration toRealUpperHalfPlane_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L134 [soft] `skeletal-proof` in `theorem toRealUpperHalfPlane_smul` — proof appears to close via minimal tactic one-liner
  - L140 [soft] `simp-law-injection` in `simp-declaration negIdSL2R_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L168 [soft] `law-field-locker` in `structure-field ProjectiveTemperatureInversion.element_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L189 [soft] `simp-law-injection` in `simp-declaration closure_theta` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L191 [soft] `skeletal-proof` in `theorem closure_theta` — proof appears to close via minimal tactic one-liner
  - L244 [soft] `skeletal-proof` in `theorem smul_eq_self_of_stationary` — proof appears to close via minimal tactic one-liner
  - L252 [soft] `skeletal-proof` in `theorem read_lift` — proof appears to close via minimal tactic one-liner
  - L286 [soft] `law-field-locker` in `structure-field ProjectiveLiftTemperatureInversion.element_sq_lift` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L316 [soft] `simp-law-injection` in `simp-declaration closure_theta` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L318 [soft] `skeletal-proof` in `theorem closure_theta` — proof appears to close via minimal tactic one-liner
  - L360 [soft] `skeletal-proof` in `theorem smul_eq_self_of_stationary` — proof appears to close via minimal tactic one-liner
  - L368 [soft] `skeletal-proof` in `theorem read_lift` — proof appears to close via minimal tactic one-liner
  - L403 [soft] `law-field-locker` in `structure-field ProjectivePSLTemperatureInversion.element_sq_projective` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L407 [soft] `law-field-locker` in `structure-field ProjectivePSLTemperatureInversion.projectiveTheta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L415 [soft] `law-field-locker` in `structure-field ProjectivePSLTemperatureInversion.projectiveTheta_eq_lift` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L419 [soft] `law-field-locker` in `structure-field ProjectivePSLTemperatureInversion.projectiveTheta_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L434 [soft] `simp-law-injection` in `simp-declaration closure_theta` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L436 [soft] `skeletal-proof` in `theorem closure_theta` — proof appears to close via minimal tactic one-liner

