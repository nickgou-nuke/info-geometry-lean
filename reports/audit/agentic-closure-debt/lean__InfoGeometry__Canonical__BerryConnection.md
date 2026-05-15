# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:42.241378+00:00`
Root: `lean/InfoGeometry/Canonical/BerryConnection.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **40**
- Hard: **0**
- Soft: **37**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BerryConnection.lean` | `advisory` | 77 | 0 | 37 | 3 | 40 |

## Findings by file

### `lean/InfoGeometry/Canonical/BerryConnection.lean`
- module: `InfoGeometry.Canonical.BerryConnection`
- status: `advisory`
- debt_score: `77`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L23 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L25 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L52 [soft] `law-field-locker` in `structure-field SuperHestenesKaehlerDatum.compat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field SuperHestenesKaehlerDatum.J_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field SuperHestenesKaehlerDatum.epsilon_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field SuperHestenesKaehlerDatum.J_anticomm_epsilon` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field SuperHestenesKaehlerDatum.K_eq_J_comp_epsilon` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field SuperHestenesKaehlerDatum.K_eq_modularComplexI` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `structure-field SuperHestenesKaehlerDatum.K_sq_neg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [soft] `simp-law-injection` in `simp-declaration K_eq_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [soft] `simp-law-injection` in `simp-declaration toQGT_compat_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L102 [soft] `simp-law-injection` in `simp-declaration ofQGT_K_eq_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L109 [soft] `simp-law-injection` in `simp-declaration toQGT_metric` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L113 [soft] `simp-law-injection` in `simp-declaration toQGT_berry` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L117 [soft] `simp-law-injection` in `simp-declaration ofQGT_metric` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L121 [soft] `simp-law-injection` in `simp-declaration ofQGT_phase` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L125 [soft] `simp-law-injection` in `simp-declaration ofQGT_J` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L130 [soft] `simp-law-injection` in `simp-declaration ofQGT_J_eq_modular_j` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L136 [soft] `simp-law-injection` in `simp-declaration ofQGT_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L141 [soft] `simp-law-injection` in `simp-declaration ofQGT_epsilon_eq_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L147 [soft] `simp-law-injection` in `simp-declaration ofQGT_K` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L205 [soft] `law-field-locker` in `structure-field BigradedSuperHestenesDatum.J_phase_odd` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L206 [soft] `law-field-locker` in `structure-field BigradedSuperHestenesDatum.epsilon_phase_odd` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L207 [soft] `law-field-locker` in `structure-field BigradedSuperHestenesDatum.K_phase_even` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L223 [soft] `simp-law-injection` in `simp-declaration JBoost_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L228 [soft] `simp-law-injection` in `simp-declaration epsilonBoost_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L233 [soft] `simp-law-injection` in `simp-declaration KRotation_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L238 [soft] `skeletal-proof` in `theorem JBoost_add` — proof appears to close via minimal tactic one-liner
  - L245 [soft] `skeletal-proof` in `theorem epsilonBoost_add` — proof appears to close via minimal tactic one-liner
  - L252 [soft] `skeletal-proof` in `theorem KRotation_add` — proof appears to close via minimal tactic one-liner
  - L259 [soft] `simp-law-injection` in `simp-declaration phase_eq_metric_of_K` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L290 [soft] `simp-law-injection` in `simp-declaration hestenesBerryTwoForm_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L298 [soft] `simp-law-injection` in `simp-declaration hestenesBerryTwoForm_apply_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L321 [soft] `skeletal-proof` in `theorem deriv_berryOfOperator_expTransport_at_zero` — proof appears to close via minimal tactic one-liner
  - L342 [soft] `skeletal-proof` in `theorem deriv_berryOfOperator_phaseAxisTransport_at_zero_eq_berryOf_phaseAxisResponse` — proof appears to close via minimal tactic one-liner
  - L371 [soft] `skeletal-proof` in `theorem deriv_berryOfOperator_phaseAxisTransport_at_zero_eq_berryOf_phaseAxisResponse_complex_i` — proof appears to close via minimal tactic one-liner
  - L419 [soft] `skeletal-proof` in `theorem deriv_berryOfOperator_phaseAxisTransport_at_zero_eq_berryOf_two_smul_comp_complex_i_of_IsPhaseAntilinear` — proof appears to close via minimal tactic one-liner
  - L581 [soft] `skeletal-proof` in `theorem deriv_hestenesWeylModularBerryTransport_at_zero_eq_hestenesWeylModularBerryTwoForm` — proof appears to close via minimal tactic one-liner
  - L601 [soft] `skeletal-proof` in `theorem deriv_hestenesWeylModularBerryTransport_at_eq_hestenesWeylModularBerryTwoForm` — proof appears to close via minimal tactic one-liner

