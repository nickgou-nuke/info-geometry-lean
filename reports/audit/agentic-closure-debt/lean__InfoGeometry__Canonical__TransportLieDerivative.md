# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:07.041500+00:00`
Root: `lean/InfoGeometry/Canonical/TransportLieDerivative.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **45**
- Hard: **0**
- Soft: **32**
- Advisory: **13**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/TransportLieDerivative.lean` | `advisory` | 77 | 0 | 32 | 13 | 45 |

## Findings by file

### `lean/InfoGeometry/Canonical/TransportLieDerivative.lean`
- module: `InfoGeometry.Canonical.TransportLieDerivative`
- status: `advisory`
- debt_score: `77`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L18 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L32 [soft] `skeletal-proof` in `lemma hasDerivAt_exp_smul_zero` — proof appears to close via minimal tactic one-liner
  - L40 [soft] `skeletal-proof` in `lemma hasDerivAt_exp_neg_smul_zero` — proof appears to close via minimal tactic one-liner
  - L48 [soft] `skeletal-proof` in `lemma hasDerivAt_expTransport_at_zero` — proof appears to close via minimal tactic one-liner
  - L56 [advisory] `local-hypothesis-injection` in `lemma hasDerivAt_expTransport_at_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L58 [advisory] `local-hypothesis-injection` in `lemma hasDerivAt_expTransport_at_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L70 [advisory] `local-hypothesis-injection` in `lemma hasDerivAt_expTransport_at_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L77 [soft] `skeletal-proof` in `lemma hasDerivAt_expTransport` — proof appears to close via minimal tactic one-liner
  - L133 [soft] `simp-law-injection` in `simp-declaration expTransport_add_seed` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L140 [soft] `skeletal-proof` in `theorem expTransport_eq_self_of_commute` — proof appears to close via minimal tactic one-liner
  - L175 [soft] `skeletal-proof` in `lemma hasDerivAt_expTransportEnd_at_zero` — proof appears to close via minimal tactic one-liner
  - L181 [soft] `skeletal-proof` in `theorem deriv_expTransportEnd_at_zero` — proof appears to close via minimal tactic one-liner
  - L206 [soft] `law-field-locker` in `structure-field KAxis.K` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L207 [soft] `law-field-locker` in `structure-field KAxis.square_neg_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L208 [soft] `law-field-locker` in `structure-field KAxis.skew` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L209 [soft] `law-field-locker` in `structure-field KAxis.orthogonal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L217 [soft] `law-field-locker` in `structure-field ModularCPTChiralAtom.eps` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L218 [soft] `law-field-locker` in `structure-field ModularCPTChiralAtom.J` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L219 [soft] `law-field-locker` in `structure-field ModularCPTChiralAtom.eps_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L220 [soft] `law-field-locker` in `structure-field ModularCPTChiralAtom.J_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L221 [soft] `law-field-locker` in `structure-field ModularCPTChiralAtom.anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L222 [soft] `law-field-locker` in `structure-field ModularCPTChiralAtom.K_sq_neg_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L223 [soft] `law-field-locker` in `structure-field ModularCPTChiralAtom.K_skew` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L224 [soft] `law-field-locker` in `structure-field ModularCPTChiralAtom.K_orthogonal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L281 [soft] `skeletal-proof` in `lemma axisConjugate_eq_neg_of_isAxisLinear` — proof appears to close via minimal tactic one-liner
  - L287 [advisory] `local-hypothesis-injection` in `lemma axisConjugate_eq_neg_of_isAxisLinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L290 [advisory] `local-hypothesis-injection` in `lemma axisConjugate_eq_neg_of_isAxisLinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L299 [soft] `skeletal-proof` in `lemma axisConjugate_eq_of_isAxisAntilinear` — proof appears to close via minimal tactic one-liner
  - L305 [advisory] `local-hypothesis-injection` in `lemma axisConjugate_eq_of_isAxisAntilinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L308 [advisory] `local-hypothesis-injection` in `lemma axisConjugate_eq_of_isAxisAntilinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L318 [soft] `skeletal-proof` in `lemma axisLinearPart_eq_self_of_isAxisLinear` — proof appears to close via minimal tactic one-liner
  - L344 [soft] `skeletal-proof` in `lemma axisAntilinearPart_eq_self_of_isAxisAntilinear` — proof appears to close via minimal tactic one-liner
  - L355 [soft] `skeletal-proof` in `lemma axisLinearPart_add_axisAntilinearPart` — proof appears to close via minimal tactic one-liner
  - L385 [soft] `skeletal-proof` in `lemma modularAxisLinearPart_add_modularAxisAntilinearPart` — proof appears to close via minimal tactic one-liner
  - L416 [soft] `skeletal-proof` in `theorem deriv_hestenesTransport_at_zero` — proof appears to close via minimal tactic one-liner
  - L421 [soft] `skeletal-proof` in `lemma complexLikeByAxis_i_sq` — proof appears to close via minimal tactic one-liner
  - L430 [advisory] `local-hypothesis-injection` in `lemma complexLikeByAxis_i_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L432 [advisory] `local-hypothesis-injection` in `lemma complexLikeByAxis_i_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L434 [advisory] `local-hypothesis-injection` in `lemma complexLikeByAxis_i_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L444 [soft] `skeletal-proof` in `lemma complexLike_i_sq` — proof appears to close via minimal tactic one-liner
  - L459 [soft] `law-field-locker` in `structure-field DifferentiableSpinConnection.U_differentiable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L462 [soft] `law-field-locker` in `structure-field DifferentiableSpinConnection.U_inv_differentiable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L604 [soft] `skeletal-proof` in `theorem lieDerivMetric_eq_zero_of_commute_exp_flow_of_commute` — proof appears to close via minimal tactic one-liner
  - L613 [advisory] `local-hypothesis-injection` in `theorem lieDerivMetric_eq_zero_of_commute_exp_flow_of_commute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

