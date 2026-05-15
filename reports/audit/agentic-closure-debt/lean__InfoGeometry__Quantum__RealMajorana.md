# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:36.251654+00:00`
Root: `lean/InfoGeometry/Quantum/RealMajorana.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **126**
- Hard: **0**
- Soft: **76**
- Advisory: **50**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/RealMajorana.lean` | `advisory` | 202 | 0 | 76 | 50 | 126 |

## Findings by file

### `lean/InfoGeometry/Quantum/RealMajorana.lean`
- module: `InfoGeometry.Quantum.RealMajorana`
- status: `advisory`
- debt_score: `202`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L50 [soft] `law-field-locker` in `structure-field RealMajoranaDatum.gamma` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field RealMajoranaDatum.J` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field RealMajoranaDatum.eps` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field RealMajoranaDatum.Pi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field RealMajoranaDatum.J_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field RealMajoranaDatum.eps_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field RealMajoranaDatum.Jeps_anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `structure-field RealMajoranaDatum.Pi_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field RealMajoranaDatum.car` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L66 [soft] `section-law-variable` in `variable M` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L84 [soft] `skeletal-proof` in `theorem K_sq` — proof appears to close via minimal tactic one-liner
  - L88 [advisory] `local-hypothesis-injection` in `theorem K_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L89 [advisory] `local-hypothesis-injection` in `theorem K_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L147 [soft] `skeletal-proof` in `theorem K_ne_Pi` — proof appears to close via minimal tactic one-liner
  - L153 [advisory] `local-hypothesis-injection` in `theorem K_ne_Pi` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L162 [advisory] `local-hypothesis-injection` in `theorem K_ne_Pi` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L164 [advisory] `local-hypothesis-injection` in `theorem K_ne_Pi` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L165 [advisory] `local-hypothesis-injection` in `theorem K_ne_Pi` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L171 [advisory] `local-hypothesis-injection` in `theorem K_ne_Pi` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L173 [advisory] `local-hypothesis-injection` in `theorem K_ne_Pi` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L186 [soft] `law-field-locker` in `structure-field KPolarization.P` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L187 [soft] `law-field-locker` in `structure-field KPolarization.P_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L188 [soft] `law-field-locker` in `structure-field KPolarization.P_K_anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L193 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L193 [soft] `section-law-variable` in `variable P0` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L222 [soft] `skeletal-proof` in `lemma K_maps_plus_to_minus` — proof appears to close via minimal tactic one-liner
  - L228 [advisory] `local-hypothesis-injection` in `lemma K_maps_plus_to_minus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L232 [soft] `skeletal-proof` in `lemma K_maps_minus_to_plus` — proof appears to close via minimal tactic one-liner
  - L238 [advisory] `local-hypothesis-injection` in `lemma K_maps_minus_to_plus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L269 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L269 [soft] `section-law-variable` in `variable M` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L283 [advisory] `local-hypothesis-injection` in `def chiralityPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L286 [advisory] `local-hypothesis-injection` in `def chiralityPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L289 [advisory] `local-hypothesis-injection` in `def chiralityPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L292 [advisory] `local-hypothesis-injection` in `def chiralityPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L301 [soft] `simp-law-injection` in `simp-declaration chiralityPolarization_P` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L304 [soft] `simp-law-injection` in `simp-declaration chiralityPolarization_plus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L307 [soft] `simp-law-injection` in `simp-declaration chiralityPolarization_minus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L317 [soft] `law-field-locker` in `structure-field RealBogoliubovTransform.B` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L318 [soft] `law-field-locker` in `structure-field RealBogoliubovTransform.Binv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L319 [soft] `law-field-locker` in `structure-field RealBogoliubovTransform.left_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L320 [soft] `law-field-locker` in `structure-field RealBogoliubovTransform.right_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L321 [soft] `law-field-locker` in `structure-field RealBogoliubovTransform.preserves_inner` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L322 [soft] `law-field-locker` in `structure-field RealBogoliubovTransform.parity_even` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L327 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L327 [soft] `section-law-variable` in `variable T` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L328 [soft] `simp-law-injection` in `simp-declaration Binv_apply_B` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L330 [advisory] `local-hypothesis-injection` in `structure RealBogoliubovTransform` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L332 [soft] `simp-law-injection` in `simp-declaration B_apply_Binv` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L334 [advisory] `local-hypothesis-injection` in `structure RealBogoliubovTransform` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L389 [soft] `skeletal-proof` in `lemma transportJ_apply_B` — proof appears to close via minimal tactic one-liner
  - L393 [soft] `skeletal-proof` in `lemma Binv_apply_transportJ` — proof appears to close via minimal tactic one-liner
  - L500 [soft] `skeletal-proof` in `theorem transportK_sq` — proof appears to close via minimal tactic one-liner
  - L519 [soft] `skeletal-proof` in `theorem transportPi_sq` — proof appears to close via minimal tactic one-liner
  - L535 [soft] `skeletal-proof` in `theorem transportGamma_car` — proof appears to close via minimal tactic one-liner
  - L570 [soft] `skeletal-proof` in `theorem preservesPolarization_iff_transportP_eq` — proof appears to close via minimal tactic one-liner
  - L584 [advisory] `local-hypothesis-injection` in `theorem preservesPolarization_iff_transportP_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L585 [advisory] `local-hypothesis-injection` in `theorem preservesPolarization_iff_transportP_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L594 [soft] `skeletal-proof` in `lemma map_plus_of_preserves` — proof appears to close via minimal tactic one-liner
  - L602 [advisory] `local-hypothesis-injection` in `lemma map_plus_of_preserves` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L606 [soft] `skeletal-proof` in `lemma map_minus_of_preserves` — proof appears to close via minimal tactic one-liner
  - L614 [advisory] `local-hypothesis-injection` in `lemma map_minus_of_preserves` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L647 [advisory] `local-hypothesis-injection` in `lemma map_minus_of_preserves` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L650 [advisory] `local-hypothesis-injection` in `lemma map_minus_of_preserves` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L656 [advisory] `local-hypothesis-injection` in `lemma map_minus_of_preserves` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L659 [advisory] `local-hypothesis-injection` in `lemma map_minus_of_preserves` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L671 [soft] `simp-law-injection` in `simp-declaration hom_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L674 [soft] `simp-law-injection` in `simp-declaration hom_comp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L685 [soft] `law-field-locker` in `structure-field PolarizationSplit.Pminus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L686 [soft] `law-field-locker` in `structure-field PolarizationSplit.Pplus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L687 [soft] `law-field-locker` in `structure-field PolarizationSplit.minus_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L688 [soft] `law-field-locker` in `structure-field PolarizationSplit.plus_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L689 [soft] `law-field-locker` in `structure-field PolarizationSplit.cross_minus_plus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L690 [soft] `law-field-locker` in `structure-field PolarizationSplit.cross_plus_minus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L691 [soft] `law-field-locker` in `structure-field PolarizationSplit.split_sum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L697 [soft] `law-field-locker` in `structure-field PolarizationSplit.f` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L698 [soft] `law-field-locker` in `structure-field PolarizationSplit.finv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L699 [soft] `law-field-locker` in `structure-field PolarizationSplit.left_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L700 [soft] `law-field-locker` in `structure-field PolarizationSplit.right_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L701 [soft] `law-field-locker` in `structure-field PolarizationSplit.intertwines_minus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L702 [soft] `law-field-locker` in `structure-field PolarizationSplit.intertwines_plus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L708 [soft] `law-field-locker` in `structure-field PolarizationSplit.finv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L709 [soft] `law-field-locker` in `structure-field PolarizationSplit.left_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L710 [soft] `law-field-locker` in `structure-field PolarizationSplit.right_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L711 [soft] `law-field-locker` in `structure-field PolarizationSplit.intertwines_minus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L712 [soft] `law-field-locker` in `structure-field PolarizationSplit.intertwines_plus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L715 [soft] `law-field-locker` in `structure-field PolarizationSplit.finv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L716 [soft] `law-field-locker` in `structure-field PolarizationSplit.left_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L718 [advisory] `local-hypothesis-injection` in `structure PolarizationSplit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L721 [advisory] `local-hypothesis-injection` in `structure PolarizationSplit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L725 [soft] `law-field-locker` in `structure-field PolarizationSplit.right_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L727 [advisory] `local-hypothesis-injection` in `structure PolarizationSplit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L730 [advisory] `local-hypothesis-injection` in `structure PolarizationSplit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L734 [soft] `law-field-locker` in `structure-field PolarizationSplit.intertwines_minus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L742 [soft] `law-field-locker` in `structure-field PolarizationSplit.intertwines_plus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L750 [soft] `simp-law-injection` in `simp-declaration hom_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L753 [soft] `simp-law-injection` in `simp-declaration hom_comp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L774 [advisory] `local-hypothesis-injection` in `def splitOfPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L789 [advisory] `local-hypothesis-injection` in `def splitOfPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L804 [advisory] `local-hypothesis-injection` in `def splitOfPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L811 [advisory] `local-hypothesis-injection` in `def splitOfPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L825 [soft] `skeletal-proof` in `lemma plus_sub_minus_eq_P` — proof appears to close via minimal tactic one-liner
  - L842 [soft] `skeletal-proof` in `theorem involutionOfSplit_sq` — proof appears to close via minimal tactic one-liner
  - L848 [advisory] `local-hypothesis-injection` in `theorem involutionOfSplit_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L851 [advisory] `local-hypothesis-injection` in `theorem involutionOfSplit_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L854 [advisory] `local-hypothesis-injection` in `theorem involutionOfSplit_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L857 [advisory] `local-hypothesis-injection` in `theorem involutionOfSplit_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L860 [advisory] `local-hypothesis-injection` in `theorem involutionOfSplit_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L861 [advisory] `local-hypothesis-injection` in `theorem involutionOfSplit_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L883 [soft] `skeletal-proof` in `theorem ofSplit_splitOfPolarization_P` — proof appears to close via minimal tactic one-liner
  - L960 [soft] `law-field-locker` in `structure-field PolarizedMajorana.polarization` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L969 [soft] `simp-law-injection` in `simp-declaration ofPolarization_polarization` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1012 [advisory] `local-hypothesis-injection` in `def ofPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1015 [advisory] `local-hypothesis-injection` in `def ofPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1021 [advisory] `local-hypothesis-injection` in `def ofPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1024 [advisory] `local-hypothesis-injection` in `def ofPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1083 [soft] `simp-law-injection` in `simp-declaration hom_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1086 [soft] `simp-law-injection` in `simp-declaration hom_comp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1100 [soft] `skeletal-proof` in `theorem Hom.gamma_intertwines` — proof appears to close via minimal tactic one-liner
  - L1106 [advisory] `local-hypothesis-injection` in `theorem Hom.gamma_intertwines` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1107 [advisory] `local-hypothesis-injection` in `theorem Hom.gamma_intertwines` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1122 [soft] `skeletal-proof` in `theorem Hom.toBogoliubovTransform_transportP_eq` — proof appears to close via minimal tactic one-liner
  - L1131 [advisory] `local-hypothesis-injection` in `theorem Hom.toBogoliubovTransform_transportP_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1143 [soft] `skeletal-proof` in `theorem Hom.toBogoliubovTransform_preservesPolarization` — proof appears to close via minimal tactic one-liner

