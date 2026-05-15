# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:36.388197+00:00`
Root: `lean/InfoGeometry/Quantum/RealMajoranaCategory.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **75**
- Hard: **0**
- Soft: **50**
- Advisory: **25**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/RealMajoranaCategory.lean` | `advisory` | 125 | 0 | 50 | 25 | 75 |

## Findings by file

### `lean/InfoGeometry/Quantum/RealMajoranaCategory.lean`
- module: `InfoGeometry.Quantum.RealMajoranaCategory`
- status: `advisory`
- debt_score: `125`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L25 [soft] `law-field-locker` in `structure-field RealMajoranaCore.J` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L26 [soft] `law-field-locker` in `structure-field RealMajoranaCore.eps` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L27 [soft] `law-field-locker` in `structure-field RealMajoranaCore.Pi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L28 [soft] `law-field-locker` in `structure-field RealMajoranaCore.J_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L29 [soft] `law-field-locker` in `structure-field RealMajoranaCore.eps_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L30 [soft] `law-field-locker` in `structure-field RealMajoranaCore.Pi_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L31 [soft] `law-field-locker` in `structure-field RealMajoranaCore.J_eps_anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `skeletal-proof` in `lemma K_sq` — proof appears to close via minimal tactic one-liner
  - L67 [soft] `skeletal-proof` in `lemma Hom.comm_K` — proof appears to close via minimal tactic one-liner
  - L113 [soft] `simp-law-injection` in `simp-declaration hom_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L115 [soft] `simp-law-injection` in `simp-declaration hom_comp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L169 [soft] `law-field-locker` in `structure-field SplitCliffordDatum.rho` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L177 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L189 [soft] `skeletal-proof` in `theorem majoranaField_anticommutator_eq_polar` — proof appears to close via minimal tactic one-liner
  - L208 [soft] `skeletal-proof` in `theorem majorana_car_of_splitClifford` — proof appears to close via minimal tactic one-liner
  - L217 [advisory] `local-hypothesis-injection` in `theorem majorana_car_of_splitClifford` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L263 [soft] `skeletal-proof` in `theorem majorana_car_of_concrete_cl11` — proof appears to close via minimal tactic one-liner
  - L291 [soft] `skeletal-proof` in `lemma cl11_uMinus_isotropic` — proof appears to close via minimal tactic one-liner
  - L296 [soft] `skeletal-proof` in `lemma cl11_uPlus_isotropic` — proof appears to close via minimal tactic one-liner
  - L301 [soft] `skeletal-proof` in `lemma cl11_uMinus_uPlus_pairing_half` — proof appears to close via minimal tactic one-liner
  - L312 [soft] `law-field-locker` in `structure-field Polarization.Pplus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L313 [soft] `law-field-locker` in `structure-field Polarization.Pminus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L314 [soft] `law-field-locker` in `structure-field Polarization.plus_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L315 [soft] `law-field-locker` in `structure-field Polarization.minus_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L318 [soft] `law-field-locker` in `structure-field Polarization.sum_id` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L319 [soft] `law-field-locker` in `structure-field Polarization.comm_Pi_plus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L320 [soft] `law-field-locker` in `structure-field Polarization.comm_Pi_minus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L329 [soft] `skeletal-proof` in `theorem involution_comm_Pi` — proof appears to close via minimal tactic one-liner
  - L339 [soft] `skeletal-proof` in `theorem involution_sq` — proof appears to close via minimal tactic one-liner
  - L344 [advisory] `local-hypothesis-injection` in `theorem involution_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L347 [advisory] `local-hypothesis-injection` in `theorem involution_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L356 [advisory] `local-hypothesis-injection` in `theorem involution_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L388 [advisory] `local-hypothesis-injection` in `def ofInvolution` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L403 [advisory] `local-hypothesis-injection` in `def ofInvolution` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L418 [advisory] `local-hypothesis-injection` in `def ofInvolution` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L425 [advisory] `local-hypothesis-injection` in `def ofInvolution` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L441 [advisory] `local-hypothesis-injection` in `def ofInvolution` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L447 [advisory] `local-hypothesis-injection` in `def ofInvolution` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L452 [soft] `skeletal-proof` in `theorem involution_ofInvolution` — proof appears to close via minimal tactic one-liner
  - L467 [soft] `skeletal-proof` in `theorem ofInvolution_involution_Pplus` — proof appears to close via minimal tactic one-liner
  - L473 [advisory] `local-hypothesis-injection` in `theorem ofInvolution_involution_Pplus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L476 [advisory] `local-hypothesis-injection` in `theorem ofInvolution_involution_Pplus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L494 [soft] `skeletal-proof` in `theorem ofInvolution_involution_Pminus` — proof appears to close via minimal tactic one-liner
  - L500 [advisory] `local-hypothesis-injection` in `theorem ofInvolution_involution_Pminus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L503 [advisory] `local-hypothesis-injection` in `theorem ofInvolution_involution_Pminus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L527 [soft] `simp-law-injection` in `simp-declaration spectralPlusProj_apply_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L540 [soft] `simp-law-injection` in `simp-declaration spectralMinusProj_apply_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L558 [advisory] `local-hypothesis-injection` in `lemma spectralPlusProj_comp_spectralMinusProj` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L568 [advisory] `local-hypothesis-injection` in `lemma spectralMinusProj_comp_spectralPlusProj` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L579 [advisory] `local-hypothesis-injection` in `lemma spectralPlusProj_comm_Pi` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L590 [advisory] `local-hypothesis-injection` in `lemma spectralMinusProj_comm_Pi` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L614 [soft] `simp-law-injection` in `simp-declaration cl11_majoranaField_uMinus_apply_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L621 [advisory] `local-hypothesis-injection` in `def cl11CanonicalPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L637 [soft] `simp-law-injection` in `simp-declaration cl11_majoranaField_uPlus_apply_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L644 [advisory] `local-hypothesis-injection` in `def cl11CanonicalPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L665 [soft] `law-field-locker` in `structure-field LadderPresentation.create` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L666 [soft] `law-field-locker` in `structure-field LadderPresentation.annihil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L667 [soft] `law-field-locker` in `structure-field LadderPresentation.create_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L668 [soft] `law-field-locker` in `structure-field LadderPresentation.annihil_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L669 [soft] `law-field-locker` in `structure-field LadderPresentation.mixed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L681 [soft] `law-field-locker` in `structure-field PolarizedMajorana.comm_Pplus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L682 [soft] `law-field-locker` in `structure-field PolarizedMajorana.comm_Pminus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L688 [soft] `law-field-locker` in `structure-field PolarizedMajorana.comm_Pplus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L689 [soft] `law-field-locker` in `structure-field PolarizedMajorana.comm_Pminus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L692 [soft] `law-field-locker` in `structure-field PolarizedMajorana.comm_Pplus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L707 [soft] `law-field-locker` in `structure-field PolarizedMajorana.comm_Pminus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L722 [soft] `simp-law-injection` in `simp-declaration hom_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L725 [soft] `simp-law-injection` in `simp-declaration hom_comp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L758 [soft] `law-field-locker` in `structure-field PolarizedLadderRealization.minus_isotropic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L759 [soft] `law-field-locker` in `structure-field PolarizedLadderRealization.plus_isotropic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L760 [soft] `law-field-locker` in `structure-field PolarizedLadderRealization.mixed_half` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L786 [advisory] `local-hypothesis-injection` in `def ladderOfRealization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L842 [advisory] `local-hypothesis-injection` in `def cl11_concrete_ladder_realization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L862 [advisory] `local-hypothesis-injection` in `def cl11_concrete_ladder_realization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

