# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:18.012587+00:00`
Root: `lean/InfoGeometry/Clifford/HestenesDirac.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **54**
- Hard: **0**
- Soft: **52**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Clifford/HestenesDirac.lean` | `advisory` | 106 | 0 | 52 | 2 | 54 |

## Findings by file

### `lean/InfoGeometry/Clifford/HestenesDirac.lean`
- module: `InfoGeometry.Clifford.HestenesDirac`
- status: `advisory`
- debt_score: `106`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [soft] `law-field-locker` in `structure-field RealSpacetimeAlgebra.gamma0_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L36 [soft] `law-field-locker` in `structure-field RealSpacetimeAlgebra.gamma1_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field RealSpacetimeAlgebra.gamma2_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field RealSpacetimeAlgebra.gamma3_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field RealSpacetimeAlgebra.ellipticBivector_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field RealSpacetimeAlgebra.hyperbolicBivector_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field RealSpacetimeAlgebra.spinPlane_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field RealRotor.rotor_reverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field RealRotor.reverse_rotor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field DiracHestenesSpinor.densityScale` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L99 [soft] `skeletal-proof` in `theorem current_eq_density_smul_velocityFrame` — proof appears to close via minimal tactic one-liner
  - L104 [soft] `skeletal-proof` in `theorem spinPlane_eq_density_smul_orientedSpinPlane` — proof appears to close via minimal tactic one-liner
  - L123 [soft] `law-field-locker` in `structure-field DiracHestenesPolarDecomposition.densityScale` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L132 [soft] `law-field-locker` in `structure-field DiracHestenesPolarDecomposition.reconstruct` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L133 [soft] `law-field-locker` in `structure-field DiracHestenesPolarDecomposition.spinor_eq_density_rotor_phase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L168 [soft] `skeletal-proof` in `theorem polar_current_eq_density_velocity` — proof appears to close via minimal tactic one-liner
  - L173 [soft] `skeletal-proof` in `theorem polar_spinPlane_eq_density_spinPlane` — proof appears to close via minimal tactic one-liner
  - L178 [soft] `skeletal-proof` in `theorem yvonTakabayasiAngle_of_polar_eq` — proof appears to close via minimal tactic one-liner
  - L183 [soft] `skeletal-proof` in `theorem phasePlane_of_polar_eq` — proof appears to close via minimal tactic one-liner
  - L199 [soft] `law-field-locker` in `structure-field DiracHestenesEquation.nabla` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L200 [soft] `law-field-locker` in `structure-field DiracHestenesEquation.rightSpinPlane` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L201 [soft] `law-field-locker` in `structure-field DiracHestenesEquation.realScale` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L204 [soft] `law-field-locker` in `structure-field DiracHestenesEquation.mass_clock_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L210 [soft] `law-field-locker` in `structure-field electromagneticGaugeRotation.rotateInSpinPlane` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L211 [soft] `law-field-locker` in `structure-field electromagneticGaugeRotation.potentialShift` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L218 [soft] `law-field-locker` in `structure-field pauliMagneticCoupling.pairing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L219 [soft] `law-field-locker` in `structure-field pauliMagneticCoupling.coupling` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L228 [soft] `law-field-locker` in `structure-field DiracHestenesConservationPacket.divergence` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L229 [soft] `law-field-locker` in `structure-field DiracHestenesConservationPacket.spinTransportDefect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L231 [soft] `law-field-locker` in `structure-field DiracHestenesConservationPacket.current_conserved` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L233 [soft] `law-field-locker` in `structure-field DiracHestenesConservationPacket.spin_plane_transported` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L265 [soft] `law-field-locker` in `structure-field RealFourByFourBiquaternionSlice.transpose` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L266 [soft] `law-field-locker` in `structure-field RealFourByFourBiquaternionSlice.determinant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L267 [soft] `law-field-locker` in `structure-field RealFourByFourBiquaternionSlice.pfaffian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L269 [soft] `law-field-locker` in `structure-field RealFourByFourBiquaternionSlice.J_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L271 [soft] `law-field-locker` in `structure-field RealFourByFourBiquaternionSlice.commutes_with_J` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L273 [soft] `law-field-locker` in `structure-field RealFourByFourBiquaternionSlice.symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L275 [soft] `law-field-locker` in `structure-field RealFourByFourBiquaternionSlice.pfaffianSJ` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L277 [soft] `law-field-locker` in `structure-field RealFourByFourBiquaternionSlice.det_realification_eq_interval_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L279 [soft] `law-field-locker` in `structure-field RealFourByFourBiquaternionSlice.interval_eq_neg_pfaffianSJ` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L281 [soft] `law-field-locker` in `structure-field RealFourByFourBiquaternionSlice.null_cone_iff_pfaffian_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L308 [soft] `law-field-locker` in `structure-field MajoranaBdGFourByFour.transpose` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L309 [soft] `law-field-locker` in `structure-field MajoranaBdGFourByFour.determinant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L310 [soft] `law-field-locker` in `structure-field MajoranaBdGFourByFour.pfaffian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L311 [soft] `law-field-locker` in `structure-field MajoranaBdGFourByFour.skewSymmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L313 [soft] `law-field-locker` in `structure-field MajoranaBdGFourByFour.det_eq_pfaffian_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L315 [soft] `law-field-locker` in `structure-field MajoranaBdGFourByFour.zero_mode_iff_pfaffian_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L532 [soft] `skeletal-proof` in `theorem concrete_det_realification_eq_interval_sq` — proof appears to close via minimal tactic one-liner
  - L593 [soft] `skeletal-proof` in `theorem concreteMajoranaBdG_det_eq_pfaffian_sq` — proof appears to close via minimal tactic one-liner
  - L626 [soft] `law-field-locker` in `structure-field RealPfaffianBridge.biquaternionNull` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L627 [soft] `law-field-locker` in `structure-field RealPfaffianBridge.bdgZeroMode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L628 [soft] `law-field-locker` in `structure-field RealPfaffianBridge.pfaffian_bridge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L635 [advisory] `bridge-shaped-declaration` in `theorem pfaffian_bridge_extract` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

