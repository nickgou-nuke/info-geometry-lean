/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.SeibergWittenMonopoleDuality

/-!
# Audit Module for Section 146: Seiberg-Witten Electromagnetic Duality
Target: `InfoGeometry/Superalgebra/SeibergWittenMonopoleDualityAudit.lean`

Provides concrete integer (`ℤ`) evaluations and checks by `decide`.
-/

namespace InfoGeometry.Superalgebra.SeibergWittenAudit

open InfoGeometry.Superalgebra.SeibergWitten

/-- Concrete integer verification of `J paraSymplecticK0 = neg paraSymplecticK0`. -/
theorem audit_cpt_time_inversion_int :
    SplitOctonion.J (SplitOctonion.paraSymplecticK0 : SplitOctonion ℤ) =
      SplitOctonion.neg (SplitOctonion.paraSymplecticK0 : SplitOctonion ℤ) := by decide

/-- Concrete integer verification of electromagnetic duality `J(quark u) = neg(antiquark u)`. -/
theorem audit_em_duality_quark_to_monopole_int :
    SplitOctonion.J (SplitOctonion.quark canonicalColorVec3Int) =
      SplitOctonion.neg (SplitOctonion.antiquark canonicalColorVec3Int) := by decide

/-- Concrete integer verification of BPS mass formula for `(q, g) = (5, 3)` (`5^2 - 3^2 = 16`). -/
theorem audit_bps_mass_formula_int :
    SplitOctonion.intervalNorm (SplitOctonion.seibergWittenBpsCharge (5 : ℤ) (3 : ℤ)) = 16 := by
  decide

/-- Concrete integer verification of massless monopole threshold at `(q, g) = (4, -4)`. -/
theorem audit_bps_null_threshold_int :
    SplitOctonion.intervalNorm (SplitOctonion.seibergWittenBpsCharge (4 : ℤ) (-4 : ℤ)) = 0 := by
  decide

/-- Concrete integer non-commutativity of split-octonion multiplication. -/
theorem audit_split_octonion_noncommutative_int :
    SplitOctonion.mul octonionBasisU1Int octonionBasisU2Int ≠
      SplitOctonion.mul octonionBasisU2Int octonionBasisU1Int := by decide

end InfoGeometry.Superalgebra.SeibergWittenAudit
