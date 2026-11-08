import InfoGeometry.Physics.PellisFineStructure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.BostConnes.BostConnesParity

namespace InfoGeometry.Physics.PellisfineStructure

open InfoGeometry.BostConnes

/-- Compatibility name for the canonical Pellis golden ratio. -/
noncomputable abbrev goldenRatio : ℝ := PellisFineStructure.phi

/-- Compatibility name for the canonical Pellis fine-structure readout. -/
noncomputable abbrev pellis_alpha_inv : ℝ := PellisFineStructure.pellis_alpha_inv

/-- The paper's displayed equation (9), kept as data rather than asserted equal
to the primary formula. -/
noncomputable def pellis_alpha_inv_v9 : ℝ :=
  (362 - 3 - 4) / goldenRatio^2 - (1 - 3 - 5) / goldenRatio

/-- The paper's displayed equation (10), kept as data rather than used as an
unproved replacement for the primary formula. -/
noncomputable def pellis_alpha_inv_v10 : ℝ :=
  (362 - 3 - 4) + (3 - 4 + 2 * 3^(-5 : ℤ) - 364) / goldenRatio

/-- The paper's displayed equation (11), kept as data rather than used as an
unproved replacement for the primary formula. -/
noncomputable def pellis_alpha_inv_v11 : ℝ :=
  goldenRatio^0 - 2 / goldenRatio + 360 / goldenRatio^2 -
    1 / goldenRatio^3 + 1 / (3 * goldenRatio)^5

/-- The golden ratio satisfies the quadratic equation `φ² = φ + 1`. -/
theorem goldenRatio_quadratic : goldenRatio ^ 2 = goldenRatio + 1 := by
  exact PellisFineStructure.phi_quadratic

/-- The golden ratio is positive. -/
theorem goldenRatio_pos : goldenRatio > 0 := by
  exact PellisFineStructure.phi_pos

/-- Reciprocal-square normal form for the golden ratio. -/
theorem goldenRatio_inv_sq : 1 / goldenRatio ^ 2 = 2 - goldenRatio := by
  exact PellisFineStructure.inv_sq

/-- Reciprocal-cube normal form for the golden ratio. -/
theorem goldenRatio_inv_cube : 1 / goldenRatio ^ 3 = 2 * goldenRatio - 3 := by
  exact PellisFineStructure.inv_cube

/-- Reciprocal-fifth normal form for the golden ratio. -/
theorem goldenRatio_inv_fifth : 1 / goldenRatio ^ 5 = 5 * goldenRatio - 8 := by
  exact PellisFineStructure.inv_fifth

/-- Pellis primary formula bounds in exact rational form. -/
theorem pellis_alpha_inv_bounds :
    (1370359991 : ℝ) / 10000000 < pellis_alpha_inv ∧
      pellis_alpha_inv < (171294999 : ℝ) / 1250000 := by
  exact PellisFineStructure.pellis_bounds

/-- Agreement with the CODATA comparison value at the stated tolerance. -/
theorem pellis_alpha_inv_matches_codata :
    |pellis_alpha_inv - (137035999084 : ℝ) / 1000000000| < (1 : ℝ) / 10000000 := by
  exact PellisFineStructure.codata_agreement

/-- Pellis primary formula in the linear basis `{1, φ}`. -/
theorem pellis_alpha_inv_normal_form :
    pellis_alpha_inv = (176410 : ℝ) / 243 - ((88447 : ℝ) / 243) * goldenRatio := by
  exact PellisFineStructure.pellis_normal_form

/-- The displayed equation (9) is exactly the stored equation-(9) expression. -/
theorem pellis_alpha_inv_v9_readback :
    pellis_alpha_inv_v9 =
      (362 - 3 - 4) / goldenRatio^2 - (1 - 3 - 5) / goldenRatio := by
  rfl

/-- Arithmetic foundation: Möbius is squarefree projection times Liouville parity. -/
theorem arithmetic_foundation_connection :
    ∀ n : ℕ, ArithmeticFunction.moebius n = squarefreeProj n * liouvilleParity n := by
  intro n
  exact moebius_eq_squarefreeProj_mul_liouvilleParity n

end InfoGeometry.Physics.PellisfineStructure
