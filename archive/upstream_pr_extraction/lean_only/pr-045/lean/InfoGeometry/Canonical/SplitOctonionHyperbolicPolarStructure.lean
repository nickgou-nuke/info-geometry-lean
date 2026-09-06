import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Complex.Exponential
import InfoGeometry.Canonical.SplitOctonionQuaternionChart
import InfoGeometry.Canonical.SplitOctonionExpLog
import InfoGeometry.Canonical.SplitOctonionQuaternionPolar

noncomputable section

namespace SplitOctonion

/-- The hyperbolic polar coordinates on the positive-norm cone N(X) > 0 with b ≠ 0. -/
structure HyperbolicPolarData where
  rho : ℝ
  eta : ℝ
  u : H
  g : H
  rho_pos : 0 < rho
  eta_nonneg : 0 ≤ eta
  norm_u : Quaternion.normSq u = 1
  norm_g : Quaternion.normSq g = 1

/-- Reconstruct a split octonion from its hyperbolic polar data. -/
def HyperbolicPolarData.reconstruct (P : HyperbolicPolarData) : SplitOctonion :=
  ⟨P.rho • P.u, 0⟩ * expHyperbolic 1 P.eta (J_g P.g)

/-- Extract hyperbolic polar data from a hyperbolic split octonion with b ≠ 0. -/
def toHyperbolicPolarData (X : SplitOctonion) (h : isHyperbolic X) (hb : X.b ≠ 0) : HyperbolicPolarData where
  rho := polarRho X h
  eta := polarEta X h
  u := polarU X (a_ne_zero_of_isHyperbolic X h)
  g := polarG X (a_ne_zero_of_isHyperbolic X h) hb
  rho_pos := Real.sqrt_pos.mpr h
  eta_nonneg := by
    unfold polarEta
    apply Real.arcosh_nonneg
    have h4 : normSQ X ≤ Quaternion.normSq X.a := by
      unfold normSQ
      have h1a : (X.a * star X.a).re = Quaternion.normSq X.a := (normSq_eq_re_mul_star X.a).symm
      have h2b : (X.b * star X.b).re = Quaternion.normSq X.b := (normSq_eq_re_mul_star X.b).symm
      rw [h1a, h2b]
      have h_b_nonneg : 0 ≤ Quaternion.normSq X.b := Quaternion.normSq_nonneg
      linarith
    apply (one_le_div (Real.sqrt_pos.mpr h)).mpr
    apply Real.sqrt_le_sqrt h4
  norm_u := normSq_polarU X (a_ne_zero_of_isHyperbolic X h)
  norm_g := normSq_polarG X (a_ne_zero_of_isHyperbolic X h) hb

/-- Reconstruction Theorem: reconstruct(toHyperbolicPolarData X h hb) = X. -/
theorem polarCoordinates_reconstruct (X : SplitOctonion) (h : isHyperbolic X) (hb : X.b ≠ 0) :
    (toHyperbolicPolarData X h hb).reconstruct = X := by
  unfold HyperbolicPolarData.reconstruct toHyperbolicPolarData
  exact (polar_decomposition X h hb).symm

end SplitOctonion
