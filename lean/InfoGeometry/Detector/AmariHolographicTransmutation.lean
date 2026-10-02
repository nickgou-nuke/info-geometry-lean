import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace DetectorGeometry.AmariHolographicTransmutation

section AmariMetric

noncomputable def metricN (N : ℝ) : ℝ := 1 / N

def countCoordinate (x : ℝ) : ℝ := x ^ 2

def jacobian (x : ℝ) : ℝ := 2 * x

noncomputable def metricX (x : ℝ) : ℝ := metricN (countCoordinate x) * jacobian x ^ 2

theorem metricX_constant {x : ℝ} (hx : x ≠ 0) : metricX x = 4 := by
  simp only [metricX, metricN, countCoordinate, jacobian]
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  field_simp [hx2]
  ring

def christoffelX : ℝ := 0

theorem christoffelX_zero : christoffelX = 0 := rfl

end AmariMetric

section HolographicInvariance

noncomputable def singleFlux (C z : ℝ) : ℝ := C / z ^ 2

noncomputable def coincidenceFlux (C z : ℝ) : ℝ := C / z ^ 4

noncomputable def calibration (C₁ C₂ z : ℝ) : ℝ :=
  singleFlux C₁ z / Real.sqrt (coincidenceFlux C₂ z)

theorem calibration_constant (C₁ C₂ z : ℝ) (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂) (hz : 0 < z) :
    calibration C₁ C₂ z = C₁ / Real.sqrt C₂ := by
  simp only [calibration, singleFlux, coincidenceFlux]
  have hz2 : 0 < z ^ 2 := sq_pos_of_pos hz
  have hz4 : z ^ 4 = (z ^ 2) ^ 2 := by ring
  rw [hz4, Real.sqrt_div (le_of_lt hC₂), Real.sqrt_sq (le_of_lt hz2)]
  field_simp [ne_of_gt hz2, ne_of_gt (Real.sqrt_pos.mpr hC₂)]

theorem rg_scale_variation_zero (C₁ C₂ z scale : ℝ) (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂) (hz : 0 < z) (hscale : 0 < scale) :
    calibration C₁ C₂ (scale * z) - calibration C₁ C₂ z = 0 := by
  rw [calibration_constant C₁ C₂ (scale * z) hC₁ hC₂ (mul_pos hscale hz),
    calibration_constant C₁ C₂ z hC₁ hC₂ hz]
  ring

end HolographicInvariance

section Transmutation

noncomputable def massScale (k W : ℝ) : ℝ := Real.sqrt (k * W)

noncomputable def lengthScale (k W : ℝ) : ℝ := (massScale k W)⁻¹

theorem transmutation_duality (k W : ℝ) (hk : 0 < k) (hW : 0 < W) :
    massScale k W * lengthScale k W = 1 := by
  simp only [massScale, lengthScale]
  exact mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (mul_pos hk hW)))

end Transmutation

section Geodesic

def flatGeodesic (a b t : ℝ) : ℝ := a * t + b

theorem geodesic_zero_intercept (a b : ℝ)
    (hzero : flatGeodesic a b 0 = 0) : b = 0 := by
  simpa [flatGeodesic] using hzero

theorem geodesic_linear (a b t : ℝ)
    (hzero : flatGeodesic a b 0 = 0) : flatGeodesic a b t = a * t := by
  rw [show b = 0 by exact geodesic_zero_intercept a b hzero]
  simp [flatGeodesic]

end Geodesic

section CausalPoset

inductive Archetype
  | amariFlattening
  | rgInvariant
  | transmutation
  | geodesicVacuum
  deriving DecidableEq, Repr

def rank : Archetype → Nat
  | .amariFlattening => 138
  | .rgInvariant => 139
  | .transmutation => 140
  | .geodesicVacuum => 141

def causallyPrecedes (a b : Archetype) : Prop := rank a ≤ rank b

theorem causal_refl (a : Archetype) : causallyPrecedes a a := le_rfl

theorem causal_trans {a b c : Archetype} :
    causallyPrecedes a b → causallyPrecedes b c → causallyPrecedes a c := by
  exact Nat.le_trans

theorem causal_antisymm {a b : Archetype} :
    causallyPrecedes a b → causallyPrecedes b a → a = b := by
  intro hab hba
  cases a <;> cases b <;> simp [causallyPrecedes, rank] at hab hba ⊢

theorem canonical_chain :
    causallyPrecedes .amariFlattening .rgInvariant ∧
    causallyPrecedes .rgInvariant .transmutation ∧
    causallyPrecedes .transmutation .geodesicVacuum := by
  norm_num [causallyPrecedes, rank]

end CausalPoset

end DetectorGeometry.AmariHolographicTransmutation
