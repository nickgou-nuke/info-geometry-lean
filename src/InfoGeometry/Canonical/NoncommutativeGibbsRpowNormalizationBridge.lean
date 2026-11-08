import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import InfoGeometry.Canonical.SouriauOnsagerBKMBridge

/-!
# Normalized Gibbs real powers through native CFC

This owner isolates the spectral/CFC normalization identity needed after the
Fréchet--Duhamel two-point theorem.

For a self-adjoint generator `H` and a strictly positive real scalar `Z`, put

`g_Z(x) = Z⁻¹ * exp x`.

The normalized Gibbs operator is `cfc g_Z H`.  Since every spectral value of
`g_Z(H)` is strictly positive, its native CFC real power may be composed back
through `H`.  The scalar identity

`(Z⁻¹ exp x)^s = Z^(-s) exp(s x)`

then gives the exact spectral formula for the Gibbs power.

The final theorem is deliberately stated as equality of CFC values.  It does
not assume an unverified theorem name for pulling a constant scalar through
CFC.  Rewriting the right side as `Z^(-s) • exp(s • H)` is a downstream
syntactic transport once that Mathlib API is pinned by compilation.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.NoncommutativeGibbsRpowNormalizationBridge

open SouriauOnsagerBKM
open scoped ComplexOrder

/-- Positive scalar normalized exponential weight. -/
def normalizedScalarGibbsWeight (Z : ℝ) (x : ℝ) : ℝ :=
  Z⁻¹ * Real.exp x

/-- Scalar power identity behind normalized Gibbs real powers. -/
theorem normalizedScalarGibbsWeight_rpow
    (Z x s : ℝ) (hZ : 0 < Z) :
    (normalizedScalarGibbsWeight Z x) ^ s =
      Z ^ (-s) * Real.exp (s * x) := by
  have hZinv : 0 < Z⁻¹ := inv_pos.mpr hZ
  have hweight : 0 < normalizedScalarGibbsWeight Z x :=
    mul_pos hZinv (Real.exp_pos x)
  simp only [normalizedScalarGibbsWeight] at hweight ⊢
  rw [Real.rpow_def_of_pos hweight]
  rw [Real.log_mul hZinv.ne' (Real.exp_pos x).ne']
  rw [Real.log_inv, Real.log_exp]
  rw [Real.rpow_def_of_pos hZ]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The normalized scalar Gibbs weight is continuous. -/
theorem continuous_normalizedScalarGibbsWeight (Z : ℝ) :
    Continuous (normalizedScalarGibbsWeight Z) := by
  unfold normalizedScalarGibbsWeight
  fun_prop

/-- On a self-adjoint carrier, the normalized Gibbs CFC weight is strictly
positive whenever `Z > 0`. -/
theorem normalizedGibbsCFC_isStrictlyPositive
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (H : A) (hH : IsSelfAdjoint H) (Z : ℝ) (hZ : 0 < Z) :
    IsStrictlyPositive (cfc (normalizedScalarGibbsWeight Z) H) := by
  have hcont := continuous_normalizedScalarGibbsWeight Z
  apply (cfc_isStrictlyPositive_iff
    (normalizedScalarGibbsWeight Z) H hcont.continuousOn).2
  intro x hx
  exact mul_pos (inv_pos.mpr hZ) (Real.exp_pos x)

/-- Spectral/CFC form of the Gibbs normalization power law.

This is the theorem-content of
`rho^s = Z^(-s) exp(sH)` before the final scalar/CFC syntactic rewrite. -/
theorem normalizedGibbsCFC_rpow
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (H : A) (hH : IsSelfAdjoint H) (Z s : ℝ) (hZ : 0 < Z) :
    CFC.rpow (cfc (normalizedScalarGibbsWeight Z) H) s =
      cfc (fun x : ℝ => Z ^ (-s) * Real.exp (s * x)) H := by
  have hpos := normalizedGibbsCFC_isStrictlyPositive H hH Z hZ
  change (cfc (normalizedScalarGibbsWeight Z) H) ^ s = _
  rw [CFC.rpow_eq_cfc_real hpos.nonneg]
  have hweight_pos : ∀ x : ℝ, 0 < normalizedScalarGibbsWeight Z x := by
    intro x
    exact mul_pos (inv_pos.mpr hZ) (Real.exp_pos x)
  have houter : ContinuousOn (fun y : ℝ => y ^ s)
      (normalizedScalarGibbsWeight Z '' spectrum ℝ H) := by
    rintro y ⟨x, hx, rfl⟩
    exact (Real.continuousAt_rpow_const _ _
      (Or.inl (ne_of_gt (hweight_pos x)))).continuousWithinAt
  have hinner : ContinuousOn (normalizedScalarGibbsWeight Z) (spectrum ℝ H) :=
    (continuous_normalizedScalarGibbsWeight Z).continuousOn
  rw [← cfc_comp (fun y : ℝ => y ^ s)
    (normalizedScalarGibbsWeight Z) H
    (ha := hH) (hg := houter) (hf := hinner)]
  apply cfc_congr
  intro x hx
  exact normalizedScalarGibbsWeight_rpow Z x s hZ

end InfoGeometry.Canonical.NoncommutativeGibbsRpowNormalizationBridge
