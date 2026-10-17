/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.UnifiedInfoGeometryPetzFockBridge

/-!
# Sign repair candidate for the varying inverse-prior metric

This scratch candidate records the ordinary one-dimensional derivative of the
inverse-prior pairing along the affine path `ρ + t X`, and an algebraic
`DualConnectionManifold` whose `diff_g` and exponential connection have the
corresponding negative sign. The derivative theorem needs only nonzero
coordinates at the basepoint; it does not assert that the full function space
is a probability simplex or a tangent bundle.
-/

noncomputable section

namespace InfoGeometry.Canonical.UnifiedInfoGeometryPetzFockBridge.SignRepairCandidate

open BigOperators
open InfoGeometry.Modular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Directional derivative of the inverse-prior pairing along `ρ + t X`.
The nonzero-coordinate basepoint hypothesis makes every reciprocal derivative
well-defined at `t = 0`; no claim is made about positivity away from zero. -/
theorem chiSquaredInner_affine_hasDerivAt
    (ρ X Y Z : ι → ℝ) (hρ : ∀ i, ρ i ≠ 0) :
    HasDerivAt
      (fun t : ℝ => chiSquaredInner (fun i => ρ i + t * X i) Y Z)
      (∑ i, -(X i * Y i * Z i / (ρ i * ρ i))) 0 := by
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => by
      have hline : HasDerivAt (fun t : ℝ => ρ i + t * X i) (X i) 0 := by
        simpa [mul_comm] using (hasDerivAt_id' (0 : ℝ)).const_mul (X i) |>.const_add (ρ i)
      have hbase : ρ i + (0 : ℝ) * X i ≠ 0 := by simpa using hρ i
      have hinv := (hasDerivAt_inv hbase).comp 0 hline
      have hterm := hinv.const_mul (Y i * Z i)
      have hrewrite : (Y i * Z i) * (-(ρ i ^ 2)⁻¹ * X i) =
          -(X i * Y i * Z i / (ρ i * ρ i)) := by
        rw [div_eq_mul_inv, pow_two]
        ring
      simpa [Function.comp_def, zero_mul, add_zero, div_eq_mul_inv, hrewrite] using hterm)
  have hfun : (fun t : ℝ => ∑ i, Y i * Z i * (ρ i + t * X i)⁻¹) =
      (fun t : ℝ => chiSquaredInner (fun i => ρ i + t * X i) Y Z) := by
    funext t
    simp [chiSquaredInner, div_eq_mul_inv]
  convert hsum using 1
  · exact hfun.symm
  · rw [Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [div_eq_mul_inv, pow_two]
    ring

/-- The derivative value in `chiSquaredInner_affine_hasDerivAt`, written as
the negative cubic form. -/
theorem chiSquaredInner_affine_derivative
    (ρ X Y Z : ι → ℝ) (hρ : ∀ i, ρ i ≠ 0) :
    deriv (fun t : ℝ => chiSquaredInner (fun i => ρ i + t * X i) Y Z) 0 =
      -∑ i, X i * Y i * Z i / (ρ i * ρ i) := by
  have h := (chiSquaredInner_affine_hasDerivAt ρ X Y Z hρ).deriv
  rw [h]
  simp only [Finset.sum_neg_distrib]

private theorem sum_add_div (x y z r : ℝ) :
    (x + y) * z / r = x * z / r + y * z / r := by ring

private theorem sum_mul_add_div (x y z r : ℝ) :
    x * (y + z) / r = x * y / r + x * z / r := by ring

/-- Algebraic sign-corrected instance for the ambient linear space at a fixed
strictly positive prior.  Its cubic tensor is the actual directional
derivative proved above. -/
def correctedChiSquaredDualManifold (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) :
    AmariChentsovDualConnections.DualConnectionManifold (ι → ℝ) where
  g := chiSquaredInner ρ
  g_add_left x y z := by
    dsimp [chiSquaredInner]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => sum_add_div (x i) (y i) (z i) (ρ i))
  g_add_right x y z := by
    dsimp [chiSquaredInner]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => sum_mul_add_div (x i) (y i) (z i) (ρ i))
  g_smul_left c x y := by
    dsimp [chiSquaredInner]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  g_smul_right c x y := by
    dsimp [chiSquaredInner]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  g_symm x y := by
    exact chiSquaredInner_symm ρ x y
  g_pos_def x hx := chiSquaredInner_pos_of_ne_zero ρ x hρ hx
  diff_g X Y Z := -∑ i, X i * Y i * Z i / (ρ i * ρ i)
  diff_g_symm x y z := by
    apply congrArg Neg.neg
    apply Finset.sum_congr rfl
    intro i hi
    ring
  diff_g_add x y z w := by
    change -(∑ i, (x i + y i) * z i * w i / (ρ i * ρ i)) =
      -(∑ i, x i * z i * w i / (ρ i * ρ i)) -
        ∑ i, y i * z i * w i / (ρ i * ρ i)
    calc
      -(∑ i, (x i + y i) * z i * w i / (ρ i * ρ i)) =
          -(∑ i, (x i * z i * w i / (ρ i * ρ i) +
            y i * z i * w i / (ρ i * ρ i))) := by
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = -(∑ i, x i * z i * w i / (ρ i * ρ i) +
          ∑ i, y i * z i * w i / (ρ i * ρ i)) := by rw [Finset.sum_add_distrib]
      _ = -(∑ i, x i * z i * w i / (ρ i * ρ i)) -
          ∑ i, y i * z i * w i / (ρ i * ρ i) := by ring
  nabla_e X Y i := -(X i * Y i / ρ i)
  nabla_m _ _ _ := 0
  nabla_e_add_left x y z := by
    funext i
    dsimp
    ring
  nabla_e_add_right x y z := by
    funext i
    dsimp
    ring
  nabla_e_smul_left c x y := by
    funext i
    dsimp
    ring
  nabla_e_smul_right c x y := by
    funext i
    dsimp
    ring
  nabla_m_add_left _ _ _ := (add_zero 0).symm
  nabla_m_add_right _ _ _ := (add_zero 0).symm
  nabla_m_smul_left _ _ _ := (smul_zero _).symm
  nabla_m_smul_right _ _ _ := (smul_zero _).symm
  amari_duality X Y Z := by
    dsimp [chiSquaredInner]
    calc
      -(∑ i, X i * Y i * Z i / (ρ i * ρ i)) =
          ∑ i, -(X i * Y i * Z i / (ρ i * ρ i)) := by
            rw [Finset.sum_neg_distrib]
      _ = ∑ i, (-(X i * Y i / ρ i) * Z i / ρ i + Y i * 0 / ρ i) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [mul_zero, add_zero]
            ring

end InfoGeometry.Canonical.UnifiedInfoGeometryPetzFockBridge.SignRepairCandidate
