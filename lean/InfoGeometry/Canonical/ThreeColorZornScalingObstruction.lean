import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.SplitOctonionBraidSU3

/-!
# Obstruction to the naive chiral scaling automorphism

The upper and lower colour sectors scale with reciprocal weights.  The
cross-product term therefore forces a cubic compatibility condition.  This
file records the concrete defect on the native complex Zorn carrier; it does
not claim a nontrivial real one-parameter automorphism.
-/

namespace InfoGeometry.Canonical.ThreeColorZornScalingObstruction

noncomputable section

open InfoGeometry.Physics.SplitOctonionBraidSU3

abbrev Zorn := InfoGeometry.Physics.SplitOctonionBraidSU3.Zorn

def zornScale (q : ℂ) (X : Zorn) : Zorn where
  a := X.a
  u := fun i => q * X.u i
  v := fun i => q⁻¹ * X.v i
  b := X.b

theorem zornScale_upper_product (q : ℂ) (hq : q ≠ 0) :
    zornMul (zornScale q (E_k 0)) (zornScale q (E_k 1)) =
      zornSmul (q ^ 2) (F_k 2) := by
  apply zorn_ext
  · simp [zornScale, zornMul, zornSmul, E_k, F_k, e_k, dot3]
  · funext i
    fin_cases i <;>
      simp [zornScale, zornMul, zornSmul, E_k, F_k, e_k, cross3,
        pow_two] <;> ring
  · funext i
    fin_cases i <;>
      simp [zornScale, zornMul, zornSmul, E_k, F_k, e_k, cross3] <;> ring
  · simp [zornScale, zornMul, zornSmul, E_k, F_k, e_k, dot3]

theorem zornScale_of_upper_product (q : ℂ) (hq : q ≠ 0) :
    zornScale q (zornMul (E_k 0) (E_k 1)) =
      zornSmul (q⁻¹) (F_k 2) := by
  apply zorn_ext
  · simp [zornScale, zornMul, zornSmul, E_k, F_k, e_k, dot3]
  · funext i
    fin_cases i <;>
      simp [zornScale, zornMul, zornSmul, E_k, F_k, e_k, cross3]
  · funext i
    fin_cases i <;>
      simp [zornScale, zornMul, zornSmul, E_k, F_k, e_k, cross3]
  · simp [zornScale, zornMul, zornSmul, E_k, F_k, e_k, dot3]

theorem zornScale_upper_product_defect (q : ℂ) (hq : q ≠ 0) :
    zornMul (zornScale q (E_k 0)) (zornScale q (E_k 1)) =
      zornScale q (zornMul (E_k 0) (E_k 1)) ↔
      q ^ 3 = 1 := by
  rw [zornScale_upper_product q hq, zornScale_of_upper_product q hq]
  constructor
  · intro h
    have hcoord := congrArg (fun X : Zorn => X.v 2) h
    simp [zornSmul, F_k, e_k] at hcoord
    calc
      q ^ 3 = q ^ 2 * q := by ring
      _ = q⁻¹ * q := by rw [hcoord]
      _ = 1 := inv_mul_cancel₀ hq
  · intro h
    have hq_inv : q ^ 2 = q⁻¹ := by
      field_simp [hq]
      simpa [pow_succ, mul_assoc] using h
    apply zorn_ext
    · simp [zornSmul, zornScale, zornMul, E_k, F_k, e_k, dot3, h]
    · funext i
      fin_cases i <;>
        simp [zornSmul, zornScale, zornMul, E_k, F_k, e_k, cross3] <;>
          rw [hq_inv]
    · funext i
      fin_cases i <;>
        simp [zornSmul, zornScale, zornMul, E_k, F_k, e_k, cross3, hq_inv]
    · simp [zornSmul, zornScale, zornMul, E_k, F_k, e_k, dot3, hq_inv]

end
end InfoGeometry.Canonical.ThreeColorZornScalingObstruction
