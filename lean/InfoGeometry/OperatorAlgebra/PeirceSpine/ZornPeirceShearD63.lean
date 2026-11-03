/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleInformationPeirce

/-! # Peirce shears on operator-valued Zorn slices

The Zorn slice is a carrier map into an associative matrix ring. No
multiplicativity of that map for the nonassociative Zorn product is assumed.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ZornPeirceShearD63

open InfoGeometry.Physics.NCG InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorZornFourPotentialGauge
open InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine.BlackHoleInformation
open scoped Matrix

variable {A : Type*} [Ring A]

/-- The shear on a Zorn slice records the ordered product of its two
operator-valued off-diagonal components. -/
theorem zorn_slice_shear_formula (i : Fin 3) (X Y : OperatorZornMatrix A) :
    horizonShear (peirceSheetProj (A := A)) (zornChiralPlaneMatrix i X)
        (zornChiralPlaneMatrix i Y) =
      !![1 - X.sigma_plus i * Y.sigma_minus i, X.sigma_plus i;
         -Y.sigma_minus i, 1] := by
  unfold horizonShear
  rw [zornChiralPlane_conePlus, zornChiralPlane_coneMinus]
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg, add_comm]

/-- The inverse shear contains the oppositely ordered product. -/
theorem zorn_slice_shear_inverse_formula (i : Fin 3) (X Y : OperatorZornMatrix A) :
    horizonShearInv (peirceSheetProj (A := A)) (zornChiralPlaneMatrix i X)
        (zornChiralPlaneMatrix i Y) =
      !![1, -X.sigma_plus i; Y.sigma_minus i,
         1 - Y.sigma_minus i * X.sigma_plus i] := by
  unfold horizonShearInv
  rw [zornChiralPlane_conePlus, zornChiralPlane_coneMinus]
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg, add_comm]

/-- The two distinct ordered products form an explicit two-sided inverse
pair over every associative coefficient ring. -/
theorem zorn_slice_shear_inverse (i : Fin 3) (X Y : OperatorZornMatrix A) :
    (!![1 - X.sigma_plus i * Y.sigma_minus i, X.sigma_plus i;
        -Y.sigma_minus i, 1] : Matrix (Fin 2) (Fin 2) A) *
      !![1, -X.sigma_plus i; Y.sigma_minus i,
        1 - Y.sigma_minus i * X.sigma_plus i] = 1 ∧
    (!![1, -X.sigma_plus i; Y.sigma_minus i,
        1 - Y.sigma_minus i * X.sigma_plus i] : Matrix (Fin 2) (Fin 2) A) *
      !![1 - X.sigma_plus i * Y.sigma_minus i, X.sigma_plus i;
        -Y.sigma_minus i, 1] = 1 := by
  rw [← zorn_slice_shear_formula i X Y, ← zorn_slice_shear_inverse_formula i X Y]
  exact peirce_shear_two_sided_inverse peirceSheetProj_idem _ _

/-- Place two arbitrary ring elements in the transverse Zorn coordinates. -/
def zornTransverseOperators (B C : A) : OperatorZornMatrix A :=
  ⟨0, 0, fun _ => 0, ![0, B, C]⟩

/-- The failure to preserve the square is exactly the internal commutator. -/
theorem zorn_transverse_square_slice_defect (B C : A) :
    zornChiralPlaneMatrix 0 (zornTransverseOperators B C * zornTransverseOperators B C) -
      zornChiralPlaneMatrix 0 (zornTransverseOperators B C) *
        zornChiralPlaneMatrix 0 (zornTransverseOperators B C) =
      !![0, -(B * C - C * B); 0, 0] := by
  rw [zornChiralPlane_zero_mul_defect]
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [zornTransverseOperators, zornChiralPlane_genV, NCZornElement.zornCross]

/-- A transverse Zorn slice preserves this square exactly when the two
operator coefficients commute. -/
theorem zorn_transverse_square_slice_preserved_iff (B C : A) :
    zornChiralPlaneMatrix 0 (zornTransverseOperators B C * zornTransverseOperators B C) =
      zornChiralPlaneMatrix 0 (zornTransverseOperators B C) *
        zornChiralPlaneMatrix 0 (zornTransverseOperators B C) ↔ B * C = C * B := by
  constructor
  · intro h
    have hz := sub_eq_zero.mpr h
    rw [zorn_transverse_square_slice_defect] at hz
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 0 1) hz
    have hcomm : -(B * C - C * B) = 0 := by simpa using he
    exact sub_eq_zero.mp (neg_eq_zero.mp hcomm)
  · intro h
    apply sub_eq_zero.mp
    rw [zorn_transverse_square_slice_defect, sub_eq_zero.mpr h]
    ext r s
    fin_cases r <;> fin_cases s <;> simp

end InfoGeometry.OperatorAlgebra.PeirceSpine.ZornPeirceShearD63
