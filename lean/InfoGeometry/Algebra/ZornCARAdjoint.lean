import InfoGeometry.Algebra.ZornLeftCAR
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# A positive adjoint pairing for the real Zorn CAR representation

The Euclidean coefficient pairing is deliberately different from the split
multiplicative Zorn norm. With this pairing the raising and lowering operators
are genuine adjoints. No positive definiteness of the split norm is asserted.
-/

namespace InfoGeometry.Algebra.ZornCARAdjoint

open InfoGeometry.Algebra
open ZornPinorReconstruction ZornLeftCAR

noncomputable section

def coefficientPairing : LinearMap.BilinForm ℝ Z where
  toFun X :=
    { toFun Y := X.a * Y.a + X.b * Y.b + ZornVec3.dot X.v Y.v + ZornVec3.dot X.w Y.w
      map_add' Y W := by
        simp [ZornVectorMatrix.add, ZornVec3.dot, Fin.sum_univ_three]
        ring
      map_smul' c Y := by
        simp [ZornVectorMatrix.smul, ZornVec3.dot, Fin.sum_univ_three]
        ring }
  map_add' X Y := by
    ext W
    simp [ZornVectorMatrix.add, ZornVec3.dot, Fin.sum_univ_three]
    ring
  map_smul' c X := by
    ext Y
    simp [ZornVectorMatrix.smul, ZornVec3.dot, Fin.sum_univ_three]
    ring

theorem coefficientPairing_symm (X Y : Z) : coefficientPairing X Y = coefficientPairing Y X := by
  simp [coefficientPairing, ZornVec3.dot, Fin.sum_univ_three]
  ring

theorem coefficientPairing_nonneg (X : Z) : 0 ≤ coefficientPairing X X := by
  dsimp [coefficientPairing]
  rw [ZornVec3.dot_eq_sum_coords, ZornVec3.dot_eq_sum_coords]
  nlinarith [sq_nonneg X.a, sq_nonneg X.b,
    sq_nonneg (X.v (0 : Fin 3)), sq_nonneg (X.v (1 : Fin 3)),
    sq_nonneg (X.v (2 : Fin 3)), sq_nonneg (X.w (0 : Fin 3)),
    sq_nonneg (X.w (1 : Fin 3)), sq_nonneg (X.w (2 : Fin 3))]

set_option maxHeartbeats 1000000 in
theorem coefficientPairing_zero_iff (X : Z) : coefficientPairing X X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have hsum : X.a ^ 2 + X.b ^ 2 + X.v 0 ^ 2 + X.v 1 ^ 2 + X.v 2 ^ 2 +
        X.w 0 ^ 2 + X.w 1 ^ 2 + X.w 2 ^ 2 = 0 := by
      simpa [coefficientPairing, ZornVec3.dot, Fin.sum_univ_three, pow_two,
        add_assoc] using h
    have ha2 : 0 ≤ X.a ^ 2 := sq_nonneg _
    have hb2 : 0 ≤ X.b ^ 2 := sq_nonneg _
    have hv02 : 0 ≤ X.v (0 : Fin 3) ^ 2 := sq_nonneg _
    have hv12 : 0 ≤ X.v (1 : Fin 3) ^ 2 := sq_nonneg _
    have hv22 : 0 ≤ X.v (2 : Fin 3) ^ 2 := sq_nonneg _
    have hw02 : 0 ≤ X.w (0 : Fin 3) ^ 2 := sq_nonneg _
    have hw12 : 0 ≤ X.w (1 : Fin 3) ^ 2 := sq_nonneg _
    have hw22 : 0 ≤ X.w (2 : Fin 3) ^ 2 := sq_nonneg _
    have ha_sq : X.a ^ 2 = 0 := by nlinarith [hsum, ha2, hb2, hv02, hv12, hv22, hw02, hw12, hw22]
    have hb_sq : X.b ^ 2 = 0 := by nlinarith [hsum, ha2, hb2, hv02, hv12, hv22, hw02, hw12, hw22]
    have ha : X.a = 0 := (sq_eq_zero_iff.mp ha_sq)
    have hb : X.b = 0 := (sq_eq_zero_iff.mp hb_sq)
    have hv : ∀ i, X.v i = 0 := by
      intro i
      fin_cases i
      · have hsq : X.v (0 : Fin 3) ^ 2 = 0 := by nlinarith [hsum, ha2, hb2, hv02, hv12, hv22, hw02, hw12, hw22]
        exact sq_eq_zero_iff.mp hsq
      · have hsq : X.v (1 : Fin 3) ^ 2 = 0 := by nlinarith [hsum, ha2, hb2, hv02, hv12, hv22, hw02, hw12, hw22]
        exact sq_eq_zero_iff.mp hsq
      · have hsq : X.v (2 : Fin 3) ^ 2 = 0 := by nlinarith [hsum, ha2, hb2, hv02, hv12, hv22, hw02, hw12, hw22]
        exact sq_eq_zero_iff.mp hsq
    have hw : ∀ i, X.w i = 0 := by
      intro i
      fin_cases i
      · have hsq : X.w (0 : Fin 3) ^ 2 = 0 := by nlinarith [hsum, ha2, hb2, hv02, hv12, hv22, hw02, hw12, hw22]
        exact sq_eq_zero_iff.mp hsq
      · have hsq : X.w (1 : Fin 3) ^ 2 = 0 := by nlinarith [hsum, ha2, hb2, hv02, hv12, hv22, hw02, hw12, hw22]
        exact sq_eq_zero_iff.mp hsq
      · have hsq : X.w (2 : Fin 3) ^ 2 = 0 := by nlinarith [hsum, ha2, hb2, hv02, hv12, hv22, hw02, hw12, hw22]
        exact sq_eq_zero_iff.mp hsq
    change X = ZornVectorMatrix.zero
    ext i <;> simp [ha, hb, hv, hw, ZornVectorMatrix.zero]
  · rintro rfl
    simp

/-- This is the adjoint identity for the explicitly constructed positive pairing. -/
theorem raise_lower_adjoint (u : V) (X Y : Z) :
    coefficientPairing (raise u X) Y = coefficientPairing X (lower u Y) := by
  simp [coefficientPairing, raise, lower, leftMultiplication_apply, creation,
    annihilation, ZornVectorMatrix.offDiagonal, ZornVectorMatrix.mul,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  ring

/-- Positivity of the quadratic form of the number operator is derived, not assumed. -/
theorem numberOperator_nonneg (u : V) (X : Z) :
    0 ≤ coefficientPairing X ((raise u * lower u) X) := by
  change 0 ≤ coefficientPairing X (raise u (lower u X))
  rw [coefficientPairing_symm X, raise_lower_adjoint]
  exact coefficientPairing_nonneg (lower u X)

/-- Unit-norm modes have idempotent number operators, by associative CAR. -/
theorem numberOperator_idempotent (u : V) (hu : ZornVec3.dot u u = 1) :
    (raise u * lower u) * (raise u * lower u) = raise u * lower u := by
  have hcar := raise_lower_car u u
  rw [hu, one_smul] at hcar
  have hlr : lower u * raise u = 1 - raise u * lower u := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using hcar
  calc
    _ = raise u * (lower u * raise u) * lower u := by simp only [mul_assoc]
    _ = raise u * (1 - raise u * lower u) * lower u := by rw [hlr]
    _ = raise u * lower u := by
      rw [mul_sub, mul_one, ← mul_assoc (raise u) (raise u), raise_square,
        zero_mul, sub_zero]

end
end InfoGeometry.Algebra.ZornCARAdjoint
