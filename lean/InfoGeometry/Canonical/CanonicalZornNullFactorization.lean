import Mathlib.Tactic
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

/-!
# Honest null-factorization facts for the canonical real Zorn carrier

This owner records the elementary algebraic normal form available on the
nonzero affine chart `a ≠ 0`.  It deliberately does not identify the factors
with physical twistors or Majorana modes; those require separate typed
representation bridges.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.CanonicalZornNullFactorization

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

abbrev CanonicalZorn := InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn
abbrev ZornSpinor := ℝ × (Fin 3 → ℝ)

def spinorOuterProduct (L R : ZornSpinor) : CanonicalZorn :=
  { a := L.1 * R.1
    b := InfoGeometry.Canonical.ZornMatrix.dot L.2 R.2
    x := L.1 • R.2
    y := R.1 • L.2 }

@[simp] theorem spinorOuterProduct_a (L R : ZornSpinor) :
    (spinorOuterProduct L R).a = L.1 * R.1 := rfl

@[simp] theorem spinorOuterProduct_b (L R : ZornSpinor) :
    (spinorOuterProduct L R).b = InfoGeometry.Canonical.ZornMatrix.dot L.2 R.2 := rfl

@[simp] theorem spinorOuterProduct_x (L R : ZornSpinor) :
    (spinorOuterProduct L R).x = L.1 • R.2 := rfl

@[simp] theorem spinorOuterProduct_y (L R : ZornSpinor) :
    (spinorOuterProduct L R).y = R.1 • L.2 := rfl

private theorem dot_swap (u v : Fin 3 → ℝ) :
    InfoGeometry.Canonical.ZornMatrix.dot u v =
      InfoGeometry.Canonical.ZornMatrix.dot v u := by
  simp [InfoGeometry.Canonical.ZornMatrix.dot]
  ring

private theorem dot_smul_right (r : ℝ) (u v : Fin 3 → ℝ) :
    InfoGeometry.Canonical.ZornMatrix.dot u (r • v) =
      r * InfoGeometry.Canonical.ZornMatrix.dot u v := by
  simp [InfoGeometry.Canonical.ZornMatrix.dot]
  ring

theorem null_zorn_is_spinor_outer_product
    (Z : CanonicalZorn)
    (hnull : InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
      realCrossProduct3 Z = 0)
    (ha : Z.a ≠ 0) :
    ∃ L R : ZornSpinor, Z = spinorOuterProduct L R := by
  let L : ZornSpinor := (Z.a, Z.y)
  let R : ZornSpinor := (1, Z.a⁻¹ • Z.x)
  have hdet : Z.a * Z.b = InfoGeometry.Canonical.ZornMatrix.dot Z.x Z.y := by
    simpa [InfoGeometry.Algebra.Zorn.ZornMatrix.detZ] using
      (sub_eq_zero.mp hnull)
  have hb : Z.b = Z.a⁻¹ * InfoGeometry.Canonical.ZornMatrix.dot Z.x Z.y := by
    field_simp [ha]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdet
  refine ⟨L, R, ?_⟩
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [L, R, spinorOuterProduct]
  · simp [L, R, spinorOuterProduct, hb, dot_smul_right, dot_swap]
  · funext i
    simp [L, R, spinorOuterProduct, smul_eq_mul]
    field_simp [ha]
  · funext i
    simp [L, R, spinorOuterProduct, smul_eq_mul]

theorem pure_vector_null_is_orthogonal
    (Z : CanonicalZorn)
    (hnull : InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
      realCrossProduct3 Z = 0)
    (hpure : Z.a = 0 ∧ Z.b = 0) :
    InfoGeometry.Canonical.ZornMatrix.dot Z.x Z.y = 0 := by
  simpa [InfoGeometry.Algebra.Zorn.ZornMatrix.detZ, hpure.1, hpure.2] using hnull

end InfoGeometry.Canonical.CanonicalZornNullFactorization
