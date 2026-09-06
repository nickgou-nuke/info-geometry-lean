import InfoGeometry.Canonical.CanonicalZornNullProjectiveBoundaryBridge

/-!
# Explicit rank-one factorization on the split Zorn carrier

This is an algebraic factorization theorem on `ZornCore.Zorn`.  It does not
identify the factorization with a spin representation or with a Majorana
module; those are separate bridges.
-/

noncomputable section

namespace InfoGeometry.Canonical.CanonicalZornTwistorFactorization

open ZornCore

abbrev ZornSpinor := ℝ × Vec3

def spinorOuterProduct (L R : ZornSpinor) : Zorn where
  a := L.1 * R.1
  u := L.1 • R.2
  v := R.1 • L.2
  b := dot L.2 R.2

theorem spinorOuterProduct_factorization
    (Z : Zorn) (hnull : Z.a * Z.b = dot Z.u Z.v) (ha : Z.a ≠ 0) :
    ∃ L R : ZornSpinor, Z = spinorOuterProduct L R := by
  let L : ZornSpinor := (Z.a, Z.v)
  let R : ZornSpinor := (1, Z.a⁻¹ • Z.u)
  refine ⟨L, R, ?_⟩
  apply Zorn.ext'
  · simp [L, R, spinorOuterProduct]
  · simp [L, R, spinorOuterProduct, smul_smul, ha]
  · simp [L, R, spinorOuterProduct]
  · simp only [L, R, spinorOuterProduct, one_mul, smul_eq_mul,
      Finset.sum_mul]
    calc
      Z.b = Z.a⁻¹ * (Z.a * Z.b) := by field_simp [ha]
      _ = Z.a⁻¹ * dot Z.u Z.v := by rw [hnull]
      _ = dot Z.v (Z.a⁻¹ • Z.u) := by
        simp [dot, Fin.sum_univ_three]
        ring

theorem pure_vector_null_orthogonal
    (Z : Zorn) (hnull : Z.a * Z.b = dot Z.u Z.v)
    (hpure : Z.a = 0 ∧ Z.b = 0) :
    dot Z.u Z.v = 0 := by
  rw [← hnull, hpure.1, zero_mul]

end InfoGeometry.Canonical.CanonicalZornTwistorFactorization
