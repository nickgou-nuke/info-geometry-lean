import InfoGeometry.Canonical.SpinorialCore.KreinAdjoint

/-!
# Hermitian incidence and positive mass

The metric sends a vector to a covector antilinearly. Its null incidence is
not an equation between two unrestricted complex-linear vector coordinates.
No spacetime topology or scattering completeness is inferred here.
-/

noncomputable section
namespace InfoGeometry.Canonical.SpinorialCore.Krein
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

def pairing (J : Matrix n n ℂ) (x y : n → ℂ) : ℂ := star x ⬝ᵥ J *ᵥ y

/-- A complex-linear covector in its evaluation variable. -/
def metricDual (J : Matrix n n ℂ) (x : n → ℂ) : Module.Dual ℂ (n → ℂ) where
  toFun y := pairing J x y
  map_add' y z := by simp [pairing, Matrix.mulVec_add, dotProduct_add]
  map_smul' a y := by simp [pairing, Matrix.mulVec_smul, dotProduct_smul]

theorem metricDual_antilinear (J : Matrix n n ℂ) (a : ℂ) (x : n → ℂ) :
    metricDual J (a • x) = star a • metricDual J x := by
  ext y
  simp [metricDual, pairing, star_smul, smul_dotProduct]

omit [DecidableEq n] in
/-- The incidence functional agrees with the indefinite Hermitian pairing. -/
theorem incidence_eq_pairing (J : Matrix n n ℂ) (x : n → ℂ) :
    metricDual J x x = pairing J x x := rfl

theorem pairing_isometry (J U : Matrix n n ℂ) (hU : IsIsometry J U)
    (x y : n → ℂ) : pairing J (U *ᵥ x) (U *ᵥ y) = pairing J x y := by
  change star (U *ᵥ x) ⬝ᵥ J *ᵥ U *ᵥ y = star x ⬝ᵥ J *ᵥ y
  have h : U.conjTranspose * J * U = J := hU
  calc
    star (U *ᵥ x) ⬝ᵥ J *ᵥ U *ᵥ y = star x ⬝ᵥ (U.conjTranspose * J * U) *ᵥ y := by
      simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
    _ = star x ⬝ᵥ J *ᵥ y := by rw [h]

theorem null_incidence_preserved (J U : Matrix n n ℂ) (hU : IsIsometry J U)
    (x : n → ℂ) : metricDual J (U *ᵥ x) (U *ᵥ x) = 0 ↔ metricDual J x x = 0 := by
  change pairing J (U *ᵥ x) (U *ᵥ x) = 0 ↔ pairing J x x = 0
  rw [pairing_isometry J U hU]

omit [DecidableEq n] in
theorem pairing_scale (J : Matrix n n ℂ) (a : ℂ) (x y : n → ℂ) :
    pairing J (a • x) (a • y) = (star a * a) * pairing J x y := by
  simp [pairing, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    mul_assoc, mul_left_comm]

theorem projective_null_iff (J : Matrix n n ℂ) (a : ℂ) (ha : a ≠ 0) (x : n → ℂ) :
    pairing J (a • x) (a • x) = 0 ↔ pairing J x x = 0 := by
  rw [pairing_scale]
  simp [mul_eq_zero, ha]

/-- Inserting the fundamental symmetry recovers the positive pairing. -/
theorem positive_pairing_recovery (J : Matrix n n ℂ) (hJ : J * J = 1)
    (x y : n → ℂ) : pairing J x (J *ᵥ y) = star x ⬝ᵥ y := by
  simp only [pairing, Matrix.mulVec_mulVec, hJ, Matrix.one_mulVec]

def positiveMass (x : n → ℂ) : ℝ := ∑ i, Complex.normSq (x i)

omit [DecidableEq n] in
theorem positiveMass_nonneg (x : n → ℂ) : 0 ≤ positiveMass x :=
  Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (x i))

theorem positiveMass_recovery (J : Matrix n n ℂ) (hJ : J * J = 1) (x : n → ℂ) :
    (pairing J x (J *ᵥ x)).re = positiveMass x := by
  rw [positive_pairing_recovery J hJ]
  simp [positiveMass, dotProduct, Complex.mul_re, Complex.normSq_apply]

namespace IncidenceExample

def signature : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
def nullVector : Fin 2 → ℂ := ![1, Complex.I]

theorem nullVector_nonzero : nullVector ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [nullVector] at h0

theorem hermitian_null : pairing signature nullVector nullVector = 0 := by
  norm_num [pairing, signature, nullVector, dotProduct, Matrix.mulVec, Fin.sum_univ_two]

theorem positiveMass_nullVector : positiveMass nullVector = 2 := by
  norm_num [positiveMass, nullVector, Fin.sum_univ_two, Complex.normSq_apply]

/-- Omitting complex conjugation changes the incidence equation. -/
theorem bilinear_not_null : nullVector ⬝ᵥ signature *ᵥ nullVector = 2 := by
  norm_num [signature, nullVector, dotProduct, Matrix.mulVec, Fin.sum_univ_two]

end IncidenceExample
end InfoGeometry.Canonical.SpinorialCore.Krein
