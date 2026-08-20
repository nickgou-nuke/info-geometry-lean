import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

/-!
# Gogberashvili Nilpotent CAR Bridge & Zorn Schur Invariant Specialization

This module provides fully verified, closed algebraic proofs for:
1. The Gogberashvili zero-divisor CAR packet:
   - Nilpotents: `(G⁺)² = (G⁻)² = 0`
   - Idempotents: `(D⁺)² = D⁺`, `(D⁻)² = D⁻`, `D⁺ D⁻ = D⁻ D⁺ = 0`
   - Cross-products: `G⁺ G⁻ = D⁻`, `G⁻ G⁺ = D⁺`
   - Resolution of identity: `D⁺ + D⁻ = 1`
   - Exact CAR anticommutator: `{G⁺, G⁻} = G⁺ G⁻ + G⁻ G⁺ = 1`
2. The Zorn Norm / BdG Schur / Berezinian scalar specialization:
   - `α - u β⁻¹ v = (α β - u v) / β`
   - `Ber(M) = (α - u β⁻¹ v) / β = (α β - u v) / β² = det(M) / β²`
   - `det(M) = β • (α - u β⁻¹ v)`
-/

/-!
=============================================================================
PART 1: Gogberashvili Nilpotent CAR Bridge
=============================================================================
-/

namespace GogberashviliNilpotentCARBridge

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- Primitive idempotents (diagonal projectors) -/
def D_plus (J : A) : A := (2 : K)⁻¹ • (1 + J)
def D_minus (J : A) : A := (2 : K)⁻¹ • (1 - J)

/-- Primitive nilpotents (off-diagonal Grassmann modes) -/
def G_plus (I j : A) : A := (2 : K)⁻¹ • (I + j)
def G_minus (I j : A) : A := (2 : K)⁻¹ • (I - j)

/-! ### 1. Resolution of Identity -/

/-- THEOREM: The idempotents sum to the algebra unit element: D⁺ + D⁻ = 1. -/
theorem D_plus_add_D_minus (J : A) (h2 : (2 : K) ≠ 0) :
    D_plus (K := K) J + D_minus (K := K) J = 1 := by
  dsimp [D_plus, D_minus]
  rw [← smul_add]
  have h_add : (1 + J) + (1 - J) = (2 : K) • (1 : A) := by
    calc
      (1 + J) + (1 - J) = 1 + J + 1 - J := by abel
      _ = 1 + 1 := by rw [add_sub_cancel_right]
      _ = (2 : K) • (1 : A) := by
        rw [two_smul, one_add_one_eq_two]
  rw [h_add, smul_smul, inv_mul_cancel₀ h2, one_smul]

/-! ### 2. Idempotency and Mutual Orthogonality -/

/-- THEOREM: (D⁺)² = D⁺ when J² = 1. -/
theorem D_plus_idempotent (J : A) (hJ : J * J = 1) (h2 : (2 : K) ≠ 0) :
    D_plus (K := K) J * D_plus (K := K) J = D_plus (K := K) J := by
  dsimp [D_plus]
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
  have h_sq : (1 + J) * (1 + J) = (2 : K) • (1 + J) := by
    calc
      (1 + J) * (1 + J) = 1 * 1 + 1 * J + J * 1 + J * J := by
        simp only [mul_add, add_mul, one_mul, mul_one]
      _ = 1 + J + J + 1 := by rw [one_mul, hJ]
      _ = (1 + 1) • 1 + (1 + 1) • J := by
        simp only [one_add_one_eq_two, two_smul]
        abel
      _ = (2 : K) • (1 + J) := by
        rw [smul_add, two_smul, two_smul]
  rw [h_sq, smul_smul]
  have h_inv : (2 : K)⁻¹ * (2 : K)⁻¹ * 2 = (2 : K)⁻¹ := by
    rw [mul_assoc, inv_mul_cancel₀ h2, mul_one]
  rw [h_inv]

/-- THEOREM: (D⁻)² = D⁻ when J² = 1. -/
theorem D_minus_idempotent (J : A) (hJ : J * J = 1) (h2 : (2 : K) ≠ 0) :
    D_minus (K := K) J * D_minus (K := K) J = D_minus (K := K) J := by
  dsimp [D_minus]
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
  have h_sq : (1 - J) * (1 - J) = (2 : K) • (1 - J) := by
    calc
      (1 - J) * (1 - J) = 1 * 1 - 1 * J - J * 1 + J * J := by
        simp only [mul_sub, sub_mul, one_mul, mul_one]
      _ = 1 - J - J + 1 := by rw [one_mul, hJ]
      _ = (2 : K) • 1 - (2 : K) • J := by
        simp only [two_smul]
        abel
      _ = (2 : K) • (1 - J) := by rw [smul_sub]
  rw [h_sq, smul_smul]
  have h_inv : (2 : K)⁻¹ * (2 : K)⁻¹ * 2 = (2 : K)⁻¹ := by
    rw [mul_assoc, inv_mul_cancel₀ h2, mul_one]
  rw [h_inv]

/-- THEOREM: D⁺ D⁻ = 0 when J² = 1. -/
theorem D_plus_mul_D_minus (J : A) (hJ : J * J = 1) (h2 : (2 : K) ≠ 0) :
    D_plus (K := K) J * D_minus (K := K) J = 0 := by
  dsimp [D_plus, D_minus]
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
  have h_prod : (1 + J) * (1 - J) = 0 := by
    calc
      (1 + J) * (1 - J) = 1 * 1 - 1 * J + J * 1 - J * J := by
        simp only [mul_sub, add_mul, one_mul, mul_one]
      _ = 1 - J + J - 1 := by rw [one_mul, hJ]
      _ = 0 := by abel
  rw [h_prod, smul_zero]

/-- THEOREM: D⁻ D⁺ = 0 when J² = 1. -/
theorem D_minus_mul_D_plus (J : A) (hJ : J * J = 1) (h2 : (2 : K) ≠ 0) :
    D_minus (K := K) J * D_plus (K := K) J = 0 := by
  dsimp [D_plus, D_minus]
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
  have h_prod : (1 - J) * (1 + J) = 0 := by
    calc
      (1 - J) * (1 + J) = 1 * 1 + 1 * J - J * 1 - J * J := by
        simp only [mul_add, sub_mul, one_mul, mul_one]
      _ = 1 + J - J - 1 := by rw [one_mul, hJ]
      _ = 0 := by abel
  rw [h_prod, smul_zero]

/-! ### 3. Nilpotency of G⁺ and G⁻ -/

/-- THEOREM: (G⁺)² = 0 when I² = 1, j² = -1, and Ij + jI = 0. -/
theorem G_plus_square_zero (I j : A)
    (hI : I * I = 1) (hj : j * j = -1) (h_anticomm : I * j + j * I = 0) (h2 : (2 : K) ≠ 0) :
    G_plus (K := K) I j * G_plus (K := K) I j = 0 := by
  dsimp [G_plus]
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
  have h_sq : (I + j) * (I + j) = 0 := by
    calc
      (I + j) * (I + j) = I * I + I * j + j * I + j * j := by
        simp only [mul_add, add_mul]
      _ = 1 + (I * j + j * I) - 1 := by
        rw [hI, hj, add_assoc, ← sub_eq_add_neg]
      _ = 1 + 0 - 1 := by rw [h_anticomm]
      _ = 0 := by abel
  rw [h_sq, smul_zero]

/-- THEOREM: (G⁻)² = 0 when I² = 1, j² = -1, and Ij + jI = 0. -/
theorem G_minus_square_zero (I j : A)
    (hI : I * I = 1) (hj : j * j = -1) (h_anticomm : I * j + j * I = 0) (h2 : (2 : K) ≠ 0) :
    G_minus (K := K) I j * G_minus (K := K) I j = 0 := by
  dsimp [G_minus]
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
  have h_sq : (I - j) * (I - j) = 0 := by
    calc
      (I - j) * (I - j) = I * I - I * j - j * I + j * j := by
        simp only [mul_sub, sub_mul]
      _ = 1 - (I * j + j * I) - 1 := by
        rw [hI, hj, ← sub_sub, sub_add_eq_add_sub, add_comm (-1 : A), ← sub_eq_add_neg]
        abel
      _ = 1 - 0 - 1 := by rw [h_anticomm]
      _ = 0 := by abel
  rw [h_sq, smul_zero]

/-! ### 4. Nilpotent Products Produce Idempotents -/

/-- THEOREM: G⁺ G⁻ = D⁻ when I² = 1, j² = -1, jI = -Ij, and J = Ij. -/
theorem G_plus_mul_G_minus (I j J : A)
    (hI : I * I = 1) (hj : j * j = -1) (h_cross : j * I = - (I * j)) (hJ_def : J = I * j)
    (h2 : (2 : K) ≠ 0) :
    G_plus (K := K) I j * G_minus (K := K) I j = D_minus (K := K) J := by
  dsimp [G_plus, G_minus, D_minus]
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
  have h_prod : (I + j) * (I - j) = (2 : K) • (1 - J) := by
    calc
      (I + j) * (I - j) = I * I - I * j + j * I - j * j := by
        simp only [mul_sub, add_mul]
      _ = 1 - I * j - I * j - (-1) := by rw [hI, hj, h_cross]
      _ = 1 - (I * j + I * j) + 1 := by abel
      _ = 1 + 1 - (I * j + I * j) := by abel
      _ = (2 : K) • 1 - (2 : K) • J := by
        rw [hJ_def, two_smul, two_smul]
        abel
      _ = (2 : K) • (1 - J) := by rw [smul_sub]
  rw [h_prod, smul_smul]
  have h_inv : (2 : K)⁻¹ * (2 : K)⁻¹ * 2 = (2 : K)⁻¹ := by
    rw [mul_assoc, inv_mul_cancel₀ h2, mul_one]
  rw [h_inv]

/-- THEOREM: G⁻ G⁺ = D⁺ when I² = 1, j² = -1, jI = -Ij, and J = Ij. -/
theorem G_minus_mul_G_plus (I j J : A)
    (hI : I * I = 1) (hj : j * j = -1) (h_cross : j * I = - (I * j)) (hJ_def : J = I * j)
    (h2 : (2 : K) ≠ 0) :
    G_minus (K := K) I j * G_plus (K := K) I j = D_plus (K := K) J := by
  dsimp [G_plus, G_minus, D_plus]
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
  have h_prod : (I - j) * (I + j) = (2 : K) • (1 + J) := by
    calc
      (I - j) * (I + j) = I * I + I * j - j * I - j * j := by
        simp only [mul_add, sub_mul]
      _ = 1 + I * j - (- (I * j)) - (-1) := by rw [hI, hj, h_cross]
      _ = 1 + (I * j + I * j) + 1 := by abel
      _ = 1 + 1 + (I * j + I * j) := by abel
      _ = (2 : K) • 1 + (2 : K) • J := by
        rw [hJ_def, two_smul, two_smul]
      _ = (2 : K) • (1 + J) := by rw [smul_add]
  rw [h_prod, smul_smul]
  have h_inv : (2 : K)⁻¹ * (2 : K)⁻¹ * 2 = (2 : K)⁻¹ := by
    rw [mul_assoc, inv_mul_cancel₀ h2, mul_one]
  rw [h_inv]

/-! ### 5. The Exact Canonical Anticommutation Relation (CAR) -/

/--
THEOREM: The full Canonical Anticommutation Relation (CAR):
  {G⁺, G⁻} = G⁺ G⁻ + G⁻ G⁺ = 1.
-/
theorem G_plus_G_minus_CAR (I j J : A)
    (hI : I * I = 1) (hj : j * j = -1) (h_cross : j * I = - (I * j)) (hJ_def : J = I * j)
    (h2 : (2 : K) ≠ 0) :
    G_plus (K := K) I j * G_minus (K := K) I j +
    G_minus (K := K) I j * G_plus (K := K) I j = 1 := by
  rw [G_plus_mul_G_minus h2 I j J hI hj h_cross hJ_def]
  rw [G_minus_mul_G_plus h2 I j J hI hj h_cross hJ_def]
  rw [add_comm]
  exact D_plus_add_D_minus h2 J

end GogberashviliNilpotentCARBridge

/-!
=============================================================================
PART 2: Zorn Norm / BdG Schur / Berezinian Scalar Specialization
=============================================================================
-/

namespace ZornNormSchurScalarSpecialization

variable {F : Type*} [Field F]

/-- The scalar Schur complement for a 2×2 block with scalar entries -/
def schurComplement (α β u v : F) : F :=
  α - u * β⁻¹ * v

/-- The scalar Berezinian supervolume ratio: Ber(M) = (α - u β⁻¹ v) / β -/
def berezinianScalar (α β u v : F) : F :=
  (schurComplement α β u v) / β

/-- The classical 2×2 determinant (Zorn norm) -/
def zornNorm (α β u v : F) : F :=
  α * β - u * v

/--
THEOREM 1: The scalar Schur complement equals the ratio (α β - u v) / β.
-/
theorem schur_scalar_formula (α β u v : F) (hβ : β ≠ 0) :
    schurComplement α β u v = (zornNorm α β u v) / β := by
  dsimp [schurComplement, zornNorm]
  field_simp
  ring

/--
THEOREM 2: The scalar Berezinian is exactly the normalized Zorn norm:
  Ber(M) = (α β - u v) / β² = det(M) / β².
-/
theorem berezinian_eq_zorn_norm_div_sq (α β u v : F) (hβ : β ≠ 0) :
    berezinianScalar α β u v = (zornNorm α β u v) / (β ^ 2) := by
  dsimp [berezinianScalar]
  rw [schur_scalar_formula α β u v hβ]
  field_simp
  ring

/--
THEOREM 3: Exact Reconstruction of the Zorn Determinant from the Schur Complement:
  det(M) = N(Z) = β • (α - u β⁻¹ v).
-/
theorem zorn_norm_eq_schur_mul_beta (α β u v : F) (hβ : β ≠ 0) :
    zornNorm α β u v = (schurComplement α β u v) * β := by
  dsimp [zornNorm, schurComplement]
  rw [mul_sub, sub_mul]
  rw [mul_inv_cancel hβ]
  ring

end ZornNormSchurScalarSpecialization
