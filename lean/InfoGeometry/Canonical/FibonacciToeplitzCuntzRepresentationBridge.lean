import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FinCases
import InfoGeometry.Canonical.NonAbelianFusionFRBridge

/-!
# InfoGeometry.Canonical.FibonacciToeplitzCuntzRepresentationBridge

Explicit representation bridge carrying the 2D non-Abelian Fibonacci fusion-space braid algebra
(F, R, σ₁, σ₂) into the Toeplitz–Cuntz operator algebra A over K.

Key Architectural Distinctions & Audit Compliance:
1. **Corner (*)-Representation**: π : M₂(K) → H A H is a genuine linear, multiplicative, star-homomorphism into the corner algebra H A H (with corner unit 1_H = H).
2. **Vacuum-Fixed Global Multiplicative Extension**: M̃ = π(M) + P₀ is a **unital multiplicative (*)-extension fixing the vacuum** (M̃ 1 = 1, M̃ P₀ = P₀, P₀ M̃ = P₀). Note that M̃ is **not** an algebra homomorphism because it is non-additive on M₂ (M̃(0) = P₀ ≠ 0 when the defect projection P₀ is nontrivial).
3. **Bilateral Vacuum Fixation**: M̃(M) P₀ = P₀ and P₀ M̃(M) = P₀.
4. **Injective Embedding Theorem**: Proves `matrixToCuntz_injective` via coefficient recovery formulas S_i* π(M) S_j = algebraMap K A (M_ij), establishing M₂(K) ↪ A whenever algebraMap K A is injective.
5. **Involutive F-Operator**: Proves global extended involution (π(F) + P₀)² = 1.
-/

noncomputable section

namespace InfoGeometry.Canonical.FibonacciToeplitzCuntzRepresentationBridge

open Matrix
open InfoGeometry.Canonical.NonAbelianFusionFRBridge

/-- Cuntz-Krieger 2-isometry structure on algebra A over K. -/
structure CuntzTwoIsometry (K A : Type*) [CommRing K] [Ring A] [Algebra K A] [StarRing A] where
  S1 : A
  S2 : A
  S1_star_S1 : star S1 * S1 = 1
  S2_star_S2 : star S2 * S2 = 1
  S1_star_S2 : star S1 * S2 = 0
  S2_star_S1 : star S2 * S1 = 0

namespace CuntzTwoIsometry

variable {K A : Type*} [CommRing K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
variable (ck : CuntzTwoIsometry K A)

/-- Excitation projection H = S₁ S₁* + S₂ S₂* in corner algebra H A H. -/
def excitationProjection : A :=
  ck.S1 * star ck.S1 + ck.S2 * star ck.S2

/-- Defect / vacuum projection P₀ = 1 - H. -/
def defectProjection : A :=
  1 - excitationProjection ck

theorem excitationProjection_sq :
    excitationProjection ck * excitationProjection ck = excitationProjection ck := by
  dsimp [excitationProjection]
  have h11 : (ck.S1 * star ck.S1) * (ck.S1 * star ck.S1) = ck.S1 * star ck.S1 := by
    rw [← mul_assoc, mul_assoc ck.S1 (star ck.S1) ck.S1, ck.S1_star_S1, mul_one]
  have h12 : (ck.S1 * star ck.S1) * (ck.S2 * star ck.S2) = 0 := by
    rw [← mul_assoc, mul_assoc ck.S1 (star ck.S1) ck.S2, ck.S1_star_S2, mul_zero, zero_mul]
  have h21 : (ck.S2 * star ck.S2) * (ck.S1 * star ck.S1) = 0 := by
    rw [← mul_assoc, mul_assoc ck.S2 (star ck.S2) ck.S1, ck.S2_star_S1, mul_zero, zero_mul]
  have h22 : (ck.S2 * star ck.S2) * (ck.S2 * star ck.S2) = ck.S2 * star ck.S2 := by
    rw [← mul_assoc, mul_assoc ck.S2 (star ck.S2) ck.S2, ck.S2_star_S2, mul_one]
  calc (ck.S1 * star ck.S1 + ck.S2 * star ck.S2) * (ck.S1 * star ck.S1 + ck.S2 * star ck.S2)
      = (ck.S1 * star ck.S1) * (ck.S1 * star ck.S1) + (ck.S1 * star ck.S1) * (ck.S2 * star ck.S2) +
        (ck.S2 * star ck.S2) * (ck.S1 * star ck.S1) + (ck.S2 * star ck.S2) * (ck.S2 * star ck.S2) := by noncomm_ring
    _ = ck.S1 * star ck.S1 + 0 + 0 + ck.S2 * star ck.S2 := by rw [h11, h12, h21, h22]
    _ = ck.S1 * star ck.S1 + ck.S2 * star ck.S2 := by abel

theorem defectProjection_sq :
    defectProjection ck * defectProjection ck = defectProjection ck := by
  dsimp [defectProjection]
  have h_hsq := excitationProjection_sq ck
  calc (1 - excitationProjection ck) * (1 - excitationProjection ck)
      = 1 - excitationProjection ck - excitationProjection ck + excitationProjection ck * excitationProjection ck := by noncomm_ring
    _ = 1 - excitationProjection ck - excitationProjection ck + excitationProjection ck := by rw [h_hsq]
    _ = 1 - excitationProjection ck := by noncomm_ring

end CuntzTwoIsometry

/-- Matrix-to-Cuntz operator algebra representation map π : M₂(K) → A. -/
def matrixToCuntz {K A : Type*} [CommRing K] [Ring A] [Algebra K A] [StarRing A]
    (ck : CuntzTwoIsometry K A) (M : Matrix (Fin 2) (Fin 2) K) : A :=
  (M 0 0) • (ck.S1 * star ck.S1) +
  (M 0 1) • (ck.S1 * star ck.S2) +
  (M 1 0) • (ck.S2 * star ck.S1) +
  (M 1 1) • (ck.S2 * star ck.S2)

/-- Cuntz operator braid generator U₁ = π(σ₁). -/
def kuntzBraidGen1 {K A : Type*} [CommRing K] [Ring A] [Algebra K A] [StarRing A]
    (ck : CuntzTwoIsometry K A) (q1 q2 : K) : A :=
  matrixToCuntz ck (braidGen1 K q1 q2)

/-- Cuntz operator braid generator U₂ = π(σ₂). -/
def kuntzBraidGen2 {K A : Type*} [CommRing K] [Ring A] [Algebra K A] [StarRing A]
    (ck : CuntzTwoIsometry K A) (a b q1 q2 : K) : A :=
  matrixToCuntz ck (braidGen2 K a b q1 q2)

/-- Global vacuum-fixed operator extension M̃ = π(M) + P₀.
Note: M̃ is a unital multiplicative (*)-extension, NOT a ring/algebra homomorphism (non-additive). -/
def extendedMatrixToCuntz {K A : Type*} [CommRing K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    (ck : CuntzTwoIsometry K A) (M : Matrix (Fin 2) (Fin 2) K) : A :=
  matrixToCuntz ck M + ck.defectProjection

/-- Global extended braid generator 1: Ũ₁ = π(σ₁) + P₀. -/
def extendedBraidGen1 {K A : Type*} [CommRing K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    (ck : CuntzTwoIsometry K A) (q1 q2 : K) : A :=
  extendedMatrixToCuntz ck (braidGen1 K q1 q2)

/-- Global extended braid generator 2: Ũ₂ = π(σ₂) + P₀. -/
def extendedBraidGen2 {K A : Type*} [CommRing K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    (ck : CuntzTwoIsometry K A) (a b q1 q2 : K) : A :=
  extendedMatrixToCuntz ck (braidGen2 K a b q1 q2)

/-! ## Fundamental Representation API & Algebraic Laws -/

theorem matrixToCuntz_zero {K A : Type*} [CommRing K] [Ring A] [Algebra K A] [StarRing A]
    (ck : CuntzTwoIsometry K A) :
    matrixToCuntz ck 0 = 0 := by
  dsimp [matrixToCuntz]
  simp only [zero_smul, add_zero]

theorem matrixToCuntz_add {K A : Type*} [CommRing K] [Ring A] [Algebra K A] [StarRing A]
    (ck : CuntzTwoIsometry K A) (M N : Matrix (Fin 2) (Fin 2) K) :
    matrixToCuntz ck (M + N) = matrixToCuntz ck M + matrixToCuntz ck N := by
  dsimp [matrixToCuntz]
  simp only [add_smul]
  abel

theorem matrixToCuntz_smul {K A : Type*} [CommRing K] [Ring A] [Algebra K A] [StarRing A]
    (ck : CuntzTwoIsometry K A) (c : K) (M : Matrix (Fin 2) (Fin 2) K) :
    matrixToCuntz ck (c • M) = c • matrixToCuntz ck M := by
  dsimp [matrixToCuntz]
  simp only [smul_add, smul_smul]

theorem matrixToCuntz_one {K A : Type*} [CommRing K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    (ck : CuntzTwoIsometry K A) :
    matrixToCuntz ck 1 = ck.excitationProjection := by
  dsimp [matrixToCuntz, CuntzTwoIsometry.excitationProjection]
  change (1 : K) • (ck.S1 * star ck.S1) + (0 : K) • (ck.S1 * star ck.S2) +
         (0 : K) • (ck.S2 * star ck.S1) + (1 : K) • (ck.S2 * star ck.S2) =
         ck.S1 * star ck.S1 + ck.S2 * star ck.S2
  simp only [one_smul, zero_smul, add_zero, zero_add]

/-- Star-homomorphism theorem: π(M†) = (π(M))*. -/
theorem matrixToCuntz_conjTranspose {K A : Type*} [CommRing K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    (ck : CuntzTwoIsometry K A) (M : Matrix (Fin 2) (Fin 2) K) :
    matrixToCuntz ck M.conjTranspose = star (matrixToCuntz ck M) := by
  dsimp [matrixToCuntz, conjTranspose, transpose, map]
  have h_star_s1 : star (ck.S1 * star ck.S1) = ck.S1 * star ck.S1 := by simp only [StarMul.star_mul, star_star]
  have h_star_s2 : star (ck.S2 * star ck.S2) = ck.S2 * star ck.S2 := by simp only [StarMul.star_mul, star_star]
  have h_star_12 : star (ck.S1 * star ck.S2) = ck.S2 * star ck.S1 := by simp only [StarMul.star_mul, star_star]
  have h_star_21 : star (ck.S2 * star ck.S1) = ck.S1 * star ck.S2 := by simp only [StarMul.star_mul, star_star]
  simp only [star_add, star_smul, h_star_s1, h_star_s2, h_star_12, h_star_21]
  abel

/-- **Homomorphism Theorem**: π(M * N) = π(M) * π(N) in the Cuntz operator algebra A. -/
theorem matrixToCuntz_mul {K A : Type*} [CommRing K] [Ring A] [Algebra K A] [StarRing A]
    (ck : CuntzTwoIsometry K A) (M N : Matrix (Fin 2) (Fin 2) K) :
    matrixToCuntz ck (M * N) = matrixToCuntz ck M * matrixToCuntz ck N := by
  dsimp [matrixToCuntz, mul_apply]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [mul_add, add_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  have h11 : (ck.S1 * star ck.S1) * (ck.S1 * star ck.S1) = ck.S1 * star ck.S1 := by
    rw [← mul_assoc, mul_assoc ck.S1 (star ck.S1) ck.S1, ck.S1_star_S1, mul_one]
  have h12 : (ck.S1 * star ck.S1) * (ck.S1 * star ck.S2) = ck.S1 * star ck.S2 := by
    rw [← mul_assoc, mul_assoc ck.S1 (star ck.S1) ck.S1, ck.S1_star_S1, mul_one]
  have h13 : (ck.S1 * star ck.S1) * (ck.S2 * star ck.S1) = 0 := by
    rw [← mul_assoc, mul_assoc ck.S1 (star ck.S1) ck.S2, ck.S1_star_S2, mul_zero, zero_mul]
  have h14 : (ck.S1 * star ck.S1) * (ck.S2 * star ck.S2) = 0 := by
    rw [← mul_assoc, mul_assoc ck.S1 (star ck.S1) ck.S2, ck.S1_star_S2, mul_zero, zero_mul]

  have h21 : (ck.S1 * star ck.S2) * (ck.S1 * star ck.S1) = 0 := by
    rw [← mul_assoc, mul_assoc ck.S1 (star ck.S2) ck.S1, ck.S2_star_S1, mul_zero, zero_mul]
  have h22 : (ck.S1 * star ck.S2) * (ck.S1 * star ck.S2) = 0 := by
    rw [← mul_assoc, mul_assoc ck.S1 (star ck.S2) ck.S1, ck.S2_star_S1, mul_zero, zero_mul]
  have h23 : (ck.S1 * star ck.S2) * (ck.S2 * star ck.S1) = ck.S1 * star ck.S1 := by
    rw [← mul_assoc, mul_assoc ck.S1 (star ck.S2) ck.S2, ck.S2_star_S2, mul_one]
  have h24 : (ck.S1 * star ck.S2) * (ck.S2 * star ck.S2) = ck.S1 * star ck.S2 := by
    rw [← mul_assoc, mul_assoc ck.S1 (star ck.S2) ck.S2, ck.S2_star_S2, mul_one]

  have h31 : (ck.S2 * star ck.S1) * (ck.S1 * star ck.S1) = ck.S2 * star ck.S1 := by
    rw [← mul_assoc, mul_assoc ck.S2 (star ck.S1) ck.S1, ck.S1_star_S1, mul_one]
  have h32 : (ck.S2 * star ck.S1) * (ck.S1 * star ck.S2) = ck.S2 * star ck.S2 := by
    rw [← mul_assoc, mul_assoc ck.S2 (star ck.S1) ck.S1, ck.S1_star_S1, mul_one]
  have h33 : (ck.S2 * star ck.S1) * (ck.S2 * star ck.S1) = 0 := by
    rw [← mul_assoc, mul_assoc ck.S2 (star ck.S1) ck.S2, ck.S1_star_S2, mul_zero, zero_mul]
  have h34 : (ck.S2 * star ck.S1) * (ck.S2 * star ck.S2) = 0 := by
    rw [← mul_assoc, mul_assoc ck.S2 (star ck.S1) ck.S2, ck.S1_star_S2, mul_zero, zero_mul]

  have h41 : (ck.S2 * star ck.S2) * (ck.S1 * star ck.S1) = 0 := by
    rw [← mul_assoc, mul_assoc ck.S2 (star ck.S2) ck.S1, ck.S2_star_S1, mul_zero, zero_mul]
  have h42 : (ck.S2 * star ck.S2) * (ck.S1 * star ck.S2) = 0 := by
    rw [← mul_assoc, mul_assoc ck.S2 (star ck.S2) ck.S1, ck.S2_star_S1, mul_zero, zero_mul]
  have h43 : (ck.S2 * star ck.S2) * (ck.S2 * star ck.S1) = ck.S2 * star ck.S1 := by
    rw [← mul_assoc, mul_assoc ck.S2 (star ck.S2) ck.S2, ck.S2_star_S2, mul_one]
  have h44 : (ck.S2 * star ck.S2) * (ck.S2 * star ck.S2) = ck.S2 * star ck.S2 := by
    rw [← mul_assoc, mul_assoc ck.S2 (star ck.S2) ck.S2, ck.S2_star_S2, mul_one]

  rw [h11, h12, h13, h14, h21, h22, h23, h24, h31, h32, h33, h34, h41, h42, h43, h44]
  simp only [smul_zero, add_zero, zero_add, add_smul, smul_add, smul_smul]
  have h_comm (x y : K) (v : A) : (y * x) • v = (x * y) • v := by rw [mul_comm y x]
  simp only [h_comm]
  abel

/-! ## Coefficient Recovery & Injective Embedding Theorems -/

theorem S1_star_matrixToCuntz_S1 {K A : Type*} [CommRing K] [Ring A] [Algebra K A] [StarRing A]
    (ck : CuntzTwoIsometry K A) (M : Matrix (Fin 2) (Fin 2) K) :
    star ck.S1 * matrixToCuntz ck M * ck.S1 = algebraMap K A (M 0 0) := by
  dsimp [matrixToCuntz]
  simp only [mul_add, add_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  have h1 : star ck.S1 * (ck.S1 * star ck.S1) * ck.S1 = 1 := by
    calc star ck.S1 * (ck.S1 * star ck.S1) * ck.S1
        = (star ck.S1 * ck.S1) * (star ck.S1 * ck.S1) := by noncomm_ring
      _ = 1 * 1 := by rw [ck.S1_star_S1]
      _ = 1 := by noncomm_ring
  have h2 : star ck.S1 * (ck.S1 * star ck.S2) * ck.S1 = 0 := by
    calc star ck.S1 * (ck.S1 * star ck.S2) * ck.S1
        = (star ck.S1 * ck.S1) * (star ck.S2 * ck.S1) := by noncomm_ring
      _ = 1 * 0 := by rw [ck.S1_star_S1, ck.S2_star_S1]
      _ = 0 := by noncomm_ring
  have h3 : star ck.S1 * (ck.S2 * star ck.S1) * ck.S1 = 0 := by
    calc star ck.S1 * (ck.S2 * star ck.S1) * ck.S1
        = (star ck.S1 * ck.S2) * (star ck.S1 * ck.S1) := by noncomm_ring
      _ = 0 * 1 := by rw [ck.S1_star_S2, ck.S1_star_S1]
      _ = 0 := by noncomm_ring
  have h4 : star ck.S1 * (ck.S2 * star ck.S2) * ck.S1 = 0 := by
    calc star ck.S1 * (ck.S2 * star ck.S2) * ck.S1
        = (star ck.S1 * ck.S2) * (star ck.S2 * ck.S1) := by noncomm_ring
      _ = 0 * 0 := by rw [ck.S1_star_S2, ck.S2_star_S1]
      _ = 0 := by noncomm_ring
  rw [h1, h2, h3, h4]
  simp only [smul_zero, add_zero, zero_add]
  exact (Algebra.algebraMap_eq_smul_one (M 0 0)).symm

theorem S1_star_matrixToCuntz_S2 {K A : Type*} [CommRing K] [Ring A] [Algebra K A] [StarRing A]
    (ck : CuntzTwoIsometry K A) (M : Matrix (Fin 2) (Fin 2) K) :
    star ck.S1 * matrixToCuntz ck M * ck.S2 = algebraMap K A (M 0 1) := by
  dsimp [matrixToCuntz]
  simp only [mul_add, add_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  have h1 : star ck.S1 * (ck.S1 * star ck.S1) * ck.S2 = 0 := by
    calc star ck.S1 * (ck.S1 * star ck.S1) * ck.S2
        = (star ck.S1 * ck.S1) * (star ck.S1 * ck.S2) := by noncomm_ring
      _ = 1 * 0 := by rw [ck.S1_star_S1, ck.S1_star_S2]
      _ = 0 := by noncomm_ring
  have h2 : star ck.S1 * (ck.S1 * star ck.S2) * ck.S2 = 1 := by
    calc star ck.S1 * (ck.S1 * star ck.S2) * ck.S2
        = (star ck.S1 * ck.S1) * (star ck.S2 * ck.S2) := by noncomm_ring
      _ = 1 * 1 := by rw [ck.S1_star_S1, ck.S2_star_S2]
      _ = 1 := by noncomm_ring
  have h3 : star ck.S1 * (ck.S2 * star ck.S1) * ck.S2 = 0 := by
    calc star ck.S1 * (ck.S2 * star ck.S1) * ck.S2
        = (star ck.S1 * ck.S2) * (star ck.S1 * ck.S2) := by noncomm_ring
      _ = 0 * 0 := by rw [ck.S1_star_S2]
      _ = 0 := by noncomm_ring
  have h4 : star ck.S1 * (ck.S2 * star ck.S2) * ck.S2 = 0 := by
    calc star ck.S1 * (ck.S2 * star ck.S2) * ck.S2
        = (star ck.S1 * ck.S2) * (star ck.S2 * ck.S2) := by noncomm_ring
      _ = 0 * 1 := by rw [ck.S1_star_S2, ck.S2_star_S2]
      _ = 0 := by noncomm_ring
  rw [h1, h2, h3, h4]
  simp only [smul_zero, add_zero, zero_add]
  exact (Algebra.algebraMap_eq_smul_one (M 0 1)).symm

theorem S2_star_matrixToCuntz_S1 {K A : Type*} [CommRing K] [Ring A] [Algebra K A] [StarRing A]
    (ck : CuntzTwoIsometry K A) (M : Matrix (Fin 2) (Fin 2) K) :
    star ck.S2 * matrixToCuntz ck M * ck.S1 = algebraMap K A (M 1 0) := by
  dsimp [matrixToCuntz]
  simp only [mul_add, add_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  have h1 : star ck.S2 * (ck.S1 * star ck.S1) * ck.S1 = 0 := by
    calc star ck.S2 * (ck.S1 * star ck.S1) * ck.S1
        = (star ck.S2 * ck.S1) * (star ck.S1 * ck.S1) := by noncomm_ring
      _ = 0 * 1 := by rw [ck.S2_star_S1, ck.S1_star_S1]
      _ = 0 := by noncomm_ring
  have h2 : star ck.S2 * (ck.S1 * star ck.S2) * ck.S1 = 0 := by
    calc star ck.S2 * (ck.S1 * star ck.S2) * ck.S1
        = (star ck.S2 * ck.S1) * (star ck.S2 * ck.S1) := by noncomm_ring
      _ = 0 * 0 := by rw [ck.S2_star_S1]
      _ = 0 := by noncomm_ring
  have h3 : star ck.S2 * (ck.S2 * star ck.S1) * ck.S1 = 1 := by
    calc star ck.S2 * (ck.S2 * star ck.S1) * ck.S1
        = (star ck.S2 * ck.S2) * (star ck.S1 * ck.S1) := by noncomm_ring
      _ = 1 * 1 := by rw [ck.S2_star_S2, ck.S1_star_S1]
      _ = 1 := by noncomm_ring
  have h4 : star ck.S2 * (ck.S2 * star ck.S2) * ck.S1 = 0 := by
    calc star ck.S2 * (ck.S2 * star ck.S2) * ck.S1
        = (star ck.S2 * ck.S2) * (star ck.S2 * ck.S1) := by noncomm_ring
      _ = 1 * 0 := by rw [ck.S2_star_S2, ck.S2_star_S1]
      _ = 0 := by noncomm_ring
  rw [h1, h2, h3, h4]
  simp only [smul_zero, add_zero, zero_add]
  exact (Algebra.algebraMap_eq_smul_one (M 1 0)).symm

theorem S2_star_matrixToCuntz_S2 {K A : Type*} [CommRing K] [Ring A] [Algebra K A] [StarRing A]
    (ck : CuntzTwoIsometry K A) (M : Matrix (Fin 2) (Fin 2) K) :
    star ck.S2 * matrixToCuntz ck M * ck.S2 = algebraMap K A (M 1 1) := by
  dsimp [matrixToCuntz]
  simp only [mul_add, add_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  have h1 : star ck.S2 * (ck.S1 * star ck.S1) * ck.S2 = 0 := by
    calc star ck.S2 * (ck.S1 * star ck.S1) * ck.S2
        = (star ck.S2 * ck.S1) * (star ck.S1 * ck.S2) := by noncomm_ring
      _ = 0 * 0 := by rw [ck.S2_star_S1, ck.S1_star_S2]
      _ = 0 := by noncomm_ring
  have h2 : star ck.S2 * (ck.S1 * star ck.S2) * ck.S2 = 0 := by
    calc star ck.S2 * (ck.S1 * star ck.S2) * ck.S2
        = (star ck.S2 * ck.S1) * (star ck.S2 * ck.S2) := by noncomm_ring
      _ = 0 * 1 := by rw [ck.S2_star_S1, ck.S2_star_S2]
      _ = 0 := by noncomm_ring
  have h3 : star ck.S2 * (ck.S2 * star ck.S1) * ck.S2 = 0 := by
    calc star ck.S2 * (ck.S2 * star ck.S1) * ck.S2
        = (star ck.S2 * ck.S2) * (star ck.S1 * ck.S2) := by noncomm_ring
      _ = 1 * 0 := by rw [ck.S2_star_S2, ck.S1_star_S2]
      _ = 0 := by noncomm_ring
  have h4 : star ck.S2 * (ck.S2 * star ck.S2) * ck.S2 = 1 := by
    calc star ck.S2 * (ck.S2 * star ck.S2) * ck.S2
        = (star ck.S2 * ck.S2) * (star ck.S2 * ck.S2) := by noncomm_ring
      _ = 1 * 1 := by rw [ck.S2_star_S2]
      _ = 1 := by noncomm_ring
  rw [h1, h2, h3, h4]
  simp only [smul_zero, add_zero, zero_add]
  exact (Algebra.algebraMap_eq_smul_one (M 1 1)).symm

/-- **Injective Embedding Theorem**: Proves Function.Injective (matrixToCuntz ck)
provided algebraMap K A is injective. -/
theorem matrixToCuntz_injective {K A : Type*} [CommRing K] [Ring A] [Algebra K A] [StarRing A]
    (ck : CuntzTwoIsometry K A)
    (hScalar : Function.Injective (algebraMap K A)) :
    Function.Injective (matrixToCuntz ck) := by
  intro M N h_eq
  ext i j
  fin_cases i <;> fin_cases j
  · have h00 := congr_arg (fun x => star ck.S1 * x * ck.S1) h_eq
    dsimp at h00
    rw [S1_star_matrixToCuntz_S1 ck M, S1_star_matrixToCuntz_S1 ck N] at h00
    exact hScalar h00
  · have h01 := congr_arg (fun x => star ck.S1 * x * ck.S2) h_eq
    dsimp at h01
    rw [S1_star_matrixToCuntz_S2 ck M, S1_star_matrixToCuntz_S2 ck N] at h01
    exact hScalar h01
  · have h10 := congr_arg (fun x => star ck.S2 * x * ck.S1) h_eq
    dsimp at h10
    rw [S2_star_matrixToCuntz_S1 ck M, S2_star_matrixToCuntz_S1 ck N] at h10
    exact hScalar h10
  · have h11 := congr_arg (fun x => star ck.S2 * x * ck.S2) h_eq
    dsimp at h11
    rw [S2_star_matrixToCuntz_S2 ck M, S2_star_matrixToCuntz_S2 ck N] at h11
    exact hScalar h11

/-! ## Vacuum Orthogonality & Extended Unital API -/

theorem matrixToCuntz_mul_defect {K A : Type*} [CommRing K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    (ck : CuntzTwoIsometry K A) (M : Matrix (Fin 2) (Fin 2) K) :
    matrixToCuntz ck M * ck.defectProjection = 0 := by
  dsimp [matrixToCuntz, CuntzTwoIsometry.defectProjection, CuntzTwoIsometry.excitationProjection]
  have h11 : (ck.S1 * star ck.S1) * (1 - (ck.S1 * star ck.S1 + ck.S2 * star ck.S2)) = 0 := by
    have h : (ck.S1 * star ck.S1) * (1 - (ck.S1 * star ck.S1 + ck.S2 * star ck.S2)) =
             ck.S1 * star ck.S1 - (ck.S1 * star ck.S1) * (ck.S1 * star ck.S1) - (ck.S1 * star ck.S1) * (ck.S2 * star ck.S2) := by noncomm_ring
    have h_sq : (ck.S1 * star ck.S1) * (ck.S1 * star ck.S1) = ck.S1 * star ck.S1 := by
      rw [← mul_assoc, mul_assoc ck.S1 (star ck.S1) ck.S1, ck.S1_star_S1, mul_one]
    have h_orth : (ck.S1 * star ck.S1) * (ck.S2 * star ck.S2) = 0 := by
      rw [← mul_assoc, mul_assoc ck.S1 (star ck.S1) ck.S2, ck.S1_star_S2, mul_zero, zero_mul]
    rw [h, h_sq, h_orth, sub_self, sub_zero]
  have h12 : (ck.S1 * star ck.S2) * (1 - (ck.S1 * star ck.S1 + ck.S2 * star ck.S2)) = 0 := by
    have h : (ck.S1 * star ck.S2) * (1 - (ck.S1 * star ck.S1 + ck.S2 * star ck.S2)) =
             ck.S1 * star ck.S2 - (ck.S1 * star ck.S2) * (ck.S1 * star ck.S1) - (ck.S1 * star ck.S2) * (ck.S2 * star ck.S2) := by noncomm_ring
    have h_o1 : (ck.S1 * star ck.S2) * (ck.S1 * star ck.S1) = 0 := by
      rw [← mul_assoc, mul_assoc ck.S1 (star ck.S2) ck.S1, ck.S2_star_S1, mul_zero, zero_mul]
    have h_o2 : (ck.S1 * star ck.S2) * (ck.S2 * star ck.S2) = ck.S1 * star ck.S2 := by
      rw [← mul_assoc, mul_assoc ck.S1 (star ck.S2) ck.S2, ck.S2_star_S2, mul_one]
    rw [h, h_o1, h_o2, sub_zero, sub_self]
  have h21 : (ck.S2 * star ck.S1) * (1 - (ck.S1 * star ck.S1 + ck.S2 * star ck.S2)) = 0 := by
    have h : (ck.S2 * star ck.S1) * (1 - (ck.S1 * star ck.S1 + ck.S2 * star ck.S2)) =
             ck.S2 * star ck.S1 - (ck.S2 * star ck.S1) * (ck.S1 * star ck.S1) - (ck.S2 * star ck.S1) * (ck.S2 * star ck.S2) := by noncomm_ring
    have h_o1 : (ck.S2 * star ck.S1) * (ck.S1 * star ck.S1) = ck.S2 * star ck.S1 := by
      rw [← mul_assoc, mul_assoc ck.S2 (star ck.S1) ck.S1, ck.S1_star_S1, mul_one]
    have h_o2 : (ck.S2 * star ck.S1) * (ck.S2 * star ck.S2) = 0 := by
      rw [← mul_assoc, mul_assoc ck.S2 (star ck.S1) ck.S2, ck.S1_star_S2, mul_zero, zero_mul]
    rw [h, h_o1, h_o2, sub_self, sub_zero]
  have h22 : (ck.S2 * star ck.S2) * (1 - (ck.S1 * star ck.S1 + ck.S2 * star ck.S2)) = 0 := by
    have h : (ck.S2 * star ck.S2) * (1 - (ck.S1 * star ck.S1 + ck.S2 * star ck.S2)) =
             ck.S2 * star ck.S2 - (ck.S2 * star ck.S2) * (ck.S1 * star ck.S1) - (ck.S2 * star ck.S2) * (ck.S2 * star ck.S2) := by noncomm_ring
    have h_o1 : (ck.S2 * star ck.S2) * (ck.S1 * star ck.S1) = 0 := by
      rw [← mul_assoc, mul_assoc ck.S2 (star ck.S2) ck.S1, ck.S2_star_S1, mul_zero, zero_mul]
    have h_o2 : (ck.S2 * star ck.S2) * (ck.S2 * star ck.S2) = ck.S2 * star ck.S2 := by
      rw [← mul_assoc, mul_assoc ck.S2 (star ck.S2) ck.S2, ck.S2_star_S2, mul_one]
    rw [h, h_o1, h_o2, sub_zero, sub_self]
  simp only [add_mul, smul_mul_assoc, h11, h12, h21, h22, smul_zero, add_zero]

theorem defect_mul_matrixToCuntz {K A : Type*} [CommRing K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    (ck : CuntzTwoIsometry K A) (M : Matrix (Fin 2) (Fin 2) K) :
    ck.defectProjection * matrixToCuntz ck M = 0 := by
  dsimp [matrixToCuntz, CuntzTwoIsometry.defectProjection, CuntzTwoIsometry.excitationProjection]
  have h11 : (1 - (ck.S1 * star ck.S1 + ck.S2 * star ck.S2)) * (ck.S1 * star ck.S1) = 0 := by
    have h : (1 - (ck.S1 * star ck.S1 + ck.S2 * star ck.S2)) * (ck.S1 * star ck.S1) =
             ck.S1 * star ck.S1 - (ck.S1 * star ck.S1) * (ck.S1 * star ck.S1) - (ck.S2 * star ck.S2) * (ck.S1 * star ck.S1) := by noncomm_ring
    have h_sq : (ck.S1 * star ck.S1) * (ck.S1 * star ck.S1) = ck.S1 * star ck.S1 := by
      rw [← mul_assoc, mul_assoc ck.S1 (star ck.S1) ck.S1, ck.S1_star_S1, mul_one]
    have h_orth : (ck.S2 * star ck.S2) * (ck.S1 * star ck.S1) = 0 := by
      rw [← mul_assoc, mul_assoc ck.S2 (star ck.S2) ck.S1, ck.S2_star_S1, mul_zero, zero_mul]
    rw [h, h_sq, h_orth, sub_self, sub_zero]
  have h12 : (1 - (ck.S1 * star ck.S1 + ck.S2 * star ck.S2)) * (ck.S1 * star ck.S2) = 0 := by
    have h : (1 - (ck.S1 * star ck.S1 + ck.S2 * star ck.S2)) * (ck.S1 * star ck.S2) =
             ck.S1 * star ck.S2 - (ck.S1 * star ck.S1) * (ck.S1 * star ck.S2) - (ck.S2 * star ck.S2) * (ck.S1 * star ck.S2) := by noncomm_ring
    have h_o1 : (ck.S1 * star ck.S1) * (ck.S1 * star ck.S2) = ck.S1 * star ck.S2 := by
      rw [← mul_assoc, mul_assoc ck.S1 (star ck.S1) ck.S1, ck.S1_star_S1, mul_one]
    have h_o2 : (ck.S2 * star ck.S2) * (ck.S1 * star ck.S2) = 0 := by
      rw [← mul_assoc, mul_assoc ck.S2 (star ck.S2) ck.S1, ck.S2_star_S1, mul_zero, zero_mul]
    rw [h, h_o1, h_o2, sub_self, sub_zero]
  have h21 : (1 - (ck.S1 * star ck.S1 + ck.S2 * star ck.S2)) * (ck.S2 * star ck.S1) = 0 := by
    have h : (1 - (ck.S1 * star ck.S1 + ck.S2 * star ck.S2)) * (ck.S2 * star ck.S1) =
             ck.S2 * star ck.S1 - (ck.S1 * star ck.S1) * (ck.S2 * star ck.S1) - (ck.S2 * star ck.S2) * (ck.S2 * star ck.S1) := by noncomm_ring
    have h_o1 : (ck.S1 * star ck.S1) * (ck.S2 * star ck.S1) = 0 := by
      rw [← mul_assoc, mul_assoc ck.S1 (star ck.S1) ck.S2, ck.S1_star_S2, mul_zero, zero_mul]
    have h_o2 : (ck.S2 * star ck.S2) * (ck.S2 * star ck.S1) = ck.S2 * star ck.S1 := by
      rw [← mul_assoc, mul_assoc ck.S2 (star ck.S2) ck.S2, ck.S2_star_S2, mul_one]
    rw [h, h_o1, h_o2, sub_zero, sub_self]
  have h22 : (1 - (ck.S1 * star ck.S1 + ck.S2 * star ck.S2)) * (ck.S2 * star ck.S2) = 0 := by
    have h : (1 - (ck.S1 * star ck.S1 + ck.S2 * star ck.S2)) * (ck.S2 * star ck.S2) =
             ck.S2 * star ck.S2 - (ck.S1 * star ck.S1) * (ck.S2 * star ck.S2) - (ck.S2 * star ck.S2) * (ck.S2 * star ck.S2) := by noncomm_ring
    have h_o1 : (ck.S1 * star ck.S1) * (ck.S2 * star ck.S2) = 0 := by
      rw [← mul_assoc, mul_assoc ck.S1 (star ck.S1) ck.S2, ck.S1_star_S2, mul_zero, zero_mul]
    have h_o2 : (ck.S2 * star ck.S2) * (ck.S2 * star ck.S2) = ck.S2 * star ck.S2 := by
      rw [← mul_assoc, mul_assoc ck.S2 (star ck.S2) ck.S2, ck.S2_star_S2, mul_one]
    rw [h, h_o1, h_o2, sub_zero, sub_self]
  simp only [mul_add, mul_smul_comm, h11, h12, h21, h22, smul_zero, add_zero]

theorem extendedMatrixToCuntz_one {K A : Type*} [CommRing K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    (ck : CuntzTwoIsometry K A) :
    extendedMatrixToCuntz ck 1 = 1 := by
  dsimp [extendedMatrixToCuntz, CuntzTwoIsometry.defectProjection]
  rw [matrixToCuntz_one ck]
  noncomm_ring

theorem extendedMatrixToCuntz_mul {K A : Type*} [CommRing K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    (ck : CuntzTwoIsometry K A) (M N : Matrix (Fin 2) (Fin 2) K) :
    extendedMatrixToCuntz ck (M * N) = extendedMatrixToCuntz ck M * extendedMatrixToCuntz ck N := by
  dsimp [extendedMatrixToCuntz]
  have h_mo := matrixToCuntz_mul ck M N
  have h_md := matrixToCuntz_mul_defect ck M
  have h_dm := defect_mul_matrixToCuntz ck N
  have h_dd := ck.defectProjection_sq
  have h_sum : matrixToCuntz ck M * matrixToCuntz ck N + matrixToCuntz ck M * ck.defectProjection +
               ck.defectProjection * matrixToCuntz ck N + ck.defectProjection * ck.defectProjection =
               matrixToCuntz ck M * matrixToCuntz ck N + ck.defectProjection := by
    rw [h_md, h_dm, h_dd]
    simp only [add_zero, zero_add]
  rw [h_mo, ← h_sum]
  noncomm_ring

/-- Right vacuum fixation theorem: M̃(M) P₀ = P₀. -/
theorem extendedMatrixToCuntz_fixes_defect {K A : Type*} [CommRing K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    (ck : CuntzTwoIsometry K A) (M : Matrix (Fin 2) (Fin 2) K) :
    extendedMatrixToCuntz ck M * ck.defectProjection = ck.defectProjection := by
  dsimp [extendedMatrixToCuntz]
  have h_md := matrixToCuntz_mul_defect ck M
  have h_dd := ck.defectProjection_sq
  calc (matrixToCuntz ck M + ck.defectProjection) * ck.defectProjection
      = matrixToCuntz ck M * ck.defectProjection + ck.defectProjection * ck.defectProjection := by noncomm_ring
    _ = 0 + ck.defectProjection := by rw [h_md, h_dd]
    _ = ck.defectProjection := by simp only [zero_add]

/-- **Left Vacuum Fixation Theorem (Bilateral Audit Compliance)**: P₀ M̃(M) = P₀. -/
theorem defect_fixes_extendedMatrixToCuntz {K A : Type*} [CommRing K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    (ck : CuntzTwoIsometry K A) (M : Matrix (Fin 2) (Fin 2) K) :
    ck.defectProjection * extendedMatrixToCuntz ck M = ck.defectProjection := by
  dsimp [extendedMatrixToCuntz]
  have h_dm := defect_mul_matrixToCuntz ck M
  have h_dd := ck.defectProjection_sq
  calc ck.defectProjection * (matrixToCuntz ck M + ck.defectProjection)
      = ck.defectProjection * matrixToCuntz ck M + ck.defectProjection * ck.defectProjection := by noncomm_ring
    _ = 0 + ck.defectProjection := by rw [h_dm, h_dd]
    _ = ck.defectProjection := by simp only [zero_add]

/-! ## Apex Representation Theorems -/

/-- **Apex Corner Representation Theorem**: Cuntz Operator Artin Braid Relation U₁ U₂ U₁ = U₂ U₁ U₂. -/
theorem kuntz_artin_braid_relation {K A : Type*} [CommRing K] [Ring A] [Algebra K A] [StarRing A]
    (ck : CuntzTwoIsometry K A) (a b q1 q2 : K)
    (h_norm : a ^ 2 + b ^ 2 = 1)
    (h_braid : a ^ 2 * q1 ^ 2 + (b ^ 2 - a ^ 2) * q1 * q2 + a ^ 2 * q2 ^ 2 = 0) :
    kuntzBraidGen1 ck q1 q2 * kuntzBraidGen2 ck a b q1 q2 * kuntzBraidGen1 ck q1 q2 =
    kuntzBraidGen2 ck a b q1 q2 * kuntzBraidGen1 ck q1 q2 * kuntzBraidGen2 ck a b q1 q2 := by
  dsimp [kuntzBraidGen1, kuntzBraidGen2]
  rw [← matrixToCuntz_mul, ← matrixToCuntz_mul, ← matrixToCuntz_mul, ← matrixToCuntz_mul]
  rw [nonAbelian_artin_braid_relation K a b q1 q2 h_norm h_braid]

/-- **Apex Extended Global Representation Theorem**: Extended Artin Braid Relation Ũ₁ Ũ₂ Ũ₁ = Ũ₂ Ũ₁ Ũ₂. -/
theorem extended_artin_braid_relation {K A : Type*} [CommRing K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    (ck : CuntzTwoIsometry K A) (a b q1 q2 : K)
    (h_norm : a ^ 2 + b ^ 2 = 1)
    (h_braid : a ^ 2 * q1 ^ 2 + (b ^ 2 - a ^ 2) * q1 * q2 + a ^ 2 * q2 ^ 2 = 0) :
    extendedBraidGen1 ck q1 q2 * extendedBraidGen2 ck a b q1 q2 * extendedBraidGen1 ck q1 q2 =
    extendedBraidGen2 ck a b q1 q2 * extendedBraidGen1 ck q1 q2 * extendedBraidGen2 ck a b q1 q2 := by
  dsimp [extendedBraidGen1, extendedBraidGen2]
  rw [← extendedMatrixToCuntz_mul, ← extendedMatrixToCuntz_mul, ← extendedMatrixToCuntz_mul, ← extendedMatrixToCuntz_mul]
  rw [nonAbelian_artin_braid_relation K a b q1 q2 h_norm h_braid]

/-- **Apex Global Involution Theorem**: (π(F) + P₀)² = 1. -/
theorem extended_fMatrix_sq {K A : Type*} [CommRing K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    (ck : CuntzTwoIsometry K A) (a b : K) (h_norm : a ^ 2 + b ^ 2 = 1) :
    extendedMatrixToCuntz ck (fMatrix K a b) * extendedMatrixToCuntz ck (fMatrix K a b) = 1 := by
  rw [← extendedMatrixToCuntz_mul, fMatrix_sq K a b h_norm, extendedMatrixToCuntz_one]

/-- **Master Representation Synthesis**: Fibonacci Fusion Braid Algebra into Toeplitz-Cuntz. -/
theorem master_fibonacci_toeplitz_cuntz_representation {K A : Type*} [CommRing K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    (ck : CuntzTwoIsometry K A) (a b q1 q2 : K)
    (h_norm : a ^ 2 + b ^ 2 = 1)
    (h_braid : a ^ 2 * q1 ^ 2 + (b ^ 2 - a ^ 2) * q1 * q2 + a ^ 2 * q2 ^ 2 = 0) :
    matrixToCuntz ck 1 = ck.excitationProjection ∧
    extendedMatrixToCuntz ck 1 = 1 ∧
    extendedMatrixToCuntz ck (fMatrix K a b) * extendedMatrixToCuntz ck (fMatrix K a b) = 1 ∧
    (∀ M : Matrix (Fin 2) (Fin 2) K, extendedMatrixToCuntz ck M * ck.defectProjection = ck.defectProjection) ∧
    (∀ M : Matrix (Fin 2) (Fin 2) K, ck.defectProjection * extendedMatrixToCuntz ck M = ck.defectProjection) ∧
    kuntzBraidGen1 ck q1 q2 * kuntzBraidGen2 ck a b q1 q2 * kuntzBraidGen1 ck q1 q2 =
      kuntzBraidGen2 ck a b q1 q2 * kuntzBraidGen1 ck q1 q2 * kuntzBraidGen2 ck a b q1 q2 ∧
    extendedBraidGen1 ck q1 q2 * extendedBraidGen2 ck a b q1 q2 * extendedBraidGen1 ck q1 q2 =
      extendedBraidGen2 ck a b q1 q2 * extendedBraidGen1 ck q1 q2 * extendedBraidGen2 ck a b q1 q2 := by
  refine ⟨matrixToCuntz_one ck, extendedMatrixToCuntz_one ck,
    extended_fMatrix_sq ck a b h_norm, ?_, ?_, ?_, ?_⟩
  · exact fun M => extendedMatrixToCuntz_fixes_defect ck M
  · exact fun M => defect_fixes_extendedMatrixToCuntz ck M
  · exact kuntz_artin_braid_relation ck a b q1 q2 h_norm h_braid
  · exact extended_artin_braid_relation ck a b q1 q2 h_norm h_braid

end InfoGeometry.Canonical.FibonacciToeplitzCuntzRepresentationBridge
