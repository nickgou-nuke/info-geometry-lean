/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import InfoGeometry.Canonical.IwasawaKANTriad
import InfoGeometry.Algebra.IwasawaRealKAN
import InfoGeometry.Algebra.BlockSchurFactorization

/-!
# Weyl–Cartan Split, Noncommutative Trace-to-Determinant & Polar Equivariance

This module implements Milestone 6C:
* KP1: Weyl–Cartan threefold matrix split, basis expansion, Lie brackets, and
  noncommutative Plemelj–Newton trace-to-determinant identity;
* KP2: Iwasawa KAN subgroup laws, polar Gram reduction eliminating unitary K,
  and division-free Schur complement recovery;
* KP3: Polar decomposition unitary equivariance under conjugation, left, and right actions;
* KP4: Iwasawa KAN symmetry equivariance under Borelian scaling, fiber gauge,
  chirality parity, and Weyl reflection;
* KP5: Unconditional existence and uniqueness of the SL(2, ℝ) Iwasawa KAN decomposition,
  and constructive closed-form GL(2, ℝ) polar decomposition;
* OpenGauss T16 non-commutativity witnesses.
-/

namespace InfoGeometry.Algebra.WeylCartanKANPolarEquivariance

open Matrix
open InfoGeometry.Canonical
open InfoGeometry.Canonical.IwasawaKANTriad

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

section KP1_WeylCartan

variable {B : Type*} [Ring B]

/-- Fiber embedding as scalar multiple of identity in Iwasawa A_grp. -/
def fiberEmbed (a : B) : Matrix (Fin 2) (Fin 2) B :=
  IwasawaKANTriad.A_grp B a a

/-- Cartan grading generator gamma1. -/
def gamma1Op : Matrix (Fin 2) (Fin 2) B :=
  IwasawaKANTriad.eps B

/-- Pauli sigma / Weyl reflection generator. -/
def sigmaOp : Matrix (Fin 2) (Fin 2) B :=
  IwasawaKANTriad.e1 B

/-- Symplectic rotation / elliptic generator omega = -e2. -/
def omegaOp : Matrix (Fin 2) (Fin 2) B :=
  -IwasawaKANTriad.e2 B

/-- Iwasawa compact factor K. -/
def iwasawaK (c s : B) : Matrix (Fin 2) (Fin 2) B :=
  IwasawaKANTriad.K_grp B c s

/-- Iwasawa diagonal factor A. -/
def iwasawaA (a_plus a_minus : B) : Matrix (Fin 2) (Fin 2) B :=
  IwasawaKANTriad.A_grp B a_plus a_minus

/-- Iwasawa upper unipotent factor N. -/
def iwasawaN (n : B) : Matrix (Fin 2) (Fin 2) B :=
  IwasawaKANTriad.N_grp B n

/-- Iwasawa lower unipotent factor NMinus. -/
def iwasawaNMinus (n : B) : Matrix (Fin 2) (Fin 2) B :=
  (IwasawaKANTriad.N_grp B n)ᵀ

/-- Central Weyl scale part: Tr(M) • I. -/
def weylScalePart (M : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  fiberEmbed (Matrix.trace M)

/-- Traceless symmetric part of a 2x2 matrix. -/
def tracelessSymPart (M : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  !![M 0 0 - M 1 1, M 0 1 + M 1 0;
     M 1 0 + M 0 1, M 1 1 - M 0 0]

/-- Traceless antisymmetric part of a 2x2 matrix. -/
def tracelessAntisymPart (M : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  !![0, M 0 1 - M 1 0;
     M 1 0 - M 0 1, 0]

/-- Noncommutative symmetric determinant. -/
def symDet (M : Matrix (Fin 2) (Fin 2) B) : B :=
  (M 0 0 * M 1 1 + M 1 1 * M 0 0) - (M 0 1 * M 1 0 + M 1 0 * M 0 1)

/-- Threefold Weyl-Cartan split: Scale + Sym_traceless + Antisym_traceless = 2 • M. -/
theorem weyl_cartan_split (M : Matrix (Fin 2) (Fin 2) B) :
    weylScalePart M + tracelessSymPart M + tracelessAntisymPart M = 2 • M := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [weylScalePart, tracelessSymPart, tracelessAntisymPart, fiberEmbed,
      IwasawaKANTriad.A_grp, Matrix.trace_fin_two, two_smul]
    try abel
  }

/-- Noncommutative fiber-generator basis expansion of traceless symmetric part. -/
theorem tracelessSymPart_eq_basis (M : Matrix (Fin 2) (Fin 2) B) :
    tracelessSymPart M =
      fiberEmbed (M 0 0 - M 1 1) * gamma1Op + fiberEmbed (M 0 1 + M 1 0) * sigmaOp := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [tracelessSymPart, fiberEmbed, gamma1Op, sigmaOp, IwasawaKANTriad.A_grp,
      IwasawaKANTriad.eps_eq, IwasawaKANTriad.e1, Matrix.mul_apply, Fin.sum_univ_two]
    try abel
  }

/-- Noncommutative fiber-generator basis expansion of traceless antisymmetric part. -/
theorem tracelessAntisymPart_eq_basis (M : Matrix (Fin 2) (Fin 2) B) :
    tracelessAntisymPart M = fiberEmbed (M 1 0 - M 0 1) * omegaOp := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [tracelessAntisymPart, fiberEmbed, omegaOp, IwasawaKANTriad.A_grp,
      IwasawaKANTriad.e2, Matrix.mul_apply, Fin.sum_univ_two]
    try abel
  }

/-- Traceless symmetric part has trace zero. -/
theorem trace_tracelessSymPart (M : Matrix (Fin 2) (Fin 2) B) :
    Matrix.trace (tracelessSymPart M) = 0 := by
  rw [Matrix.trace_fin_two]
  simp [tracelessSymPart]
  try abel

/-- Traceless antisymmetric part has trace zero. -/
theorem trace_tracelessAntisymPart (M : Matrix (Fin 2) (Fin 2) B) :
    Matrix.trace (tracelessAntisymPart M) = 0 := by
  rw [Matrix.trace_fin_two]
  simp [tracelessAntisymPart]

/-- Traceless symmetric part is symmetric under transpose. -/
theorem transpose_tracelessSymPart (M : Matrix (Fin 2) (Fin 2) B) :
    (tracelessSymPart M)ᵀ = tracelessSymPart M := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [tracelessSymPart, Matrix.transpose_apply]
    try abel
  }

/-- Traceless antisymmetric part is skew-symmetric under transpose. -/
theorem transpose_tracelessAntisymPart (M : Matrix (Fin 2) (Fin 2) B) :
    (tracelessAntisymPart M)ᵀ = -tracelessAntisymPart M := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [tracelessAntisymPart, Matrix.transpose_apply]
    try abel
  }

/-- Noncommutative Plemelj-Newton trace-to-determinant identity. -/
theorem noncommutative_plemelj_newton_trace_to_det (M : Matrix (Fin 2) (Fin 2) B) :
    Matrix.trace M *
      Matrix.trace M - Matrix.trace (M * M) = symDet M := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, symDet]
  noncomm_ring

/-- Commutative specialization: symDet equals 2 * det. -/
theorem symDet_comm {R : Type*} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) :
    symDet A = 2 * A.det := by
  simp only [symDet, Matrix.det_fin_two]
  ring

/-- 2x2 Cayley-Hamilton theorem over commutative ring. -/
theorem cayley_hamilton_two {R : Type*} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) :
    A * A - Matrix.trace A • A + A.det • (1 : Matrix (Fin 2) (Fin 2) R) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
      Matrix.det_fin_two, Matrix.one_apply]
    ring
  }

/-- Lie bracket [gamma1, sigma] = -(2 • omega). -/
theorem cartan_lie_gamma1_sigma :
    ⁅gamma1Op (B := B), sigmaOp (B := B)⁆ = -(2 • omegaOp (B := B)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [Bracket.bracket, gamma1Op, sigmaOp, omegaOp, IwasawaKANTriad.eps_eq,
      IwasawaKANTriad.e1, IwasawaKANTriad.e2, Matrix.mul_apply, Fin.sum_univ_two, two_smul]
    try abel
  }

/-- Lie bracket [omega, gamma1] = 2 • sigma. -/
theorem cartan_lie_omega_gamma1 :
    ⁅omegaOp (B := B), gamma1Op (B := B)⁆ = 2 • sigmaOp (B := B) := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [Bracket.bracket, gamma1Op, sigmaOp, omegaOp, IwasawaKANTriad.eps_eq,
      IwasawaKANTriad.e1, IwasawaKANTriad.e2, Matrix.mul_apply, Fin.sum_univ_two, two_smul]
    try abel
  }

/-- Lie bracket [omega, sigma] = -(2 • gamma1). -/
theorem cartan_lie_omega_sigma :
    ⁅omegaOp (B := B), sigmaOp (B := B)⁆ = -(2 • gamma1Op (B := B)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [Bracket.bracket, gamma1Op, sigmaOp, omegaOp, IwasawaKANTriad.eps_eq,
      IwasawaKANTriad.e1, IwasawaKANTriad.e2, Matrix.mul_apply, Fin.sum_univ_two, two_smul]
    try abel
  }

end KP1_WeylCartan

section KP2_IwasawaSubgroupsAndPolarGram

variable {B : Type*} [Ring B]

/-- Subgroup law for N: N(n₁) * N(n₂) = N(n₁ + n₂). -/
theorem iwasawaN_mul (n₁ n₂ : B) :
    iwasawaN n₁ * iwasawaN n₂ = iwasawaN (n₁ + n₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [iwasawaN, IwasawaKANTriad.N_grp, Matrix.mul_apply, Fin.sum_univ_two]
    try abel
  }

/-- Subgroup law for A: componentwise multiplication. -/
theorem iwasawaA_mul (a₁ a₂ b₁ b₂ : B) :
    iwasawaA a₁ a₂ * iwasawaA b₁ b₂ = iwasawaA (a₁ * b₁) (a₂ * b₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [iwasawaA, IwasawaKANTriad.A_grp, Matrix.mul_apply, Fin.sum_univ_two]
    try abel
  }

/-- Unipotent inverse: N(n) * N(-n) = 1. -/
theorem iwasawaN_mul_neg (n : B) :
    iwasawaN n * iwasawaN (-n) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [iwasawaN, IwasawaKANTriad.N_grp, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply]
    try abel
  }

/-- Product A * N in explicit coordinates. -/
theorem iwasawaA_mul_iwasawaN (a_plus a_minus n : B) :
    iwasawaA a_plus a_minus * iwasawaN n = !![a_plus, a_plus * n; 0, a_minus] := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [iwasawaA, iwasawaN, IwasawaKANTriad.A_grp, IwasawaKANTriad.N_grp,
      Matrix.mul_apply, Fin.sum_univ_two]
    try abel
  }

/-- Polar Gram reduction: Unitary K drops out of Mᴴ * M. -/
theorem polar_gram_reduction [StarRing B] (c s a_plus a_minus n : B)
    (hK : (iwasawaK c s)ᴴ * iwasawaK c s = 1) :
    (iwasawaK c s * iwasawaA a_plus a_minus * iwasawaN n)ᴴ *
        (iwasawaK c s * iwasawaA a_plus a_minus * iwasawaN n) =
      (iwasawaN n)ᴴ * iwasawaA (star a_plus * a_plus) (star a_minus * a_minus) * iwasawaN n := by
  have h_assoc : iwasawaK c s * iwasawaA a_plus a_minus * iwasawaN n =
      iwasawaK c s * (iwasawaA a_plus a_minus * iwasawaN n) := by
    rw [Matrix.mul_assoc]
  rw [h_assoc, Matrix.conjTranspose_mul]
  have h_mid : (iwasawaA a_plus a_minus * iwasawaN n)ᴴ * (iwasawaK c s)ᴴ *
        (iwasawaK c s * (iwasawaA a_plus a_minus * iwasawaN n)) =
      (iwasawaA a_plus a_minus * iwasawaN n)ᴴ * ((iwasawaK c s)ᴴ * iwasawaK c s) *
        (iwasawaA a_plus a_minus * iwasawaN n) := by
    repeat rw [Matrix.mul_assoc]
  rw [h_mid, hK, Matrix.mul_one, Matrix.conjTranspose_mul]
  have hA_conj : (iwasawaA a_plus a_minus)ᴴ = iwasawaA (star a_plus) (star a_minus) := by
    ext i j
    fin_cases i <;> fin_cases j <;> {
      simp [iwasawaA, IwasawaKANTriad.A_grp, Matrix.conjTranspose_apply, star_zero]
    }
  have hAA : (iwasawaA a_plus a_minus)ᴴ * iwasawaA a_plus a_minus =
      iwasawaA (star a_plus * a_plus) (star a_minus * a_minus) := by
    rw [hA_conj, iwasawaA_mul]
  have h_mid2 : (iwasawaN n)ᴴ * (iwasawaA a_plus a_minus)ᴴ * (iwasawaA a_plus a_minus * iwasawaN n) =
      (iwasawaN n)ᴴ * ((iwasawaA a_plus a_minus)ᴴ * iwasawaA a_plus a_minus) * iwasawaN n := by
    repeat rw [Matrix.mul_assoc]
  rw [h_mid2, hAA]

/-- Explicit Cholesky matrix entries of the reduced Gram matrix. -/
theorem gram_matrix_explicit_entries [StarRing B] (a_plus a_minus n : B) :
    (iwasawaN n)ᴴ * iwasawaA (star a_plus * a_plus) (star a_minus * a_minus) * iwasawaN n =
      !![star a_plus * a_plus, (star a_plus * a_plus) * n;
         star n * (star a_plus * a_plus),
         star n * (star a_plus * a_plus) * n + star a_minus * a_minus] := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [iwasawaN, iwasawaA, IwasawaKANTriad.N_grp, IwasawaKANTriad.A_grp,
      Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two, star_one, star_zero]
    try noncomm_ring
  }

/-- Division-free noncommutative Schur complement recovery. -/
theorem schur_complement_recovery [StarRing B] (S : Matrix (Fin 2) (Fin 2) B) (a_plus a_minus n : B)
    (hS : S = (iwasawaN n)ᴴ * iwasawaA (star a_plus * a_plus) (star a_minus * a_minus) * iwasawaN n) :
    S 1 1 - star n * S 0 0 * n = star a_minus * a_minus := by
  have hG : S = !![star a_plus * a_plus, (star a_plus * a_plus) * n;
                   star n * (star a_plus * a_plus),
                   star n * (star a_plus * a_plus) * n + star a_minus * a_minus] := by
    rw [hS, gram_matrix_explicit_entries]
  have h11 : S 1 1 = star n * (star a_plus * a_plus) * n + star a_minus * a_minus := by
    rw [hG]
    rfl
  have h00 : S 0 0 = star a_plus * a_plus := by
    rw [hG]
    rfl
  rw [h11, h00]
  abel

end KP2_IwasawaSubgroupsAndPolarGram

section KP3_PolarEquivariance

variable {R : Type*} [Ring R] [StarRing R]

/-- Polar decomposition equivariance under unitary conjugation G * · * G⁻¹. -/
theorem polar_decomposition_unitary_equivariance
    (U P : R) (hU : star U * U = 1) (hP : star P = P)
    (G : Rˣ) (hG : (↑G⁻¹ : R) = star (G : R)) :
    let U_G := (G : R) * U * (↑G⁻¹ : R)
    let P_G := (G : R) * P * (↑G⁻¹ : R)
    let M_G := (G : R) * (U * P) * (↑G⁻¹ : R)
    M_G = U_G * P_G ∧
    star U_G * U_G = 1 ∧
    star P_G = P_G ∧
    star M_G * M_G = (G : R) * (star (U * P) * (U * P)) * (↑G⁻¹ : R) ∧
    star M_G * M_G = P_G * P_G ∧
    (U * star U = 1 → U_G * star U_G = 1) := by
  intro U_G P_G M_G
  have hG_star_inv : star (↑G⁻¹ : R) = (G : R) := by
    rw [hG, star_star]
  have hG_star : star (G : R) = (↑G⁻¹ : R) := hG.symm
  have h_fact : M_G = U_G * P_G := by
    dsimp [M_G, U_G, P_G]
    calc (G : R) * (U * P) * (↑G⁻¹ : R)
      _ = (G : R) * U * 1 * P * (↑G⁻¹ : R) := by
        noncomm_ring
      _ = (G : R) * U * ((↑G⁻¹ : R) * (G : R)) * P * (↑G⁻¹ : R) := by
        rw [Units.inv_mul]
      _ = ((G : R) * U * (↑G⁻¹ : R)) * ((G : R) * P * (↑G⁻¹ : R)) := by
        noncomm_ring
  have h_U_unit : star U_G * U_G = 1 := by
    dsimp [U_G]
    rw [star_mul, star_mul, hG_star_inv, hG_star]
    calc (G : R) * (star U * (↑G⁻¹ : R)) * ((G : R) * U * (↑G⁻¹ : R))
      _ = (G : R) * star U * ((↑G⁻¹ : R) * (G : R)) * U * (↑G⁻¹ : R) := by
        noncomm_ring
      _ = (G : R) * star U * 1 * U * (↑G⁻¹ : R) := by
        rw [Units.inv_mul]
      _ = (G : R) * (star U * U) * (↑G⁻¹ : R) := by
        noncomm_ring
      _ = (G : R) * 1 * (↑G⁻¹ : R) := by
        rw [hU]
      _ = 1 := by
        rw [mul_one, Units.mul_inv]
  have h_P_self : star P_G = P_G := by
    dsimp [P_G]
    rw [star_mul, star_mul, hG_star_inv, hG_star, hP]
    rw [mul_assoc]
  have h_MM : star (U * P) * (U * P) = P * P := by
    calc star (U * P) * (U * P)
      _ = star P * (star U * U) * P := by
        rw [star_mul]
        noncomm_ring
      _ = star P * 1 * P := by
        rw [hU]
      _ = P * P := by
        rw [hP, mul_one]
  have h_Gram : star M_G * M_G = (G : R) * (star (U * P) * (U * P)) * (↑G⁻¹ : R) := by
    dsimp [M_G]
    rw [star_mul, star_mul, hG_star_inv, hG_star]
    calc (G : R) * (star (U * P) * (↑G⁻¹ : R)) * ((G : R) * (U * P) * (↑G⁻¹ : R))
      _ = (G : R) * star (U * P) * ((↑G⁻¹ : R) * (G : R)) * (U * P) * (↑G⁻¹ : R) := by
        noncomm_ring
      _ = (G : R) * star (U * P) * 1 * (U * P) * (↑G⁻¹ : R) := by
        rw [Units.inv_mul]
      _ = (G : R) * (star (U * P) * (U * P)) * (↑G⁻¹ : R) := by
        noncomm_ring
  have h_PP : star M_G * M_G = P_G * P_G := by
    rw [h_Gram, h_MM]
    dsimp [P_G]
    calc (G : R) * (P * P) * (↑G⁻¹ : R)
      _ = (G : R) * P * 1 * P * (↑G⁻¹ : R) := by
        noncomm_ring
      _ = (G : R) * P * ((↑G⁻¹ : R) * (G : R)) * P * (↑G⁻¹ : R) := by
        rw [Units.inv_mul]
      _ = ((G : R) * P * (↑G⁻¹ : R)) * ((G : R) * P * (↑G⁻¹ : R)) := by
        noncomm_ring
  have h_two_sided : U * star U = 1 → U_G * star U_G = 1 := by
    intro hU_right
    dsimp [U_G]
    rw [star_mul, star_mul, hG_star_inv, hG_star]
    calc (G : R) * U * (↑G⁻¹ : R) * ((G : R) * (star U * (↑G⁻¹ : R)))
      _ = (G : R) * U * ((↑G⁻¹ : R) * (G : R)) * star U * (↑G⁻¹ : R) := by
        noncomm_ring
      _ = (G : R) * U * 1 * star U * (↑G⁻¹ : R) := by
        rw [Units.inv_mul]
      _ = (G : R) * (U * star U) * (↑G⁻¹ : R) := by
        noncomm_ring
      _ = (G : R) * 1 * (↑G⁻¹ : R) := by
        rw [hU_right]
      _ = 1 := by
        rw [mul_one, Units.mul_inv]
  exact ⟨h_fact, h_U_unit, h_P_self, h_Gram, h_PP, h_two_sided⟩

/-- Left unitary equivariance: M = U P => W M = (W U) P. -/
theorem polar_decomposition_left_unitary_equivariance
    (U P W : R) (hU : star U * U = 1) (hW : star W * W = 1) :
    let M := U * P
    W * M = (W * U) * P ∧
    star (W * U) * (W * U) = 1 ∧
    star (W * M) * (W * M) = star M * M := by
  intro M
  have h_fact : W * M = (W * U) * P := by
    dsimp [M]
    rw [mul_assoc]
  have h_U : star (W * U) * (W * U) = 1 := by
    calc star (W * U) * (W * U)
      _ = star U * (star W * W) * U := by
        rw [star_mul]
        noncomm_ring
      _ = star U * 1 * U := by
        rw [hW]
      _ = star U * U := by
        noncomm_ring
      _ = 1 := hU
  have h_Gram : star (W * M) * (W * M) = star M * M := by
    calc star (W * M) * (W * M)
      _ = star M * (star W * W) * M := by
        rw [star_mul]
        noncomm_ring
      _ = star M * 1 * M := by
        rw [hW]
      _ = star M * M := by
        noncomm_ring
  exact ⟨h_fact, h_U, h_Gram⟩

/-- Right unitary equivariance: M = U P => M W = (U W) (W* P W). -/
theorem polar_decomposition_right_unitary_equivariance
    (U P W : R) (hU : star U * U = 1) (hP : star P = P)
    (hW_left : star W * W = 1) (hW_right : W * star W = 1) :
    let M := U * P
    let U_W := U * W
    let P_W := star W * P * W
    M * W = U_W * P_W ∧
    star U_W * U_W = 1 ∧
    star P_W = P_W ∧
    star (M * W) * (M * W) = P_W * P_W ∧
    (U * star U = 1 → U_W * star U_W = 1) := by
  intro M U_W P_W
  have h_fact : M * W = U_W * P_W := by
    dsimp [M, U_W, P_W]
    calc U * P * W
      _ = U * 1 * P * W := by
        noncomm_ring
      _ = U * (W * star W) * P * W := by
        rw [hW_right]
      _ = (U * W) * (star W * P * W) := by
        noncomm_ring
  have h_U : star U_W * U_W = 1 := by
    dsimp [U_W]
    calc star (U * W) * (U * W)
      _ = star W * (star U * U) * W := by
        rw [star_mul]
        noncomm_ring
      _ = star W * 1 * W := by
        rw [hU]
      _ = star W * W := by
        noncomm_ring
      _ = 1 := hW_left
  have h_P : star P_W = P_W := by
    dsimp [P_W]
    rw [star_mul, star_mul, star_star, hP]
    rw [mul_assoc]
  have h_Gram : star (M * W) * (M * W) = P_W * P_W := by
    dsimp [M, P_W]
    calc star (U * P * W) * (U * P * W)
      _ = star W * star P * (star U * U) * P * W := by
        rw [star_mul, star_mul]
        noncomm_ring
      _ = star W * star P * 1 * P * W := by
        rw [hU]
      _ = star W * (P * 1 * P) * W := by
        rw [hP]
        noncomm_ring
      _ = star W * (P * (W * star W) * P) * W := by
        rw [hW_right]
      _ = (star W * P * W) * (star W * P * W) := by
        noncomm_ring
  have h_two_sided : U * star U = 1 → U_W * star U_W = 1 := by
    intro hU_right
    dsimp [U_W]
    calc U * W * star (U * W)
      _ = U * (W * star W) * star U := by
        rw [star_mul]
        noncomm_ring
      _ = U * 1 * star U := by
        rw [hW_right]
      _ = U * star U := by
        noncomm_ring
      _ = 1 := hU_right
  exact ⟨h_fact, h_U, h_P, h_Gram, h_two_sided⟩

end KP3_PolarEquivariance

section KP4_IwasawaSymmetryEquivariance

variable {B : Type*} [Ring B]

/-- Iwasawa Borelian scaling equivariance. -/
theorem iwasawa_borel_scaling_equivariance
    (g_plus g_minus : Bˣ) (a_plus a_minus n : B) :
    let G := iwasawaA (g_plus : B) (g_minus : B)
    let G_inv := iwasawaA (↑g_plus⁻¹ : B) (↑g_minus⁻¹ : B)
    G * G_inv = 1 ∧ G_inv * G = 1 ∧
    G * iwasawaA a_plus a_minus * G_inv =
      iwasawaA ((g_plus : B) * a_plus * (↑g_plus⁻¹ : B)) ((g_minus : B) * a_minus * (↑g_minus⁻¹ : B)) ∧
    G * iwasawaN n * G_inv =
      iwasawaN ((g_plus : B) * n * (↑g_minus⁻¹ : B)) := by
  intro G G_inv
  have h1 : G * G_inv = 1 := by
    rw [iwasawaA_mul, Units.mul_inv, Units.mul_inv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [iwasawaA, IwasawaKANTriad.A_grp, Matrix.one_apply]
  have h2 : G_inv * G = 1 := by
    rw [iwasawaA_mul, Units.inv_mul, Units.inv_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [iwasawaA, IwasawaKANTriad.A_grp, Matrix.one_apply]
  have h3 : G * iwasawaA a_plus a_minus * G_inv =
      iwasawaA ((g_plus : B) * a_plus * (↑g_plus⁻¹ : B)) ((g_minus : B) * a_minus * (↑g_minus⁻¹ : B)) := by
    rw [iwasawaA_mul, iwasawaA_mul]
  have h4 : G * iwasawaN n * G_inv = iwasawaN ((g_plus : B) * n * (↑g_minus⁻¹ : B)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> {
      simp [G, G_inv, iwasawaA, iwasawaN, IwasawaKANTriad.A_grp, IwasawaKANTriad.N_grp,
        Matrix.mul_apply, Fin.sum_univ_two]
      try noncomm_ring
    }
  exact ⟨h1, h2, h3, h4⟩

/-- Iwasawa non-Abelian fiber gauge equivariance. -/
theorem iwasawa_fiber_gauge_equivariance
    (g : Bˣ) (c s a_plus a_minus n : B) :
    let G := fiberEmbed (g : B)
    let G_inv := fiberEmbed (↑g⁻¹ : B)
    G * G_inv = 1 ∧ G_inv * G = 1 ∧
    G * iwasawaK c s * G_inv =
      iwasawaK ((g : B) * c * (↑g⁻¹ : B)) ((g : B) * s * (↑g⁻¹ : B)) ∧
    G * iwasawaA a_plus a_minus * G_inv =
      iwasawaA ((g : B) * a_plus * (↑g⁻¹ : B)) ((g : B) * a_minus * (↑g⁻¹ : B)) ∧
    G * iwasawaN n * G_inv =
      iwasawaN ((g : B) * n * (↑g⁻¹ : B)) ∧
    G * (iwasawaK c s * iwasawaA a_plus a_minus * iwasawaN n) * G_inv =
      iwasawaK ((g : B) * c * (↑g⁻¹ : B)) ((g : B) * s * (↑g⁻¹ : B)) *
        iwasawaA ((g : B) * a_plus * (↑g⁻¹ : B)) ((g : B) * a_minus * (↑g⁻¹ : B)) *
        iwasawaN ((g : B) * n * (↑g⁻¹ : B)) := by
  intro G G_inv
  have h1 : G * G_inv = 1 := by
    dsimp [G, G_inv, fiberEmbed]
    rw [IwasawaKANTriad.A_grp_mul, Units.mul_inv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [IwasawaKANTriad.A_grp, Matrix.one_apply]
  have h2 : G_inv * G = 1 := by
    dsimp [G, G_inv, fiberEmbed]
    rw [IwasawaKANTriad.A_grp_mul, Units.inv_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [IwasawaKANTriad.A_grp, Matrix.one_apply]
  have hK : G * iwasawaK c s * G_inv =
      iwasawaK ((g : B) * c * (↑g⁻¹ : B)) ((g : B) * s * (↑g⁻¹ : B)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> {
      simp [G, G_inv, fiberEmbed, iwasawaK, IwasawaKANTriad.A_grp, IwasawaKANTriad.K_grp,
        Matrix.mul_apply, Fin.sum_univ_two]
      try noncomm_ring
    }
  have hA : G * iwasawaA a_plus a_minus * G_inv =
      iwasawaA ((g : B) * a_plus * (↑g⁻¹ : B)) ((g : B) * a_minus * (↑g⁻¹ : B)) := by
    dsimp [G, G_inv, fiberEmbed, iwasawaA]
    rw [IwasawaKANTriad.A_grp_mul, IwasawaKANTriad.A_grp_mul]
  have hN : G * iwasawaN n * G_inv = iwasawaN ((g : B) * n * (↑g⁻¹ : B)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> {
      simp [G, G_inv, fiberEmbed, iwasawaN, IwasawaKANTriad.A_grp, IwasawaKANTriad.N_grp,
        Matrix.mul_apply, Fin.sum_univ_two, Units.mul_inv]
      try noncomm_ring
    }
  have hKAN : G * (iwasawaK c s * iwasawaA a_plus a_minus * iwasawaN n) * G_inv =
      iwasawaK ((g : B) * c * (↑g⁻¹ : B)) ((g : B) * s * (↑g⁻¹ : B)) *
        iwasawaA ((g : B) * a_plus * (↑g⁻¹ : B)) ((g : B) * a_minus * (↑g⁻¹ : B)) *
        iwasawaN ((g : B) * n * (↑g⁻¹ : B)) := by
    calc G * (iwasawaK c s * iwasawaA a_plus a_minus * iwasawaN n) * G_inv
      _ = G * iwasawaK c s * 1 * iwasawaA a_plus a_minus * 1 * iwasawaN n * G_inv := by
        noncomm_ring
      _ = G * iwasawaK c s * (G_inv * G) * iwasawaA a_plus a_minus * (G_inv * G) * iwasawaN n * G_inv := by
        rw [h2]
      _ = (G * iwasawaK c s * G_inv) * (G * iwasawaA a_plus a_minus * G_inv) * (G * iwasawaN n * G_inv) := by
        noncomm_ring
      _ = iwasawaK ((g : B) * c * (↑g⁻¹ : B)) ((g : B) * s * (↑g⁻¹ : B)) *
            iwasawaA ((g : B) * a_plus * (↑g⁻¹ : B)) ((g : B) * a_minus * (↑g⁻¹ : B)) *
            iwasawaN ((g : B) * n * (↑g⁻¹ : B)) := by
        rw [hK, hA, hN]
  exact ⟨h1, h2, hK, hA, hN, hKAN⟩

/-- Iwasawa chirality parity equivariance. -/
theorem iwasawa_chirality_parity_equivariance (c s a_plus a_minus n : B) :
    gamma1Op (B := B) * gamma1Op (B := B) = 1 ∧
    gamma1Op (B := B) * iwasawaK c s * gamma1Op (B := B) = iwasawaK c (-s) ∧
    gamma1Op (B := B) * iwasawaA a_plus a_minus * gamma1Op (B := B) = iwasawaA a_plus a_minus ∧
    gamma1Op (B := B) * iwasawaN n * gamma1Op (B := B) = iwasawaN (-n) ∧
    gamma1Op (B := B) * (iwasawaK c s * iwasawaA a_plus a_minus * iwasawaN n) * gamma1Op (B := B) =
      iwasawaK c (-s) * iwasawaA a_plus a_minus * iwasawaN (-n) := by
  have h1 : gamma1Op (B := B) * gamma1Op (B := B) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> {
      simp [gamma1Op, IwasawaKANTriad.eps_eq, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply]
      try abel
    }
  have hK : gamma1Op (B := B) * iwasawaK c s * gamma1Op (B := B) = iwasawaK c (-s) := by
    ext i j
    fin_cases i <;> fin_cases j <;> {
      simp [gamma1Op, iwasawaK, IwasawaKANTriad.eps_eq, IwasawaKANTriad.K_grp,
        Matrix.mul_apply, Fin.sum_univ_two]
      try abel
    }
  have hA : gamma1Op (B := B) * iwasawaA a_plus a_minus * gamma1Op (B := B) = iwasawaA a_plus a_minus := by
    ext i j
    fin_cases i <;> fin_cases j <;> {
      simp [gamma1Op, iwasawaA, IwasawaKANTriad.eps_eq, IwasawaKANTriad.A_grp,
        Matrix.mul_apply, Fin.sum_univ_two]
      try abel
    }
  have hN : gamma1Op (B := B) * iwasawaN n * gamma1Op (B := B) = iwasawaN (-n) := by
    ext i j
    fin_cases i <;> fin_cases j <;> {
      simp [gamma1Op, iwasawaN, IwasawaKANTriad.eps_eq, IwasawaKANTriad.N_grp,
        Matrix.mul_apply, Fin.sum_univ_two]
      try abel
    }
  have hKAN : gamma1Op (B := B) * (iwasawaK c s * iwasawaA a_plus a_minus * iwasawaN n) * gamma1Op (B := B) =
      iwasawaK c (-s) * iwasawaA a_plus a_minus * iwasawaN (-n) := by
    calc gamma1Op (B := B) * (iwasawaK c s * iwasawaA a_plus a_minus * iwasawaN n) * gamma1Op (B := B)
      _ = gamma1Op * iwasawaK c s * 1 * iwasawaA a_plus a_minus * 1 * iwasawaN n * gamma1Op := by
        noncomm_ring
      _ = gamma1Op * iwasawaK c s * (gamma1Op * gamma1Op) * iwasawaA a_plus a_minus * (gamma1Op * gamma1Op) * iwasawaN n * gamma1Op := by
        rw [h1]
      _ = (gamma1Op * iwasawaK c s * gamma1Op) * (gamma1Op * iwasawaA a_plus a_minus * gamma1Op) * (gamma1Op * iwasawaN n * gamma1Op) := by
        noncomm_ring
      _ = iwasawaK c (-s) * iwasawaA a_plus a_minus * iwasawaN (-n) := by
        rw [hK, hA, hN]
  exact ⟨h1, hK, hA, hN, hKAN⟩

/-- Iwasawa Weyl reflection equivariance. -/
theorem iwasawa_weyl_reflection_equivariance (c s a_plus a_minus n : B) :
    sigmaOp (B := B) * sigmaOp (B := B) = 1 ∧
    sigmaOp (B := B) * iwasawaK c s * sigmaOp (B := B) = iwasawaK c (-s) ∧
    sigmaOp (B := B) * iwasawaA a_plus a_minus * sigmaOp (B := B) = iwasawaA a_minus a_plus ∧
    sigmaOp (B := B) * iwasawaN n * sigmaOp (B := B) = iwasawaNMinus n ∧
    sigmaOp (B := B) * (iwasawaK c s * iwasawaA a_plus a_minus * iwasawaN n) * sigmaOp (B := B) =
      iwasawaK c (-s) * iwasawaA a_minus a_plus * iwasawaNMinus n := by
  have h1 : sigmaOp (B := B) * sigmaOp (B := B) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> {
      simp [sigmaOp, IwasawaKANTriad.e1, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply]
      try abel
    }
  have hK : sigmaOp (B := B) * iwasawaK c s * sigmaOp (B := B) = iwasawaK c (-s) := by
    ext i j
    fin_cases i <;> fin_cases j <;> {
      simp [sigmaOp, iwasawaK, IwasawaKANTriad.e1, IwasawaKANTriad.K_grp,
        Matrix.mul_apply, Fin.sum_univ_two]
      try abel
    }
  have hA : sigmaOp (B := B) * iwasawaA a_plus a_minus * sigmaOp (B := B) = iwasawaA a_minus a_plus := by
    ext i j
    fin_cases i <;> fin_cases j <;> {
      simp [sigmaOp, iwasawaA, IwasawaKANTriad.e1, IwasawaKANTriad.A_grp,
        Matrix.mul_apply, Fin.sum_univ_two]
      try abel
    }
  have hN : sigmaOp (B := B) * iwasawaN n * sigmaOp (B := B) = iwasawaNMinus n := by
    ext i j
    fin_cases i <;> fin_cases j <;> {
      simp [sigmaOp, iwasawaN, iwasawaNMinus, IwasawaKANTriad.e1, IwasawaKANTriad.N_grp,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
      try abel
    }
  have hKAN : sigmaOp (B := B) * (iwasawaK c s * iwasawaA a_plus a_minus * iwasawaN n) * sigmaOp (B := B) =
      iwasawaK c (-s) * iwasawaA a_minus a_plus * iwasawaNMinus n := by
    calc sigmaOp (B := B) * (iwasawaK c s * iwasawaA a_plus a_minus * iwasawaN n) * sigmaOp (B := B)
      _ = sigmaOp * iwasawaK c s * 1 * iwasawaA a_plus a_minus * 1 * iwasawaN n * sigmaOp := by
        noncomm_ring
      _ = sigmaOp * iwasawaK c s * (sigmaOp * sigmaOp) * iwasawaA a_plus a_minus * (sigmaOp * sigmaOp) * iwasawaN n * sigmaOp := by
        rw [h1]
      _ = (sigmaOp * iwasawaK c s * sigmaOp) * (sigmaOp * iwasawaA a_plus a_minus * sigmaOp) * (sigmaOp * iwasawaN n * sigmaOp) := by
        noncomm_ring
      _ = iwasawaK c (-s) * iwasawaA a_minus a_plus * iwasawaNMinus n := by
        rw [hK, hA, hN]
  exact ⟨h1, hK, hA, hN, hKAN⟩

end KP4_IwasawaSymmetryEquivariance

section NonCommutativityWitnesses

/-- OpenGauss Trap T16: Cartan split generators do not commute. -/
theorem cartan_split_noncommuting :
    IwasawaKANTriad.eps ℤ * IwasawaKANTriad.e1 ℤ ≠
      IwasawaKANTriad.e1 ℤ * IwasawaKANTriad.eps ℤ := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  revert h01
  rw [IwasawaKANTriad.eps_eq]
  simp [IwasawaKANTriad.e1, Matrix.mul_apply, Fin.sum_univ_two]

/-- OpenGauss Trap T16: Opposite unipotent Borel subgroups do not commute. -/
theorem iwasawa_borel_noncommuting :
    IwasawaKANTriad.N_grp ℤ 1 * iwasawaNMinus (1 : ℤ) ≠
      iwasawaNMinus (1 : ℤ) * IwasawaKANTriad.N_grp ℤ 1 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  revert h00
  simp [IwasawaKANTriad.N_grp, iwasawaNMinus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

/-- OpenGauss Trap T16: Real carrier non-commutativity witness. -/
theorem cartan_split_noncommuting_real :
    IwasawaKANTriad.eps ℝ * IwasawaKANTriad.e1 ℝ ≠
      IwasawaKANTriad.e1 ℝ * IwasawaKANTriad.eps ℝ := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  revert h01
  rw [IwasawaKANTriad.eps_eq]
  simp [IwasawaKANTriad.e1, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

/-- OpenGauss Trap T16: Non-commutativity witness for 2x2 matrices over ring `B`. -/
theorem matrix_carrier_B_noncommutative {B : Type*} [Ring B] [Nontrivial B] :
    ∃ M N : Matrix (Fin 2) (Fin 2) B, M * N ≠ N * M := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have h00 := congrFun (congrFun h 0) 0
  revert h00
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- OpenGauss Trap T16: Non-commutativity witness for 2x2 matrices over ring `R`. -/
theorem matrix_carrier_R_noncommutative {R : Type*} [Ring R] [Nontrivial R] :
    ∃ M N : Matrix (Fin 2) (Fin 2) R, M * N ≠ N * M := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have h00 := congrFun (congrFun h 0) 0
  revert h00
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- OpenGauss Trap T16: Non-commutativity witness for 2x2 real matrices. -/
theorem matrix_carrier_Real_noncommutative :
    ∃ M N : Matrix (Fin 2) (Fin 2) ℝ, M * N ≠ N * M := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have h00 := congrFun (congrFun h 0) 0
  revert h00
  simp [Matrix.mul_apply, Fin.sum_univ_two]

end NonCommutativityWitnesses

section KP5_SL2IwasawaAndGL2Polar

open InfoGeometry.Algebra.IwasawaRealKAN

private theorem iwasawaKAN2_ext (I₁ I₂ : IwasawaRealKAN.IwasawaKAN2)
    (hk : I₁.k = I₂.k) (ha : I₁.a = I₂.a) (hu : I₁.u = I₂.u) : I₁ = I₂ := by
  cases I₁
  cases I₂
  dsimp at hk ha hu
  subst hk ha hu
  rfl

/-- SL(2, ℝ) Iwasawa K A N decomposition existence and uniqueness. -/
theorem sl2_iwasawa_kan_exists_unique (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det = 1) :
    ∃! I : IwasawaRealKAN.IwasawaKAN2, I.product = M := by
  have hr2_pos : 0 < M 0 0 ^ 2 + M 1 0 ^ 2 := by
    by_contra hc
    have h_le : M 0 0 ^ 2 + M 1 0 ^ 2 ≤ 0 := not_lt.mp hc
    have h00_zero : M 0 0 = 0 := by
      nlinarith [sq_nonneg (M 0 0), sq_nonneg (M 1 0)]
    have h10_zero : M 1 0 = 0 := by
      nlinarith [sq_nonneg (M 0 0), sq_nonneg (M 1 0)]
    have hdet_zero : M.det = 0 := by
      rw [Matrix.det_fin_two, h00_zero, h10_zero]
      ring
    rw [hdet_zero] at hM
    exact zero_ne_one hM
  let r := Real.sqrt (M 0 0 ^ 2 + M 1 0 ^ 2)
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hr2_pos
  have hr_ne_zero : r ≠ 0 := ne_of_gt hr_pos
  have hr2_nonneg : 0 ≤ M 0 0 ^ 2 + M 1 0 ^ 2 := le_of_lt hr2_pos
  have hr_sq : r ^ 2 = M 0 0 ^ 2 + M 1 0 ^ 2 := Real.sq_sqrt hr2_nonneg
  have hr_sq_pos : 0 < r ^ 2 := sq_pos_of_pos hr_pos
  have hr_sq_ne_zero : r ^ 2 ≠ 0 := ne_of_gt hr_sq_pos
  let k : Matrix (Fin 2) (Fin 2) ℝ := !![M 0 0 / r, -(M 1 0 / r); M 1 0 / r, M 0 0 / r]
  let a : Matrix (Fin 2) (Fin 2) ℝ := !![r, 0; 0, r⁻¹]
  let u : Matrix (Fin 2) (Fin 2) ℝ := !![1, (M 0 0 * M 0 1 + M 1 0 * M 1 1) / r ^ 2; 0, 1]
  have hk_orth : kᵀ * k = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply]
      dsimp [k]
      have h_num : (M 0 0 / r) * (M 0 0 / r) + (M 1 0 / r) * (M 1 0 / r) = (M 0 0 ^ 2 + M 1 0 ^ 2) / r ^ 2 := by
        have : (M 0 0 / r) * (M 0 0 / r) + (M 1 0 / r) * (M 1 0 / r) = (M 0 0 ^ 2 + M 1 0 ^ 2) * (r⁻¹ * r⁻¹) := by ring
        rw [this]
        have h_inv : r⁻¹ * r⁻¹ = (r ^ 2)⁻¹ := by rw [← mul_inv, ← sq]
        rw [h_inv, div_eq_mul_inv]
      rw [h_num, ← hr_sq]
      exact div_self hr_sq_ne_zero
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply]
      dsimp [k]
      ring
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply]
      dsimp [k]
      ring
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply]
      dsimp [k]
      have h_num : (-(M 1 0 / r)) * (-(M 1 0 / r)) + (M 0 0 / r) * (M 0 0 / r) = (M 0 0 ^ 2 + M 1 0 ^ 2) / r ^ 2 := by
        have : (-(M 1 0 / r)) * (-(M 1 0 / r)) + (M 0 0 / r) * (M 0 0 / r) = (M 0 0 ^ 2 + M 1 0 ^ 2) * (r⁻¹ * r⁻¹) := by ring
        rw [this]
        have h_inv : r⁻¹ * r⁻¹ = (r ^ 2)⁻¹ := by rw [← mul_inv, ← sq]
        rw [h_inv, div_eq_mul_inv]
      rw [h_num, ← hr_sq]
      exact div_self hr_sq_ne_zero
  have hk_det : k.det = 1 := by
    rw [Matrix.det_fin_two]
    have h_num : k 0 0 * k 1 1 - k 0 1 * k 1 0 = (M 0 0 ^ 2 + M 1 0 ^ 2) / r ^ 2 := by
      dsimp [k]
      have : (M 0 0 / r) * (M 0 0 / r) - (-(M 1 0 / r)) * (M 1 0 / r) = (M 0 0 ^ 2 + M 1 0 ^ 2) * (r⁻¹ * r⁻¹) := by ring
      rw [this]
      have h_inv : r⁻¹ * r⁻¹ = (r ^ 2)⁻¹ := by rw [← mul_inv, ← sq]
      rw [h_inv, div_eq_mul_inv]
    rw [h_num, ← hr_sq]
    exact div_self hr_sq_ne_zero
  have ha_pos : 0 < a 0 0 ∧ 0 < a 1 1 := by
    dsimp [a]
    exact ⟨hr_pos, inv_pos.mpr hr_pos⟩
  have ha_diag : a 0 1 = 0 ∧ a 1 0 = 0 := by
    dsimp [a]
    exact ⟨rfl, rfl⟩
  have ha_det : a.det = 1 := by
    rw [Matrix.det_fin_two]
    dsimp [a]
    simp only [mul_zero, sub_zero]
    exact mul_inv_cancel₀ hr_ne_zero
  have hu_unit : u 0 0 = 1 ∧ u 1 1 = 1 ∧ u 1 0 = 0 := by
    dsimp [u]
    exact ⟨rfl, rfl, rfl⟩
  let I_can : IwasawaRealKAN.IwasawaKAN2 := {
    k := k
    a := a
    u := u
    k_orth := hk_orth
    k_det := hk_det
    a_pos := ha_pos
    a_is_diag := ha_diag
    a_det := ha_det
    u_unit := hu_unit
  }
  have h_prod : I_can.product = M := by
    dsimp [IwasawaRealKAN.IwasawaKAN2.product, I_can]
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      dsimp [k, a, u]
      have : (M 0 0 / r * r + -(M 1 0 / r) * 0) * 1 + (M 0 0 / r * 0 + -(M 1 0 / r) * r⁻¹) * 0 = (M 0 0 / r) * r := by
        ring
      rw [this]
      exact div_mul_cancel₀ (M 0 0) hr_ne_zero
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      dsimp [k, a, u]
      have hr_mul_inv : (-(M 1 0 / r)) * r⁻¹ = - (M 1 0 / r ^ 2) := by
        have : (-(M 1 0 / r)) * r⁻¹ = -(M 1 0 * (r⁻¹ * r⁻¹)) := by ring
        rw [this]
        have h_inv : r⁻¹ * r⁻¹ = (r ^ 2)⁻¹ := by rw [← mul_inv, ← sq]
        rw [h_inv, div_eq_mul_inv]
      have h_div_cancel : (M 0 0 / r) * r = M 0 0 := div_mul_cancel₀ (M 0 0) hr_ne_zero
      have h_alg : (M 0 0 / r * r + -(M 1 0 / r) * 0) * ((M 0 0 * M 0 1 + M 1 0 * M 1 1) / r ^ 2) +
          (M 0 0 / r * 0 + -(M 1 0 / r) * r⁻¹) * 1 =
          (M 0 0 * (M 0 0 * M 0 1 + M 1 0 * M 1 1) - M 1 0) / r ^ 2 := by
        rw [h_div_cancel, hr_mul_inv]
        ring
      rw [h_alg]
      have hdet_sub : M 0 0 * (M 0 0 * M 0 1 + M 1 0 * M 1 1) - M 1 0 = r ^ 2 * M 0 1 := by
        have hdet_val : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := Matrix.det_fin_two M
        rw [hM] at hdet_val
        rw [hr_sq]
        linear_combination -M 1 0 * hdet_val
      rw [hdet_sub]
      exact mul_div_cancel_left₀ (M 0 1) hr_sq_ne_zero
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      dsimp [k, a, u]
      have : (M 1 0 / r * r + M 0 0 / r * 0) * 1 + (M 1 0 / r * 0 + M 0 0 / r * r⁻¹) * 0 = (M 1 0 / r) * r := by
        ring
      rw [this]
      exact div_mul_cancel₀ (M 1 0) hr_ne_zero
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      dsimp [k, a, u]
      have hr_mul_inv : (M 0 0 / r) * r⁻¹ = M 0 0 / r ^ 2 := by
        have : (M 0 0 / r) * r⁻¹ = M 0 0 * (r⁻¹ * r⁻¹) := by ring
        rw [this]
        have h_inv : r⁻¹ * r⁻¹ = (r ^ 2)⁻¹ := by rw [← mul_inv, ← sq]
        rw [h_inv, div_eq_mul_inv]
      have h_div_cancel : (M 1 0 / r) * r = M 1 0 := div_mul_cancel₀ (M 1 0) hr_ne_zero
      have h_alg : (M 1 0 / r * r + M 0 0 / r * 0) * ((M 0 0 * M 0 1 + M 1 0 * M 1 1) / r ^ 2) +
          (M 1 0 / r * 0 + M 0 0 / r * r⁻¹) * 1 =
          (M 1 0 * (M 0 0 * M 0 1 + M 1 0 * M 1 1) + M 0 0) / r ^ 2 := by
        rw [h_div_cancel, hr_mul_inv]
        ring
      rw [h_alg]
      have hdet_sub : M 1 0 * (M 0 0 * M 0 1 + M 1 0 * M 1 1) + M 0 0 = r ^ 2 * M 1 1 := by
        have hdet_val : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := Matrix.det_fin_two M
        rw [hM] at hdet_val
        rw [hr_sq]
        linear_combination M 0 0 * hdet_val
      rw [hdet_sub]
      exact mul_div_cancel_left₀ (M 1 1) hr_sq_ne_zero
  refine ⟨I_can, h_prod, ?_⟩
  intro J hJ
  have hJ_k_orth := J.k_orth
  have hJ_k_det := J.k_det
  have hJ_a_pos := J.a_pos
  have hJ_a_diag := J.a_is_diag
  have hJ_a_det := J.a_det
  have hJ_u_unit := J.u_unit
  have hJ_prod_eq : J.k * J.a * J.u = M := hJ
  have hGram : Mᵀ * M = J.uᵀ * (J.aᵀ * J.a) * J.u := by
    have h1 : M = J.k * (J.a * J.u) := by
      rw [← hJ_prod_eq, Matrix.mul_assoc]
    have h2 : Mᵀ = (J.a * J.u)ᵀ * J.kᵀ := by
      rw [h1, Matrix.transpose_mul]
    have h3 : Mᵀ * M = (J.a * J.u)ᵀ * (J.kᵀ * J.k) * (J.a * J.u) := by
      rw [h2, h1]
      repeat rw [Matrix.mul_assoc]
    rw [hJ_k_orth, Matrix.mul_one, Matrix.transpose_mul] at h3
    rw [h3]
    repeat rw [Matrix.mul_assoc]
  have ha_transpose : J.aᵀ = J.a := by
    ext i j
    have h01 := hJ_a_diag.1
    have h10 := hJ_a_diag.2
    fin_cases i <;> fin_cases j <;> {
      simp [Matrix.transpose_apply, h01, h10]
    }
  have ha_sq : J.aᵀ * J.a = !![J.a 0 0 ^ 2, 0; 0, J.a 1 1 ^ 2] := by
    rw [ha_transpose]
    ext i j
    have h01 := hJ_a_diag.1
    have h10 := hJ_a_diag.2
    fin_cases i <;> fin_cases j <;> {
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta, Fin.reduceEq]
      dsimp
      try rw [h01]
      try rw [h10]
      ring
    }
  have hGram_00 : (Mᵀ * M) 0 0 = J.a 0 0 ^ 2 := by
    rw [hGram, ha_sq]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      hJ_u_unit.1, hJ_u_unit.2.2]
    dsimp
    ring
  have hM_Gram_00 : (Mᵀ * M) 0 0 = r ^ 2 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
    rw [hr_sq]
    ring
  have ha00_sq : J.a 0 0 ^ 2 = r ^ 2 := by
    rw [← hGram_00, hM_Gram_00]
  have ha00_eq_r : J.a 0 0 = r := by
    have h_diff : (J.a 0 0 - r) * (J.a 0 0 + r) = 0 := by
      calc (J.a 0 0 - r) * (J.a 0 0 + r)
        _ = J.a 0 0 ^ 2 - r ^ 2 := by ring
        _ = 0 := by linarith [ha00_sq]
    have h_sum_pos : 0 < J.a 0 0 + r := add_pos hJ_a_pos.1 hr_pos
    cases mul_eq_zero.mp h_diff with
    | inl h_sub => linarith
    | inr h_sum => linarith
  have ha11_eq_inv : J.a 1 1 = r⁻¹ := by
    have h_det_calc : J.a.det = J.a 0 0 * J.a 1 1 := by
      rw [Matrix.det_fin_two, hJ_a_diag.1]
      ring
    rw [hJ_a_det, ha00_eq_r] at h_det_calc
    have : r⁻¹ * 1 = r⁻¹ * (r * J.a 1 1) := by
      rw [h_det_calc]
    rw [mul_one, ← mul_assoc, inv_mul_cancel₀ hr_ne_zero, one_mul] at this
    exact this.symm
  have ha_eq_a : J.a = a := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [a]; exact ha00_eq_r
    · simp only [a]; exact hJ_a_diag.1
    · simp only [a]; exact hJ_a_diag.2
    · simp only [a]; exact ha11_eq_inv
  have hGram_01 : (Mᵀ * M) 0 1 = r ^ 2 * J.u 0 1 := by
    rw [hGram, ha_sq, ha00_eq_r]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      hJ_u_unit.1, hJ_u_unit.2.1, hJ_u_unit.2.2]
    dsimp
    ring
  have hM_Gram_01 : (Mᵀ * M) 0 1 = M 0 0 * M 0 1 + M 1 0 * M 1 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  have hu01_eq : J.u 0 1 = (M 0 0 * M 0 1 + M 1 0 * M 1 1) / r ^ 2 := by
    have : r ^ 2 * J.u 0 1 = M 0 0 * M 0 1 + M 1 0 * M 1 1 := by
      rw [← hGram_01, hM_Gram_01]
    rw [← this, mul_div_cancel_left₀ (J.u 0 1) hr_sq_ne_zero]
  have hu_eq_u : J.u = u := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [u]; exact hJ_u_unit.1
    · simp only [u]; exact hu01_eq
    · simp only [u]; exact hJ_u_unit.2.2
    · simp only [u]; exact hJ_u_unit.2.1
  have hT : J.k * (a * u) = M := by
    rw [← ha_eq_a, ← hu_eq_u, ← Matrix.mul_assoc, hJ_prod_eq]
  have hk00 : J.k 0 0 = M 0 0 / r := by
    have h_entry : (J.k * (a * u)) 0 0 = M 0 0 := by
      rw [hT]
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h_entry
    dsimp [a, u] at h_entry
    have h_ring : J.k 0 0 * (r * 1 + 0 * 0) + J.k 0 1 * (0 * 1 + r⁻¹ * 0) = J.k 0 0 * r := by
      ring
    rw [h_ring] at h_entry
    have h_cancel : J.k 0 0 = (J.k 0 0 * r) / r := (mul_div_cancel_right₀ (J.k 0 0) hr_ne_zero).symm
    rw [h_cancel, h_entry]
  have hk10 : J.k 1 0 = M 1 0 / r := by
    have h_entry : (J.k * (a * u)) 1 0 = M 1 0 := by
      rw [hT]
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h_entry
    dsimp [a, u] at h_entry
    have h_ring : J.k 1 0 * (r * 1 + 0 * 0) + J.k 1 1 * (0 * 1 + r⁻¹ * 0) = J.k 1 0 * r := by
      ring
    rw [h_ring] at h_entry
    have h_cancel : J.k 1 0 = (J.k 1 0 * r) / r := (mul_div_cancel_right₀ (J.k 1 0) hr_ne_zero).symm
    rw [h_cancel, h_entry]
  have hk_orth_01 : J.k 0 0 * J.k 0 1 + J.k 1 0 * J.k 1 1 = 0 := by
    have h_orth : (J.kᵀ * J.k) 0 1 = 0 := by
      rw [hJ_k_orth]
      rfl
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] at h_orth
    exact h_orth
  have hk_det_eq : J.k 0 0 * J.k 1 1 - J.k 0 1 * J.k 1 0 = 1 := by
    have h_det : J.k.det = 1 := hJ_k_det
    rw [Matrix.det_fin_two] at h_det
    exact h_det
  have hk_orth_00 : J.k 0 0 ^ 2 + J.k 1 0 ^ 2 = 1 := by
    have h_orth : (J.kᵀ * J.k) 0 0 = 1 := by
      rw [hJ_k_orth]
      rfl
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] at h_orth
    calc J.k 0 0 ^ 2 + J.k 1 0 ^ 2
      _ = J.k 0 0 * J.k 0 0 + J.k 1 0 * J.k 1 0 := by ring
      _ = 1 := h_orth
  have hk11 : J.k 1 1 = M 0 0 / r := by
    have h_comb : (J.k 0 0 ^ 2 + J.k 1 0 ^ 2) * J.k 1 1 = J.k 0 0 := by
      linear_combination J.k 0 0 * hk_det_eq + J.k 1 0 * hk_orth_01
    rw [hk_orth_00, one_mul] at h_comb
    rw [h_comb, hk00]
  have hk01 : J.k 0 1 = -(M 1 0 / r) := by
    have h_comb : (J.k 0 0 ^ 2 + J.k 1 0 ^ 2) * J.k 0 1 = -J.k 1 0 := by
      linear_combination -(J.k 1 0 * hk_det_eq) + J.k 0 0 * hk_orth_01
    rw [hk_orth_00, one_mul] at h_comb
    rw [h_comb, hk10]
  have hk_eq_k : J.k = k := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [k]; exact hk00
    · simp only [k]; exact hk01
    · simp only [k]; exact hk10
    · simp only [k]; exact hk11
  exact iwasawaKAN2_ext J I_can hk_eq_k ha_eq_a hu_eq_u

/-- GL(2, ℝ) closed-form polar decomposition. -/
theorem gl2_polar_decomposition_closed_form (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0) :
    ∃ (U P : Matrix (Fin 2) (Fin 2) ℝ),
      M = U * P ∧
      Matrix.transpose U * U = 1 ∧
      U * Matrix.transpose U = 1 ∧
      Matrix.transpose P = P ∧
      P * P = Matrix.transpose M * M ∧
      P.det = |M.det| ∧
      ∀ v : Fin 2 → ℝ, v ≠ 0 → 0 < dotProduct v (P.mulVec v) := by
  let S := Mᵀ * M
  have hS_symm : Sᵀ = S := by
    dsimp [S]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  let δ := |M.det|
  have hδ_pos : 0 < δ := abs_pos.mpr hM
  have h_detS : S.det = δ ^ 2 := by
    dsimp [S]
    rw [Matrix.det_mul, Matrix.det_transpose]
    dsimp [δ]
    rw [sq, abs_mul_abs_self]
  have h_trS_nonneg : 0 ≤ Matrix.trace S := by
    rw [Matrix.trace_fin_two]
    simp only [S, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
    repeat rw [← sq]
    positivity
  have h_sum_pos : 0 < Matrix.trace S + 2 * δ := by
    positivity
  let τ := Real.sqrt (Matrix.trace S + 2 * δ)
  have hτ_pos : 0 < τ := Real.sqrt_pos.mpr h_sum_pos
  have hτ_ne_zero : τ ≠ 0 := ne_of_gt hτ_pos
  have h_sum_nonneg : 0 ≤ Matrix.trace S + 2 * δ := le_of_lt h_sum_pos
  have hτ_sq : τ ^ 2 = Matrix.trace S + 2 * δ := Real.sq_sqrt h_sum_nonneg
  have hτ_sq_pos : 0 < τ ^ 2 := sq_pos_of_pos hτ_pos
  have hτ_sq_ne_zero : τ ^ 2 ≠ 0 := ne_of_gt hτ_sq_pos
  let P : Matrix (Fin 2) (Fin 2) ℝ :=
    !![τ⁻¹ * (S 0 0 + δ), τ⁻¹ * S 0 1;
       τ⁻¹ * S 1 0, τ⁻¹ * (S 1 1 + δ)]
  have hP_symm : Pᵀ = P := by
    ext i j
    have hS_10 : S 1 0 = S 0 1 := congrFun (congrFun hS_symm 0) 1
    fin_cases i <;> fin_cases j <;> {
      simp [P, Matrix.transpose_apply, hS_10]
    }
  have hPP : P * P = S := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      dsimp [P]
      have hS_10 : S 1 0 = S 0 1 := congrFun (congrFun hS_symm 0) 1
      rw [hS_10]
      have h_alg : (τ⁻¹ * (S 0 0 + δ)) * (τ⁻¹ * (S 0 0 + δ)) + (τ⁻¹ * S 0 1) * (τ⁻¹ * S 0 1) =
          ((S 0 0 + δ) ^ 2 + S 0 1 ^ 2) / τ ^ 2 := by
        have : τ⁻¹ * (S 0 0 + δ) * (τ⁻¹ * (S 0 0 + δ)) + τ⁻¹ * S 0 1 * (τ⁻¹ * S 0 1) =
            ((S 0 0 + δ) ^ 2 + S 0 1 ^ 2) * (τ⁻¹ * τ⁻¹) := by ring
        rw [this]
        have h_inv : τ⁻¹ * τ⁻¹ = (τ ^ 2)⁻¹ := by rw [← mul_inv, ← sq]
        rw [h_inv, div_eq_mul_inv]
        try ring
      rw [h_alg]
      have h_trS : Matrix.trace S = S 0 0 + S 1 1 := Matrix.trace_fin_two S
      have h_detS_val : S.det = S 0 0 * S 1 1 - S 0 1 * S 1 0 := Matrix.det_fin_two S
      rw [hS_10] at h_detS_val
      have h_sq : S 0 1 * S 0 1 = S 0 1 ^ 2 := by ring
      rw [h_sq] at h_detS_val
      have h_num : (S 0 0 + δ) ^ 2 + S 0 1 ^ 2 = S 0 0 * (Matrix.trace S + 2 * δ) := by
        rw [h_trS]
        linear_combination -h_detS + h_detS_val
      rw [h_num, ← hτ_sq]
      exact mul_div_cancel_right₀ (S 0 0) hτ_sq_ne_zero
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      dsimp [P]
      have h_alg : (τ⁻¹ * (S 0 0 + δ)) * (τ⁻¹ * S 0 1) + (τ⁻¹ * S 0 1) * (τ⁻¹ * (S 1 1 + δ)) =
          (S 0 1 * (Matrix.trace S + 2 * δ)) / τ ^ 2 := by
        have h_trS : Matrix.trace S = S 0 0 + S 1 1 := Matrix.trace_fin_two S
        rw [h_trS]
        have : (τ⁻¹ * (S 0 0 + δ)) * (τ⁻¹ * S 0 1) + (τ⁻¹ * S 0 1) * (τ⁻¹ * (S 1 1 + δ)) =
            (S 0 1 * (S 0 0 + S 1 1 + 2 * δ)) * (τ⁻¹ * τ⁻¹) := by ring
        rw [this]
        have h_inv : τ⁻¹ * τ⁻¹ = (τ ^ 2)⁻¹ := by rw [← mul_inv, ← sq]
        rw [h_inv, div_eq_mul_inv]
        try ring
      rw [h_alg, ← hτ_sq]
      exact mul_div_cancel_right₀ (S 0 1) hτ_sq_ne_zero
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      dsimp [P]
      have hS_10 : S 1 0 = S 0 1 := congrFun (congrFun hS_symm 0) 1
      rw [hS_10]
      have h_alg : (τ⁻¹ * S 0 1) * (τ⁻¹ * (S 0 0 + δ)) + (τ⁻¹ * (S 1 1 + δ)) * (τ⁻¹ * S 0 1) =
          (S 0 1 * (Matrix.trace S + 2 * δ)) / τ ^ 2 := by
        have h_trS : Matrix.trace S = S 0 0 + S 1 1 := Matrix.trace_fin_two S
        rw [h_trS]
        have : (τ⁻¹ * S 0 1) * (τ⁻¹ * (S 0 0 + δ)) + (τ⁻¹ * (S 1 1 + δ)) * (τ⁻¹ * S 0 1) =
            (S 0 1 * (S 0 0 + S 1 1 + 2 * δ)) * (τ⁻¹ * τ⁻¹) := by ring
        rw [this]
        have h_inv : τ⁻¹ * τ⁻¹ = (τ ^ 2)⁻¹ := by rw [← mul_inv, ← sq]
        rw [h_inv, div_eq_mul_inv]
        try ring
      rw [h_alg, ← hτ_sq]
      exact mul_div_cancel_right₀ (S 0 1) hτ_sq_ne_zero
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      dsimp [P]
      have hS_10 : S 1 0 = S 0 1 := congrFun (congrFun hS_symm 0) 1
      rw [hS_10]
      have h_alg : (τ⁻¹ * S 0 1) * (τ⁻¹ * S 0 1) + (τ⁻¹ * (S 1 1 + δ)) * (τ⁻¹ * (S 1 1 + δ)) =
          ((S 1 1 + δ) ^ 2 + S 0 1 ^ 2) / τ ^ 2 := by
        have : τ⁻¹ * S 0 1 * (τ⁻¹ * S 0 1) + τ⁻¹ * (S 1 1 + δ) * (τ⁻¹ * (S 1 1 + δ)) =
            ((S 1 1 + δ) ^ 2 + S 0 1 ^ 2) * (τ⁻¹ * τ⁻¹) := by ring
        rw [this]
        have h_inv : τ⁻¹ * τ⁻¹ = (τ ^ 2)⁻¹ := by rw [← mul_inv, ← sq]
        rw [h_inv, div_eq_mul_inv]
        try ring
      rw [h_alg]
      have h_trS : Matrix.trace S = S 0 0 + S 1 1 := Matrix.trace_fin_two S
      have h_detS_val : S.det = S 0 0 * S 1 1 - S 0 1 * S 1 0 := Matrix.det_fin_two S
      rw [hS_10] at h_detS_val
      have h_sq : S 0 1 * S 0 1 = S 0 1 ^ 2 := by ring
      rw [h_sq] at h_detS_val
      have h_num : (S 1 1 + δ) ^ 2 + S 0 1 ^ 2 = S 1 1 * (Matrix.trace S + 2 * δ) := by
        rw [h_trS]
        linear_combination -h_detS + h_detS_val
      rw [h_num, ← hτ_sq]
      exact mul_div_cancel_right₀ (S 1 1) hτ_sq_ne_zero
  have hP_det : P.det = δ := by
    rw [Matrix.det_fin_two]
    have hS_10 : S 1 0 = S 0 1 := congrFun (congrFun hS_symm 0) 1
    have h_alg : P 0 0 * P 1 1 - P 0 1 * P 1 0 =
        ((S 0 0 + δ) * (S 1 1 + δ) - S 0 1 ^ 2) / τ ^ 2 := by
      dsimp [P]
      have : (τ⁻¹ * (S 0 0 + δ)) * (τ⁻¹ * (S 1 1 + δ)) - (τ⁻¹ * S 0 1) * (τ⁻¹ * S 1 0) =
          ((S 0 0 + δ) * (S 1 1 + δ) - S 0 1 * S 1 0) * (τ⁻¹ * τ⁻¹) := by ring
      rw [this, hS_10]
      have h_inv : τ⁻¹ * τ⁻¹ = (τ ^ 2)⁻¹ := by rw [← mul_inv, ← sq]
      rw [h_inv, div_eq_mul_inv]
      ring
    rw [h_alg]
    have h_trS : Matrix.trace S = S 0 0 + S 1 1 := Matrix.trace_fin_two S
    have h_detS_val : S.det = S 0 0 * S 1 1 - S 0 1 * S 1 0 := Matrix.det_fin_two S
    rw [hS_10] at h_detS_val
    have h_sq : S 0 1 * S 0 1 = S 0 1 ^ 2 := by ring
    rw [h_sq] at h_detS_val
    have h_num : (S 0 0 + δ) * (S 1 1 + δ) - S 0 1 ^ 2 = δ * (Matrix.trace S + 2 * δ) := by
      rw [h_trS]
      linear_combination h_detS - h_detS_val
    rw [h_num, ← hτ_sq]
    exact mul_div_cancel_right₀ δ hτ_sq_ne_zero
  let P_inv : Matrix (Fin 2) (Fin 2) ℝ :=
    !![(δ * τ)⁻¹ * (Matrix.trace S + δ - S 0 0), -(δ * τ)⁻¹ * S 0 1;
       -(δ * τ)⁻¹ * S 1 0, (δ * τ)⁻¹ * (Matrix.trace S + δ - S 1 1)]
  have hP_inv_mul : P * P_inv = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Fin.reduceEq]
      dsimp [P, P_inv]
      have hS_10 : S 1 0 = S 0 1 := congrFun (congrFun hS_symm 0) 1
      have h_trS : Matrix.trace S = S 0 0 + S 1 1 := Matrix.trace_fin_two S
      have h_alg : (τ⁻¹ * (S 0 0 + δ)) * ((δ * τ)⁻¹ * (Matrix.trace S + δ - S 0 0)) +
          (τ⁻¹ * S 0 1) * (-(δ * τ)⁻¹ * S 1 0) =
          ((S 0 0 + δ) * (S 1 1 + δ) - S 0 1 ^ 2) / (δ * τ ^ 2) := by
        rw [h_trS, hS_10]
        have : (τ⁻¹ * (S 0 0 + δ)) * ((δ * τ)⁻¹ * (S 0 0 + S 1 1 + δ - S 0 0)) +
            (τ⁻¹ * S 0 1) * (-(δ * τ)⁻¹ * S 0 1) =
            ((S 0 0 + δ) * (S 1 1 + δ) - S 0 1 ^ 2) * (τ⁻¹ * (δ * τ)⁻¹) := by ring
        rw [this]
        have : τ⁻¹ * (δ * τ)⁻¹ = (δ * τ ^ 2)⁻¹ := by
          rw [mul_inv, mul_inv, mul_comm δ⁻¹, ← mul_assoc, ← inv_pow, inv_eq_one_div, inv_eq_one_div]
          ring
        rw [this, inv_eq_one_div]
        ring
      rw [h_alg]
      have h_detS_val : S.det = S 0 0 * S 1 1 - S 0 1 * S 1 0 := Matrix.det_fin_two S
      rw [hS_10] at h_detS_val
      have h_sq : S 0 1 * S 0 1 = S 0 1 ^ 2 := by ring
      rw [h_sq] at h_detS_val
      have h_num : (S 0 0 + δ) * (S 1 1 + δ) - S 0 1 ^ 2 = δ * (Matrix.trace S + 2 * δ) := by
        rw [h_trS]
        linear_combination h_detS - h_detS_val
      rw [h_num, ← hτ_sq]
      have h_δτ2_ne : δ * τ ^ 2 ≠ 0 := mul_ne_zero (ne_of_gt hδ_pos) hτ_sq_ne_zero
      exact div_self h_δτ2_ne
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Fin.zero_eta,
        Fin.reduceEq]
      dsimp [P, P_inv]
      have h_trS : Matrix.trace S = S 0 0 + S 1 1 := Matrix.trace_fin_two S
      rw [h_trS]
      have : (τ⁻¹ * (S 0 0 + δ)) * (-(δ * τ)⁻¹ * S 0 1) +
          (τ⁻¹ * S 0 1) * ((δ * τ)⁻¹ * (S 0 0 + S 1 1 + δ - S 1 1)) =
          (-(S 0 0 + δ) * S 0 1 + S 0 1 * (S 0 0 + δ)) * (τ⁻¹ * (δ * τ)⁻¹) := by ring
      rw [this]
      have : -(S 0 0 + δ) * S 0 1 + S 0 1 * (S 0 0 + δ) = 0 := by ring
      rw [this, zero_mul]
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Fin.reduceEq]
      dsimp [P, P_inv]
      have h_trS : Matrix.trace S = S 0 0 + S 1 1 := Matrix.trace_fin_two S
      rw [h_trS]
      have : (τ⁻¹ * S 1 0) * ((δ * τ)⁻¹ * (S 0 0 + S 1 1 + δ - S 0 0)) +
          (τ⁻¹ * (S 1 1 + δ)) * (-(δ * τ)⁻¹ * S 1 0) =
          (S 1 0 * (S 1 1 + δ) - (S 1 1 + δ) * S 1 0) * (τ⁻¹ * (δ * τ)⁻¹) := by ring
      rw [this]
      have : S 1 0 * (S 1 1 + δ) - (S 1 1 + δ) * S 1 0 = 0 := by ring
      rw [this, zero_mul]
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Fin.reduceEq]
      dsimp [P, P_inv]
      have hS_10 : S 1 0 = S 0 1 := congrFun (congrFun hS_symm 0) 1
      rw [hS_10]
      have h_trS : Matrix.trace S = S 0 0 + S 1 1 := Matrix.trace_fin_two S
      have h_alg : (τ⁻¹ * S 0 1) * (-(δ * τ)⁻¹ * S 0 1) +
          (τ⁻¹ * (S 1 1 + δ)) * ((δ * τ)⁻¹ * (Matrix.trace S + δ - S 1 1)) =
          ((S 0 0 + δ) * (S 1 1 + δ) - S 0 1 ^ 2) / (δ * τ ^ 2) := by
        rw [h_trS]
        have : (τ⁻¹ * S 0 1) * (-(δ * τ)⁻¹ * S 0 1) +
            (τ⁻¹ * (S 1 1 + δ)) * ((δ * τ)⁻¹ * (S 0 0 + S 1 1 + δ - S 1 1)) =
            ((S 0 0 + δ) * (S 1 1 + δ) - S 0 1 ^ 2) * (τ⁻¹ * (δ * τ)⁻¹) := by ring
        rw [this]
        have : τ⁻¹ * (δ * τ)⁻¹ = (δ * τ ^ 2)⁻¹ := by
          rw [mul_inv, mul_inv, mul_comm δ⁻¹, ← mul_assoc, ← inv_pow, inv_eq_one_div, inv_eq_one_div]
          ring
        rw [this, inv_eq_one_div]
        ring
      rw [h_alg]
      have h_detS_val : S.det = S 0 0 * S 1 1 - S 0 1 * S 1 0 := Matrix.det_fin_two S
      rw [hS_10] at h_detS_val
      have h_sq : S 0 1 * S 0 1 = S 0 1 ^ 2 := by ring
      rw [h_sq] at h_detS_val
      have h_num : (S 0 0 + δ) * (S 1 1 + δ) - S 0 1 ^ 2 = δ * (Matrix.trace S + 2 * δ) := by
        rw [h_trS]
        linear_combination h_detS - h_detS_val
      rw [h_num, ← hτ_sq]
      have h_δτ2_ne : δ * τ ^ 2 ≠ 0 := mul_ne_zero (ne_of_gt hδ_pos) hτ_sq_ne_zero
      exact div_self h_δτ2_ne
  have hP_inv_P : P_inv * P = 1 := by
    rw [mul_eq_one_comm]
    exact hP_inv_mul
  let U := M * P_inv
  have hU_P : U * P = M := by
    dsimp [U]
    rw [Matrix.mul_assoc, hP_inv_P, Matrix.mul_one]
  have hP_inv_symm : P_invᵀ = P_inv := by
    ext i j
    have hS_10 : S 1 0 = S 0 1 := congrFun (congrFun hS_symm 0) 1
    fin_cases i <;> fin_cases j <;> {
      simp [P_inv, Matrix.transpose_apply, hS_10]
    }
  have hUt_U : Uᵀ * U = 1 := by
    dsimp [U]
    rw [Matrix.transpose_mul, hP_inv_symm]
    have : P_inv * Mᵀ * (M * P_inv) = P_inv * S * P_inv := by
      change P_inv * Mᵀ * (M * P_inv) = P_inv * (Mᵀ * M) * P_inv
      repeat rw [Matrix.mul_assoc]
    rw [this, ← hPP]
    have : P_inv * (P * P) * P_inv = (P_inv * P) * (P * P_inv) := by
      repeat rw [Matrix.mul_assoc]
    rw [this, hP_inv_P, hP_inv_mul, mul_one]
  have hU_Ut : U * Uᵀ = 1 := by
    rw [mul_eq_one_comm]
    exact hUt_U
  have hP_pos : ∀ v : Fin 2 → ℝ, v ≠ 0 → 0 < dotProduct v (P.mulVec v) := by
    intro v hv
    have hv_sq : 0 < v 0 ^ 2 + v 1 ^ 2 := by
      by_contra hc
      have h_le : v 0 ^ 2 + v 1 ^ 2 ≤ 0 := not_lt.mp hc
      have hv0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
      have hv1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
      have hv_zero : v = 0 := by
        ext i
        fin_cases i
        · exact hv0
        · exact hv1
      exact hv hv_zero
    have hS_10 : S 1 0 = S 0 1 := congrFun (congrFun hS_symm 0) 1
    have h_dot : dotProduct v (P.mulVec v) =
        τ⁻¹ * (((M 0 0 * v 0 + M 0 1 * v 1) ^ 2 + (M 1 0 * v 0 + M 1 1 * v 1) ^ 2) +
          δ * (v 0 ^ 2 + v 1 ^ 2)) := by
      have hP00 : P 0 0 = τ⁻¹ * (S 0 0 + δ) := rfl
      have hP01 : P 0 1 = τ⁻¹ * S 0 1 := rfl
      have hP10 : P 1 0 = τ⁻¹ * S 1 0 := rfl
      have hP11 : P 1 1 = τ⁻¹ * (S 1 1 + δ) := rfl
      have h_expand : dotProduct v (P.mulVec v) =
          v 0 * (P 0 0 * v 0 + P 0 1 * v 1) + v 1 * (P 1 0 * v 0 + P 1 1 * v 1) := by
        simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      rw [h_expand, hP00, hP01, hP10, hP11, hS_10]
      have h_quad : v 0 * (τ⁻¹ * (S 0 0 + δ) * v 0 + τ⁻¹ * S 0 1 * v 1) +
          v 1 * (τ⁻¹ * S 0 1 * v 0 + τ⁻¹ * (S 1 1 + δ) * v 1) =
          τ⁻¹ * ((S 0 0 * v 0 ^ 2 + 2 * S 0 1 * v 0 * v 1 + S 1 1 * v 1 ^ 2) +
            δ * (v 0 ^ 2 + v 1 ^ 2)) := by ring
      rw [h_quad]
      congr 1
      congr 1
      have hS00 : S 0 0 = M 0 0 * M 0 0 + M 1 0 * M 1 0 := by
        simp [S, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
      have hS01 : S 0 1 = M 0 0 * M 0 1 + M 1 0 * M 1 1 := by
        simp [S, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
      have hS11 : S 1 1 = M 0 1 * M 0 1 + M 1 1 * M 1 1 := by
        simp [S, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
      rw [hS00, hS01, hS11]
      ring
    rw [h_dot]
    have h_sum_sq_nonneg : 0 ≤ (M 0 0 * v 0 + M 0 1 * v 1) ^ 2 + (M 1 0 * v 0 + M 1 1 * v 1) ^ 2 := by
      positivity
    have h_inner_pos : 0 < ((M 0 0 * v 0 + M 0 1 * v 1) ^ 2 + (M 1 0 * v 0 + M 1 1 * v 1) ^ 2) +
        δ * (v 0 ^ 2 + v 1 ^ 2) := by
      have h_del_sq_pos : 0 < δ * (v 0 ^ 2 + v 1 ^ 2) := mul_pos hδ_pos hv_sq
      linarith
    exact mul_pos (inv_pos.mpr hτ_pos) h_inner_pos
  exact ⟨U, P, hU_P.symm, hUt_U, hU_Ut, hP_symm, hPP, hP_det, hP_pos⟩

end KP5_SL2IwasawaAndGL2Polar

end InfoGeometry.Algebra.WeylCartanKANPolarEquivariance
