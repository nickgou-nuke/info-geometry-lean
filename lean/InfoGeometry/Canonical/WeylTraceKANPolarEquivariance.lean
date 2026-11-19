/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Cocycle.MatrixDetExpTrace
import InfoGeometry.Dynamics.KanDecomposition
import InfoGeometry.Optimization.PolarDecomposition
import InfoGeometry.Canonical.RealLieJordanGeometry
import InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Weyl scale, trace/determinant, and decomposition covariance

This bridge works in full matrix algebras.  It records the exact effect of a
central scalar scale and an invertible change of frame, then transports a
given real polar factorization under an orthogonal symmetry.  The KAN result
is a factorization identity; it does not claim uniqueness or subgroup
membership for the conjugated factors.
-/

noncomputable section

namespace InfoGeometry.Canonical.WeylTraceKANPolarEquivariance

open Matrix
open scoped InfoGeometry.Canonical.RealLieJordanGeometry

/-! ## Noncommutative two-sheet Cartan/trace core -/

section NoncommutativeTwoByTwoCore

variable {B : Type*} [Ring B]

def mat2Ring (a b c d : B) : Matrix (Fin 2) (Fin 2) B :=
  Matrix.of ![![a, b], ![c, d]]

omit [Ring B] in
lemma ext_fin2Ring {M N : Matrix (Fin 2) (Fin 2) B}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

lemma mat2Ring_mul (a b c d e f g h : B) :
    mat2Ring a b c d * mat2Ring e f g h =
      mat2Ring (a * e + b * g) (a * f + b * h)
        (c * e + d * g) (c * f + d * h) := by
  apply ext_fin2Ring <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mat2Ring]

@[simp] lemma trace_fin2Ring (M : Matrix (Fin 2) (Fin 2) B) :
    Matrix.trace M = M 0 0 + M 1 1 := by
  dsimp [Matrix.trace, Matrix.diag]
  exact Fin.sum_univ_two _

def weylScalarPart (M : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  mat2Ring (M 0 0 + M 1 1) 0 0 (M 0 0 + M 1 1)

def tracelessSymmetricPart (M : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  mat2Ring (M 0 0 - M 1 1) (M 0 1 + M 1 0)
    (M 1 0 + M 0 1) (M 1 1 - M 0 0)

def tracelessSkewPart (M : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  mat2Ring 0 (M 0 1 - M 1 0) (M 1 0 - M 0 1) 0

def symmetrizedDet2 (M : Matrix (Fin 2) (Fin 2) B) : B :=
  (M 0 0 * M 1 1 + M 1 1 * M 0 0) -
    (M 0 1 * M 1 0 + M 1 0 * M 0 1)

def gamma1Ring : Matrix (Fin 2) (Fin 2) B := mat2Ring 1 0 0 (-1)
def sigmaRing : Matrix (Fin 2) (Fin 2) B := mat2Ring 0 1 1 0
def omegaRing : Matrix (Fin 2) (Fin 2) B := mat2Ring 0 (-1) 1 0

/-- Exact noncommutative scalar/symmetric/skew split and Plemelj–Newton
trace-to-symmetrized-determinant identity in the operator algebra `M₂(B)`. -/
theorem noncommutative_weyl_cartan_trace_determinant
    (M : Matrix (Fin 2) (Fin 2) B) :
    weylScalarPart M + tracelessSymmetricPart M + tracelessSkewPart M = 2 • M ∧
    Matrix.trace (tracelessSymmetricPart M) = 0 ∧
    Matrix.trace (tracelessSkewPart M) = 0 ∧
    (tracelessSymmetricPart M)ᵀ = tracelessSymmetricPart M ∧
    (tracelessSkewPart M)ᵀ = -tracelessSkewPart M ∧
    Matrix.trace M *
      Matrix.trace M - Matrix.trace (M * M) = symmetrizedDet2 M ∧
    ⁅(gamma1Ring : Matrix (Fin 2) (Fin 2) B),
      (sigmaRing : Matrix (Fin 2) (Fin 2) B)⁆ =
        -(2 • (omegaRing : Matrix (Fin 2) (Fin 2) B)) ∧
    ⁅(omegaRing : Matrix (Fin 2) (Fin 2) B),
      (gamma1Ring : Matrix (Fin 2) (Fin 2) B)⁆ =
        2 • (sigmaRing : Matrix (Fin 2) (Fin 2) B) ∧
    ⁅(omegaRing : Matrix (Fin 2) (Fin 2) B),
      (sigmaRing : Matrix (Fin 2) (Fin 2) B)⁆ =
        -(2 • (gamma1Ring : Matrix (Fin 2) (Fin 2) B)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2Ring <;>
      simp [weylScalarPart, tracelessSymmetricPart, tracelessSkewPart, mat2Ring,
        two_smul] <;> noncomm_ring
  · simp [tracelessSymmetricPart, mat2Ring, trace_fin2Ring]
  · simp [tracelessSkewPart, mat2Ring, trace_fin2Ring]
  · apply ext_fin2Ring <;> simp [tracelessSymmetricPart, mat2Ring, Matrix.transpose_apply, add_comm]
  · apply ext_fin2Ring <;> simp [tracelessSkewPart, mat2Ring, Matrix.transpose_apply]
  · simp [symmetrizedDet2, trace_fin2Ring, mat2Ring, Matrix.mul_apply,
      Fin.sum_univ_two]
    noncomm_ring
  · rw [Ring.lie_def]; apply ext_fin2Ring <;> simp [gamma1Ring, sigmaRing, omegaRing, two_smul, mat2Ring] <;> abel
  · rw [Ring.lie_def]; apply ext_fin2Ring <;> simp [gamma1Ring, sigmaRing, omegaRing, two_smul, mat2Ring] <;> abel
  · rw [Ring.lie_def]; apply ext_fin2Ring <;> simp [gamma1Ring, sigmaRing, omegaRing, two_smul, mat2Ring] <;> abel

/-- OpenGauss Trap T16: Non-commutativity witness for 2x2 matrices over ring `B`. -/
theorem matrix_carrier_B_noncommutative {B : Type*} [Ring B] [Nontrivial B] :
    ∃ M N : Matrix (Fin 2) (Fin 2) B, M * N ≠ N * M := by
  refine ⟨mat2Ring 0 1 0 0, mat2Ring 0 0 1 0, ?_⟩
  intro h
  have h00 := congrFun (congrFun h 0) 0
  revert h00
  simp [mat2Ring, Matrix.mul_apply, Fin.sum_univ_two]

/-- OpenGauss Trap T16: Non-commutativity witness for 2x2 real matrices. -/
theorem matrix_carrier_Real_noncommutative :
    ∃ M N : Matrix (Fin 2) (Fin 2) ℝ, M * N ≠ N * M := by
  refine ⟨mat2Ring 0 1 0 0, mat2Ring 0 0 1 0, ?_⟩
  intro h
  have h00 := congrFun (congrFun h 0) 0
  revert h00
  simp [mat2Ring, Matrix.mul_apply, Fin.sum_univ_two]

end NoncommutativeTwoByTwoCore

/-! ## Noncommutative KAN--Gram bridge -/

section NoncommutativeKANGram

variable {B : Type*} [Ring B]

def kanDiagonal (aPlus aMinus : B) : Matrix (Fin 2) (Fin 2) B :=
  mat2Ring aPlus 0 0 aMinus

def kanUpper (n : B) : Matrix (Fin 2) (Fin 2) B :=
  mat2Ring 1 n 0 1

def kanLower (n : B) : Matrix (Fin 2) (Fin 2) B :=
  mat2Ring 1 0 n 1

theorem kanUpper_add (n₁ n₂ : B) :
    kanUpper n₁ * kanUpper n₂ = kanUpper (n₁ + n₂) := by
  apply ext_fin2Ring <;>
    simp [kanUpper, mat2Ring, Matrix.mul_apply, Fin.sum_univ_two] <;> abel

theorem kanUpper_inverse (n : B) :
    kanUpper n * kanUpper (-n) = 1 := by
  apply ext_fin2Ring <;> simp [kanUpper, mat2Ring, Matrix.mul_apply, Fin.sum_univ_two]

theorem kanDiagonal_upper (aPlus aMinus n : B) :
    kanDiagonal aPlus aMinus * kanUpper n = mat2Ring aPlus (aPlus * n) 0 aMinus := by
  apply ext_fin2Ring <;> simp [kanDiagonal, kanUpper, mat2Ring, Matrix.mul_apply,
    Fin.sum_univ_two]

variable [StarRing B]

/-- The Gram matrix of `K A N` depends only on `A N` when the left factor
is an isometry (`Kᴴ K = 1`). This is an algebraic identity, without a
positivity or square-root assertion. -/
theorem kan_gram_formula (aPlus aMinus n : B)
    {K : Matrix (Fin 2) (Fin 2) B} (hK : Kᴴ * K = 1) :
    let M := K * kanDiagonal aPlus aMinus * kanUpper n
    Mᴴ * M = mat2Ring (star aPlus * aPlus) (star aPlus * aPlus * n)
      (star n * star aPlus * aPlus) (star n * star aPlus * aPlus * n + star aMinus * aMinus) := by
  dsimp
  have h_elim :
      (K * kanDiagonal aPlus aMinus * kanUpper n)ᴴ *
          (K * kanDiagonal aPlus aMinus * kanUpper n) =
        (kanDiagonal aPlus aMinus * kanUpper n)ᴴ *
          (kanDiagonal aPlus aMinus * kanUpper n) := by
    change (((K * kanDiagonal aPlus aMinus) * kanUpper n)ᴴ *
      ((K * kanDiagonal aPlus aMinus) * kanUpper n)) =
      (kanDiagonal aPlus aMinus * kanUpper n)ᴴ *
        (kanDiagonal aPlus aMinus * kanUpper n)
    rw [Matrix.mul_assoc K (kanDiagonal aPlus aMinus) (kanUpper n)]
    let X := kanDiagonal aPlus aMinus * kanUpper n
    change (K * X)ᴴ * (K * X) = Xᴴ * X
    calc
      (K * X)ᴴ * (K * X) = Xᴴ * (Kᴴ * K) * X := by
        simp only [Matrix.conjTranspose_mul]
        noncomm_ring
      _ = Xᴴ * X := by rw [hK]; simp
  rw [h_elim]
  apply ext_fin2Ring <;>
    simp [kanDiagonal, kanUpper, mat2Ring, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Fin.sum_univ_two, star_mul]
    <;> noncomm_ring

theorem kan_gram_schur_complement (aPlus aMinus n : B)
    {K : Matrix (Fin 2) (Fin 2) B} (hK : Kᴴ * K = 1) :
    let M := K * kanDiagonal aPlus aMinus * kanUpper n
    (Mᴴ * M) 1 1 - star n * (Mᴴ * M) 0 0 * n = star aMinus * aMinus := by
  change ((K * kanDiagonal aPlus aMinus * kanUpper n)ᴴ *
    (K * kanDiagonal aPlus aMinus * kanUpper n)) 1 1 -
      star n * ((K * kanDiagonal aPlus aMinus * kanUpper n)ᴴ *
        (K * kanDiagonal aPlus aMinus * kanUpper n)) 0 0 * n = star aMinus * aMinus
  rw [kan_gram_formula aPlus aMinus n hK]
  simp [mat2Ring]
  noncomm_ring

end NoncommutativeKANGram

/-! ## Constructive real `GL₂⁺` Iwasawa coordinates -/

abbrev RealMat2 := Matrix (Fin 2) (Fin 2) ℝ

def firstColumnNorm (M : RealMat2) : ℝ := Real.sqrt ((M 0 0) ^ 2 + (M 1 0) ^ 2)

def realIwasawaK (M : RealMat2) : RealMat2 :=
  let r := firstColumnNorm M
  mat2Ring (M 0 0 / r) (-M 1 0 / r) (M 1 0 / r) (M 0 0 / r)

def realIwasawaA (M : RealMat2) : RealMat2 :=
  let r := firstColumnNorm M
  mat2Ring r 0 0 (Matrix.det M / r)

def realIwasawaN (M : RealMat2) : RealMat2 :=
  let r := firstColumnNorm M
  mat2Ring 1 ((M 0 0 * M 0 1 + M 1 0 * M 1 1) / r ^ 2) 0 1

private lemma firstColumnNorm_pos {M : RealMat2} (hdet : 0 < Matrix.det M) :
    0 < firstColumnNorm M := by
  apply Real.sqrt_pos.mpr
  by_contra hn
  have hsum : (M 0 0) ^ 2 + (M 1 0) ^ 2 = 0 := by
    have hnonneg : 0 ≤ (M 0 0) ^ 2 + (M 1 0) ^ 2 := by positivity
    nlinarith
  have ha : M 0 0 = 0 := by nlinarith [sq_nonneg (M 0 0)]
  have hc : M 1 0 = 0 := by nlinarith [sq_nonneg (M 1 0)]
  have hdet_formula : Matrix.det M = M 0 0 * M 1 1 - M 0 1 * M 1 0 :=
    Matrix.det_fin_two M
  rw [hdet_formula, ha, hc] at hdet
  norm_num at hdet

/-- Every real two-by-two matrix with positive determinant has the displayed
`K A N` factorization. The factors are the standard Euclidean Iwasawa factors;
the proof is an explicit first-column normalization and reconstruction. -/
theorem real_gl2_pos_iwasawa_factorization {M : RealMat2}
    (hdet : 0 < Matrix.det M) :
    (realIwasawaK M)ᵀ * realIwasawaK M = 1 ∧
    0 < realIwasawaA M 0 0 ∧ 0 < realIwasawaA M 1 1 ∧
    realIwasawaA M 0 1 = 0 ∧ realIwasawaA M 1 0 = 0 ∧
    realIwasawaN M 0 0 = 1 ∧ realIwasawaN M 1 1 = 1 ∧
    realIwasawaN M 1 0 = 0 ∧
    realIwasawaK M * realIwasawaA M * realIwasawaN M = M := by
  have hr : 0 < firstColumnNorm M := firstColumnNorm_pos hdet
  have hr0 : firstColumnNorm M ≠ 0 := ne_of_gt hr
  have hrsq : firstColumnNorm M ^ 2 = (M 0 0) ^ 2 + (M 1 0) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hdet_eq : Matrix.det M = M 0 0 * M 1 1 - M 0 1 * M 1 0 :=
    Matrix.det_fin_two M
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · let r := firstColumnNorm M
    have hr2 : r ^ 2 = (M 0 0) ^ 2 + (M 1 0) ^ 2 := hrsq
    have hrn : r ≠ 0 := hr0
    change (mat2Ring (M 0 0 / r) (-M 1 0 / r) (M 1 0 / r) (M 0 0 / r))ᵀ *
        mat2Ring (M 0 0 / r) (-M 1 0 / r) (M 1 0 / r) (M 0 0 / r) = 1
    apply ext_fin2Ring <;>
      simp [mat2Ring, Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp [hrn] <;> nlinarith [hr2]
  · simpa [realIwasawaA, firstColumnNorm, mat2Ring] using hr
  · dsimp [realIwasawaA]
    exact div_pos hdet hr
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · let r := firstColumnNorm M
    have hr2 : r ^ 2 = (M 0 0) ^ 2 + (M 1 0) ^ 2 := hrsq
    have hrn : r ≠ 0 := hr0
    change (mat2Ring (M 0 0 / r) (-M 1 0 / r) (M 1 0 / r) (M 0 0 / r) *
        mat2Ring r 0 0 (Matrix.det M / r)) *
        mat2Ring 1 ((M 0 0 * M 0 1 + M 1 0 * M 1 1) / r ^ 2) 0 1 = M
    apply ext_fin2Ring <;>
      simp [mat2Ring, Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp [hrn] <;> rw [hr2, hdet_eq] <;> ring

/-- An orientation-preserving orthogonal two-by-two matrix has the standard
rotation form. -/
private theorem real_orthogonal_det_one_shape {K : RealMat2}
    (hK : Kᵀ * K = 1) (hdetK : Matrix.det K = 1) :
    K 0 1 = -K 1 0 ∧ K 1 1 = K 0 0 := by
  have hnorm : K 0 0 ^ 2 + K 1 0 ^ 2 = 1 := by
    have h := congrArg (fun Q : RealMat2 => Q 0 0) hK
    simpa [pow_two, Matrix.transpose_apply, Matrix.mul_apply,
      Fin.sum_univ_two] using h
  have hdot : K 0 0 * K 0 1 + K 1 0 * K 1 1 = 0 := by
    have h := congrArg (fun Q : RealMat2 => Q 0 1) hK
    simpa [Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_two] using h
  have hdet : K 0 0 * K 1 1 - K 0 1 * K 1 0 = 1 := by
    simpa [Matrix.det_fin_two] using hdetK
  have hnorm' : K 0 0 * K 0 0 + K 1 0 * K 1 0 = 1 := by
    simpa [pow_two] using hnorm
  have h01 : K 0 1 = -K 1 0 := by
    have hid : K 0 0 * (K 0 0 * K 0 1 + K 1 0 * K 1 1) -
        K 1 0 * (K 0 0 * K 1 1 - K 0 1 * K 1 0) =
          K 0 1 * (K 0 0 * K 0 0 + K 1 0 * K 1 0) := by ring
    rw [hdot, hdet, hnorm'] at hid
    linarith
  have h11 : K 1 1 = K 0 0 := by
    have hmul : K 0 0 * (K 1 1 - K 0 0) = 0 := by
      rw [h01] at hdet
      nlinarith [hdet, hnorm]
    by_cases hx : K 0 0 = 0
    · have hy : K 1 0 ≠ 0 := by
        intro hy
        rw [hx, hy] at hnorm
        norm_num at hnorm
      have hdot' : K 1 0 * K 1 1 = 0 := by
        rw [hx, h01] at hdot
        simpa using hdot
      have : K 1 1 = 0 := (mul_eq_zero.mp hdot').resolve_left hy
      rw [hx, this]
    · have hdiff := (mul_eq_zero.mp hmul).resolve_left hx
      linarith
  exact ⟨h01, h11⟩

/-- Uniqueness of the group-level real `GL₂⁺` KAN factors with the stated
normalization: `K ∈ SO(2)`, `A` is positive diagonal, and `N` is upper
unipotent. This compares arbitrary factors satisfying those conditions; it
does not assume they equal the explicit coordinate functions. -/
theorem real_gl2_pos_kan_unique
    {M K₁ K₂ A₁ A₂ N₁ N₂ : RealMat2}
    (hfact₁ : K₁ * A₁ * N₁ = M) (hfact₂ : K₂ * A₂ * N₂ = M)
    (hK₁ : K₁ᵀ * K₁ = 1) (hK₂ : K₂ᵀ * K₂ = 1)
    (hdetK₁ : Matrix.det K₁ = 1) (hdetK₂ : Matrix.det K₂ = 1)
    (hA₁₀ : 0 < A₁ 0 0)
    (hA₁₀₁ : A₁ 0 1 = 0) (hA₁₁₀ : A₁ 1 0 = 0)
    (hA₂₀ : 0 < A₂ 0 0)
    (hA₂₀₁ : A₂ 0 1 = 0) (hA₂₁₀ : A₂ 1 0 = 0)
    (hN₁₀₀ : N₁ 0 0 = 1) (hN₁₁₁ : N₁ 1 1 = 1)
    (hN₁₁₀ : N₁ 1 0 = 0)
    (hN₂₀₀ : N₂ 0 0 = 1) (hN₂₁₁ : N₂ 1 1 = 1)
    (hN₂₁₀ : N₂ 1 0 = 0) :
    K₁ = K₂ ∧ A₁ = A₂ ∧ N₁ = N₂ := by
  have hK₁shape := real_orthogonal_det_one_shape hK₁ hdetK₁
  have hK₂shape := real_orthogonal_det_one_shape hK₂ hdetK₂
  have hm00₁ : M 0 0 = K₁ 0 0 * A₁ 0 0 := by
    have h := congrArg (fun Q : RealMat2 => Q 0 0) hfact₁.symm
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hA₁₀₁, hA₁₁₀,
      hN₁₀₀, hN₁₁₀] using h
  have hm10₁ : M 1 0 = K₁ 1 0 * A₁ 0 0 := by
    have h := congrArg (fun Q : RealMat2 => Q 1 0) hfact₁.symm
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hA₁₀₁, hA₁₁₀,
      hN₁₀₀, hN₁₁₀] using h
  have hm00₂ : M 0 0 = K₂ 0 0 * A₂ 0 0 := by
    have h := congrArg (fun Q : RealMat2 => Q 0 0) hfact₂.symm
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hA₂₀₁, hA₂₁₀,
      hN₂₀₀, hN₂₁₀] using h
  have hm10₂ : M 1 0 = K₂ 1 0 * A₂ 0 0 := by
    have h := congrArg (fun Q : RealMat2 => Q 1 0) hfact₂.symm
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hA₂₀₁, hA₂₁₀,
      hN₂₀₀, hN₂₁₀] using h
  have hknorm₁ : K₁ 0 0 ^ 2 + K₁ 1 0 ^ 2 = 1 := by
    have h := congrArg (fun Q : RealMat2 => Q 0 0) hK₁
    simpa [pow_two, Matrix.transpose_apply, Matrix.mul_apply,
      Fin.sum_univ_two] using h
  have hknorm₂ : K₂ 0 0 ^ 2 + K₂ 1 0 ^ 2 = 1 := by
    have h := congrArg (fun Q : RealMat2 => Q 0 0) hK₂
    simpa [pow_two, Matrix.transpose_apply, Matrix.mul_apply,
      Fin.sum_univ_two] using h
  have ha₀sq : A₁ 0 0 ^ 2 = A₂ 0 0 ^ 2 := by
    calc
      A₁ 0 0 ^ 2 = M 0 0 ^ 2 + M 1 0 ^ 2 := by
        rw [hm00₁, hm10₁]
        nlinarith [hknorm₁]
      _ = A₂ 0 0 ^ 2 := by
        rw [hm00₂, hm10₂]
        nlinarith [hknorm₂]
  have ha₀ : A₁ 0 0 = A₂ 0 0 := by
    have hprod : (A₁ 0 0 - A₂ 0 0) * (A₁ 0 0 + A₂ 0 0) = 0 := by
      calc
        (A₁ 0 0 - A₂ 0 0) * (A₁ 0 0 + A₂ 0 0) =
            A₁ 0 0 ^ 2 - A₂ 0 0 ^ 2 := by ring
        _ = 0 := by rw [ha₀sq]; ring
    rcases mul_eq_zero.mp hprod with hdiff | hsum
    · linarith
    · linarith [hA₁₀, hA₂₀]
  have hk00 : K₁ 0 0 = K₂ 0 0 := by
    apply mul_left_cancel₀ (ne_of_gt hA₁₀)
    calc
      A₁ 0 0 * K₁ 0 0 = K₁ 0 0 * A₁ 0 0 := by ring
      _ = M 0 0 := hm00₁.symm
      _ = K₂ 0 0 * A₂ 0 0 := hm00₂
      _ = A₁ 0 0 * K₂ 0 0 := by rw [ha₀]; ring
  have hk10 : K₁ 1 0 = K₂ 1 0 := by
    apply mul_left_cancel₀ (ne_of_gt hA₁₀)
    calc
      A₁ 0 0 * K₁ 1 0 = K₁ 1 0 * A₁ 0 0 := by ring
      _ = M 1 0 := hm10₁.symm
      _ = K₂ 1 0 * A₂ 0 0 := hm10₂
      _ = A₁ 0 0 * K₂ 1 0 := by rw [ha₀]; ring
  have hdetM₁ : Matrix.det M = A₁ 0 0 * A₁ 1 1 := by
    calc
      Matrix.det M = Matrix.det (K₁ * A₁ * N₁) := by rw [hfact₁]
      _ = A₁ 0 0 * A₁ 1 1 := by
        rw [Matrix.det_mul, Matrix.det_mul, hdetK₁]
        simp [Matrix.det_fin_two, hA₁₀₁, hA₁₁₀,
          hN₁₀₀, hN₁₁₁, hN₁₁₀]
  have hdetM₂ : Matrix.det M = A₂ 0 0 * A₂ 1 1 := by
    calc
      Matrix.det M = Matrix.det (K₂ * A₂ * N₂) := by rw [hfact₂]
      _ = A₂ 0 0 * A₂ 1 1 := by
        rw [Matrix.det_mul, Matrix.det_mul, hdetK₂]
        simp [Matrix.det_fin_two, hA₂₀₁, hA₂₁₀,
          hN₂₀₀, hN₂₁₁, hN₂₁₀]
  have ha₁ : A₁ 1 1 = A₂ 1 1 := by
    have hdet_eq : A₁ 0 0 * A₁ 1 1 = A₂ 0 0 * A₂ 1 1 := by
      calc
        A₁ 0 0 * A₁ 1 1 = Matrix.det M := hdetM₁.symm
        _ = A₂ 0 0 * A₂ 1 1 := hdetM₂
    rw [ha₀] at hdet_eq
    exact mul_left_cancel₀ (ne_of_gt hA₂₀) hdet_eq
  have hK : K₁ = K₂ := by
    apply ext_fin2Ring
    · exact hk00
    · rw [hK₁shape.1, hK₂shape.1, hk10]
    · exact hk10
    · rw [hK₁shape.2, hK₂shape.2, hk00]
  have hA : A₁ = A₂ := by
    apply ext_fin2Ring
    · exact ha₀
    · rw [hA₁₀₁, hA₂₀₁]
    · rw [hA₁₁₀, hA₂₁₀]
    · exact ha₁
  have hleft₁ : K₁ᵀ * M = A₁ * N₁ := by
    calc
      K₁ᵀ * M = K₁ᵀ * (K₁ * A₁ * N₁) := by rw [hfact₁]
      _ = (K₁ᵀ * K₁) * A₁ * N₁ := by noncomm_ring
      _ = A₁ * N₁ := by rw [hK₁]; noncomm_ring
  have hleft₂ : K₂ᵀ * M = A₂ * N₂ := by
    calc
      K₂ᵀ * M = K₂ᵀ * (K₂ * A₂ * N₂) := by rw [hfact₂]
      _ = (K₂ᵀ * K₂) * A₂ * N₂ := by noncomm_ring
      _ = A₂ * N₂ := by rw [hK₂]; noncomm_ring
  have hAN : A₁ * N₁ = A₂ * N₂ := by
    calc
      A₁ * N₁ = K₁ᵀ * M := hleft₁.symm
      _ = K₂ᵀ * M := by rw [hK]
      _ = A₂ * N₂ := hleft₂
  have hn₀₁ : N₁ 0 1 = N₂ 0 1 := by
    have h := congrArg (fun Q : RealMat2 => Q 0 1) hAN
    simp [Matrix.mul_apply, Fin.sum_univ_two,
      hA₁₀₁, hA₁₁₀, hN₁₁₀, hA₂₀₁, hA₂₁₀, hN₂₁₀] at h
    rw [ha₀] at h
    exact (mul_left_cancel₀ (ne_of_gt hA₂₀)) h
  have hN : N₁ = N₂ := by
    apply ext_fin2Ring
    · rw [hN₁₀₀, hN₂₀₀]
    · exact hn₀₁
    · rw [hN₁₁₀, hN₂₁₀]
    · rw [hN₁₁₁, hN₂₁₁]
  exact ⟨hK, hA, hN⟩

/-- Positive-diagonal (indeed, nonzero diagonal) conjugation scales the
upper-unipotent root coordinate. Both diagonal entries must be nonzero because
the formula uses the inverse matrix. -/
theorem real_kan_upper_diagonal_root_scaling
    (l₀ l₁ u : ℝ) (h₀ : l₀ ≠ 0) (h₁ : l₁ ≠ 0) :
    mat2Ring l₀ 0 0 l₁ * kanUpper u *
        mat2Ring (l₀⁻¹) 0 0 (l₁⁻¹) =
      kanUpper ((l₀ / l₁) * u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kanUpper, mat2Ring, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [h₀, h₁] <;> ring

private theorem real_signed_diagonal_conjugate_entries
    (M : RealMat2) (ε₀ ε₁ : ℝ)
    (hε₀ : ε₀ ^ 2 = 1) (hε₁ : ε₁ ^ 2 = 1) :
    mat2Ring ε₀ 0 0 ε₁ * M * mat2Ring ε₀ 0 0 ε₁ =
      mat2Ring (M 0 0) (ε₀ * ε₁ * M 0 1)
        (ε₀ * ε₁ * M 1 0) (M 1 1) := by
  have hM : M = mat2Ring (M 0 0) (M 0 1) (M 1 0) (M 1 1) := by
    apply ext_fin2Ring <;> rfl
  rcases sq_eq_one_iff.mp hε₀ with hε₀ | hε₀ <;>
    rcases sq_eq_one_iff.mp hε₁ with hε₁ | hε₁
  · subst ε₀; subst ε₁
    rw [hM, mat2Ring_mul, mat2Ring_mul]
    apply ext_fin2Ring <;> simp [mat2Ring] <;> ring
  · subst ε₀; subst ε₁
    rw [hM, mat2Ring_mul, mat2Ring_mul]
    apply ext_fin2Ring <;> simp [mat2Ring] <;> ring
  · subst ε₀; subst ε₁
    rw [hM, mat2Ring_mul, mat2Ring_mul]
    apply ext_fin2Ring <;> simp [mat2Ring] <;> ring
  · subst ε₀; subst ε₁
    rw [hM, mat2Ring_mul, mat2Ring_mul]
    apply ext_fin2Ring <;> simp [mat2Ring] <;> ring

private theorem real_signed_diagonal_conjugation_invariants
    (M : RealMat2) (ε₀ ε₁ : ℝ)
    (hε₀ : ε₀ ^ 2 = 1) (hε₁ : ε₁ ^ 2 = 1) :
    Matrix.det (mat2Ring ε₀ 0 0 ε₁ * M * mat2Ring ε₀ 0 0 ε₁) =
      Matrix.det M ∧
    firstColumnNorm (mat2Ring ε₀ 0 0 ε₁ * M * mat2Ring ε₀ 0 0 ε₁) =
      firstColumnNorm M := by
  have hc := real_signed_diagonal_conjugate_entries M ε₀ ε₁ hε₀ hε₁
  constructor
  · rw [hc, Matrix.det_fin_two]
    simp [mat2Ring, Matrix.det_fin_two]
    ring_nf
    rw [hε₀, hε₁]
    ring
  · apply congrArg Real.sqrt
    rw [hc]
    simp [mat2Ring, firstColumnNorm]
    ring_nf
    rw [hε₀, hε₁]
    ring

/-- The explicit Euclidean KAN factors on `GL₂⁺(ℝ)` transform factor by
factor under conjugation by a diagonal sign matrix. -/
theorem real_gl2_pos_kan_signed_diagonal_equivariance
    {M : RealMat2} (hdet : 0 < Matrix.det M)
    (ε₀ ε₁ : ℝ) (hε₀ : ε₀ ^ 2 = 1) (hε₁ : ε₁ ^ 2 = 1) :
    let D : RealMat2 := mat2Ring ε₀ 0 0 ε₁
    realIwasawaK (D * M * D) = D * realIwasawaK M * D ∧
    realIwasawaA (D * M * D) = realIwasawaA M ∧
    realIwasawaN (D * M * D) = D * realIwasawaN M * D := by
  dsimp only
  let D : RealMat2 := mat2Ring ε₀ 0 0 ε₁
  have hInv := real_signed_diagonal_conjugation_invariants M ε₀ ε₁ hε₀ hε₁
  have hconj := real_signed_diagonal_conjugate_entries M ε₀ ε₁ hε₀ hε₁
  have hconjK := real_signed_diagonal_conjugate_entries (realIwasawaK M)
    ε₀ ε₁ hε₀ hε₁
  have hconjN := real_signed_diagonal_conjugate_entries (realIwasawaN M)
    ε₀ ε₁ hε₀ hε₁
  have hnormE : firstColumnNorm
      (mat2Ring (M 0 0) (ε₀ * ε₁ * M 0 1) (ε₀ * ε₁ * M 1 0) (M 1 1)) =
        firstColumnNorm M := by
    rw [← hconj]
    exact hInv.2
  have hdetE : Matrix.det
      (mat2Ring (M 0 0) (ε₀ * ε₁ * M 0 1) (ε₀ * ε₁ * M 1 0) (M 1 1)) =
        Matrix.det M := by
    rw [← hconj]
    exact hInv.1
  have hrpos : 0 < firstColumnNorm M := firstColumnNorm_pos hdet
  refine ⟨?_, ?_, ?_⟩
  · rw [hconj, hconjK]
    unfold realIwasawaK
    rw [hnormE]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mat2Ring, firstColumnNorm, hε₀, hε₁] <;>
      field_simp [ne_of_gt hrpos] <;> ring
  · rw [hconj]
    unfold realIwasawaA
    rw [hdetE, hnormE]
  · rw [hconj, hconjN]
    unfold realIwasawaN
    rw [hnormE]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mat2Ring, firstColumnNorm, hε₀, hε₁] <;>
      field_simp [ne_of_gt hrpos] <;> ring

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The central Weyl rescaling of an operator matrix. -/
def weylScale (c : ℂ) (A : Matrix n n ℂ) : Matrix n n ℂ := c • A

omit [DecidableEq n] in
@[simp] theorem trace_weylScale (c : ℂ) (A : Matrix n n ℂ) :
    Matrix.trace (weylScale c A) = c * Matrix.trace A := by
  simp [weylScale, Matrix.trace_smul, smul_eq_mul]

@[simp] theorem det_weylScale (c : ℂ) (A : Matrix n n ℂ) :
    (weylScale c A).det = c ^ Fintype.card n * A.det := by
  exact Matrix.det_smul A c

/-- Weyl scaling of a generator turns the trace into the determinant of its
exponential, by the existing unrestricted matrix determinant/trace theorem. -/
theorem det_exp_weylScale (c : ℂ) (A : Matrix n n ℂ) :
    (Matrix.det (NormedSpace.exp (weylScale c A))) =
      NormedSpace.exp (c * Matrix.trace A) := by
  calc
    Matrix.det (NormedSpace.exp (weylScale c A)) =
        NormedSpace.exp (Matrix.trace (weylScale c A)) :=
          InfoGeometry.Cocycle.MatrixDetExpTrace.det_exp_eq_exp_trace _
    _ = NormedSpace.exp (c * Matrix.trace A) := by
      simp [weylScale, Matrix.trace_smul, smul_eq_mul]

/-- Scalar and traceless operator components, normalized by the matrix size. -/
def tracePart (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (Matrix.trace A / (Fintype.card n : ℂ)) • (1 : Matrix n n ℂ)

def tracelessPart (A : Matrix n n ℂ) : Matrix n n ℂ := A - tracePart A

theorem trace_tracelessPart [Nonempty n] (A : Matrix n n ℂ) :
    Matrix.trace (tracelessPart A) = 0 := by
  have hcardNat : 0 < Fintype.card n := Fintype.card_pos_iff.mpr inferInstance
  have hcard : (Fintype.card n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hcardNat)
  simp only [tracelessPart, tracePart, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, smul_eq_mul]
  field_simp
  ring

theorem tracePart_add_tracelessPart (A : Matrix n n ℂ) :
    tracePart A + tracelessPart A = A := by
  simp [tracelessPart]

/-- Symmetric component of a real operator matrix. -/
def symmetricPart {n : Type*} (A : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (A + Aᵀ)

/-- Skew-symmetric component of a real operator matrix. -/
def skewPart {n : Type*} (A : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (A - Aᵀ)

theorem symmetric_skew_decomposition {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : symmetricPart A + skewPart A = A := by
  simp only [symmetricPart, skewPart, smul_add, smul_sub]
  module

@[simp] theorem transpose_symmetricPart {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : (symmetricPart A)ᵀ = symmetricPart A := by
  simp [symmetricPart, Matrix.transpose_add, add_comm]

@[simp] theorem transpose_skewPart {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : (skewPart A)ᵀ = -skewPart A := by
  simp [skewPart, sub_eq_add_neg]

/-- Congruence action used for the orthogonal symmetry action on operators. -/
def congruence {n : Type*} [Fintype n] (S A : Matrix n n ℝ) : Matrix n n ℝ :=
  S * A * Sᵀ

@[simp] theorem transpose_congruence {n : Type*} [Fintype n] [DecidableEq n]
    (S A : Matrix n n ℝ) : (congruence S A)ᵀ = congruence S Aᵀ := by
  simp [congruence, Matrix.transpose_mul, Matrix.transpose_transpose]
  noncomm_ring

@[simp] theorem congruence_add {n : Type*} [Fintype n]
    (S A B : Matrix n n ℝ) :
    congruence S (A + B) = congruence S A + congruence S B := by
  simp [congruence, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

@[simp] theorem congruence_sub {n : Type*} [Fintype n]
    (S A B : Matrix n n ℝ) :
    congruence S (A - B) = congruence S A - congruence S B := by
  simp [congruence, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

@[simp] theorem congruence_smul {n : Type*} [Fintype n]
    (S : Matrix n n ℝ) (c : ℝ) (A : Matrix n n ℝ) :
    congruence S (c • A) = c • congruence S A := by
  simp [congruence, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem congruence_symmetricPart {n : Type*} [Fintype n] [DecidableEq n]
    (S A : Matrix n n ℝ) :
    congruence S (symmetricPart A) = symmetricPart (congruence S A) := by
  simp [symmetricPart]

theorem congruence_skewPart {n : Type*} [Fintype n] [DecidableEq n]
    (S A : Matrix n n ℝ) :
    congruence S (skewPart A) = skewPart (congruence S A) := by
  simp [skewPart]

/-- Weyl scalar component of a real operator matrix in finite dimension. -/
def realWeylScalePart {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) : Matrix n n ℝ :=
  (Matrix.trace A / (Fintype.card n : ℝ)) • (1 : Matrix n n ℝ)

/-- Traceless symmetric strain in the real Cartan decomposition. -/
def realTracelessSymmetricPart {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) : Matrix n n ℝ :=
  symmetricPart A - realWeylScalePart A

/-- The normalized scalar part has the same trace as the original operator. -/
theorem trace_realWeylScalePart {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (A : Matrix n n ℝ) :
    Matrix.trace (realWeylScalePart A) = Matrix.trace A := by
  have hcard : (Fintype.card n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr inferInstance))
  simp only [realWeylScalePart, Matrix.trace_smul, Matrix.trace_one,
    smul_eq_mul]
  field_simp

/-- Symmetrization preserves the trace of a real operator matrix. -/
theorem trace_symmetricPart {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    Matrix.trace (symmetricPart A) = Matrix.trace A := by
  simp [symmetricPart, Matrix.trace_smul, Matrix.trace_add]
  ring

/-- The symmetric strain has zero trace, in every finite dimension. -/
theorem trace_realTracelessSymmetricPart {n : Type*} [Fintype n]
    [DecidableEq n] [Nonempty n] (A : Matrix n n ℝ) :
    Matrix.trace (realTracelessSymmetricPart A) = 0 := by
  rw [realTracelessSymmetricPart, Matrix.trace_sub,
    trace_symmetricPart, trace_realWeylScalePart]
  exact sub_self _

/-- The skew part has zero trace, in every finite dimension. -/
theorem trace_skewPart {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : Matrix.trace (skewPart A) = 0 := by
  simp [skewPart, Matrix.trace_smul, Matrix.trace_sub]

/-- Trace is invariant under orthogonal congruence. -/
theorem trace_congruence_of_orthogonal {n : Type*} [Fintype n] [DecidableEq n]
    {S A : Matrix n n ℝ} (hS : Sᵀ * S = 1) :
    Matrix.trace (congruence S A) = Matrix.trace A := by
  unfold congruence
  calc
    Matrix.trace (S * A * Sᵀ) = Matrix.trace (Sᵀ * (S * A)) := by
      rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((Sᵀ * S) * A) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace A := by rw [hS]; simp

/-- The Weyl scalar component is fixed by orthogonal congruence. -/
theorem congruence_realWeylScalePart {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] {S A : Matrix n n ℝ}
    (hS' : S * Sᵀ = 1) :
    congruence S (realWeylScalePart A) = realWeylScalePart A := by
  rw [realWeylScalePart, congruence_smul]
  have h_id : congruence S (1 : Matrix n n ℝ) = 1 := by
    unfold congruence
    simp [hS']
  rw [h_id]

/-- The Weyl scale of an operator is invariant under orthogonal change of frame. -/
theorem realWeylScalePart_congruence {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] {S A : Matrix n n ℝ} (hS : Sᵀ * S = 1) :
    realWeylScalePart (congruence S A) = realWeylScalePart A := by
  rw [realWeylScalePart, realWeylScalePart, trace_congruence_of_orthogonal hS]

/-- The full three-way Cartan split is equivariant under the orthogonal
congruence action.  In particular its Weyl component is fixed, while the
traceless symmetric and skew components are transported by the same action. -/
theorem real_weyl_cartan_congruence_equivariance
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {S A : Matrix n n ℝ} (hS : Sᵀ * S = 1)
    (hS' : S * Sᵀ = 1) :
    congruence S (realWeylScalePart A) = realWeylScalePart A ∧
    congruence S (realTracelessSymmetricPart A) =
      realTracelessSymmetricPart (congruence S A) ∧
    Matrix.trace (realTracelessSymmetricPart A) = 0 ∧
    congruence S (skewPart A) = skewPart (congruence S A) ∧
    Matrix.trace (skewPart A) = 0 ∧
    realWeylScalePart A + realTracelessSymmetricPart A + skewPart A = A := by
  refine ⟨congruence_realWeylScalePart hS', ?_,
    trace_realTracelessSymmetricPart A, congruence_skewPart S A,
    trace_skewPart A, ?_⟩
  · change congruence S (symmetricPart A - realWeylScalePart A) =
      symmetricPart (congruence S A) - realWeylScalePart (congruence S A)
    rw [congruence_sub, congruence_symmetricPart,
      congruence_realWeylScalePart hS', realWeylScalePart_congruence hS]
  · change realWeylScalePart A +
      (symmetricPart A - realWeylScalePart A) + skewPart A = A
    calc
      realWeylScalePart A + (symmetricPart A - realWeylScalePart A) + skewPart A =
          symmetricPart A + skewPart A := by abel
      _ = A := symmetric_skew_decomposition A

/-- The three Cartan components are equivariant under conformal-orthogonal
similarity.  Scaling an orthogonal frame by a nonzero scalar does not change
its conjugation action, so the result follows from the orthogonal congruence
theorem after identifying `G * A * H` with `S * A * Sᵀ`. -/
theorem real_weyl_cartan_conformal_conjugation_equivariance
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {G H : Matrix n n ℝ} {c : ℝ}
    (hc : c ≠ 0) (hGH : G * H = 1)
    (hco : Gᵀ * G = c ^ 2 • (1 : Matrix n n ℝ))
    (A : Matrix n n ℝ) :
    G * realWeylScalePart A * H = realWeylScalePart A ∧
    G * realTracelessSymmetricPart A * H =
      realTracelessSymmetricPart (G * A * H) ∧
    G * skewPart A * H = skewPart (G * A * H) ∧
    realWeylScalePart A + realTracelessSymmetricPart A + skewPart A = A := by
  let S : Matrix n n ℝ := (1 / c) • G
  have hH : H = (1 / c ^ 2) • Gᵀ := by
    calc
      H = ((1 / c ^ 2) • (Gᵀ * G)) * H := by
        rw [hco, smul_smul]
        have hc' : (1 / c ^ 2) * c ^ 2 = 1 := by field_simp [hc]
        rw [hc', one_smul, one_mul]
      _ = (1 / c ^ 2) • (Gᵀ * (G * H)) := by
        rw [Matrix.smul_mul, Matrix.mul_assoc]
      _ = (1 / c ^ 2) • Gᵀ := by rw [hGH, mul_one]
  have hGGt : G * Gᵀ = c ^ 2 • (1 : Matrix n n ℝ) := by
    have hscaled : (1 / c ^ 2) • (G * Gᵀ) = 1 := by
      calc
        (1 / c ^ 2) • (G * Gᵀ) = G * ((1 / c ^ 2) • Gᵀ) := by
          rw [Matrix.mul_smul]
        _ = G * H := by rw [hH]
        _ = 1 := hGH
    calc
      G * Gᵀ = (c ^ 2) • ((1 / c ^ 2) • (G * Gᵀ)) := by
        rw [smul_smul]
        have hc' : c ^ 2 * (1 / c ^ 2) = 1 := by field_simp [hc]
        rw [hc', one_smul]
      _ = c ^ 2 • (1 : Matrix n n ℝ) := by rw [hscaled]
  have hS : Sᵀ * S = 1 := by
    dsimp [S]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hco]
    have hc' : (1 / c) * (1 / c) * c ^ 2 = 1 := by field_simp [hc]
    rw [smul_smul, hc', one_smul]
  have hS' : S * Sᵀ = 1 := by
    dsimp [S]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hGGt]
    have hc' : (1 / c) * (1 / c) * c ^ 2 = 1 := by field_simp [hc]
    rw [smul_smul, hc', one_smul]
  have hconj (X : Matrix n n ℝ) : G * X * H = congruence S X := by
    rw [hH]
    dsimp [congruence, S]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1
    field_simp [hc]
  rcases real_weyl_cartan_congruence_equivariance hS hS' with
    ⟨hW, hSym, _, hSkew, _, hSplit⟩
  refine ⟨?_, ?_, ?_, hSplit⟩
  · rw [hconj]; exact hW
  · calc
      G * realTracelessSymmetricPart A * H =
          congruence S (realTracelessSymmetricPart A) := hconj _
      _ = realTracelessSymmetricPart (congruence S A) := hSym
      _ = realTracelessSymmetricPart (G * A * H) := by rw [hconj A]
  · calc
      G * skewPart A * H = congruence S (skewPart A) := hconj _
      _ = skewPart (congruence S A) := hSkew
      _ = skewPart (G * A * H) := by rw [hconj A]

/-- The Weyl, traceless symmetric, and skew components are pairwise
orthogonal for the repository's native Frobenius inner product. This uses
the actual finite-dimensional real matrix algebra and its trace pairing. -/
theorem real_weyl_cartan_frobenius_orthogonality
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) :
    inner ℝ (realWeylScalePart A) (realTracelessSymmetricPart A) = 0 ∧
    inner ℝ (realWeylScalePart A) (skewPart A) = 0 ∧
    inner ℝ (realTracelessSymmetricPart A) (skewPart A) = 0 := by
  have hsym : (realTracelessSymmetricPart A)ᵀ =
      realTracelessSymmetricPart A := by
    simp [realTracelessSymmetricPart, symmetricPart, realWeylScalePart,
      Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.transpose_add, add_comm]
  have hskew : (skewPart A)ᵀ = -skewPart A := by
    simp [skewPart, Matrix.transpose_smul, Matrix.transpose_sub,
      sub_eq_add_neg]
  have htraceSym : Matrix.trace (realTracelessSymmetricPart A) = 0 :=
    trace_realTracelessSymmetricPart A
  have htraceSkew : Matrix.trace (skewPart A) = 0 := trace_skewPart A
  have hws : inner ℝ (realWeylScalePart A)
      (realTracelessSymmetricPart A) = 0 := by
    rw [InfoGeometry.Canonical.RealLieJordanGeometry.inner_eq_trace_transpose_mul]
    let c := Matrix.trace A / (Fintype.card n : ℝ)
    change Matrix.trace ((c • (1 : Matrix n n ℝ))ᵀ *
      realTracelessSymmetricPart A) = 0
    rw [Matrix.transpose_smul, Matrix.transpose_one, smul_mul_assoc,
      one_mul, Matrix.trace_smul, htraceSym]
    simp
  have hwk : inner ℝ (realWeylScalePart A) (skewPart A) = 0 := by
    rw [InfoGeometry.Canonical.RealLieJordanGeometry.inner_eq_trace_transpose_mul]
    let c := Matrix.trace A / (Fintype.card n : ℝ)
    change Matrix.trace ((c • (1 : Matrix n n ℝ))ᵀ * skewPart A) = 0
    rw [Matrix.transpose_smul, Matrix.transpose_one, smul_mul_assoc,
      one_mul, Matrix.trace_smul, htraceSkew]
    simp
  have hsk : inner ℝ (realTracelessSymmetricPart A) (skewPart A) = 0 := by
    rw [InfoGeometry.Canonical.RealLieJordanGeometry.inner_eq_trace_transpose_mul,
      hsym]
    let q := Matrix.trace (realTracelessSymmetricPart A * skewPart A)
    have hq : q = -q := by
      dsimp [q]
      calc
        Matrix.trace (realTracelessSymmetricPart A * skewPart A) =
            Matrix.trace ((realTracelessSymmetricPart A * skewPart A)ᵀ) := by
              rw [Matrix.trace_transpose]
        _ = Matrix.trace (-skewPart A * realTracelessSymmetricPart A) := by
          simp only [Matrix.transpose_mul, hsym, hskew]
        _ = -Matrix.trace (skewPart A * realTracelessSymmetricPart A) := by
          simp [Matrix.neg_mul]
        _ = -Matrix.trace (realTracelessSymmetricPart A * skewPart A) := by
          rw [Matrix.trace_mul_comm]
    dsimp [q] at hq ⊢
    linarith
  exact ⟨hws, hwk, hsk⟩

/-- Pythagoras for the Weyl/Cartan split: the squared Frobenius norm is the
sum of the scale, symmetric-strain, and skew-spin contributions. -/
theorem real_weyl_cartan_frobenius_pythagorean
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) :
    ‖A‖ ^ 2 = (Matrix.trace A) ^ 2 / (Fintype.card n : ℝ) +
      ‖realTracelessSymmetricPart A‖ ^ 2 + ‖skewPart A‖ ^ 2 := by
  rcases real_weyl_cartan_frobenius_orthogonality A with ⟨hws, hwk, hsk⟩
  have hsplit : A = realWeylScalePart A +
      realTracelessSymmetricPart A + skewPart A := by
    calc
      A = symmetricPart A + skewPart A :=
        (symmetric_skew_decomposition A).symm
      _ = realWeylScalePart A +
          realTracelessSymmetricPart A + skewPart A := by
            rw [realTracelessSymmetricPart]
            abel
  have hxy : inner ℝ (realWeylScalePart A +
      realTracelessSymmetricPart A) (skewPart A) = 0 := by
    rw [inner_add_left, hwk, hsk, zero_add]
  have hnorm : ‖A‖ ^ 2 =
      ‖realWeylScalePart A‖ ^ 2 +
        ‖realTracelessSymmetricPart A‖ ^ 2 + ‖skewPart A‖ ^ 2 := by
    calc
      ‖A‖ ^ 2 = ‖realWeylScalePart A +
          realTracelessSymmetricPart A + skewPart A‖ ^ 2 :=
            congrArg (fun X : Matrix n n ℝ => ‖X‖ ^ 2) hsplit
      _ = ‖realWeylScalePart A + realTracelessSymmetricPart A‖ ^ 2 +
          ‖skewPart A‖ ^ 2 :=
            by simpa [pow_two] using
              (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
                (realWeylScalePart A + realTracelessSymmetricPart A)
                (skewPart A) hxy)
      _ = ‖realWeylScalePart A‖ ^ 2 +
          ‖realTracelessSymmetricPart A‖ ^ 2 + ‖skewPart A‖ ^ 2 := by
            simpa [pow_two] using
              (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
                (realWeylScalePart A) (realTracelessSymmetricPart A) hws)
  have hw_norm : ‖realWeylScalePart A‖ ^ 2 =
      (Matrix.trace A) ^ 2 / (Fintype.card n : ℝ) := by
    have hnorm_sq := InnerProductSpace.norm_sq_eq_re_inner
      (𝕜 := ℝ) (realWeylScalePart A)
    rw [hnorm_sq,
      InfoGeometry.Canonical.RealLieJordanGeometry.inner_eq_trace_transpose_mul]
    simp only [realWeylScalePart, Matrix.transpose_smul, Matrix.transpose_one,
      smul_mul_assoc, one_mul, Matrix.trace_smul, smul_eq_mul,
      RCLike.re_to_real]
    rw [Matrix.trace_one]
    have hcard : (Fintype.card n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr inferInstance))
    field_simp
  linarith [hnorm, hw_norm]

/-- Similarity action by an actual general-linear matrix. -/
def conjugate (g : (Matrix n n ℂ)ˣ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (g : Matrix n n ℂ) * A * (↑g⁻¹ : Matrix n n ℂ)

@[simp] theorem trace_conjugate (g : (Matrix n n ℂ)ˣ) (A : Matrix n n ℂ) :
    Matrix.trace (conjugate g A) = Matrix.trace A := by
  exact Matrix.trace_units_conj g A

@[simp] theorem det_conjugate (g : (Matrix n n ℂ)ˣ) (A : Matrix n n ℂ) :
    (conjugate g A).det = A.det := by
  exact Matrix.det_units_conj g A

theorem conjugate_tracePart (g : (Matrix n n ℂ)ˣ) (A : Matrix n n ℂ) :
    conjugate g (tracePart A) = tracePart A := by
  simp [conjugate, tracePart]

theorem conjugate_tracelessPart (g : (Matrix n n ℂ)ˣ) (A : Matrix n n ℂ) :
    conjugate g (tracelessPart A) = tracelessPart (conjugate g A) := by
  have hsub : conjugate g (A - tracePart A) =
      conjugate g A - conjugate g (tracePart A) := by
    simp [conjugate, Matrix.mul_sub, Matrix.sub_mul]
  have htp : tracePart (conjugate g A) = tracePart A := by
    simp [tracePart]
  rw [tracelessPart, hsub, conjugate_tracePart, tracelessPart, htp]

/-- The KAN product remains a factorization after simultaneous conjugation. -/
theorem conjugate_kanProduct (g : (Matrix (Fin 2) (Fin 2) ℂ)ˣ)
    (θ lam t : ℂ) :
    (g : Matrix (Fin 2) (Fin 2) ℂ) *
        InfoGeometry.Dynamics.KanDecomposition.kanProduct θ lam t *
        (↑g⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) =
      ((g : Matrix (Fin 2) (Fin 2) ℂ) *
          InfoGeometry.Dynamics.KanDecomposition.componentK θ *
          (↑g⁻¹ : Matrix (Fin 2) (Fin 2) ℂ)) *
        ((g : Matrix (Fin 2) (Fin 2) ℂ) *
          InfoGeometry.Dynamics.KanDecomposition.componentA lam *
          (↑g⁻¹ : Matrix (Fin 2) (Fin 2) ℂ)) *
        ((g : Matrix (Fin 2) (Fin 2) ℂ) *
          InfoGeometry.Dynamics.KanDecomposition.componentN t *
          (↑g⁻¹ : Matrix (Fin 2) (Fin 2) ℂ)) := by
  simp [InfoGeometry.Dynamics.KanDecomposition.kanProduct,
    Matrix.mul_assoc]

/-- A transported orthogonal factor is an isometry for the transported metric.

If `H` is the inverse frame change (`H * G = G * H = 1`), then `Hᵀ * H`
is the metric in the new frame and `G * K * H` is orthogonal relative to it.
This is the metric-covariant statement available for arbitrary invertible
changes of frame; it does not assert Euclidean polar equivariance for a
non-orthogonal `G`. -/
theorem conjugate_orthogonal_isometry_for_pushforward_metric
    {n : Type*} [Fintype n] [DecidableEq n]
    (G H K : Matrix n n ℝ)
    (hHG : H * G = 1)
    (hK : Kᵀ * K = 1) :
    (G * K * H)ᵀ * (Hᵀ * H) * (G * K * H) = Hᵀ * H := by
  have htrans : Gᵀ * Hᵀ = 1 := by
    simpa using congrArg Matrix.transpose hHG
  calc
    (G * K * H)ᵀ * (Hᵀ * H) * (G * K * H) =
        Hᵀ * (Kᵀ * (Gᵀ * Hᵀ) * (H * G) * K) * H := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
          noncomm_ring
    _ = Hᵀ * (Kᵀ * K) * H := by
          rw [htrans, hHG]
          noncomm_ring
    _ = Hᵀ * H := by rw [hK]; noncomm_ring

/-- A full polar pair transported by an arbitrary change of frame remains a
polar pair relative to the pushed-forward metric. This records the metric
isometry of the orthogonal factor, metric self-adjointness and Gram transport
of the symmetric factor, and preservation of the factorization. -/
theorem polar_pair_conjugation_for_pushforward_metric
    {n : Type*} [Fintype n] [DecidableEq n]
    (G H K P : Matrix n n ℝ)
    (hHG : H * G = 1)
    (hK : Kᵀ * K = 1) (hP : Pᵀ = P) :
    let Q := Hᵀ * H
    let K' := G * K * H
    let P' := G * P * H
    K'ᵀ * Q * K' = Q ∧
    P'ᵀ * Q = Q * P' ∧
    P'ᵀ * Q * P' = Hᵀ * (Pᵀ * P) * H ∧
    G * (K * P) * H = K' * P' := by
  dsimp only
  have hGtHt : Gᵀ * Hᵀ = 1 := by
    simpa using congrArg Matrix.transpose hHG
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      Hᵀ * (Kᵀ * Gᵀ) * (Hᵀ * H) * (G * K * H) =
          Hᵀ * (Kᵀ * (Gᵀ * Hᵀ) * (H * G) * K) * H := by noncomm_ring
      _ = Hᵀ * (Kᵀ * K) * H := by rw [hGtHt, hHG]; noncomm_ring
      _ = Hᵀ * H := by rw [hK]; noncomm_ring
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      Hᵀ * (Pᵀ * Gᵀ) * (Hᵀ * H) = Hᵀ * Pᵀ * (Gᵀ * Hᵀ) * H := by noncomm_ring
      _ = Hᵀ * P * H := by rw [hP, hGtHt]; noncomm_ring
      _ = Hᵀ * (H * G) * P * H := by rw [hHG]; noncomm_ring
      _ = Hᵀ * H * (G * P * H) := by noncomm_ring
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      Hᵀ * (Pᵀ * Gᵀ) * (Hᵀ * H) * (G * P * H) =
          Hᵀ * (Pᵀ * (Gᵀ * Hᵀ) * (H * G) * P) * H := by noncomm_ring
      _ = Hᵀ * (Pᵀ * P) * H := by rw [hGtHt, hHG]; noncomm_ring
  · calc
      G * (K * P) * H = G * K * (H * G) * P * H := by rw [hHG]; noncomm_ring
      _ = (G * K * H) * (G * P * H) := by noncomm_ring

/-- Positive definiteness of the stretch factor is transported as positivity
of its metric-lowered operator. The injectivity hypothesis is the concrete
finite-dimensional invertibility condition needed by the congruence theorem. -/
theorem polar_stretch_positive_for_pushforward_metric
    {n : Type*} [Fintype n] [DecidableEq n]
    (G H P : Matrix n n ℝ) (hHG : H * G = 1)
    (hP : P.PosDef) (hH : Function.Injective H.mulVec) :
    (Hᵀ * H * (G * P * H)).PosDef := by
  have hcong : (Hᵀ * P * H).PosDef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.PosDef.conjTranspose_mul_mul_same hP hH)
  have heq : Hᵀ * H * (G * P * H) = Hᵀ * P * H := by
    calc
      Hᵀ * H * (G * P * H) = Hᵀ * (H * G) * P * H := by noncomm_ring
      _ = Hᵀ * P * H := by rw [hHG]; noncomm_ring
  rw [heq]
  exact hcong

/-! ## KAN decomposition transported with its metric and flag -/

/-- Change from the reference frame to the transported frame. H is the
inverse frame map and G is the forward frame map. -/
def framePush (G H X : RealMat2) : RealMat2 := G * X * H

/-- Pull an operator and its flag data back to the reference frame. -/
def framePull (H G X : RealMat2) : RealMat2 := H * X * G

/-- KAN factors in the transported frame, obtained from the standard factors
of the pulled-back operator. -/
def relativeIwasawaK (G H M : RealMat2) : RealMat2 :=
  framePush G H (realIwasawaK (framePull H G M))

def relativeIwasawaA (G H M : RealMat2) : RealMat2 :=
  framePush G H (realIwasawaA (framePull H G M))

def relativeIwasawaN (G H M : RealMat2) : RealMat2 :=
  framePush G H (realIwasawaN (framePull H G M))

/-- The explicit first-column-normalized compact factor has positive
orientation, so it lies in SO(2), not just O(2). -/
theorem real_iwasawaK_det_one {M : RealMat2}
    (hdet : 0 < Matrix.det M) :
    Matrix.det (realIwasawaK M) = 1 := by
  have hr : 0 < firstColumnNorm M := firstColumnNorm_pos hdet
  have hr0 : firstColumnNorm M ≠ 0 := ne_of_gt hr
  have hrsq : firstColumnNorm M ^ 2 = (M 0 0) ^ 2 + (M 1 0) ^ 2 :=
    Real.sq_sqrt (by positivity)
  simp [realIwasawaK, mat2Ring, Matrix.det_fin_two]
  field_simp [hr0]
  nlinarith [hrsq]

/-- The compact factor remains special orthogonal after frame transport:
its determinant is invariant under conjugation by the frame isomorphism. -/
theorem relative_iwasawaK_det_one
    (G H M : RealMat2) (hGH : G * H = 1)
    (hdet : 0 < Matrix.det (framePull H G M)) :
    Matrix.det (relativeIwasawaK G H M) = 1 := by
  have hGHdet : Matrix.det G * Matrix.det H = 1 := by
    have h := congrArg Matrix.det hGH
    simpa [Matrix.det_mul] using h
  rw [relativeIwasawaK, framePush, Matrix.det_mul, Matrix.det_mul,
    real_iwasawaK_det_one hdet]
  calc
    Matrix.det G * 1 * Matrix.det H =
        Matrix.det G * Matrix.det H := by ring
    _ = 1 := hGHdet

/-- Existence of KAN factors in a pushed-forward flag. The hypotheses say
that G and H are inverse frame maps and the pulled-back operator is in
GL₂⁺. Diagonal and upper-unipotent conditions are stated after pullback,
which is the precise meaning of the transported flag. -/
theorem relative_iwasawa_factorization
    (G H M : RealMat2) (hHG : H * G = 1) (hGH : G * H = 1)
    (hdet : 0 < Matrix.det (framePull H G M)) :
    relativeIwasawaK G H M * relativeIwasawaA G H M *
        relativeIwasawaN G H M = M ∧
    (relativeIwasawaK G H M)ᵀ * (Hᵀ * H) *
        relativeIwasawaK G H M = Hᵀ * H ∧
    0 < (framePull H G (relativeIwasawaA G H M)) 0 0 ∧
    0 < (framePull H G (relativeIwasawaA G H M)) 1 1 ∧
    (framePull H G (relativeIwasawaA G H M)) 0 1 = 0 ∧
    (framePull H G (relativeIwasawaA G H M)) 1 0 = 0 ∧
    (framePull H G (relativeIwasawaN G H M)) 0 0 = 1 ∧
    (framePull H G (relativeIwasawaN G H M)) 1 1 = 1 ∧
    (framePull H G (relativeIwasawaN G H M)) 1 0 = 0 := by
  let M₀ := framePull H G M
  have hstd := real_gl2_pos_iwasawa_factorization hdet
  rcases hstd with ⟨hK, hA₀, hA₁, hA₀₁, hA₁₀, hN₀₀, hN₁₁, hN₁₀, hfact⟩
  have hfactor : framePush G H M₀ = M := by
    dsimp [framePush, M₀, framePull]
    calc G * (H * M * G) * H = (G * H) * M * (G * H) := by noncomm_ring
      _ = M := by rw [hGH]; noncomm_ring
  have hframe_mul (X Y : RealMat2) :
      framePush G H X * framePush G H Y = framePush G H (X * Y) := by
    dsimp [framePush]
    calc
      (G * X * H) * (G * Y * H) =
          G * X * (H * G) * Y * H := by noncomm_ring
      _ = G * (X * Y) * H := by rw [hHG]; noncomm_ring
  have hpush_factor :
      framePush G H (realIwasawaK M₀) *
        framePush G H (realIwasawaA M₀) *
        framePush G H (realIwasawaN M₀) = framePush G H M₀ := by
    calc
      framePush G H (realIwasawaK M₀) *
          framePush G H (realIwasawaA M₀) *
          framePush G H (realIwasawaN M₀) =
          framePush G H (realIwasawaK M₀ * realIwasawaA M₀) *
            framePush G H (realIwasawaN M₀) := by rw [hframe_mul]
      _ = framePush G H
          (realIwasawaK M₀ * realIwasawaA M₀ * realIwasawaN M₀) :=
            hframe_mul _ _
      _ = framePush G H M₀ := by rw [hfact]
  have hpull_A : framePull H G (framePush G H (realIwasawaA M₀)) =
      realIwasawaA M₀ := by
    dsimp [framePull, framePush]
    calc
      H * (G * realIwasawaA M₀ * H) * G =
          (H * G) * realIwasawaA M₀ * (H * G) := by noncomm_ring
      _ = realIwasawaA M₀ := by rw [hHG]; noncomm_ring
  have hpull_N : framePull H G (framePush G H (realIwasawaN M₀)) =
      realIwasawaN M₀ := by
    dsimp [framePull, framePush]
    calc
      H * (G * realIwasawaN M₀ * H) * G =
          (H * G) * realIwasawaN M₀ * (H * G) := by noncomm_ring
      _ = realIwasawaN M₀ := by rw [hHG]; noncomm_ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [relativeIwasawaK, relativeIwasawaA, relativeIwasawaN, M₀] using
      hpush_factor.trans hfactor
  · simpa [relativeIwasawaK, framePush, framePull, M₀] using
      conjugate_orthogonal_isometry_for_pushforward_metric G H
        (realIwasawaK M₀) hHG hK
  · simpa [relativeIwasawaA, hpull_A, M₀] using hA₀
  · simpa [relativeIwasawaA, hpull_A, M₀] using hA₁
  · simpa [relativeIwasawaA, hpull_A, M₀] using hA₀₁
  · simpa [relativeIwasawaA, hpull_A, M₀] using hA₁₀
  · simpa [relativeIwasawaN, hpull_N, M₀] using hN₀₀
  · simpa [relativeIwasawaN, hpull_N, M₀] using hN₁₁
  · simpa [relativeIwasawaN, hpull_N, M₀] using hN₁₀

/-- Uniqueness of transported KAN factors reduces to the standard real
GL₂⁺ uniqueness theorem by pulling both factorizations back to the reference
frame. Conditions state orthogonality, positive diagonal normalization, and
upper-unipotent normalization in that pulled-back flag. -/
theorem relative_iwasawa_unique
    (G H M K₁ K₂ A₁ A₂ N₁ N₂ : RealMat2)
    (hGH : G * H = 1)
    (hfact₁ : K₁ * A₁ * N₁ = M) (hfact₂ : K₂ * A₂ * N₂ = M)
    (hK₁ : (framePull H G K₁)ᵀ * framePull H G K₁ = 1)
    (hK₂ : (framePull H G K₂)ᵀ * framePull H G K₂ = 1)
    (hdetK₁ : Matrix.det (framePull H G K₁) = 1)
    (hdetK₂ : Matrix.det (framePull H G K₂) = 1)
    (hA₁₀ : 0 < (framePull H G A₁) 0 0)
    (hA₁₀₁ : (framePull H G A₁) 0 1 = 0)
    (hA₁₁₀ : (framePull H G A₁) 1 0 = 0)
    (hA₂₀ : 0 < (framePull H G A₂) 0 0)
    (hA₂₀₁ : (framePull H G A₂) 0 1 = 0)
    (hA₂₁₀ : (framePull H G A₂) 1 0 = 0)
    (hN₁₀₀ : (framePull H G N₁) 0 0 = 1)
    (hN₁₁₁ : (framePull H G N₁) 1 1 = 1)
    (hN₁₁₀ : (framePull H G N₁) 1 0 = 0)
    (hN₂₀₀ : (framePull H G N₂) 0 0 = 1)
    (hN₂₁₁ : (framePull H G N₂) 1 1 = 1)
    (hN₂₁₀ : (framePull H G N₂) 1 0 = 0) :
    K₁ = K₂ ∧ A₁ = A₂ ∧ N₁ = N₂ := by
  have hpull_prod (K A N : RealMat2) :
      framePull H G (K * A * N) =
        framePull H G K * framePull H G A * framePull H G N := by
    dsimp [framePull]
    calc
      H * (K * A * N) * G =
          H * K * (G * H) * A * (G * H) * N * G := by
            rw [hGH]
            noncomm_ring
      _ = (H * K * G) * (H * A * G) * (H * N * G) := by noncomm_ring
  have hpull_fact₁ : framePull H G M =
      framePull H G K₁ * framePull H G A₁ * framePull H G N₁ := by
    calc
      framePull H G M = framePull H G (K₁ * A₁ * N₁) := by rw [hfact₁]
      _ = _ := hpull_prod K₁ A₁ N₁
  have hpull_fact₂ : framePull H G M =
      framePull H G K₂ * framePull H G A₂ * framePull H G N₂ := by
    calc
      framePull H G M = framePull H G (K₂ * A₂ * N₂) := by rw [hfact₂]
      _ = _ := hpull_prod K₂ A₂ N₂
  have hstd := real_gl2_pos_kan_unique hpull_fact₁.symm hpull_fact₂.symm
    hK₁ hK₂ hdetK₁ hdetK₂
    hA₁₀ hA₁₀₁ hA₁₁₀ hA₂₀ hA₂₀₁ hA₂₁₀
    hN₁₀₀ hN₁₁₁ hN₁₁₀ hN₂₀₀ hN₂₁₁ hN₂₁₀
  rcases hstd with ⟨hK, hA, hN⟩
  have hrecover (X Y : RealMat2)
      (hXY : framePull H G X = framePull H G Y) : X = Y := by
    have h := congrArg (fun Z : RealMat2 => G * Z * H) hXY
    dsimp [framePull] at h
    calc
      X = (G * H) * X * (G * H) := by rw [hGH]; noncomm_ring
      _ = G * (H * X * G) * H := by noncomm_ring
      _ = G * (H * Y * G) * H := h
      _ = (G * H) * Y * (G * H) := by noncomm_ring
      _ = Y := by rw [hGH]; noncomm_ring
  exact ⟨hrecover K₁ K₂ hK, hrecover A₁ A₂ hA, hrecover N₁ N₂ hN⟩

/-- Orthogonal conjugation transports the exact polar data carried by the
repository's `PolarDecomposition` structure. -/
def orthogonalConjugatePolar {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (S : Matrix n n ℝ) (hSS : S * Sᵀ = 1)
    (hTS : Sᵀ * S = 1)
    (D : InfoGeometry.Optimization.PolarDecomposition A) :
    InfoGeometry.Optimization.PolarDecomposition (S * A * Sᵀ) where
  U := S * D.U * Sᵀ
  P := S * D.P * Sᵀ
  decomp := by
    have h := congrArg (fun X : Matrix n n ℝ => S * X * Sᵀ) D.decomp
    have hfact :
        (S * D.P * Sᵀ) * (S * D.U * Sᵀ) = S * (D.P * D.U) * Sᵀ := by
      calc
        (S * D.P * Sᵀ) * (S * D.U * Sᵀ) =
            S * D.P * (Sᵀ * S) * D.U * Sᵀ := by noncomm_ring
        _ = S * (D.P * D.U) * Sᵀ := by rw [hTS]; noncomm_ring
    calc S * A * Sᵀ = S * (D.P * D.U) * Sᵀ := by simpa using h
      _ = (S * D.P * Sᵀ) * (S * D.U * Sᵀ) := hfact.symm
  unitary := by
    calc (S * D.U * Sᵀ) * (S * D.U * Sᵀ)ᵀ
        = S * (D.U * D.Uᵀ) * Sᵀ := by
            simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
            calc
              S * D.U * Sᵀ * (S * (D.Uᵀ * Sᵀ)) =
                  S * D.U * (Sᵀ * S) * D.Uᵀ * Sᵀ := by noncomm_ring
              _ = S * (D.U * D.Uᵀ) * Sᵀ := by rw [hTS]; noncomm_ring
      _ = 1 := by rw [D.unitary]; simp [hSS]
  self_adjoint := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [D.self_adjoint]
    noncomm_ring

section RealTwoByTwoWeylCartan

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ

/-- The Weyl (scalar) component of a real two-by-two matrix. -/
def weylPart2 (X : Mat2R) : Mat2R :=
  (Matrix.trace X / 2) • (1 : Mat2R)

/-- Traceless symmetric component of the real two-by-two Cartan split. -/
def symTracelessPart2 (X : Mat2R) : Mat2R :=
  !![ (X 0 0 - X 1 1) / 2, (X 0 1 + X 1 0) / 2;
      (X 0 1 + X 1 0) / 2, -(X 0 0 - X 1 1) / 2 ]

/-- Skew-symmetric component of the real two-by-two Cartan split. -/
def skewPart2 (X : Mat2R) : Mat2R :=
  !![0, (X 0 1 - X 1 0) / 2;
      -(X 0 1 - X 1 0) / 2, 0]

/-- The actual three-term real `gl₂` split, including trace, symmetry, and skewness. -/
theorem real_twoByTwo_weyl_cartan_split (X : Mat2R) :
    X = weylPart2 X + symTracelessPart2 X + skewPart2 X ∧
    Matrix.trace (symTracelessPart2 X) = 0 ∧
    (symTracelessPart2 X)ᵀ = symTracelessPart2 X ∧
    Matrix.trace (skewPart2 X) = 0 ∧
    (skewPart2 X)ᵀ = -skewPart2 X ∧
    Matrix.trace ((weylPart2 X)ᵀ * symTracelessPart2 X) = 0 ∧
    Matrix.trace ((weylPart2 X)ᵀ * skewPart2 X) = 0 ∧
    Matrix.trace ((symTracelessPart2 X)ᵀ * skewPart2 X) = 0 ∧
    Matrix.trace (Xᵀ * X) = (Matrix.trace X) ^ 2 / 2 +
      Matrix.trace ((symTracelessPart2 X)ᵀ * symTracelessPart2 X) +
      Matrix.trace ((skewPart2 X)ᵀ * skewPart2 X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2Ring <;> simp [weylPart2, symTracelessPart2, skewPart2] <;> ring
  · simp [symTracelessPart2, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    ring
  · apply ext_fin2Ring <;> simp [symTracelessPart2, Matrix.transpose_apply]
  · simp [skewPart2, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  · apply ext_fin2Ring <;> simp [skewPart2, Matrix.transpose_apply] <;> ring
  · simp [weylPart2, symTracelessPart2, Matrix.trace, Matrix.diag,
      Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · simp [weylPart2, skewPart2, Matrix.trace, Matrix.diag,
      Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · simp [symTracelessPart2, skewPart2, Matrix.trace, Matrix.diag,
      Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · simp [weylPart2, symTracelessPart2, skewPart2, Matrix.trace,
      Matrix.diag, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Solder the division-free arbitrary-ring Cartan decomposition to the
normalized real `gl₂` decomposition. The arbitrary-ring owner proves that its
three pieces sum to `2 • X`; over `ℝ`, multiplying each piece by `1/2`
recovers exactly the real components. This is the carrier-changing edge to
the real matrix geometry; it does not imply a factorization theorem. -/
theorem real_cartan_split_soldered_to_noncommutative_owner (X : Mat2R) :
    weylPart2 X = (1 / 2 : ℝ) •
        InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance.weylScalePart X ∧
    symTracelessPart2 X = (1 / 2 : ℝ) •
        InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance.tracelessSymPart X ∧
    skewPart2 X = (1 / 2 : ℝ) •
        InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance.tracelessAntisymPart X ∧
    X = weylPart2 X + symTracelessPart2 X + skewPart2 X := by
  have hW : weylPart2 X = (1 / 2 : ℝ) •
      InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance.weylScalePart X := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [weylPart2, InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance.weylScalePart,
        InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance.fiberEmbed,
        Matrix.trace, Matrix.diag, Fin.sum_univ_two] <;> ring
  have hS : symTracelessPart2 X = (1 / 2 : ℝ) •
      InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance.tracelessSymPart X := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symTracelessPart2,
        InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance.tracelessSymPart,
        InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance.mat2] <;> ring
  have hA : skewPart2 X = (1 / 2 : ℝ) •
      InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance.tracelessAntisymPart X := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [skewPart2,
        InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance.tracelessAntisymPart,
        InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance.mat2] <;> ring
  have hdecomp := InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance.weyl_cartan_split_and_noncommutative_trace_to_det X
  have hreal : X = weylPart2 X + symTracelessPart2 X + skewPart2 X := by
    have hhalf : (1 / 2 : ℝ) • (2 • X) = X := by
      calc (1 / 2 : ℝ) • (2 • X)
          = (1 / 2 : ℝ) • (X + X) := by rw [two_smul]
        _ = (1 / 2 : ℝ) • X + (1 / 2 : ℝ) • X := by rw [smul_add]
        _ = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • X := by rw [← add_smul]
        _ = X := by norm_num
    calc X = (1 / 2 : ℝ) • (2 • X) := hhalf.symm
      _ = (1 / 2 : ℝ) •
          (InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance.weylScalePart X +
           InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance.tracelessSymPart X +
           InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance.tracelessAntisymPart X) := by
            rw [hdecomp.1]
      _ = weylPart2 X + symTracelessPart2 X + skewPart2 X := by
            rw [smul_add, smul_add, ← hW, ← hS, ← hA]
  exact ⟨hW, hS, hA, hreal⟩

/-- Cartan bracket inclusions for the traceless symmetric and skew subspaces.
The hypotheses are membership conditions on these explicit subspaces only. -/
theorem real_twoByTwo_cartan_brackets
    {K₁ K₂ S₁ S₂ : Mat2R}
    (hK₁ : K₁ᵀ = -K₁) (hK₂ : K₂ᵀ = -K₂)
    (hS₁ : S₁ᵀ = S₁) (hS₂ : S₂ᵀ = S₂)
    (htrS₁ : Matrix.trace S₁ = 0) (htrS₂ : Matrix.trace S₂ = 0) :
    K₁ * K₂ - K₂ * K₁ = 0 ∧
    (K₁ * S₁ - S₁ * K₁)ᵀ = K₁ * S₁ - S₁ * K₁ ∧
    Matrix.trace (K₁ * S₁ - S₁ * K₁) = 0 ∧
    (S₁ * S₂ - S₂ * S₁)ᵀ = -(S₁ * S₂ - S₂ * S₁) := by
  have hK₁shape : K₁ 0 0 = 0 ∧ K₁ 1 1 = 0 ∧ K₁ 1 0 = -K₁ 0 1 := by
    constructor
    · have h := congrArg (fun M : Mat2R => M 0 0) hK₁
      simp at h
      linarith
    constructor
    · have h := congrArg (fun M : Mat2R => M 1 1) hK₁
      simp at h
      linarith
    · have h := congrArg (fun M : Mat2R => M 0 1) hK₁
      simp at h
      linarith
  have hK₂shape : K₂ 0 0 = 0 ∧ K₂ 1 1 = 0 ∧ K₂ 1 0 = -K₂ 0 1 := by
    constructor
    · have h := congrArg (fun M : Mat2R => M 0 0) hK₂
      simp at h
      linarith
    constructor
    · have h := congrArg (fun M : Mat2R => M 1 1) hK₂
      simp at h
      linarith
    · have h := congrArg (fun M : Mat2R => M 0 1) hK₂
      simp at h
      linarith
  have hS₁shape : S₁ 1 1 = -S₁ 0 0 ∧ S₁ 1 0 = S₁ 0 1 := by
    constructor
    · have ht := htrS₁
      rw [trace_fin2Ring] at ht
      linarith
    · have h := congrArg (fun M : Mat2R => M 0 1) hS₁
      simpa using h
  have hS₂shape : S₂ 1 1 = -S₂ 0 0 ∧ S₂ 1 0 = S₂ 0 1 := by
    constructor
    · have ht := htrS₂
      rw [trace_fin2Ring] at ht
      linarith
    · have h := congrArg (fun M : Mat2R => M 0 1) hS₂
      simpa using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ext_fin2Ring <;> simp [hK₁shape.1, hK₁shape.2.1, hK₁shape.2.2,
      hK₂shape.1, hK₂shape.2.1, hK₂shape.2.2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · apply ext_fin2Ring <;>
      simp [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.mul_apply,
        Fin.sum_univ_two, hK₁shape.1, hK₁shape.2.1, hK₁shape.2.2,
        hS₁shape.1, hS₁shape.2] <;> ring
  · simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
      hK₁shape.1, hK₁shape.2.1, hK₁shape.2.2,
      hS₁shape.1, hS₁shape.2]
  · simp [Matrix.transpose_mul, Matrix.transpose_sub, hS₁, hS₂]

end RealTwoByTwoWeylCartan

/-! ## Explicit Euclidean polar factors and the KAN Gram identity -/

section RealTwoByTwoPolarBridge

def realPolarScale (M : RealMat2) : ℝ :=
  Real.sqrt ((M 0 0 + M 1 1) ^ 2 + (M 0 1 - M 1 0) ^ 2)

def realPolarK (M : RealMat2) : RealMat2 :=
  let τ := realPolarScale M
  mat2Ring ((M 0 0 + M 1 1) / τ) ((M 0 1 - M 1 0) / τ)
    ((M 1 0 - M 0 1) / τ) ((M 0 0 + M 1 1) / τ)

def realPolarP (M : RealMat2) : RealMat2 := (realPolarK M)ᵀ * M

private lemma realPolarScale_pos {M : RealMat2} (hdet : 0 < Matrix.det M) :
    0 < realPolarScale M := by
  apply Real.sqrt_pos.mpr
  have hdet' : 0 < M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
    simpa [Matrix.det_fin_two] using hdet
  have hpos : 0 < (M 0 0 + M 1 1) ^ 2 + (M 0 1 - M 1 0) ^ 2 := by
    nlinarith [sq_nonneg (M 0 0 - M 1 1), sq_nonneg (M 0 1 + M 1 0)]
  exact hpos

/-- Closed-form `SO(2) × SPD(2)` polar data for a real matrix with positive
determinant. Positive definiteness is recorded by the two-by-two Sylvester
minors, not inferred from the current repository `PolarDecomposition`
structure (whose fields assert only self-adjointness). -/
theorem real_gl2_pos_polar_factorization {M : RealMat2}
    (hdet : 0 < Matrix.det M) :
    (realPolarK M)ᵀ * realPolarK M = 1 ∧
    Matrix.det (realPolarK M) = 1 ∧
    (realPolarP M)ᵀ = realPolarP M ∧
    0 < realPolarP M 0 0 ∧
    0 < Matrix.det (realPolarP M) ∧
    Matrix.trace (realPolarP M) = realPolarScale M ∧
    realPolarK M * realPolarP M = M ∧
    realPolarP M * realPolarP M = Mᵀ * M := by
  have hτ : 0 < realPolarScale M := realPolarScale_pos hdet
  have hτ0 : realPolarScale M ≠ 0 := ne_of_gt hτ
  have hτsq : realPolarScale M ^ 2 =
      (M 0 0 + M 1 1) ^ 2 + (M 0 1 - M 1 0) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hdet_eq : Matrix.det M = M 0 0 * M 1 1 - M 0 1 * M 1 0 :=
    Matrix.det_fin_two M
  have hKorth : (realPolarK M)ᵀ * realPolarK M = 1 := by
    apply ext_fin2Ring <;>
      simp [realPolarK, mat2Ring, Matrix.transpose_apply, Matrix.mul_apply,
        Fin.sum_univ_two] <;>
      field_simp [hτ0] <;> nlinarith [hτsq]
  have hKorth' : realPolarK M * (realPolarK M)ᵀ = 1 := by
    apply ext_fin2Ring <;>
      simp [realPolarK, mat2Ring, Matrix.transpose_apply, Matrix.mul_apply,
        Fin.sum_univ_two] <;>
      field_simp [hτ0] <;> nlinarith [hτsq]
  have hdetK : Matrix.det (realPolarK M) = 1 := by
    rw [Matrix.det_fin_two]
    simp [realPolarK, mat2Ring]
    field_simp [hτ0]
    nlinarith [hτsq]
  have hsym : (realPolarP M)ᵀ = realPolarP M := by
    apply ext_fin2Ring <;>
      simp [realPolarP, realPolarK, mat2Ring, Matrix.transpose_apply,
        Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp [hτ0] <;> ring
  have hP00 : 0 < realPolarP M 0 0 := by
    rw [realPolarP, realPolarK]
    simp [mat2Ring, Matrix.mul_apply, Fin.sum_univ_two]
    have hr2 : 0 ≤ (M 0 0) ^ 2 + (M 1 0) ^ 2 := by positivity
    have hdet_eq : Matrix.det M = M 0 0 * M 1 1 - M 0 1 * M 1 0 :=
      Matrix.det_fin_two M
    field_simp [hτ0]
    nlinarith [hτsq, hdet_eq, hdet]
  have hdetP : 0 < Matrix.det (realPolarP M) := by
    rw [realPolarP, Matrix.det_mul, Matrix.det_transpose, hdetK, one_mul]
    exact hdet
  have htraceP : Matrix.trace (realPolarP M) = realPolarScale M := by
    rw [realPolarP, Matrix.trace_fin_two]
    simp [realPolarK, mat2Ring, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp [hτ0]
    nlinarith [hτsq]
  have hrec : realPolarK M * realPolarP M = M := by
    rw [realPolarP, ← Matrix.mul_assoc, hKorth']
    simp
  have hgram : realPolarP M * realPolarP M = Mᵀ * M := by
    calc
      realPolarP M * realPolarP M = (realPolarP M)ᵀ * realPolarP M := by rw [hsym]
      _ = Mᵀ * (realPolarK M * (realPolarK M)ᵀ) * M := by
        rw [realPolarP]
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
        noncomm_ring
      _ = Mᵀ * M := by rw [hKorth']; noncomm_ring
  exact ⟨hKorth, hdetK, hsym, hP00, hdetP, htraceP, hrec, hgram⟩

private lemma real_mat2_pos_polar_quadratic_form
    (P : RealMat2) (hsym : P 1 0 = P 0 1) (x : Fin 2 → ℝ) :
    star x ⬝ᵥ (P *ᵥ x) =
      P 0 0 * x 0 ^ 2 + 2 * P 0 1 * x 0 * x 1 + P 1 1 * x 1 ^ 2 := by
  simp [dotProduct, Matrix.mulVec, hsym]
  ring

private lemma real_mat2_pos_polar_quadratic_completion
    (P : RealMat2) (h00 : 0 < P 0 0) (hsym : P 1 0 = P 0 1)
    (hdet : Matrix.det P = P 0 0 * P 1 1 - P 0 1 * P 1 0) (x : Fin 2 → ℝ) :
    P 0 0 * x 0 ^ 2 + 2 * P 0 1 * x 0 * x 1 + P 1 1 * x 1 ^ 2 =
      P 0 0 * (x 0 + (P 0 1 / P 0 0) * x 1) ^ 2 +
        (Matrix.det P / P 0 0) * x 1 ^ 2 := by
  rw [hdet, hsym]
  field_simp [ne_of_gt h00]
  ring

/-- The explicit polar stretch is positive definite in Mathlib's quadratic-form
sense.  The proof uses the actual two-dimensional form: completing the square
reduces positivity to the positive leading minor and determinant. -/
theorem real_gl2_pos_polar_stretch_posDef {M : RealMat2}
    (hdet : 0 < Matrix.det M) : (realPolarP M).PosDef := by
  obtain ⟨_, _, hsym, h00, hdetP, _, _, _⟩ := real_gl2_pos_polar_factorization hdet
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · simpa [Matrix.IsHermitian, hsym]
  · intro x hx
    have hsymEntry : realPolarP M 1 0 = realPolarP M 0 1 := by
      have h := congrArg (fun A : RealMat2 => A 0 1) hsym
      simpa [Matrix.transpose_apply] using h
    have hdetFormula : Matrix.det (realPolarP M) =
        realPolarP M 0 0 * realPolarP M 1 1 -
          realPolarP M 0 1 * realPolarP M 1 0 := by
      exact Matrix.det_fin_two _
    rw [real_mat2_pos_polar_quadratic_form (realPolarP M) hsymEntry x]
    rw [real_mat2_pos_polar_quadratic_completion (realPolarP M) h00 hsymEntry hdetFormula x]
    by_cases hx1 : x 1 = 0
    · have hx0 : x 0 ≠ 0 := by
        intro hx0
        apply hx
        funext i
        fin_cases i <;> simp [hx0, hx1]
      simp [hx1, hx0]
      positivity
    · have hsecond : 0 < (Matrix.det (realPolarP M) / realPolarP M 0 0) * x 1 ^ 2 :=
        mul_pos (div_pos hdetP h00) (sq_pos_of_ne_zero hx1)
      nlinarith [sq_nonneg
        (x 0 + (realPolarP M 0 1 / realPolarP M 0 0) * x 1)]

/-- Adapt the explicit left polar factorization `M = K P` to the repository's
right-oriented `PolarDecomposition` structure `M = P₊ U`.  The structure only
stores self-adjointness (not positivity); strict positivity of the constructed
record's stretch is proved separately by
`real_gl2_pos_polarDecomposition_factor_posDef`. -/
def real_gl2_pos_to_polarDecomposition {M : RealMat2}
    (hdet : 0 < Matrix.det M) :
    InfoGeometry.Optimization.PolarDecomposition M := {
    U := realPolarK M
    P := realPolarK M * realPolarP M * (realPolarK M)ᵀ
    decomp := by
      obtain ⟨hK, _, _, _, _, _, hrec, _⟩ :=
        real_gl2_pos_polar_factorization hdet
      calc
        M = realPolarK M * realPolarP M := hrec.symm
        _ = (realPolarK M * realPolarP M * (realPolarK M)ᵀ) * realPolarK M := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hK]
          simp
    unitary := by
      have hτ : 0 < realPolarScale M := realPolarScale_pos hdet
      have hτ0 : realPolarScale M ≠ 0 := ne_of_gt hτ
      have hτsq : realPolarScale M ^ 2 =
          (M 0 0 + M 1 1) ^ 2 + (M 0 1 - M 1 0) ^ 2 :=
        Real.sq_sqrt (by positivity)
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [realPolarK, mat2Ring, Matrix.transpose_apply, Matrix.mul_apply,
          Fin.sum_univ_two] <;>
        field_simp [hτ0] <;>
        nlinarith [hτsq]
    self_adjoint := by
      obtain ⟨_, _, hPsym, _, _, _, _, _⟩ :=
        real_gl2_pos_polar_factorization hdet
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
      rw [hPsym]
      noncomm_ring }

/-- The stretch stored by `real_gl2_pos_to_polarDecomposition` is positive
definite as well: it is the orthogonal congruence `K P Kᵀ` of the explicit
positive left stretch. -/
theorem real_gl2_pos_polarDecomposition_factor_posDef {M : RealMat2}
    (hdet : 0 < Matrix.det M) :
    (real_gl2_pos_to_polarDecomposition hdet).P.PosDef := by
  change (realPolarK M * realPolarP M * (realPolarK M)ᵀ).PosDef
  obtain ⟨_, hdetK, _, _, _, _, _, _⟩ := real_gl2_pos_polar_factorization hdet
  have hdetKT : Matrix.det (realPolarK M)ᵀ = 1 := by
    rw [Matrix.det_transpose, hdetK]
  have hKTunit : IsUnit ((realPolarK M)ᵀ) := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    rw [hdetKT]
    exact isUnit_one
  have hinj : Function.Injective ((realPolarK M)ᵀ).mulVec :=
    Matrix.mulVec_injective_of_isUnit hKTunit
  have hcong :=
    (real_gl2_pos_polar_stretch_posDef hdet).conjTranspose_mul_mul_same hinj
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_transpose] using hcong

/-- Convert a positive-definite right polar record `M = P U` into left-polar
data `M = U (Uᵀ P U)`.  The positive determinant hypothesis fixes the
orientation of the orthogonal factor to `SO(2)`. -/
private theorem polar_record_left_factor_data {M : RealMat2}
    (hMdet : 0 < Matrix.det M)
    (D : InfoGeometry.Optimization.PolarDecomposition M)
    (hP : D.P.PosDef) :
    D.U * (D.Uᵀ * D.P * D.U) = M ∧
    (D.Uᵀ * D.P * D.U)ᵀ = D.Uᵀ * D.P * D.U ∧
    0 < (D.Uᵀ * D.P * D.U) 0 0 ∧
    0 < Matrix.det (D.Uᵀ * D.P * D.U) ∧
    D.Uᵀ * D.U = 1 ∧ Matrix.det D.U = 1 := by
  have hUleft : D.Uᵀ * D.U = 1 := mul_eq_one_comm.mpr D.unitary
  have hdetP : 0 < Matrix.det D.P := hP.det_pos
  have hdetrel : Matrix.det M = Matrix.det D.P * Matrix.det D.U := by
    have h := congrArg Matrix.det D.decomp
    rw [Matrix.det_mul] at h
    simpa [mul_comm] using h
  have hdetU_pos : 0 < Matrix.det D.U := by
    rw [hdetrel] at hMdet
    exact (mul_pos_iff_of_pos_left hdetP).mp hMdet
  have hdetU_sq : (Matrix.det D.U) ^ 2 = 1 := by
    have h := congrArg Matrix.det D.unitary
    rw [Matrix.det_mul, Matrix.det_transpose] at h
    have h' : Matrix.det D.U * Matrix.det D.U = 1 := by simpa using h
    nlinarith [h']
  have hdetU : Matrix.det D.U = 1 := by
    nlinarith
  have hUunit : IsUnit D.U := by
    apply (Matrix.isUnit_iff_isUnit_det _).2
    rw [hdetU]
    exact isUnit_one
  have hinj : Function.Injective D.U.mulVec :=
    Matrix.mulVec_injective_of_isUnit hUunit
  have hQpos : (D.Uᵀ * D.P * D.U).PosDef :=
    hP.conjTranspose_mul_mul_same hinj
  have hQsym : (D.Uᵀ * D.P * D.U)ᵀ = D.Uᵀ * D.P * D.U := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [D.self_adjoint]
    noncomm_ring
  have hfactor : D.U * (D.Uᵀ * D.P * D.U) = M := by
    calc
      D.U * (D.Uᵀ * D.P * D.U) = (D.U * D.Uᵀ) * D.P * D.U := by noncomm_ring
      _ = D.P * D.U := by rw [D.unitary]; noncomm_ring
      _ = M := D.decomp.symm
  exact ⟨hfactor, hQsym, hQpos.diag_pos, hQpos.det_pos, hUleft, hdetU⟩

private lemma real_mat2_trace_sq (Q : RealMat2) :
    (Matrix.trace Q) ^ 2 = Matrix.trace (Q * Q) + 2 * Matrix.det Q := by
  rw [trace_fin2Ring, trace_fin2Ring, Matrix.det_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

private lemma real_gl2_pos_polar_trace_eq {P₁ P₂ : RealMat2}
    (htrsq : (Matrix.trace P₁) ^ 2 = (Matrix.trace P₂) ^ 2)
    (htr₁ : 0 < Matrix.trace P₁) (htr₂ : 0 < Matrix.trace P₂) :
    Matrix.trace P₁ = Matrix.trace P₂ := by
  have hprod : (Matrix.trace P₁ - Matrix.trace P₂) *
      (Matrix.trace P₁ + Matrix.trace P₂) = 0 := by
    calc
      (Matrix.trace P₁ - Matrix.trace P₂) *
          (Matrix.trace P₁ + Matrix.trace P₂) =
            (Matrix.trace P₁) ^ 2 - (Matrix.trace P₂) ^ 2 := by ring
      _ = 0 := by rw [htrsq]; ring
  rcases mul_eq_zero.mp hprod with hdiff | hsum
  · linarith [hdiff]
  · have hpos : 0 < Matrix.trace P₁ + Matrix.trace P₂ := add_pos htr₁ htr₂
    linarith [hsum, hpos]

private lemma real_mat2_trace_pos (Q : RealMat2) (hsym : Qᵀ = Q)
    (hQ₀ : 0 < Q 0 0) (hdetQ : 0 < Matrix.det Q) :
    0 < Matrix.trace Q := by
  have hoff : Q 1 0 = Q 0 1 := by
    have hij := congrArg (fun X : RealMat2 => X 0 1) hsym
    simpa [Matrix.transpose_apply] using hij
  have hdiagpos : 0 < Q 1 1 := by
    have hdet' : 0 < Q 0 0 * Q 1 1 - Q 0 1 * Q 1 0 := by
      simpa [Matrix.det_fin_two] using hdetQ
    rw [hoff] at hdet'
    nlinarith [sq_nonneg (Q 0 1)]
  rw [trace_fin2Ring]
  exact add_pos hQ₀ hdiagpos

private lemma real_mat2_cayley_hamilton (Q : RealMat2) :
    Matrix.trace Q • Q = Q * Q + Matrix.det Q • (1 : RealMat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

/-- Uniqueness of the real `SO(2) × SPD(2)` polar factors. For a symmetric
two-by-two matrix, positive leading principal minor and positive determinant
are the Sylvester conditions for positive definiteness. -/
theorem real_gl2_pos_polar_unique
    {M K₁ K₂ P₁ P₂ : RealMat2}
    (hfac₁ : K₁ * P₁ = M) (hfac₂ : K₂ * P₂ = M)
    (hK₁ : K₁ᵀ * K₁ = 1) (hK₂ : K₂ᵀ * K₂ = 1)
    (hdetK₁ : Matrix.det K₁ = 1) (hdetK₂ : Matrix.det K₂ = 1)
    (hsym₁ : P₁ᵀ = P₁) (hsym₂ : P₂ᵀ = P₂)
    (hP₁₀ : 0 < P₁ 0 0) (hdetP₁ : 0 < Matrix.det P₁)
    (hP₂₀ : 0 < P₂ 0 0) (hdetP₂ : 0 < Matrix.det P₂) :
    K₁ = K₂ ∧ P₁ = P₂ := by
  have hgram : P₁ * P₁ = P₂ * P₂ := by
    calc
      P₁ * P₁ = P₁ᵀ * (K₁ᵀ * K₁) * P₁ := by rw [hK₁]; simp [hsym₁]
      _ = (K₁ * P₁)ᵀ * (K₁ * P₁) := by
        simp only [Matrix.transpose_mul]
        noncomm_ring
      _ = (K₂ * P₂)ᵀ * (K₂ * P₂) := by rw [hfac₁, hfac₂]
      _ = P₂ᵀ * (K₂ᵀ * K₂) * P₂ := by
        simp only [Matrix.transpose_mul]
        noncomm_ring
      _ = P₂ * P₂ := by rw [hK₂, hsym₂]; simp
  have hdetP : Matrix.det P₁ = Matrix.det P₂ := by
    have h := congrArg Matrix.det (hfac₁.trans hfac₂.symm)
    rw [Matrix.det_mul, Matrix.det_mul, hdetK₁, hdetK₂] at h
    simpa using h
  have htrsq : (Matrix.trace P₁) ^ 2 = (Matrix.trace P₂) ^ 2 := by
    rw [real_mat2_trace_sq P₁, real_mat2_trace_sq P₂, hgram, hdetP]
  have htr₁ : 0 < Matrix.trace P₁ := real_mat2_trace_pos P₁ hsym₁ hP₁₀ hdetP₁
  have htr₂ : 0 < Matrix.trace P₂ := real_mat2_trace_pos P₂ hsym₂ hP₂₀ hdetP₂
  have htrace : Matrix.trace P₁ = Matrix.trace P₂ :=
    real_gl2_pos_polar_trace_eq htrsq htr₁ htr₂
  have hch (Q : RealMat2) :
      Matrix.trace Q • Q = Q * Q + Matrix.det Q • (1 : RealMat2) :=
    real_mat2_cayley_hamilton Q
  have hP : P₁ = P₂ := by
    have hsmul : Matrix.trace P₁ • P₁ = Matrix.trace P₁ • P₂ := by
      calc
        Matrix.trace P₁ • P₁ = P₁ * P₁ + Matrix.det P₁ • (1 : RealMat2) := hch P₁
        _ = P₂ * P₂ + Matrix.det P₂ • (1 : RealMat2) := by rw [hgram, hdetP]
        _ = Matrix.trace P₂ • P₂ := (hch P₂).symm
        _ = Matrix.trace P₁ • P₂ := by rw [htrace]
    ext i j
    have hij := congrArg (fun X : RealMat2 => X i j) hsmul
    simpa [Matrix.smul_apply] using
      (mul_left_cancel₀ (ne_of_gt htr₁) hij)
  have hK : K₁ = K₂ := by
    have hPdet : IsUnit (Matrix.det P₂) :=
      isUnit_iff_ne_zero.mpr (ne_of_gt hdetP₂)
    have hPunit : P₂ * P₂⁻¹ = 1 := Matrix.mul_nonsing_inv P₂ hPdet
    have hfac₁' : K₁ * P₂ = M := by simpa [hP] using hfac₁
    have hKP : K₁ * P₂ = K₂ * P₂ := hfac₁'.trans hfac₂.symm
    calc
      K₁ = K₁ * (P₂ * P₂⁻¹) := by rw [hPunit]; simp
      _ = (K₁ * P₂) * P₂⁻¹ := by noncomm_ring
      _ = (K₂ * P₂) * P₂⁻¹ := by rw [hKP]
      _ = K₂ * (P₂ * P₂⁻¹) := by noncomm_ring
      _ = K₂ := by rw [hPunit]; simp
  exact ⟨hK, hP⟩

/-- Uniqueness of a polar pair in an arbitrary pushed-forward frame. Here
`Q = Hᵀ * H` is the transported metric: the orthogonal factor is a Q-isometry,
the stretch is Q-self-adjoint, and `Q * P` is positive definite. Pullback
reduces this statement to the Euclidean `SO(2) × SPD(2)` uniqueness theorem. -/
theorem real_gl2_pos_metric_polar_unique
    {M G H K₁ K₂ P₁ P₂ : RealMat2}
    (hHG : H * G = 1) (hGH : G * H = 1)
    (hdet : 0 < Matrix.det (H * M * G))
    (hfac₁ : M = K₁ * P₁) (hfac₂ : M = K₂ * P₂)
    (hK₁ : K₁ᵀ * (Hᵀ * H) * K₁ = Hᵀ * H)
    (hK₂ : K₂ᵀ * (Hᵀ * H) * K₂ = Hᵀ * H)
    (hP₁ : P₁ᵀ * (Hᵀ * H) = (Hᵀ * H) * P₁)
    (hP₂ : P₂ᵀ * (Hᵀ * H) = (Hᵀ * H) * P₂)
    (hpos₁ : ((Hᵀ * H) * P₁).PosDef)
    (hpos₂ : ((Hᵀ * H) * P₂).PosDef) :
    K₁ = K₂ ∧ P₁ = P₂ := by
  have hdetG : Matrix.det G ≠ 0 := by
    have h := congrArg Matrix.det hHG
    rw [Matrix.det_mul, Matrix.det_one] at h
    intro hz
    rw [hz, mul_zero] at h
    norm_num at h
  have hGunit : IsUnit (Matrix.det G) := isUnit_iff_ne_zero.mpr hdetG
  have hGinj : Function.Injective G.mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hGunit)
  have hQG : (Hᵀ * H) * G = Hᵀ := by
    calc
      (Hᵀ * H) * G = Hᵀ * (H * G) := by noncomm_ring
      _ = Hᵀ := by rw [hHG]; simp
  have hGtQ : Gᵀ * (Hᵀ * H) = H := by
    calc
      Gᵀ * (Hᵀ * H) = (Gᵀ * Hᵀ) * H := by noncomm_ring
      _ = H := by rw [← Matrix.transpose_mul, hHG]; simp
  let k₁ := framePull H G K₁
  let k₂ := framePull H G K₂
  let p₁ := framePull H G P₁
  let p₂ := framePull H G P₂
  have hk₁ : k₁ᵀ * k₁ = 1 := by
    dsimp [k₁, framePull]
    calc
      (H * K₁ * G)ᵀ * (H * K₁ * G) =
          Gᵀ * K₁ᵀ * Hᵀ * (H * K₁ * G) := by
            simp only [Matrix.transpose_mul] <;> noncomm_ring
      _ =
          Gᵀ * (K₁ᵀ * (Hᵀ * H) * K₁) * G := by noncomm_ring
      _ = Gᵀ * (Hᵀ * H) * G := by rw [hK₁]
      _ = 1 := by
        calc
          Gᵀ * (Hᵀ * H) * G = (Gᵀ * Hᵀ) * (H * G) := by noncomm_ring
          _ = 1 := by rw [← Matrix.transpose_mul, hHG]; simp
  have hk₂ : k₂ᵀ * k₂ = 1 := by
    dsimp [k₂, framePull]
    calc
      (H * K₂ * G)ᵀ * (H * K₂ * G) =
          Gᵀ * K₂ᵀ * Hᵀ * (H * K₂ * G) := by
            simp only [Matrix.transpose_mul] <;> noncomm_ring
      _ =
          Gᵀ * (K₂ᵀ * (Hᵀ * H) * K₂) * G := by noncomm_ring
      _ = Gᵀ * (Hᵀ * H) * G := by rw [hK₂]
      _ = 1 := by
        calc
          Gᵀ * (Hᵀ * H) * G = (Gᵀ * Hᵀ) * (H * G) := by noncomm_ring
          _ = 1 := by rw [← Matrix.transpose_mul, hHG]; simp
  have hp₁sym : p₁ᵀ = p₁ := by
    dsimp [p₁, framePull]
    calc
      (H * P₁ * G)ᵀ = Gᵀ * P₁ᵀ * Hᵀ := by
        simp only [Matrix.transpose_mul] <;> noncomm_ring
      _ = Gᵀ * P₁ᵀ * ((Hᵀ * H) * G) := by
        rw [hQG]
      _ = Gᵀ * (P₁ᵀ * (Hᵀ * H)) * G := by
        simp only [Matrix.mul_assoc]
      _ = Gᵀ * ((Hᵀ * H) * P₁) * G := by rw [hP₁]
      _ = H * P₁ * G := by
        rw [← Matrix.mul_assoc, hGtQ]
  have hp₂sym : p₂ᵀ = p₂ := by
    dsimp [p₂, framePull]
    calc
      (H * P₂ * G)ᵀ = Gᵀ * P₂ᵀ * Hᵀ := by
        simp only [Matrix.transpose_mul] <;> noncomm_ring
      _ = Gᵀ * P₂ᵀ * ((Hᵀ * H) * G) := by
        rw [hQG]
      _ = Gᵀ * (P₂ᵀ * (Hᵀ * H)) * G := by
        simp only [Matrix.mul_assoc]
      _ = Gᵀ * ((Hᵀ * H) * P₂) * G := by rw [hP₂]
      _ = H * P₂ * G := by
        rw [← Matrix.mul_assoc, hGtQ]
  have hp₁pos : p₁.PosDef := by
    have hpos := hpos₁.conjTranspose_mul_mul_same hGinj
    have heq : Gᵀ * ((Hᵀ * H) * P₁) * G = p₁ := by
      dsimp [p₁, framePull]
      calc
        Gᵀ * ((Hᵀ * H) * P₁) * G = (Gᵀ * (Hᵀ * H)) * P₁ * G := by noncomm_ring
        _ = H * P₁ * G := by rw [hGtQ]
    rw [← heq]
    exact hpos
  have hp₂pos : p₂.PosDef := by
    have hpos := hpos₂.conjTranspose_mul_mul_same hGinj
    have heq : Gᵀ * ((Hᵀ * H) * P₂) * G = p₂ := by
      dsimp [p₂, framePull]
      calc
        Gᵀ * ((Hᵀ * H) * P₂) * G = (Gᵀ * (Hᵀ * H)) * P₂ * G := by noncomm_ring
        _ = H * P₂ * G := by rw [hGtQ]
    rw [← heq]
    exact hpos
  have hpull_fact (K P k p : RealMat2) (hk : k = framePull H G K)
      (hp : p = framePull H G P) (hfac : M = K * P) :
      H * M * G = k * p := by
    have hpull_mul : framePull H G (K * P) =
        framePull H G K * framePull H G P := by
      unfold framePull
      calc
        H * (K * P) * G = (H * K) * (P * G) := by simp only [Matrix.mul_assoc]
        _ = (H * K) * (G * H) * (P * G) := by rw [hGH]; simp
        _ = (H * K * G) * (H * P * G) := by simp only [Matrix.mul_assoc]
    calc
      H * M * G = framePull H G M := rfl
      _ = framePull H G (K * P) := by rw [hfac]
      _ = framePull H G K * framePull H G P := hpull_mul
      _ = k * p := by rw [hk, hp]
  have hfac₁' : H * M * G = k₁ * p₁ := by
    apply hpull_fact K₁ P₁ k₁ p₁ rfl rfl hfac₁
  have hfac₂' : H * M * G = k₂ * p₂ := by
    apply hpull_fact K₂ P₂ k₂ p₂ rfl rfl hfac₂
  have hdetp₁ : 0 < Matrix.det p₁ := hp₁pos.det_pos
  have hdetp₂ : 0 < Matrix.det p₂ := hp₂pos.det_pos
  have hdetk₁sq : Matrix.det k₁ * Matrix.det k₁ = 1 := by
    have h := congrArg Matrix.det hk₁
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    simpa using h
  have hdetk₂sq : Matrix.det k₂ * Matrix.det k₂ = 1 := by
    have h := congrArg Matrix.det hk₂
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    simpa using h
  have hdetrel₁ : Matrix.det (H * M * G) = Matrix.det k₁ * Matrix.det p₁ := by
    simpa only [Matrix.det_mul] using congrArg Matrix.det hfac₁'
  have hdetrel₂ : Matrix.det (H * M * G) = Matrix.det k₂ * Matrix.det p₂ := by
    simpa only [Matrix.det_mul] using congrArg Matrix.det hfac₂'
  have hdetk₁pos : 0 < Matrix.det k₁ := by
    rw [hdetrel₁] at hdet
    exact (mul_pos_iff_of_pos_right hdetp₁).mp hdet
  have hdetk₂pos : 0 < Matrix.det k₂ := by
    rw [hdetrel₂] at hdet
    exact (mul_pos_iff_of_pos_right hdetp₂).mp hdet
  have hdetk₁ : Matrix.det k₁ = 1 := by
    have hsquare : (Matrix.det k₁) ^ 2 = 1 := by simpa [pow_two] using hdetk₁sq
    rcases sq_eq_one_iff.mp hsquare with hpos | hneg
    · exact hpos
    · rw [hneg] at hdetk₁pos
      norm_num at hdetk₁pos
  have hdetk₂ : Matrix.det k₂ = 1 := by
    have hsquare : (Matrix.det k₂) ^ 2 = 1 := by simpa [pow_two] using hdetk₂sq
    rcases sq_eq_one_iff.mp hsquare with hpos | hneg
    · exact hpos
    · rw [hneg] at hdetk₂pos
      norm_num at hdetk₂pos
  have h00₁ : 0 < p₁ 0 0 := hp₁pos.diag_pos
  have h00₂ : 0 < p₂ 0 0 := hp₂pos.diag_pos
  have hstd := real_gl2_pos_polar_unique hfac₁'.symm hfac₂'.symm hk₁ hk₂
    hdetk₁ hdetk₂ hp₁sym hp₂sym h00₁ hdetp₁ h00₂ hdetp₂
  rcases hstd with ⟨hk, hp⟩
  have hrecover (X Y : RealMat2)
      (hXY : framePull H G X = framePull H G Y) : X = Y := by
    have h := congrArg (fun Z : RealMat2 => G * Z * H) hXY
    dsimp [framePull] at h
    calc
      X = (G * H) * X * (G * H) := by rw [hGH]; noncomm_ring
      _ = G * (H * X * G) * H := by noncomm_ring
      _ = G * (H * Y * G) * H := h
      _ = (G * H) * Y * (G * H) := by noncomm_ring
      _ = Y := by rw [hGH]; noncomm_ring
  exact ⟨hrecover K₁ K₂ hk, hrecover P₁ P₂ hp⟩

/-- Uniqueness of the repository's right-oriented polar record for positive
determinant two-by-two real matrices, assuming each stretch is positive
definite. This supplements the record's algebraic fields with the analytic
condition needed to distinguish the positive square root. -/
theorem real_gl2_pos_polarDecomposition_unique
    {M : RealMat2} (hMdet : 0 < Matrix.det M)
    (D₁ D₂ : InfoGeometry.Optimization.PolarDecomposition M)
    (hP₁ : D₁.P.PosDef) (hP₂ : D₂.P.PosDef) :
    D₁.U = D₂.U ∧ D₁.P = D₂.P := by
  obtain ⟨hfac₁, hsym₁, h00₁, hdet₁, hU₁, hdetU₁⟩ :=
    polar_record_left_factor_data hMdet D₁ hP₁
  obtain ⟨hfac₂, hsym₂, h00₂, hdet₂, hU₂, hdetU₂⟩ :=
    polar_record_left_factor_data hMdet D₂ hP₂
  let Q₁ := D₁.Uᵀ * D₁.P * D₁.U
  let Q₂ := D₂.Uᵀ * D₂.P * D₂.U
  have hleft_unique := real_gl2_pos_polar_unique hfac₁ hfac₂ hU₁ hU₂
    hdetU₁ hdetU₂ hsym₁ hsym₂ h00₁ hdet₁ h00₂ hdet₂
  rcases hleft_unique with ⟨hU, hQ⟩
  have hrecover₁ : D₁.P = D₁.U * Q₁ * D₁.Uᵀ := by
    calc
      D₁.P = (D₁.U * D₁.Uᵀ) * D₁.P * (D₁.U * D₁.Uᵀ) := by
        rw [D₁.unitary]; simp
      _ = D₁.U * Q₁ * D₁.Uᵀ := by dsimp [Q₁]; noncomm_ring
  have hrecover₂ : D₂.P = D₂.U * Q₂ * D₂.Uᵀ := by
    calc
      D₂.P = (D₂.U * D₂.Uᵀ) * D₂.P * (D₂.U * D₂.Uᵀ) := by
        rw [D₂.unitary]; simp
      _ = D₂.U * Q₂ * D₂.Uᵀ := by dsimp [Q₂]; noncomm_ring
  refine ⟨hU, ?_⟩
  calc
    D₁.P = D₁.U * Q₁ * D₁.Uᵀ := hrecover₁
    _ = D₂.U * Q₂ * D₂.Uᵀ := by
      rw [hU]
      exact congrArg (fun Q : RealMat2 => D₂.U * Q * D₂.Uᵀ) hQ
    _ = D₂.P := hrecover₂.symm

/-- Orthogonal conjugation transports a positive right-polar record to the
canonical explicit record: uniqueness identifies both transported factors
with the factors constructed for the conjugated matrix. -/
private theorem real_orthogonal_conjugate_preserves_det_pos
    {M S : RealMat2} (hMdet : 0 < Matrix.det M)
    (hST : Sᵀ * S = 1) : 0 < Matrix.det (S * M * Sᵀ) := by
  have hd := congrArg Matrix.det hST
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
  have hd' : Matrix.det S * Matrix.det S = 1 := by simpa using hd
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  nlinarith [hd', hMdet]

theorem real_gl2_pos_orthogonal_conjugate_polar_factors
    {M S : RealMat2} (hMdet : 0 < Matrix.det M)
    (hS : S * Sᵀ = 1) (hST : Sᵀ * S = 1)
    (D : InfoGeometry.Optimization.PolarDecomposition M)
    (hDP : D.P.PosDef) :
    (orthogonalConjugatePolar S hS hST D).U =
        (real_gl2_pos_to_polarDecomposition
          (real_orthogonal_conjugate_preserves_det_pos hMdet hST)).U ∧
    (orthogonalConjugatePolar S hS hST D).P =
        (real_gl2_pos_to_polarDecomposition
          (real_orthogonal_conjugate_preserves_det_pos hMdet hST)).P := by
  have hdetS : Matrix.det S ≠ 0 := by
    have hd := congrArg Matrix.det hST
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
    have hd' : Matrix.det S * Matrix.det S = 1 := by simpa using hd
    intro hz
    rw [hz] at hd'
    norm_num at hd'
  have hconjdet : 0 < Matrix.det (S * M * Sᵀ) :=
    real_orthogonal_conjugate_preserves_det_pos hMdet hST
  let D' := orthogonalConjugatePolar S hS hST D
  have hD'pos : D'.P.PosDef := by
    dsimp [D', orthogonalConjugatePolar]
    have hSTunit : IsUnit (Matrix.det Sᵀ) := by
      rw [Matrix.det_transpose]
      exact isUnit_iff_ne_zero.mpr hdetS
    have hSTinj : Function.Injective Sᵀ.mulVec :=
      Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hSTunit)
    have hpos := hDP.conjTranspose_mul_mul_same hSTinj
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_transpose] using hpos
  have hcanonicalPos := real_gl2_pos_polarDecomposition_factor_posDef hconjdet
  have huniq := real_gl2_pos_polarDecomposition_unique hconjdet D'
    (real_gl2_pos_to_polarDecomposition hconjdet) hD'pos hcanonicalPos
  change D'.U = (real_gl2_pos_to_polarDecomposition hconjdet).U ∧
    D'.P = (real_gl2_pos_to_polarDecomposition hconjdet).P
  exact huniq

/-- The explicit Euclidean polar factors are equivariant under conformal
orthogonal conjugation. The inverse frame maps `G` and `H` satisfy both
inverse identities, and `GᵀG = c² I` with `c ≠ 0`; this includes rotations,
reflections, and nonzero scalar rescalings. -/
theorem real_gl2_pos_polar_conjugation_equivariance
    {M G H : RealMat2} {c : ℝ}
    (hdet : 0 < Matrix.det M)
    (hHG : H * G = 1) (hGH : G * H = 1)
    (hc : c ≠ 0) (hco : Gᵀ * G = c ^ 2 • (1 : RealMat2)) :
    realPolarK (G * M * H) = G * realPolarK M * H ∧
    realPolarP (G * M * H) = G * realPolarP M * H := by
  have hdetGH : Matrix.det G * Matrix.det H = 1 := by
    have h := congrArg Matrix.det hGH
    simpa [Matrix.det_mul] using h
  have hdetConj : Matrix.det (G * M * H) = Matrix.det M := by
    rw [Matrix.det_mul, Matrix.det_mul]
    calc
      Matrix.det G * Matrix.det M * Matrix.det H =
          (Matrix.det G * Matrix.det H) * Matrix.det M := by
            rw [mul_assoc, mul_comm (Matrix.det M), ← mul_assoc]
      _ = Matrix.det M := by rw [hdetGH, one_mul]
  have hdet' : 0 < Matrix.det (G * M * H) := by rw [hdetConj]; exact hdet
  have hHscale : c ^ 2 • H = Gᵀ := by
    calc
      c ^ 2 • H = (Gᵀ * G) * H := by rw [hco]; simp [smul_mul_assoc]
      _ = Gᵀ * (G * H) := by rw [Matrix.mul_assoc]
      _ = Gᵀ := by rw [hGH]; simp
  have hH : H = (1 / c ^ 2) • Gᵀ := by
    calc
      H = (1 / c ^ 2) • (c ^ 2 • H) := by
        rw [smul_smul, one_div_mul_cancel (pow_ne_zero 2 hc), one_smul]
      _ = (1 / c ^ 2) • Gᵀ := by rw [hHscale]
  have hGGt : G * Gᵀ = c ^ 2 • (1 : RealMat2) := by
    have h1 : (1 / c ^ 2) • (G * Gᵀ) = 1 := by
      calc
        (1 / c ^ 2) • (G * Gᵀ) = G * ((1 / c ^ 2) • Gᵀ) := by
          rw [Matrix.mul_smul]
        _ = G * H := by rw [← hH]
        _ = 1 := hGH
    apply ext_fin2Ring
    · have h00 := congrArg (fun X : RealMat2 => X 0 0) h1
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq] at h00 ⊢
      field_simp [hc] at h00 ⊢
      nlinarith
    · have h01 := congrArg (fun X : RealMat2 => X 0 1) h1
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_ne] at h01 ⊢
      field_simp [hc] at h01 ⊢
      nlinarith
    · have h10 := congrArg (fun X : RealMat2 => X 1 0) h1
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_ne] at h10 ⊢
      field_simp [hc] at h10 ⊢
      nlinarith
    · have h11 := congrArg (fun X : RealMat2 => X 1 1) h1
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq] at h11 ⊢
      field_simp [hc] at h11 ⊢
      nlinarith
  have hQ : Hᵀ * H = (1 / c ^ 2) • (1 : RealMat2) := by
    ext i j
    simp only [Matrix.transpose_smul, Matrix.transpose_transpose,
      Matrix.smul_mul, Matrix.mul_smul, hH, hGGt, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply]
    field_simp [hc]
  rcases real_gl2_pos_polar_factorization hdet with
    ⟨hKorth, hdetK, hPsym, hP00, hdetP, htraceP, hrec, _⟩
  let K' := G * realPolarK M * H
  let P' := G * realPolarP M * H
  have hpair := polar_pair_conjugation_for_pushforward_metric
    G H (realPolarK M) (realPolarP M) hHG hKorth hPsym
  have hqne : (1 / c ^ 2 : ℝ) ≠ 0 := by positivity
  have hKorth' : K'ᵀ * K' = 1 := by
    have hmetric := hpair.1
    rw [hQ] at hmetric
    have hsmul : (1 / c ^ 2 : ℝ) • (K'ᵀ * K') =
        (1 / c ^ 2 : ℝ) • (1 : RealMat2) := by
      simpa [K', smul_mul_assoc, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one] using hmetric
    ext i j
    have hij := congrArg (fun X : RealMat2 => X i j) hsmul
    simpa [Matrix.smul_apply] using (smul_right_injective ℝ hqne hij)
  have hPsym' : P'ᵀ = P' := by
    have hmetric := hpair.2.1
    rw [hQ] at hmetric
    have hsmul : (1 / c ^ 2 : ℝ) • P'ᵀ =
        (1 / c ^ 2 : ℝ) • P' := by
      simpa [P', Matrix.transpose_mul, Matrix.transpose_smul,
        smul_mul_assoc, Matrix.mul_smul] using hmetric
    ext i j
    have hij := congrArg (fun X : RealMat2 => X i j) hsmul
    simpa [Matrix.smul_apply] using (smul_right_injective ℝ hqne hij)
  have hdetK' : Matrix.det K' = 1 := by
    dsimp [K']
    rw [Matrix.det_mul, Matrix.det_mul, hdetK]
    calc
      Matrix.det G * 1 * Matrix.det H = Matrix.det G * Matrix.det H := by ring
      _ = 1 := hdetGH
  have hdetP' : 0 < Matrix.det P' := by
    dsimp [P']
    rw [Matrix.det_mul, Matrix.det_mul]
    have hval : Matrix.det G * Matrix.det (realPolarP M) * Matrix.det H =
        Matrix.det (realPolarP M) := by
      calc
        Matrix.det G * Matrix.det (realPolarP M) * Matrix.det H =
            (Matrix.det G * Matrix.det H) * Matrix.det (realPolarP M) := by ring
        _ = Matrix.det (realPolarP M) := by rw [hdetGH, one_mul]
    rw [hval]
    exact hdetP
  have htraceP' : Matrix.trace P' = Matrix.trace (realPolarP M) := by
    dsimp [P']
    calc
      Matrix.trace (G * realPolarP M * H) =
          Matrix.trace (H * (G * realPolarP M)) := by rw [Matrix.trace_mul_comm]
      _ = Matrix.trace ((H * G) * realPolarP M) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (realPolarP M) := by rw [hHG]; simp
  have hP00' : 0 < P' 0 0 := by
    have htrace' : 0 < Matrix.trace P' := by
      rw [htraceP', htraceP]
      exact realPolarScale_pos hdet
    have hdetEval : 0 < P' 0 0 * P' 1 1 - P' 0 1 * P' 1 0 := by
      simpa [Matrix.det_fin_two] using hdetP'
    have hoff : P' 1 0 = P' 0 1 := by
      have h := congrArg (fun X : RealMat2 => X 0 1) hPsym'
      simpa [Matrix.transpose_apply] using h
    rw [hoff] at hdetEval
    by_contra hnot
    have hnonpos : P' 0 0 ≤ 0 := le_of_not_gt hnot
    rw [trace_fin2Ring] at htrace'
    nlinarith [sq_nonneg (P' 0 1)]
  have hfac' : K' * P' = G * M * H := by
    calc
      K' * P' = G * (realPolarK M * realPolarP M) * H := by
        dsimp [K', P']
        calc
          (G * realPolarK M * H) * (G * realPolarP M * H) =
              G * realPolarK M * (H * G) * realPolarP M * H := by
                simp only [Matrix.mul_assoc]
          _ = G * (realPolarK M * realPolarP M) * H := by rw [hHG]; noncomm_ring
      _ = G * M * H := by rw [hrec]
  rcases real_gl2_pos_polar_factorization hdet' with
    ⟨hKorth0, hdetK0, hPsym0, hP000, hdetP0, htraceP0, hrec0, _⟩
  have huniq := real_gl2_pos_polar_unique hrec0 hfac'
    hKorth0 hKorth' hdetK0 hdetK' hPsym0 hPsym' hP000 hdetP0 hP00' hdetP'
  rcases huniq with ⟨hK, hP⟩
  exact ⟨hK, hP⟩

/-- Euclidean polar factors are not equivariant under arbitrary `GL₂` changes
of frame. Conjugating a quarter-turn by `diag(2,1)` leaves the canonical
Euclidean polar rotation equal to the quarter-turn, whereas conjugation sends
the original rotation to a non-orthogonal matrix. This witnesses why the
conformal-orthogonal hypothesis above cannot simply be dropped. -/
theorem real_gl2_euclidean_polar_not_equivariant_under_general_conjugation :
    let M : RealMat2 := mat2Ring 0 (-1) 1 0
    let G : RealMat2 := mat2Ring 2 0 0 1
    let H : RealMat2 := mat2Ring (1 / 2) 0 0 1
    realPolarK (G * M * H) ≠ G * realPolarK M * H := by
  dsimp
  intro h
  have h01 := congrArg (fun A : RealMat2 => A 0 1) h
  norm_num [realPolarK, realPolarScale, mat2Ring, Matrix.mul_apply,
    Fin.sum_univ_two] at h01

/-- The Euclidean Gram metric of the `GL₂⁺` Iwasawa solvable factor is exactly
the square of the polar stretch. -/
theorem real_iwasawa_polar_gram_bridge {M : RealMat2}
    (hdet : 0 < Matrix.det M) :
    realPolarP M * realPolarP M = Mᵀ * M ∧
    Mᵀ * M = (realIwasawaN M)ᵀ *
      (realIwasawaA M * realIwasawaA M) * realIwasawaN M ∧
    Matrix.det (realIwasawaA M) = Matrix.det M := by
  rcases real_gl2_pos_iwasawa_factorization hdet with
    ⟨hK, hA0, hA1, hA01, hA10, hN0, hN1, hN10, hkan⟩
  rcases real_gl2_pos_polar_factorization hdet with
    ⟨_, _, _, _, _, _, _, hP2⟩
  have hgram : Mᵀ * M = (realIwasawaN M)ᵀ *
      (realIwasawaA M * realIwasawaA M) * realIwasawaN M := by
    have hAsymm : (realIwasawaA M)ᵀ = realIwasawaA M := by
      apply ext_fin2Ring <;> simp [realIwasawaA, mat2Ring]
    calc
      Mᵀ * M = (realIwasawaK M * realIwasawaA M * realIwasawaN M)ᵀ *
          (realIwasawaK M * realIwasawaA M * realIwasawaN M) := by rw [hkan]
      _ = (realIwasawaN M)ᵀ *
          (realIwasawaA M)ᵀ * ((realIwasawaK M)ᵀ * realIwasawaK M) *
            realIwasawaA M * realIwasawaN M := by
        simp only [Matrix.transpose_mul]
        noncomm_ring
      _ = (realIwasawaN M)ᵀ *
          (realIwasawaA M * realIwasawaA M) * realIwasawaN M := by
        rw [hK, hAsymm]
        noncomm_ring
  have hdetA : Matrix.det (realIwasawaA M) = Matrix.det M := by
    rw [Matrix.det_fin_two]
    simp [realIwasawaA, mat2Ring]
    have hr : firstColumnNorm M ≠ 0 := ne_of_gt (firstColumnNorm_pos hdet)
    field_simp [hr]
  exact ⟨hP2, hgram, hdetA⟩

/-- The positive diagonal factor in the real `GL₂⁺` Iwasawa decomposition
splits into its Weyl scale and a determinant-one diagonal factor.  Here
`sqrt(det M)` is the scalar Weyl scale, while the second factor has positive
diagonal entries and determinant one. -/
theorem real_iwasawa_weyl_scale_split {M : RealMat2}
    (hdet : 0 < Matrix.det M) :
    let s := Real.sqrt (Matrix.det M)
    let r := firstColumnNorm M
    realIwasawaA M = s • mat2Ring (r / s) 0 0 (s / r) ∧
    Matrix.det (mat2Ring (r / s) 0 0 (s / r)) = 1 ∧
    0 < r / s ∧ 0 < s / r := by
  have hr : 0 < firstColumnNorm M := firstColumnNorm_pos hdet
  have hs : 0 < Real.sqrt (Matrix.det M) := Real.sqrt_pos.mpr hdet
  have hs_sq : (Real.sqrt (Matrix.det M)) ^ 2 = Matrix.det M :=
    Real.sq_sqrt (le_of_lt hdet)
  have hr_ne : firstColumnNorm M ≠ 0 := ne_of_gt hr
  have hs_ne : Real.sqrt (Matrix.det M) ≠ 0 := ne_of_gt hs
  refine ⟨?_, ?_, div_pos hr hs, div_pos hs hr⟩
  · apply ext_fin2Ring <;>
      simp [realIwasawaA, mat2Ring, smul_eq_mul] <;>
      field_simp [hr_ne, hs_ne] <;>
      nlinarith [hs_sq]
  · simp [Matrix.det_fin_two, mat2Ring]
    field_simp [hr_ne]
    have hs_ne' : Real.sqrt
        (M 0 0 * M 1 1 - M 0 1 * M 1 0) ≠ 0 := by
      rw [← Matrix.det_fin_two M]
      exact hs_ne
    exact div_self hs_ne'

end RealTwoByTwoPolarBridge

/-- In a frame transported by inverse maps `G` and `H`, the KAN and polar
stretch factors induce the same Gram form for the metric `Q = Hᵀ * H`.
The displayed identity transports the Euclidean `GL₂⁺` KAN–polar Gram bridge;
the determinant equality records that the positive diagonal KAN scale is
unchanged by frame transport. -/
theorem relative_iwasawa_polar_gram_bridge
    (G H M : RealMat2) (hHG : H * G = 1) (hGH : G * H = 1)
    (hdet : 0 < Matrix.det (framePull H G M)) :
    let Q := Hᵀ * H
    let M₀ := framePull H G M
    let A := relativeIwasawaA G H M
    let N := relativeIwasawaN G H M
    let P := framePush G H (realPolarP M₀)
    Mᵀ * Q * M = Nᵀ * (Aᵀ * Q * A) * N ∧
    Mᵀ * Q * M = Pᵀ * Q * P ∧
    Matrix.det A = Matrix.det M := by
  dsimp only
  let M₀ := framePull H G M
  let A₀ := realIwasawaA M₀
  let N₀ := realIwasawaN M₀
  let A := relativeIwasawaA G H M
  let N := relativeIwasawaN G H M
  let P := framePush G H (realPolarP M₀)
  have hGQG : Gᵀ * (Hᵀ * H) * G = 1 := by
    calc
      Gᵀ * (Hᵀ * H) * G = (H * G)ᵀ * (H * G) := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
        noncomm_ring
      _ = 1 := by rw [hHG]; simp
  have hframeGram (X : RealMat2) :
      (framePush G H X)ᵀ * (Hᵀ * H) * framePush G H X =
        Hᵀ * (Xᵀ * X) * H := by
    dsimp [framePush]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      Hᵀ * (Xᵀ * Gᵀ) * (Hᵀ * H) * (G * X * H) =
          Hᵀ * Xᵀ * (Gᵀ * (Hᵀ * H) * G) * X * H := by noncomm_ring
      _ = Hᵀ * (Xᵀ * X) * H := by rw [hGQG]; noncomm_ring
  have hpushM : framePush G H M₀ = M := by
    dsimp [framePush, M₀, framePull]
    calc
      G * (H * M * G) * H = (G * H) * M * (G * H) := by noncomm_ring
      _ = M := by rw [hGH]; noncomm_ring
  have hKAN := real_iwasawa_polar_gram_bridge hdet
  have hPolar := real_gl2_pos_polar_factorization hdet
  have hA₀sym : A₀ᵀ = A₀ := by
    apply ext_fin2Ring <;> simp [A₀, realIwasawaA, mat2Ring]
  have hfactorGram :
      (A₀ * N₀)ᵀ * (A₀ * N₀) =
        N₀ᵀ * (A₀ᵀ * A₀) * N₀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [hA₀sym]
    noncomm_ring
  have hpushAN : framePush G H (A₀ * N₀) = A * N := by
    dsimp [A, N, relativeIwasawaA, relativeIwasawaN,
      framePush, framePull]
    calc
      G * (A₀ * N₀) * H = G * A₀ * N₀ * H := by noncomm_ring
      _ = G * A₀ * (H * G) * N₀ * H := by rw [hHG]; noncomm_ring
      _ = (G * A₀ * H) * (G * N₀ * H) := by noncomm_ring
  have hKANframe :
      (A * N)ᵀ * (Hᵀ * H) * (A * N) =
        Hᵀ * (N₀ᵀ * (A₀ᵀ * A₀) * N₀) * H := by
    calc
      (A * N)ᵀ * (Hᵀ * H) * (A * N) =
          (framePush G H (A₀ * N₀))ᵀ * (Hᵀ * H) *
            framePush G H (A₀ * N₀) := by rw [hpushAN]
      _ = Hᵀ * ((A₀ * N₀)ᵀ * (A₀ * N₀)) * H := hframeGram (A₀ * N₀)
      _ = Hᵀ * (N₀ᵀ * (A₀ᵀ * A₀) * N₀) * H := by rw [hfactorGram]
  have hMframe : Mᵀ * (Hᵀ * H) * M = Hᵀ * (M₀ᵀ * M₀) * H := by
    rw [← hpushM]
    exact hframeGram M₀
  have hKANeq : M₀ᵀ * M₀ = N₀ᵀ * (A₀ᵀ * A₀) * N₀ := by
    have hA₂ : A₀ * A₀ = A₀ᵀ * A₀ := by rw [hA₀sym]
    calc
      M₀ᵀ * M₀ = N₀ᵀ * (A₀ * A₀) * N₀ := hKAN.2.1
      _ = N₀ᵀ * (A₀ᵀ * A₀) * N₀ := by rw [hA₂]
  have hPolarEq : M₀ᵀ * M₀ = (realPolarP M₀)ᵀ * realPolarP M₀ := by
    rcases hPolar with ⟨_, _, hPsym, _, _, _, _, hPgram⟩
    rw [hPsym]
    exact hPgram.symm
  have hdetFrame : Matrix.det G * Matrix.det H = 1 := by
    have h := congrArg Matrix.det hGH
    simpa [Matrix.det_mul] using h
  have hdetM : Matrix.det M = Matrix.det M₀ := by
    have h := congrArg Matrix.det hpushM
    rw [framePush, Matrix.det_mul, Matrix.det_mul] at h
    calc
      Matrix.det M = Matrix.det G * Matrix.det M₀ * Matrix.det H := by
        simpa [Matrix.det_mul, mul_assoc] using h.symm
      _ = Matrix.det M₀ := by
        calc
          Matrix.det G * Matrix.det M₀ * Matrix.det H =
              (Matrix.det G * Matrix.det H) * Matrix.det M₀ := by
                rw [mul_assoc, mul_comm (Matrix.det M₀), ← mul_assoc]
          _ = Matrix.det M₀ := by rw [hdetFrame, one_mul]
  have hdetA : Matrix.det A = Matrix.det A₀ := by
    dsimp [A, relativeIwasawaA, framePush, framePull]
    rw [Matrix.det_mul, Matrix.det_mul]
    calc
      Matrix.det G * Matrix.det (realIwasawaA M₀) * Matrix.det H =
          (Matrix.det G * Matrix.det H) * Matrix.det (realIwasawaA M₀) := by
            rw [mul_assoc, mul_comm (Matrix.det (realIwasawaA M₀)), ← mul_assoc]
      _ = Matrix.det (realIwasawaA M₀) := by rw [hdetFrame, one_mul]
  have hdetA₀ : Matrix.det A₀ = Matrix.det M₀ := hKAN.2.2
  have hprodGram :
      Nᵀ * (Aᵀ * (Hᵀ * H) * A) * N = (A * N)ᵀ * (Hᵀ * H) * (A * N) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    noncomm_ring
  refine ⟨?_, ?_, ?_⟩
  · calc
      Mᵀ * (Hᵀ * H) * M = Hᵀ * (M₀ᵀ * M₀) * H := hMframe
      _ = Hᵀ * (N₀ᵀ * (A₀ᵀ * A₀) * N₀) * H := by rw [hKANeq]
      _ = (A * N)ᵀ * (Hᵀ * H) * (A * N) := hKANframe.symm
      _ = Nᵀ * (Aᵀ * (Hᵀ * H) * A) * N := hprodGram.symm
  · calc
      Mᵀ * (Hᵀ * H) * M = Hᵀ * (M₀ᵀ * M₀) * H := hMframe
      _ = Hᵀ * ((realPolarP M₀)ᵀ * realPolarP M₀) * H := by rw [hPolarEq]
      _ = (framePush G H (realPolarP M₀))ᵀ * (Hᵀ * H) *
          framePush G H (realPolarP M₀) := (hframeGram (realPolarP M₀)).symm
  · rw [hdetA, hdetA₀, hdetM]

/-- The explicit polar factors of the pulled-back matrix give a complete
left-polar factorization in the transported metric.  The compact factor is a
`Q`-isometry, the stretch is `Q`-self-adjoint, and its metric-lowered form is
positive definite.  The final Gram equality links this factorization to the
KAN Gram form from `relative_iwasawa_polar_gram_bridge`. -/
theorem relative_metric_polar_factorization
    (G H M : RealMat2) (hHG : H * G = 1) (hGH : G * H = 1)
    (hdet : 0 < Matrix.det (framePull H G M)) :
    let Q := Hᵀ * H
    let M₀ := framePull H G M
    let K := framePush G H (realPolarK M₀)
    let P := framePush G H (realPolarP M₀)
    M = K * P ∧
    Kᵀ * Q * K = Q ∧
    Pᵀ * Q = Q * P ∧
    (Q * P).PosDef ∧
    Mᵀ * Q * M = Pᵀ * Q * P := by
  dsimp only
  let M₀ := framePull H G M
  let K₀ := realPolarK M₀
  let P₀ := realPolarP M₀
  let K := framePush G H K₀
  let P := framePush G H P₀
  have hdetH : Matrix.det H ≠ 0 := by
    have hdetHG := congrArg Matrix.det hHG
    rw [Matrix.det_mul, Matrix.det_one] at hdetHG
    intro hzero
    rw [hzero, zero_mul] at hdetHG
    norm_num at hdetHG
  have hHunit : IsUnit (Matrix.det H) := isUnit_iff_ne_zero.mpr hdetH
  have hHinj : Function.Injective H.mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hHunit)
  have hPolar := real_gl2_pos_polar_factorization hdet
  have hPair := polar_pair_conjugation_for_pushforward_metric
    G H K₀ P₀ hHG hPolar.1 hPolar.2.2.1
  have hQPos : (Hᵀ * H * P).PosDef := by
    dsimp [P, framePush]
    have hP₀Pos := real_gl2_pos_polar_stretch_posDef hdet
    have hcong := polar_stretch_positive_for_pushforward_metric G H P₀ hHG hP₀Pos hHinj
    simpa [Matrix.mul_assoc] using hcong
  have hpushM : framePush G H M₀ = M := by
    dsimp [framePush, M₀, framePull]
    calc
      G * (H * M * G) * H = (G * H) * M * (G * H) := by noncomm_ring
      _ = M := by rw [hGH]; noncomm_ring
  have hfactor0 : K₀ * P₀ = M₀ := hPolar.2.2.2.2.2.2.1
  have hfactor : M = K * P := by
    calc
      M = framePush G H M₀ := hpushM.symm
      _ = framePush G H (K₀ * P₀) := by rw [hfactor0]
      _ = K * P := hPair.2.2.2
  have hGram := relative_iwasawa_polar_gram_bridge G H M hHG hGH hdet
  refine ⟨hfactor, ?_, ?_, hQPos, ?_⟩
  · simpa [K, framePush] using hPair.1
  · simpa [P, framePush] using hPair.2.1
  · simpa [P, framePush] using hGram.2.1

end InfoGeometry.Canonical.WeylTraceKANPolarEquivariance

end noncomputable section
