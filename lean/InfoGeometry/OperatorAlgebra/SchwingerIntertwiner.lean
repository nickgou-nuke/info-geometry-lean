/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.WeylFrameMasks
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Seeded Schwinger averaging on the full operator algebra

The cross-family sum for an already supplied conjugator is an ordered Kraus
expression. Its algebraic identity does not require that conjugator to be
unitary. Matrix-unit averaging is also valid over noncommutative coefficient
rings; the resulting coefficient-diagonal matrix need not be central.

For Schwinger's normalization formula (PNAS 46 (1960), p. 571), the two native
real matrix-unit bases related by conjugation with `Gamma_mat` give an exact
zero unseeded sum. The seed `E₀₀` instead recovers that orthogonal conjugator.
This establishes a nonvanishing requirement for the displayed normalization,
not a failure of existence of an intertwiner.
-/

namespace InfoGeometry.OperatorAlgebra.SchwingerIntertwiner

open Matrix
open scoped BigOperators
open InfoGeometry.Clifford
open InfoGeometry.Clifford.WeylFrameMasks
open InfoGeometry.OperatorAlgebra.NoncommutativeKrausChannel

section OrderedAveraging

variable {A : Type*} [Ring A] [StarRing A]
variable {ι : Type*} [Fintype ι]

/-- Preserve the order of the seed and supplied conjugator in the cross sum.
No invertibility or unitarity hypothesis is needed for this identity. -/
theorem seeded_cross_sum_eq_kraus (X : ι → A) (B T : A) :
    (∑ i, X i * B * star (star T * X i * T)) =
      krausChannel X (B * star T) * T := by
  simp only [star_mul, star_star, krausChannel, Finset.sum_mul, mul_assoc]

/-- The existing four-Weyl twirl supplies the full ring-valued specialization.
The coefficient on the diagonal is not asserted to commute with all entries. -/
theorem weyl_seeded_cross_sum {R : Type*} [Ring R] [StarRing R]
    (B T : Matrix (Fin 2) (Fin 2) R) :
    (∑ i : Fin 4, weylFamily i * B * star (star T * weylFamily i * T)) =
      Matrix.scalar (Fin 2)
        (2 * ((B * star T) 0 0 + (B * star T) 1 1)) * T := by
  rw [seeded_cross_sum_eq_kraus, weyl_twirl]

end OrderedAveraging

section MatrixUnits

variable {R n : Type*} [Ring R] [StarRing R] [Fintype n] [DecidableEq n]

omit [StarRing R] in
/-- The native matrix-unit basis has the usual ordered multiplication table. -/
theorem stdBasis_mul (i j k l : n) :
    Matrix.stdBasis R n n (i, j) * Matrix.stdBasis R n n (k, l) =
      if j = k then Matrix.stdBasis R n n (i, l) else 0 := by
  simp only [Matrix.stdBasis_eq_single]
  by_cases h : j = k
  · subst k
    simp
  · simp [h, Matrix.single_mul_single_of_ne]

/-- Matrix units are normalized for the star-trace pairing, without assuming
commutativity of the coefficient ring. -/
theorem stdBasis_trace_gram (p q : n × n) :
    Matrix.trace (star (Matrix.stdBasis R n n p) * Matrix.stdBasis R n n q) =
      if p = q then 1 else 0 := by
  rcases p with ⟨i, j⟩
  rcases q with ⟨k, l⟩
  simp [Matrix.stdBasis_eq_single, Matrix.star_eq_conjTranspose,
    Matrix.trace_single_mul, Matrix.single_apply, Prod.mk.injEq, eq_comm]

/-- The native matrix-unit basis averages to the coefficient-valued trace.
There is no cyclic-trace or central-coefficient hypothesis. -/
theorem stdBasis_krausChannel (B : Matrix n n R) :
    krausChannel (Matrix.stdBasis R n n) B = Matrix.scalar n (Matrix.trace B) := by
  simp only [krausChannel, Fintype.sum_prod_type, Matrix.stdBasis_eq_single,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one,
    Matrix.single_mul_mul_single, one_mul, mul_one]
  rw [Finset.sum_comm]
  simp_rw [Matrix.sum_single_eq_diagonal]
  apply Matrix.ext
  intro i j
  by_cases h : i = j <;>
    simp [Matrix.sum_apply, Matrix.scalar_apply, Matrix.trace, h]

/-- A supplied conjugator gives the ordered matrix-unit cross-sum formula. -/
theorem stdBasis_seeded_cross_sum (B T : Matrix n n R) :
    (∑ p : n × n, Matrix.stdBasis R n n p * B *
      star (star T * Matrix.stdBasis R n n p * T)) =
      Matrix.scalar n (Matrix.trace (B * star T)) * T := by
  rw [seeded_cross_sum_eq_kraus, stdBasis_krausChannel]

end MatrixUnits

section RealCounterexample

/-- Two vectors of the actual native real basis have distinct ordered products. -/
theorem real_matrix_units_noncommute :
    ∃ X Y : Matrix (Fin 2) (Fin 2) ℝ, X * Y ≠ Y * X := by
  refine ⟨Matrix.stdBasis ℝ (Fin 2) (Fin 2) (0, 1),
    Matrix.stdBasis ℝ (Fin 2) (Fin 2) (1, 0), ?_⟩
  intro h
  rw [stdBasis_mul, stdBasis_mul] at h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [Matrix.stdBasis_eq_single, Matrix.single_apply] at h00

/-- The already owned real Weyl involution is an orthogonal operator. -/
theorem gamma_mem_unitary :
    Gamma_mat (B := ℝ) ∈ unitary (Matrix (Fin 2) (Fin 2) ℝ) := by
  simpa [weylFamily] using (weylFamily_mem_unitary (B := ℝ) (1 : Fin 4))

@[simp] theorem gamma_star : star (Gamma_mat (B := ℝ)) = Gamma_mat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gamma_mat, Matrix.star_apply]

@[simp] theorem gamma_trace : Matrix.trace (Gamma_mat (B := ℝ)) = 0 := by
  simp [Gamma_mat, Matrix.trace, Fin.sum_univ_two]

/-- Native star-algebra conjugation by the existing real operator. -/
noncomputable def gammaConjugation :
    Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  Unitary.conjStarAlgAut ℝ _ ⟨Gamma_mat, gamma_mem_unitary⟩

@[simp] theorem gammaConjugation_apply (X : Matrix (Fin 2) (Fin 2) ℝ) :
    gammaConjugation X = Gamma_mat * X * Gamma_mat := by
  change Gamma_mat * X * star (Gamma_mat (B := ℝ)) = _
  rw [gamma_star]

/-- Transport of the native real matrix-unit basis by the actual conjugation
equivalence. Both bases span the full four-dimensional real matrix algebra. -/
noncomputable def gammaConjugatedBasis :
    Module.Basis (Fin 2 × Fin 2) ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
  (Matrix.stdBasis ℝ (Fin 2) (Fin 2)).map gammaConjugation.toAlgEquiv.toLinearEquiv

theorem gammaConjugatedBasis_apply (p : Fin 2 × Fin 2) :
    gammaConjugatedBasis p =
      gammaConjugation (Matrix.stdBasis ℝ (Fin 2) (Fin 2) p) := by
  simp only [gammaConjugatedBasis, Module.Basis.map_apply]
  rfl

theorem gammaConjugatedBasis_eq_conjugate (p : Fin 2 × Fin 2) :
    gammaConjugatedBasis p =
      star (Gamma_mat (B := ℝ)) * Matrix.stdBasis ℝ (Fin 2) (Fin 2) p * Gamma_mat := by
  rw [gammaConjugatedBasis_apply, gammaConjugation_apply, gamma_star]

/-- The second native basis has exactly the same multiplication table. -/
theorem gammaConjugatedBasis_mul (i j k l : Fin 2) :
    gammaConjugatedBasis (i, j) * gammaConjugatedBasis (k, l) =
      if j = k then gammaConjugatedBasis (i, l) else 0 := by
  simp only [gammaConjugatedBasis_apply, ← map_mul, stdBasis_mul]
  split_ifs <;> simp

/-- Cyclicity is used only for the real coefficient trace in this section. -/
theorem trace_gammaConjugation (X : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.trace (gammaConjugation X) = Matrix.trace X := by
  change Matrix.trace (Gamma_mat * X * star (Gamma_mat (B := ℝ))) = Matrix.trace X
  exact Matrix.trace_units_conj (Unitary.toUnits ⟨Gamma_mat, gamma_mem_unitary⟩) X

/-- The conjugated native basis has the same normalized trace Gram matrix. -/
theorem gammaConjugatedBasis_trace_gram (p q : Fin 2 × Fin 2) :
    Matrix.trace (star (gammaConjugatedBasis p) * gammaConjugatedBasis q) =
      if p = q then 1 else 0 := by
  simp only [gammaConjugatedBasis_apply, ← map_star, ← map_mul]
  rw [trace_gammaConjugation, stdBasis_trace_gram]

/-- The nonzero orthogonal operator really intertwines the two bases. -/
theorem gamma_intertwines (p : Fin 2 × Fin 2) :
    Matrix.stdBasis ℝ (Fin 2) (Fin 2) p * Gamma_mat =
      Gamma_mat * gammaConjugatedBasis p := by
  have hΓ : Gamma_mat (B := ℝ) * Gamma_mat = 1 := by
    simpa only [gamma_star] using (Unitary.mem_iff.mp gamma_mem_unitary).1
  rw [gammaConjugatedBasis_apply, gammaConjugation_apply]
  simp only [← mul_assoc, hΓ, one_mul]

/-- The unseeded cross sum vanishes although an orthogonal intertwiner exists. -/
theorem unseeded_cross_sum_zero :
    (∑ p : Fin 2 × Fin 2,
      Matrix.stdBasis ℝ (Fin 2) (Fin 2) p * star (gammaConjugatedBasis p)) = 0 := by
  calc
    _ = ∑ p : Fin 2 × Fin 2,
        Matrix.stdBasis ℝ (Fin 2) (Fin 2) p * 1 *
          star (star (Gamma_mat (B := ℝ)) *
            Matrix.stdBasis ℝ (Fin 2) (Fin 2) p * Gamma_mat) := by
      simp only [mul_one, gammaConjugatedBasis_eq_conjugate]
    _ = Matrix.scalar (Fin 2) (Matrix.trace (1 * star (Gamma_mat (B := ℝ)))) *
        Gamma_mat := stdBasis_seeded_cross_sum 1 Gamma_mat
    _ = 0 := by simp

/-- The corresponding overlap sum in the displayed normalization is zero. -/
theorem unseeded_gram_overlap_zero :
    (∑ p : Fin 2 × Fin 2,
      Matrix.trace (star (Matrix.stdBasis ℝ (Fin 2) (Fin 2) p) *
        gammaConjugatedBasis p)) = 0 := by
  calc
    _ = Matrix.trace (star (∑ p : Fin 2 × Fin 2,
        Matrix.stdBasis ℝ (Fin 2) (Fin 2) p * star (gammaConjugatedBasis p))) := by
      simp only [star_sum, star_mul, star_star, Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro p _
      exact Matrix.trace_mul_comm _ _
    _ = 0 := by rw [unseeded_cross_sum_zero]; simp

/-- No real scalar can normalize this zero sum to a unitary operator. -/
theorem no_scalar_normalization (c : ℝ) :
    c • (∑ p : Fin 2 × Fin 2,
      Matrix.stdBasis ℝ (Fin 2) (Fin 2) p * star (gammaConjugatedBasis p)) ∉
        unitary (Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [unseeded_cross_sum_zero, smul_zero]
  simp [Unitary.mem_iff]

/-- The single matrix-unit seed recovers the exhibited conjugator itself. -/
theorem matrix_unit_seed_recovers_gamma :
    (∑ p : Fin 2 × Fin 2,
      Matrix.stdBasis ℝ (Fin 2) (Fin 2) p * Matrix.single 0 0 (1 : ℝ) *
        star (gammaConjugatedBasis p)) = Gamma_mat := by
  simp only [gammaConjugatedBasis_eq_conjugate]
  rw [stdBasis_seeded_cross_sum, gamma_star, Matrix.trace_single_mul]
  simp [Gamma_mat]

/-- The successful seeded sum is a unitary in the full real matrix algebra. -/
theorem matrix_unit_seed_mem_unitary :
    (∑ p : Fin 2 × Fin 2,
      Matrix.stdBasis ℝ (Fin 2) (Fin 2) p * Matrix.single 0 0 (1 : ℝ) *
        star (gammaConjugatedBasis p)) ∈ unitary (Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [matrix_unit_seed_recovers_gamma]
  exact gamma_mem_unitary

end RealCounterexample

end InfoGeometry.OperatorAlgebra.SchwingerIntertwiner
