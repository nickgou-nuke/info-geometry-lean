import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Diagonal matrix exponential trace-determinant law

This module proves the finite diagonal form of the determinant/log-volume
identity directly from mathlib matrix facts:

* `Matrix.exp_diagonal`
* `Matrix.det_diagonal`
* `Matrix.trace_diagonal`
* `NormedSpace.exp_sum`

The result is the canonical diagonal model for the `H^1` determinant cocycle:
the multiplicative determinant of a diagonal matrix exponential is the
exponential of its additive trace generator.
-/

noncomputable section

namespace MatrixExponentialTraceDet

open scoped BigOperators Matrix

variable {n : ℕ}

/-- Matrix exponential of a diagonal real matrix is the diagonal of scalar exponentials. -/
lemma exp_diagonal_step (v : Fin n → ℝ) :
    NormedSpace.exp (Matrix.diagonal v) = Matrix.diagonal (NormedSpace.exp v) := by
  exact Matrix.exp_diagonal v

/-- Determinant of the diagonal exponential is the product of scalar exponentials. -/
lemma det_diagonal_step (v : Fin n → ℝ) :
    Matrix.det (Matrix.diagonal (NormedSpace.exp v)) = ∏ i, (NormedSpace.exp v) i := by
  have hfun : NormedSpace.exp v = fun i => NormedSpace.exp (v i) := by
    funext i
    exact Pi.coe_exp v i
  rw [hfun]
  exact Matrix.det_diagonal (d := fun i => NormedSpace.exp (v i))

/-- Trace of a diagonal matrix is the sum of its diagonal entries. -/
lemma trace_diagonal_step (v : Fin n → ℝ) :
    Matrix.trace (Matrix.diagonal v) = ∑ i, v i := by
  exact Matrix.trace_diagonal (d := v)

/-- Exponential of the diagonal trace is the product of scalar exponentials. -/
lemma exp_trace_diagonal_step (v : Fin n → ℝ) :
    NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) = ∏ i, (NormedSpace.exp v) i := by
  rw [trace_diagonal_step]
  simpa [Pi.coe_exp] using (NormedSpace.exp_sum (s := Finset.univ) (f := v))

/--
Diagonal trace-determinant law for the matrix exponential:
`det (exp (diagonal v)) = exp (trace (diagonal v))`.
-/
theorem det_exp_diagonal_eq_exp_trace_explicit (v : Fin n → ℝ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) := by
  rw [exp_diagonal_step]
  rw [det_diagonal_step]
  rw [exp_trace_diagonal_step]

/-- Short name for the diagonal determinant/trace law. -/
theorem det_exp_diagonal_eq_exp_trace (v : Fin n → ℝ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) :=
  det_exp_diagonal_eq_exp_trace_explicit v

/-- Compatibility alias for existing downstream imports. -/
theorem det_exp_diagonal_eq_exp_trace_shadow (v : Fin n → ℝ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) :=
  det_exp_diagonal_eq_exp_trace v

/-- Complex diagonal shadow of the determinant/trace law. -/
theorem det_exp_diagonal_eq_exp_trace_complex (v : Fin n → ℂ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) := by
  rw [Matrix.exp_diagonal, Matrix.det_diagonal, Matrix.trace_diagonal]
  simpa [Pi.coe_exp] using (NormedSpace.exp_sum (s := Finset.univ) (f := v)).symm

theorem det_exp_diagonal_eq_exp_trace_complex_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) := by
  rw [Matrix.exp_diagonal, Matrix.det_diagonal, Matrix.trace_diagonal]
  simpa [Pi.coe_exp] using (NormedSpace.exp_sum (s := Finset.univ) (f := v)).symm

/--
Trace-determinant law for matrices explicitly diagonalized by an invertible matrix.

This is the no-calculus diagonalizable owner surface: the proof uses mathlib's
matrix exponential conjugation law, determinant conjugation invariance, trace
conjugation invariance, and the diagonal theorem above.
-/
theorem det_exp_eq_exp_trace_of_units_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : (Matrix ι ι ℂ)ˣ) (v : ι → ℂ) :
    Matrix.det
        (NormedSpace.exp
          ((U : Matrix ι ι ℂ) * Matrix.diagonal v * (↑U⁻¹ : Matrix ι ι ℂ))) =
      NormedSpace.exp
        (Matrix.trace
          ((U : Matrix ι ι ℂ) * Matrix.diagonal v * (↑U⁻¹ : Matrix ι ι ℂ))) := by
  let D : Matrix ι ι ℂ := Matrix.diagonal v
  have hExp :
      NormedSpace.exp ((U : Matrix ι ι ℂ) * D * (↑U⁻¹ : Matrix ι ι ℂ)) =
        (U : Matrix ι ι ℂ) * NormedSpace.exp D * (↑U⁻¹ : Matrix ι ι ℂ) := by
    simpa [D] using Matrix.exp_units_conj U D
  have hDetConj :
      Matrix.det ((U : Matrix ι ι ℂ) * NormedSpace.exp D * (↑U⁻¹ : Matrix ι ι ℂ)) =
        Matrix.det (NormedSpace.exp D) := by
    simpa using Matrix.det_units_conj U (NormedSpace.exp D)
  have hTraceConj :
      Matrix.trace ((U : Matrix ι ι ℂ) * D * (↑U⁻¹ : Matrix ι ι ℂ)) =
        Matrix.trace D := by
    simpa using Matrix.trace_units_conj U D
  have hD :
      Matrix.det (NormedSpace.exp D) = NormedSpace.exp (Matrix.trace D) := by
    simpa [D] using det_exp_diagonal_eq_exp_trace_complex_fintype v
  calc
    Matrix.det
        (NormedSpace.exp
          ((U : Matrix ι ι ℂ) * Matrix.diagonal v * (↑U⁻¹ : Matrix ι ι ℂ)))
        = Matrix.det
            (NormedSpace.exp ((U : Matrix ι ι ℂ) * D * (↑U⁻¹ : Matrix ι ι ℂ))) := by
            simp [D]
    _ = Matrix.det
          ((U : Matrix ι ι ℂ) * NormedSpace.exp D * (↑U⁻¹ : Matrix ι ι ℂ)) := by
            rw [hExp]
    _ = Matrix.det (NormedSpace.exp D) := hDetConj
    _ = NormedSpace.exp (Matrix.trace D) := hD
    _ = NormedSpace.exp
          (Matrix.trace ((U : Matrix ι ι ℂ) * D * (↑U⁻¹ : Matrix ι ι ℂ))) := by
            rw [hTraceConj]
    _ = NormedSpace.exp
          (Matrix.trace
            ((U : Matrix ι ι ℂ) * Matrix.diagonal v * (↑U⁻¹ : Matrix ι ι ℂ))) := by
            simp [D]

/-- Trace-determinant law for a matrix supplied with an explicit diagonalization. -/
theorem det_exp_eq_exp_trace_of_is_units_diagonalizable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (U : (Matrix ι ι ℂ)ˣ) (v : ι → ℂ)
    (hA : A = (U : Matrix ι ι ℂ) * Matrix.diagonal v * (↑U⁻¹ : Matrix ι ι ℂ)) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) := by
  rw [hA]
  exact det_exp_eq_exp_trace_of_units_diagonal U v

theorem det_exp_eq_exp_trace_of_isHermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) := by
  let U := hA.eigenvectorUnitary
  let D : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hspec : A = (U : Matrix ι ι ℂ) * D * star (U : Matrix ι ι ℂ) := by
    simpa [U, D, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
  have hexp :
      NormedSpace.exp ((U : Matrix ι ι ℂ) * D * star (U : Matrix ι ι ℂ)) =
        (U : Matrix ι ι ℂ) * NormedSpace.exp D * star (U : Matrix ι ι ℂ) := by
    simpa [U] using Matrix.exp_units_conj (Unitary.toUnits U) D
  have hdetU :
      Matrix.det (U : Matrix ι ι ℂ) * Matrix.det (star (U : Matrix ι ι ℂ)) = 1 := by
    have hunit : Matrix.det (U : Matrix ι ι ℂ) ∈ unitary ℂ :=
      Matrix.det_of_mem_unitary U.2
    have hdetStar :
        Matrix.det (star (U : Matrix ι ι ℂ)) = star (Matrix.det (U : Matrix ι ι ℂ)) := by
      simp [star, Matrix.det_conjTranspose]
    rw [hdetStar]
    exact Unitary.mul_star_self_of_mem hunit
  have hdetConj :
      Matrix.det ((U : Matrix ι ι ℂ) * NormedSpace.exp D * star (U : Matrix ι ι ℂ)) =
        Matrix.det (NormedSpace.exp D) := by
    rw [Matrix.det_mul, Matrix.det_mul]
    rw [mul_assoc]
    rw [mul_comm (Matrix.det (NormedSpace.exp D)) (Matrix.det (star (U : Matrix ι ι ℂ)))]
    rw [← mul_assoc, hdetU, one_mul]
  have hD :
      Matrix.det (NormedSpace.exp D) = NormedSpace.exp (Matrix.trace D) := by
    simpa [D] using
      (det_exp_diagonal_eq_exp_trace_complex_fintype
        (RCLike.ofReal ∘ hA.eigenvalues : ι → ℂ))
  have htrace : Matrix.trace D = Matrix.trace A := by
    rw [Matrix.IsHermitian.trace_eq_sum_eigenvalues hA]
    simp [D, Matrix.trace_diagonal]
  calc
    Matrix.det (NormedSpace.exp A)
        = Matrix.det
            (NormedSpace.exp
              ((U : Matrix ι ι ℂ) * D * star (U : Matrix ι ι ℂ))) := by
            rw [hspec]
    _ = Matrix.det
          ((U : Matrix ι ι ℂ) * NormedSpace.exp D * star (U : Matrix ι ι ℂ)) := by
            rw [hexp]
    _ = Matrix.det (NormedSpace.exp D) := hdetConj
    _ = NormedSpace.exp (Matrix.trace D) := hD
    _ = NormedSpace.exp (Matrix.trace A) := by rw [htrace]

section UpperTriangular

open Matrix.Norms.Frobenius

variable {ι : Type*}

/-- Coordinate projection from a finite matrix to one entry, as a continuous linear map. -/
private noncomputable def matrixEntryCLM (i j : ι) : Matrix ι ι ℂ →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) j : (ι → ℂ) →L[ℂ] ℂ).comp
    (ContinuousLinearMap.proj (R := ℂ) i : Matrix ι ι ℂ →L[ℂ] (ι → ℂ))

@[simp]
private lemma matrixEntryCLM_apply (i j : ι) (A : Matrix ι ι ℂ) :
    matrixEntryCLM i j A = A i j := by
  change ((ContinuousLinearMap.proj (R := ℂ) i : Matrix ι ι ℂ →L[ℂ] (ι → ℂ)) A) j =
    A i j
  rfl

lemma upperTriangular_pow
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℂ} (hA : A.BlockTriangular id) (k : ℕ) :
    (A ^ k).BlockTriangular id := by
  induction k with
  | zero =>
      simpa using (Matrix.blockTriangular_one (b := id) (R := ℂ) (m := ι))
  | succ k ih =>
      simpa [pow_succ] using ih.mul hA

lemma exp_upperTriangular
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℂ} (hA : A.BlockTriangular id) :
    (NormedSpace.exp A).BlockTriangular id := by
  intro i j hij
  rw [NormedSpace.exp_eq_tsum_rat]
  let f : ℕ → Matrix ι ι ℂ := fun k => ((↑k.factorial : ℚ)⁻¹ : ℚ) • A ^ k
  have hs : Summable f := by
    simpa [f] using (NormedSpace.expSeries_summable' (𝕂 := ℚ) A)
  have hmap := (matrixEntryCLM i j).map_tsum hs
  have hzero : (fun k => matrixEntryCLM i j (f k)) = fun _ : ℕ => 0 := by
    funext k
    simp [f, upperTriangular_pow hA k hij]
  change (∑' k : ℕ, f k) i j = 0
  simpa [matrixEntryCLM] using
    (by rw [hmap, hzero, tsum_zero] :
      matrixEntryCLM i j (∑' k : ℕ, f k) = 0)

lemma upperTriangular_pow_diag
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℂ} (hA : A.BlockTriangular id) (k : ℕ) (i : ι) :
    (A ^ k) i i = (A i i) ^ k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      trans (A ^ k) i i * A i i
      · refine Finset.sum_eq_single i ?_ ?_
        · intro l _ hli
          by_cases hlt : l < i
          · simp [upperTriangular_pow hA k hlt]
          · have hil : i < l := lt_of_le_of_ne (le_of_not_gt hlt) hli.symm
            simp [hA hil]
        · intro hi
          simp at hi
      · rw [ih]
        exact (pow_succ (A i i) k).symm

lemma upperTriangular_exp_diag
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {A : Matrix ι ι ℂ} (hA : A.BlockTriangular id) (i : ι) :
    (NormedSpace.exp A) i i = NormedSpace.exp (A i i) := by
  rw [NormedSpace.exp_eq_tsum_rat, NormedSpace.exp_eq_tsum_rat]
  let f : ℕ → Matrix ι ι ℂ := fun k => ((↑k.factorial : ℚ)⁻¹ : ℚ) • A ^ k
  let g : ℕ → ℂ := fun k => ((↑k.factorial : ℚ)⁻¹ : ℚ) • (A i i) ^ k
  have hs : Summable f := by
    simpa [f] using (NormedSpace.expSeries_summable' (𝕂 := ℚ) A)
  have hmap := (matrixEntryCLM i i).map_tsum hs
  have hfg : (fun k => matrixEntryCLM i i (f k)) = g := by
    funext k
    simp [f, g, upperTriangular_pow_diag hA k i]
  change (∑' k : ℕ, f k) i i = ∑' k : ℕ, g k
  simpa [matrixEntryCLM, g] using
    (by rw [hmap, hfg] :
      matrixEntryCLM i i (∑' k : ℕ, f k) = ∑' k : ℕ, g k)

/--
Trace-determinant law for complex upper-triangular matrices.

This is a non-diagonal no-calculus owner theorem.  It does not close the
unrestricted mathlib TODO, but it proves the full identity on the canonical
triangular normal form target.
-/
theorem det_exp_eq_exp_trace_of_upperTriangular
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.BlockTriangular id) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) := by
  rw [Matrix.det_of_upperTriangular (exp_upperTriangular hA)]
  rw [Matrix.trace]
  calc
    (∏ i, NormedSpace.exp A i i) = ∏ i, NormedSpace.exp (A i i) := by
      exact Finset.prod_congr rfl (fun i _ => upperTriangular_exp_diag hA i)
    _ = NormedSpace.exp (∑ i, A i i) := by
      simpa using (NormedSpace.exp_sum (s := Finset.univ) (f := fun i => A i i)).symm

/--
Trace-determinant law for matrices explicitly conjugate to an upper-triangular
matrix by a unit.
-/
theorem det_exp_eq_exp_trace_of_units_upperTriangular
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (U : (Matrix ι ι ℂ)ˣ) (T : Matrix ι ι ℂ) (hT : T.BlockTriangular id) :
    Matrix.det
        (NormedSpace.exp
          ((U : Matrix ι ι ℂ) * T * (↑U⁻¹ : Matrix ι ι ℂ))) =
      NormedSpace.exp
        (Matrix.trace
          ((U : Matrix ι ι ℂ) * T * (↑U⁻¹ : Matrix ι ι ℂ))) := by
  have hExp :
      NormedSpace.exp ((U : Matrix ι ι ℂ) * T * (↑U⁻¹ : Matrix ι ι ℂ)) =
        (U : Matrix ι ι ℂ) * NormedSpace.exp T * (↑U⁻¹ : Matrix ι ι ℂ) := by
    simpa using Matrix.exp_units_conj U T
  have hDetConj :
      Matrix.det ((U : Matrix ι ι ℂ) * NormedSpace.exp T * (↑U⁻¹ : Matrix ι ι ℂ)) =
        Matrix.det (NormedSpace.exp T) := by
    simpa using Matrix.det_units_conj U (NormedSpace.exp T)
  have hTraceConj :
      Matrix.trace ((U : Matrix ι ι ℂ) * T * (↑U⁻¹ : Matrix ι ι ℂ)) =
        Matrix.trace T := by
    simpa using Matrix.trace_units_conj U T
  calc
    Matrix.det
        (NormedSpace.exp
          ((U : Matrix ι ι ℂ) * T * (↑U⁻¹ : Matrix ι ι ℂ)))
        = Matrix.det
            ((U : Matrix ι ι ℂ) * NormedSpace.exp T * (↑U⁻¹ : Matrix ι ι ℂ)) := by
            rw [hExp]
    _ = Matrix.det (NormedSpace.exp T) := hDetConj
    _ = NormedSpace.exp (Matrix.trace T) := det_exp_eq_exp_trace_of_upperTriangular T hT
    _ = NormedSpace.exp
          (Matrix.trace ((U : Matrix ι ι ℂ) * T * (↑U⁻¹ : Matrix ι ι ℂ))) := by
            rw [hTraceConj]

/-- Trace-determinant law from an explicit upper-triangularization equality. -/
theorem det_exp_eq_exp_trace_of_is_units_upperTriangular
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (U : (Matrix ι ι ℂ)ˣ) (T : Matrix ι ι ℂ)
    (hT : T.BlockTriangular id)
    (hA : A = (U : Matrix ι ι ℂ) * T * (↑U⁻¹ : Matrix ι ι ℂ)) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) := by
  rw [hA]
  exact det_exp_eq_exp_trace_of_units_upperTriangular U T hT

end UpperTriangular

end MatrixExponentialTraceDet

namespace Matrix

open scoped BigOperators Matrix
open Matrix.Norms.Frobenius

lemma hasDerivAt_matrix_exp_smul_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (t : ℂ) :
    HasDerivAt
      (fun z : ℂ => NormedSpace.exp (z • A))
      (NormedSpace.exp (t • A) * A)
      t := by
  simpa using (hasDerivAt_exp_smul_const (x := A) (t := t))

lemma hasDerivAt_matrix_exp_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (t : ℂ) :
    HasDerivAt
      (fun z : ℂ => NormedSpace.exp (z • A))
      (A * NormedSpace.exp (t • A))
      t := by
  simpa using (hasDerivAt_exp_smul_const' (x := A) (t := t))

lemma matrix_exp_smul_inverse
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (t : ℂ) :
    (NormedSpace.exp (t • A))⁻¹ = NormedSpace.exp ((-t) • A) := by
  rw [← Matrix.exp_neg (t • A)]
  congr 1
  simp

lemma matrix_exp_smul_mul_exp_neg_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (t : ℂ) :
    NormedSpace.exp (t • A) * NormedSpace.exp ((-t) • A) = 1 := by
  rw [← matrix_exp_smul_inverse, Matrix.nonsing_inv_eq_ringInverse]
  exact Ring.mul_inverse_cancel _ (Matrix.isUnit_exp (t • A))

lemma trace_inv_mul_mul_of_isUnit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X A : Matrix ι ι ℂ) (hX : IsUnit X) :
    Matrix.trace (X⁻¹ * A * X) = Matrix.trace A := by
  simpa using Matrix.trace_conj' hX A

/--
Mathlib-style spelling of the real diagonal determinant/exponential trace law.

This is a proved diagonal form of the finite-dimensional `H¹` volume cocycle.
The unrestricted theorem for arbitrary matrices is still not asserted here.
-/
theorem det_exp_diagonal_eq_exp_trace_real
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) := by
  rw [Matrix.exp_diagonal, Matrix.det_diagonal, Matrix.trace_diagonal]
  simpa [Pi.coe_exp] using (NormedSpace.exp_sum (s := Finset.univ) (f := v)).symm

/--
Mathlib-style spelling of the complex diagonal determinant/exponential trace law.
-/
theorem det_exp_diagonal_eq_exp_trace_complex
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) :=
  MatrixExponentialTraceDet.det_exp_diagonal_eq_exp_trace_complex_fintype v

/--
Mathlib-style spelling for matrices explicitly diagonalized by a unit.

This proves `det (exp A) = exp (trace A)` for the displayed matrix
`A = U * diagonal v * U⁻¹`.
-/
theorem det_exp_eq_exp_trace_of_units_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : (Matrix ι ι ℂ)ˣ) (v : ι → ℂ) :
    Matrix.det
        (NormedSpace.exp
          ((U : Matrix ι ι ℂ) * Matrix.diagonal v * (↑U⁻¹ : Matrix ι ι ℂ))) =
      NormedSpace.exp
        (Matrix.trace
          ((U : Matrix ι ι ℂ) * Matrix.diagonal v * (↑U⁻¹ : Matrix ι ι ℂ))) :=
  MatrixExponentialTraceDet.det_exp_eq_exp_trace_of_units_diagonal U v

/--
Mathlib-style spelling for a complex matrix supplied with an explicit
diagonalization equality.
-/
theorem det_exp_eq_exp_trace_of_is_units_diagonalizable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (U : (Matrix ι ι ℂ)ˣ) (v : ι → ℂ)
    (hA : A = (U : Matrix ι ι ℂ) * Matrix.diagonal v * (↑U⁻¹ : Matrix ι ι ℂ)) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) :=
  MatrixExponentialTraceDet.det_exp_eq_exp_trace_of_is_units_diagonalizable
    A U v hA

/--
Mathlib-style spelling for complex upper-triangular matrices.
-/
theorem det_exp_eq_exp_trace_of_upperTriangular
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (hA : A.BlockTriangular id) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) :=
  MatrixExponentialTraceDet.det_exp_eq_exp_trace_of_upperTriangular A hA

/--
Mathlib-style spelling for matrices explicitly conjugate to an upper-triangular
matrix by a unit.
-/
theorem det_exp_eq_exp_trace_of_units_upperTriangular
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (U : (Matrix ι ι ℂ)ˣ) (T : Matrix ι ι ℂ) (hT : T.BlockTriangular id) :
    Matrix.det
        (NormedSpace.exp
          ((U : Matrix ι ι ℂ) * T * (↑U⁻¹ : Matrix ι ι ℂ))) =
      NormedSpace.exp
        (Matrix.trace
          ((U : Matrix ι ι ℂ) * T * (↑U⁻¹ : Matrix ι ι ℂ))) :=
  MatrixExponentialTraceDet.det_exp_eq_exp_trace_of_units_upperTriangular
    U T hT

/--
Mathlib-style spelling for a complex matrix supplied with an explicit
upper-triangularization equality.
-/
theorem det_exp_eq_exp_trace_of_is_units_upperTriangular
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (A : Matrix ι ι ℂ) (U : (Matrix ι ι ℂ)ˣ) (T : Matrix ι ι ℂ)
    (hT : T.BlockTriangular id)
    (hA : A = (U : Matrix ι ι ℂ) * T * (↑U⁻¹ : Matrix ι ι ℂ)) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) :=
  MatrixExponentialTraceDet.det_exp_eq_exp_trace_of_is_units_upperTriangular
    A U T hT hA

/--
Mathlib-style spelling of the currently proved non-diagonal theorem:
complex Hermitian matrices satisfy `det (exp A) = exp (trace A)`.
-/
theorem det_exp_eq_exp_trace_of_isHermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    Matrix.det (NormedSpace.exp A) =
      NormedSpace.exp (Matrix.trace A) :=
  MatrixExponentialTraceDet.det_exp_eq_exp_trace_of_isHermitian A hA

end Matrix
