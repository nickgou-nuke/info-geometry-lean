import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite matrix Jacobi derivative

This owner derives the determinant-rate identity for a real finite matrix path.
The determinant derivative is first expanded by the Leibniz formula, then the
coefficient is identified using the determinant derivative at the identity and
an affine factorization through the inverse matrix.
-/

noncomputable section

namespace InfoGeometry.Analysis.FiniteMatrixJacobiDerivative

open scoped Matrix Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The explicit Leibniz coefficient for the derivative of `det` at `A` in
the matrix direction `B`. -/
def detLeibnizDerivative (A B : Matrix n n ℝ) : ℝ :=
  ∑ σ : Equiv.Perm n,
    (Equiv.Perm.sign σ : ℝ) *
      ∑ i : n, (∏ j ∈ Finset.univ.erase i, A (σ j) j) * B (σ i) i

/-- Differentiating the finite Leibniz expansion entrywise. -/
theorem hasDerivAt_det_leibniz
    {X : ℝ → Matrix n n ℝ} {X' : Matrix n n ℝ} {t : ℝ}
    (hX : ∀ i j : n, HasDerivAt (fun z : ℝ => X z i j) (X' i j) t) :
    HasDerivAt
      (fun z : ℝ => Matrix.det (X z))
      (detLeibnizDerivative (X t) X') t := by
  have hsum :
      HasDerivAt
        (fun z : ℝ =>
          ∑ σ : Equiv.Perm n,
            (Equiv.Perm.sign σ : ℝ) * ∏ i : n, X z (σ i) i)
        (detLeibnizDerivative (X t) X') t := by
    apply HasDerivAt.fun_sum
    intro σ _hσ
    have hprod :
        HasDerivAt
          (fun z : ℝ => ∏ i : n, X z (σ i) i)
          (∑ i : n,
            (∏ j ∈ Finset.univ.erase i, X t (σ j) j) * X' (σ i) i) t := by
      simpa [detLeibnizDerivative, smul_eq_mul] using
        (HasDerivAt.fun_finset_prod (u := Finset.univ)
          (f := fun i z => X z (σ i) i)
          (f' := fun i => X' (σ i) i)
          (x := t)
          (fun i _hi => hX (σ i) i))
    simpa [detLeibnizDerivative, Finset.mul_sum] using
      hprod.const_mul (Equiv.Perm.sign σ : ℝ)
  simpa [detLeibnizDerivative, Matrix.det_apply'] using hsum

/-- The identity-line determinant derivative is the matrix trace. -/
theorem hasDerivAt_det_one_add_smul_zero (M : Matrix n n ℝ) :
    HasDerivAt (fun z : ℝ => Matrix.det (1 + z • M)) (Matrix.trace M) 0 := by
  let p : ℝ[X] := Matrix.det (1 + (Polynomial.X : ℝ[X]) • M.map Polynomial.C)
  have hpder : p.derivative.eval 0 = Matrix.trace M := by
    simpa [p] using Matrix.derivative_det_one_add_X_smul (R := ℝ) M
  have hp := Polynomial.hasDerivAt (p := p) (x := 0)
  rw [hpder] at hp
  convert hp using 1
  ext z
  simp [p, eval_det, ← Matrix.smul_eq_mul_diagonal]

/-- At an invertible matrix, the Leibniz coefficient is the Jacobi trace
factor. -/
theorem detLeibnizDerivative_eq_det_mul_trace_inv_mul
    (A B : Matrix n n ℝ) (hA : IsUnit A.det) :
    detLeibnizDerivative A B =
      A.det * Matrix.trace (A⁻¹ * B) := by
  let C : Matrix n n ℝ := A⁻¹ * B
  have hfactor (s : ℝ) :
      A + s • B = A * (1 + s • C) := by
    dsimp [C]
    calc
      A + s • B = A + s • ((A * A⁻¹) * B) := by
        rw [Matrix.mul_nonsing_inv A hA]
        simp
      _ = A + s • (A * (A⁻¹ * B)) := by
        rw [Matrix.mul_assoc]
      _ = A + A * (s • (A⁻¹ * B)) := by
        rw [Matrix.mul_smul]
      _ = A * (1 + s • (A⁻¹ * B)) := by
        rw [Matrix.mul_add, Matrix.mul_one]
  have hraw :
      HasDerivAt
        (fun s : ℝ => Matrix.det (A + s • B))
        (detLeibnizDerivative A B) 0 := by
    have h := hasDerivAt_det_leibniz
      (X := fun s : ℝ => A + s • B) (X' := B) (t := 0) (by
        intro i j
        simpa [Pi.smul_apply, smul_eq_mul, add_comm] using
          (((hasDerivAt_id' (0 : ℝ)).mul_const (B i j)).const_add
            (A i j)))
    simpa [detLeibnizDerivative] using h
  have hbase :
      HasDerivAt
        (fun s : ℝ => Matrix.det (1 + s • C))
        (Matrix.trace C) 0 :=
    hasDerivAt_det_one_add_smul_zero C
  have hprod := hbase.const_mul A.det
  have hprod' :
      HasDerivAt
        (fun s : ℝ => A.det * Matrix.det (1 + s • C))
        (A.det * Matrix.trace C) 0 := by
    simpa [mul_comm] using hprod
  have hdet_eq :
      (fun s : ℝ => Matrix.det (A + s • B)) =
        (fun s : ℝ => A.det * Matrix.det (1 + s • C)) := by
    funext s
    rw [hfactor, Matrix.det_mul]
  rw [hdet_eq] at hraw
  exact hraw.unique hprod'

/-- Jacobi's determinant derivative formula for a finite real matrix path. -/
theorem hasDerivAt_det_of_hasDerivAt_matrix
    {J : ℝ → Matrix n n ℝ} {Jdot : Matrix n n ℝ} {t : ℝ}
    (hJ : ∀ i j : n, HasDerivAt (fun u : ℝ => J u i j) (Jdot i j) t)
    (hinv : IsUnit (J t)) :
    HasDerivAt
      (fun u : ℝ => (J u).det)
      ((J t).det * Matrix.trace ((J t)⁻¹ * Jdot)) t := by
  have hraw := hasDerivAt_det_leibniz (X := J) (X' := Jdot) hJ
  have hunitdet : IsUnit (J t).det :=
    (Matrix.isUnit_iff_isUnit_det (J t)).mp hinv
  have hcoeff := detLeibnizDerivative_eq_det_mul_trace_inv_mul
    (J t) Jdot hunitdet
  rw [hcoeff] at hraw
  exact hraw

end InfoGeometry.Analysis.FiniteMatrixJacobiDerivative
