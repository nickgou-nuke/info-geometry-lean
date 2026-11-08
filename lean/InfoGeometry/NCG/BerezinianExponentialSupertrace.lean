import InfoGeometry.NCG.BlockSupermatrixGradedTrace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Analysis.LieExponentialTraceDeterminant

noncomputable section

open Matrix

namespace InfoGeometry.NCG.BerezinianExponentialSupertrace

open InfoGeometry.NCG.BlockSupermatrixGradedTrace
open InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix

variable {m n : Type*}
variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Block-diagonal exponential of an even `(m|n)` generator. -/
def expBlockDiag (A : Matrix m m ℝ) (D : Matrix n n ℝ) :
    SuperMatrix (m := m) (n := n) (R := ℝ) :=
  ⟨NormedSpace.exp A, 0, 0, NormedSpace.exp D⟩

/-- Determinant-ratio Berezinian on the block-diagonal real model. -/
def blockBerezinian
    (M : SuperMatrix (m := m) (n := n) (R := ℝ)) : ℝ :=
  Matrix.det M.A / Matrix.det M.D

/-- The exponential block is homogeneous even. -/
theorem expBlockDiag_even (A : Matrix m m ℝ) (D : Matrix n n ℝ) :
    IsHomogeneous .even (expBlockDiag A D) := by
  constructor <;> rfl

/-- Its supertrace is the difference of traces of the two exponentials. -/
@[simp]
theorem supertrace_expBlockDiag (A : Matrix m m ℝ) (D : Matrix n n ℝ) :
    supertrace (expBlockDiag A D) =
      Matrix.trace (NormedSpace.exp A) - Matrix.trace (NormedSpace.exp D) :=
  rfl

/--
Finite block-diagonal Berezinian exponential law:

`Ber(exp A, exp D) = exp(Tr A - Tr D)`.

This is the branch-free exponential form of the supertrace/Berezinian identity.
-/
theorem blockBerezinian_exp_eq_exp_supertrace_generator
    (A : Matrix m m ℝ) (D : Matrix n n ℝ) :
    blockBerezinian (expBlockDiag A D) =
      Real.exp (Matrix.trace A - Matrix.trace D) := by
  unfold blockBerezinian expBlockDiag
  have hA :=
    InfoGeometry.Cocycle.MatrixDetExpTrace.det_exp_eq_exp_trace_real A
  have hD :=
    InfoGeometry.Cocycle.MatrixDetExpTrace.det_exp_eq_exp_trace_real D
  rw [hA, hD]
  simpa only [Real.exp_eq_exp_ℝ] using
    (Real.exp_sub (Matrix.trace A) (Matrix.trace D)).symm

/-- The same law written with the supertrace of the logarithmic generator. -/
theorem blockBerezinian_exp_eq_exp_supertrace
    (A : Matrix m m ℝ) (D : Matrix n n ℝ) :
    blockBerezinian (expBlockDiag A D) =
      Real.exp (supertrace
        (⟨A, 0, 0, D⟩ : SuperMatrix (m := m) (n := n) (R := ℝ))) := by
  simpa [supertrace] using
    blockBerezinian_exp_eq_exp_supertrace_generator A D

/-- The Berezinian of every real block exponential is strictly positive. -/
theorem blockBerezinian_exp_pos
    (A : Matrix m m ℝ) (D : Matrix n n ℝ) :
    0 < blockBerezinian (expBlockDiag A D) := by
  rw [blockBerezinian_exp_eq_exp_supertrace_generator]
  exact Real.exp_pos _

/--
Negative-log form on the canonical exponential chart:

`-log Ber(exp X) = -str X`.

No matrix logarithm or branch choice is required: `X` is the supplied
logarithmic generator and `exp X` is its positive-determinant chart image.
-/
theorem neg_log_blockBerezinian_exp_eq_neg_supertrace
    (A : Matrix m m ℝ) (D : Matrix n n ℝ) :
    -Real.log (blockBerezinian (expBlockDiag A D)) =
      -supertrace
        (⟨A, 0, 0, D⟩ : SuperMatrix (m := m) (n := n) (R := ℝ)) := by
  rw [blockBerezinian_exp_eq_exp_supertrace]
  rw [Real.log_exp]

/-- Unit supertrace generator gives unit Berezinian on the exponential chart. -/
theorem blockBerezinian_exp_eq_one_of_supertrace_zero
    (A : Matrix m m ℝ) (D : Matrix n n ℝ)
    (h : supertrace
      (⟨A, 0, 0, D⟩ : SuperMatrix (m := m) (n := n) (R := ℝ)) = 0) :
    blockBerezinian (expBlockDiag A D) = 1 := by
  rw [blockBerezinian_exp_eq_exp_supertrace, h]
  simp

/--
Constant-generator finite graded flow law:

`Ber(exp(t A), exp(t D)) = exp(t * str(A,D))`.

This is a kinematic Jacobian-volume statement.  No entropy-production
interpretation is built into the theorem.
-/
theorem blockBerezinian_lieFlow
    (A : Matrix m m ℝ) (D : Matrix n n ℝ) (t : ℝ) :
    blockBerezinian (expBlockDiag (t • A) (t • D)) =
      Real.exp
        (t * supertrace
          (⟨A, 0, 0, D⟩ : SuperMatrix (m := m) (n := n) (R := ℝ))) := by
  rw [blockBerezinian_exp_eq_exp_supertrace_generator]
  simp [supertrace, Matrix.trace_smul, smul_eq_mul]
  congr 1
  ring

/-- Negative logarithm of the finite graded flow Berezinian. -/
theorem neg_log_blockBerezinian_lieFlow
    (A : Matrix m m ℝ) (D : Matrix n n ℝ) (t : ℝ) :
    -Real.log (blockBerezinian (expBlockDiag (t • A) (t • D))) =
      -(t * supertrace
        (⟨A, 0, 0, D⟩ : SuperMatrix (m := m) (n := n) (R := ℝ))) := by
  rw [blockBerezinian_lieFlow, Real.log_exp]

/-- Supertrace-zero generators preserve the finite graded Berezinian volume at every time. -/
theorem blockBerezinian_lieFlow_eq_one_of_supertrace_zero
    (A : Matrix m m ℝ) (D : Matrix n n ℝ)
    (h : supertrace
      (⟨A, 0, 0, D⟩ : SuperMatrix (m := m) (n := n) (R := ℝ)) = 0) :
    ∀ t : ℝ, blockBerezinian (expBlockDiag (t • A) (t • D)) = 1 := by
  intro t
  rw [blockBerezinian_lieFlow, h]
  simp

end InfoGeometry.NCG.BerezinianExponentialSupertrace
