import InfoGeometry.Canonical.GLSupermatrixCore
import InfoGeometry.NCG.BerezinianExponentialSupertrace

/-!
# Finite supertrace scale/kernel decomposition

On the native finite `(m|n)` matrix carrier, this file proves that when `m ≠ n`
every element has a unique decomposition into a scalar identity component and
a supertrace-zero remainder. In balanced dimensions the scalar direction lies
inside the kernel (including the degenerate `0|0` case). The odd block sector
also has zero supertrace, so it is contained in this kernel rather than being
an additional summand beside it.

This is a finite supermatrix result. It does not identify the supermatrix
grading with a Krein polarization or assert a projective metric decomposition.
The Berezinian results below use the existing NCG block-diagonal exponential
chart; no equivalence with the canonical `SuperMatrix` carrier is asserted.
-/

namespace InfoGeometry.Canonical.SupertraceScaleKernelSplit

open Matrix
open GLSupermatrixCore
open InfoGeometry.NCG.BerezinianExponentialSupertrace

variable {m n : ℕ}

/-- The scalar endomorphism on both diagonal parity blocks. -/
def scalarBlockGenerator (a : ℝ) : SuperMatrix m n ℝ :=
  evenMatrix (a • (1 : Matrix (Fin m) (Fin m) ℝ))
    (a • (1 : Matrix (Fin n) (Fin n) ℝ))

/-- The supertrace detects a scalar generator by the superdimension. -/
theorem supertrace_scalarBlockGenerator (a : ℝ) :
    supertrace (scalarBlockGenerator (m := m) (n := n) a) =
      ((m : ℝ) - (n : ℝ)) * a := by
  change supertrace (evenMatrix (a • (1 : Matrix (Fin m) (Fin m) ℝ))
    (a • (1 : Matrix (Fin n) (Fin n) ℝ))) = _
  rw [supertrace_evenMatrix]
  simp only [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, Fintype.card_fin]
  ring

/-- In balanced dimensions every scalar generator has zero supertrace. -/
theorem supertrace_scalarBlockGenerator_balanced (m : ℕ) (a : ℝ) :
    supertrace (scalarBlockGenerator (m := m) (n := m) a) = 0 := by
  rw [supertrace_scalarBlockGenerator]
  simp

/-- The proposed `diag(A, -Aᵀ)` block has supertrace `2 * trace A`. -/
theorem supertrace_even_neg_transpose (A : Matrix (Fin m) (Fin m) ℝ) :
    supertrace (evenMatrix A (-Aᵀ)) = 2 * Matrix.trace A := by
  rw [supertrace_evenMatrix, Matrix.trace_neg, Matrix.trace_transpose]
  ring

/-- The proposed volume block is supertraceless exactly when `A` is traceless. -/
theorem supertrace_even_neg_transpose_eq_zero_iff
    (A : Matrix (Fin m) (Fin m) ℝ) :
    supertrace (evenMatrix A (-Aᵀ)) = 0 ↔ Matrix.trace A = 0 := by
  rw [supertrace_even_neg_transpose]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  · intro h
    rw [h, mul_zero]

/-- Berezinian scale law for the existing finite block-diagonal exponential chart. -/
theorem blockBerezinian_exp_scalar_scale (a : ℝ) :
    blockBerezinian
        (expBlockDiag (a • (1 : Matrix (Fin m) (Fin m) ℝ))
          (a • (1 : Matrix (Fin n) (Fin n) ℝ))) =
      Real.exp (((m : ℝ) - (n : ℝ)) * a) := by
  rw [blockBerezinian_exp_eq_exp_supertrace_generator]
  simp only [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, Fintype.card_fin]
  congr 1
  ring

/-- Balanced scalar scaling is invisible to this block-diagonal Berezinian. -/
theorem blockBerezinian_exp_scalar_scale_balanced (m : ℕ) (a : ℝ) :
    blockBerezinian
        (expBlockDiag (a • (1 : Matrix (Fin m) (Fin m) ℝ))
          (a • (1 : Matrix (Fin m) (Fin m) ℝ))) = 1 := by
  rw [blockBerezinian_exp_scalar_scale]
  simp

/-- A trace-free `diag(A, -Aᵀ)` generator has unit Berezinian exponential. -/
theorem blockBerezinian_exp_even_neg_transpose_eq_one
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : Matrix.trace A = 0) :
    blockBerezinian (expBlockDiag A (-Aᵀ)) = 1 := by
  rw [blockBerezinian_exp_eq_exp_supertrace_generator]
  simp [Matrix.trace_neg, Matrix.trace_transpose, hA]

/-- Supertrace is additive on the finite matrix carrier. -/
theorem supertrace_add (X Y : SuperMatrix m n ℝ) :
    supertrace (X + Y) = supertrace X + supertrace Y := by
  change Matrix.trace (blockA X + blockA Y) - Matrix.trace (blockD X + blockD Y) =
    (Matrix.trace (blockA X) - Matrix.trace (blockD X)) +
      (Matrix.trace (blockA Y) - Matrix.trace (blockD Y))
  rw [Matrix.trace_add, Matrix.trace_add]
  ring

/-- Supertrace subtraction on the finite matrix carrier. -/
theorem supertrace_sub (X Y : SuperMatrix m n ℝ) :
    supertrace (X - Y) = supertrace X - supertrace Y := by
  change Matrix.trace (blockA X - blockA Y) - Matrix.trace (blockD X - blockD Y) =
    (Matrix.trace (blockA X) - Matrix.trace (blockD X)) -
      (Matrix.trace (blockA Y) - Matrix.trace (blockD Y))
  rw [Matrix.trace_sub, Matrix.trace_sub]
  ring

/-- For unequal dimensions, a scalar generator is supertraceless only at zero. -/
theorem scalarBlockGenerator_supertrace_zero_iff (h_dim : m ≠ n) (a : ℝ) :
    supertrace (scalarBlockGenerator (m := m) (n := n) a) = 0 ↔ a = 0 := by
  have hdimR : ((m : ℝ) - (n : ℝ)) ≠ 0 := by
    intro h
    apply h_dim
    exact Nat.cast_injective (sub_eq_zero.mp h)
  rw [supertrace_scalarBlockGenerator]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hdimR
  · intro h
    rw [h, mul_zero]

/-- Canonical coefficient of the scalar component when the dimensions differ. -/
noncomputable def scaleCoefficient (X : SuperMatrix m n ℝ) : ℝ :=
  supertrace X / ((m : ℝ) - (n : ℝ))

/--
For unequal even and odd dimensions, every matrix is a scalar generator plus a
supertrace-zero remainder, with scalar coefficient `str(X)/(m-n)`.
-/
theorem scalar_kernel_decomposition (h_dim : m ≠ n) (X : SuperMatrix m n ℝ) :
    X = scalarBlockGenerator (scaleCoefficient X) +
      (X - scalarBlockGenerator (scaleCoefficient X)) ∧
    supertrace (X - scalarBlockGenerator (scaleCoefficient X)) = 0 := by
  have hdimR : ((m : ℝ) - (n : ℝ)) ≠ 0 := by
    intro h
    apply h_dim
    exact Nat.cast_injective (sub_eq_zero.mp h)
  constructor
  · calc
      X = (X - scalarBlockGenerator (scaleCoefficient X)) +
          scalarBlockGenerator (scaleCoefficient X) := (sub_add_cancel _ _).symm
      _ = scalarBlockGenerator (scaleCoefficient X) +
          (X - scalarBlockGenerator (scaleCoefficient X)) := add_comm _ _
  · rw [supertrace_sub, supertrace_scalarBlockGenerator]
    unfold scaleCoefficient
    field_simp [hdimR]
    ring

/-- Any two scalar-plus-kernel decompositions have the same scalar and remainder. -/
theorem scalar_kernel_decomposition_unique
    (h_dim : m ≠ n) (a b : ℝ) (Y Z : SuperMatrix m n ℝ)
    (hY : supertrace Y = 0) (hZ : supertrace Z = 0)
    (hdecomp : scalarBlockGenerator (m := m) (n := n) a + Y =
      scalarBlockGenerator (m := m) (n := n) b + Z) :
    a = b ∧ Y = Z := by
  have hdimR : ((m : ℝ) - (n : ℝ)) ≠ 0 := by
    intro h
    apply h_dim
    exact Nat.cast_injective (sub_eq_zero.mp h)
  have htr := congrArg supertrace hdecomp
  rw [supertrace_add, supertrace_add,
    supertrace_scalarBlockGenerator, supertrace_scalarBlockGenerator,
    hY, hZ] at htr
  have htr' : ((m : ℝ) - (n : ℝ)) * a = ((m : ℝ) - (n : ℝ)) * b := by
    simpa using htr
  have hab : a = b := mul_left_cancel₀ hdimR htr'
  constructor
  · exact hab
  · rw [hab] at hdecomp
    exact add_left_cancel hdecomp

end InfoGeometry.Canonical.SupertraceScaleKernelSplit
