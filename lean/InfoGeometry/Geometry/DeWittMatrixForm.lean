/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# The spacetime DeWitt pairing on symmetric matrix perturbations

This file defines the actual finite-dimensional matrix carrier and the
Lorentzian trace pairing

`Tr (η h η k) - (1/2) Tr (η h) Tr (η k)`.

The owner proves symmetry, bilinearity, the entrywise quadratic expansion,
nondegeneracy away from dimension two, a Sylvester weighted-sign normal form,
and the exact inertia `(D(D-1)/2, D)` for `D ≥ 3`. It also constructs `D`
mutually orthogonal normalized hyperbolic pairs and the positive spatial
anisotropic kernel, proves its dimension `D(D-3)/2`, and splits the spatial
block carrier as that kernel plus the explicit trace/shift section image. The
full spacetime carrier is also proved to be the internal direct sum of that
positive anisotropic image and the explicit `D`-plane hyperbolic frame.
-/

noncomputable section

namespace InfoGeometry.Geometry.DeWittMatrixForm

open Matrix

/-- Symmetric real matrix perturbations in spacetime dimension `D`. -/
def SymmetricPerturbation (D : ℕ) : Submodule ℝ (Matrix (Fin D) (Fin D) ℝ) where
  carrier := {h | h.IsSymm}
  add_mem' := fun hh hk => hh.add hk
  zero_mem' := Matrix.isSymm_zero
  smul_mem' := fun c _h hh => hh.smul c

/-- Reconstruct a symmetric block matrix from its corner, first row, and
remaining symmetric block. -/
private def symmetricUnpeelMatrix (d : ℕ) (a : ℝ) (r : Fin d → ℝ)
    (S : SymmetricPerturbation d) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Fin.cases (fun j => Fin.cases a (fun j => r j) j)
    (fun i j => Fin.cases (r i) (fun j => S.1 i j) j)

private theorem symmetricUnpeelMatrix_isSymm (d : ℕ) (a : ℝ) (r : Fin d → ℝ)
    (S : SymmetricPerturbation d) : (symmetricUnpeelMatrix d a r S).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  cases i using Fin.cases with
  | zero => cases j using Fin.cases <;> simp [symmetricUnpeelMatrix]
  | succ i =>
      cases j using Fin.cases with
      | zero => simp [symmetricUnpeelMatrix]
      | succ j => simpa [symmetricUnpeelMatrix] using S.2.apply i j

/-- Recursive linear decomposition of a symmetric `(d+1) × (d+1)` matrix
into one corner entry, its first row, and a symmetric `d × d` block. -/
def symmetricPeel (d : ℕ) :
    SymmetricPerturbation (d + 1) ≃ₗ[ℝ]
      ℝ × ((Fin d → ℝ) × SymmetricPerturbation d) where
  toFun h := (h.1 0 0,
    (fun i => h.1 0 i.succ,
      ⟨fun i j => h.1 i.succ j.succ, by
        ext i j
        exact h.2.apply i.succ j.succ⟩))
  invFun t := ⟨symmetricUnpeelMatrix d t.1 t.2.1 t.2.2,
    symmetricUnpeelMatrix_isSymm d t.1 t.2.1 t.2.2⟩
  left_inv h := by
    apply Subtype.ext
    ext i j
    cases i using Fin.cases with
    | zero => cases j using Fin.cases <;> simp [symmetricUnpeelMatrix]
    | succ i =>
        cases j using Fin.cases with
        | zero => simp [symmetricUnpeelMatrix, h.2.apply]
        | succ j => rfl
  right_inv t := by
    rcases t with ⟨a, r, S⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        rfl
  map_add' h k := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        rfl
  map_smul' c h := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        rfl

/-- Dimension recursion obtained from the actual symmetric-matrix
decomposition. -/
theorem finrank_symmetricPerturbation_succ (d : ℕ) :
    Module.finrank ℝ (SymmetricPerturbation (d + 1)) =
      d + 1 + Module.finrank ℝ (SymmetricPerturbation d) := by
  rw [(symmetricPeel d).finrank_eq]
  simp [Module.finrank_fintype_fun_eq_card]
  omega

/-- Exact dimension of symmetric matrix perturbations, derived from the
recursive matrix decomposition rather than assumed as an ambient count. -/
theorem finrank_symmetricPerturbation (D : ℕ) :
    Module.finrank ℝ (SymmetricPerturbation D) = Nat.choose (D + 1) 2 := by
  induction D with
  | zero =>
      simpa using
        (Module.finrank_eq_zero_of_subsingleton ℝ (SymmetricPerturbation 0))
  | succ d ih =>
      have hchoose : Nat.choose (d + 2) 2 = d + 1 + Nat.choose (d + 1) 2 := by
        rw [show d + 2 = (d + 1) + 1 by omega, Nat.choose_succ_succ']
        simp
      rw [finrank_symmetricPerturbation_succ, ih, hchoose]

/-- The diagonal Lorentzian form `diag(-1,1,…,1)`. -/
def minkowskiMatrix (D : ℕ) : Matrix (Fin D) (Fin D) ℝ :=
  Matrix.diagonal fun i => if i.val = 0 then -1 else 1

/-- The diagonal coefficient of the chosen Lorentzian form. -/
def minkowskiSign (i : Fin D) : ℝ := if i.val = 0 then -1 else 1

/-- DeWitt's trace-reversed pairing, restricted to symmetric perturbations. -/
def pairing (D : ℕ) (h k : SymmetricPerturbation D) : ℝ :=
  Matrix.trace (minkowskiMatrix D * h.1 * minkowskiMatrix D * k.1) -
    ((1 : ℝ) / 2) * Matrix.trace (minkowskiMatrix D * h.1) *
      Matrix.trace (minkowskiMatrix D * k.1)

/-- The quadratic value associated with the DeWitt pairing. -/
def quadratic (D : ℕ) (h : SymmetricPerturbation D) : ℝ := pairing D h h

/-- The trace-reversal operator representing the DeWitt pairing in the
ordinary Frobenius trace pairing. -/
def traceReverse (D : ℕ) (h : SymmetricPerturbation D) :
    Matrix (Fin D) (Fin D) ℝ :=
  minkowskiMatrix D * h.1 * minkowskiMatrix D -
    (((1 : ℝ) / 2) * Matrix.trace (minkowskiMatrix D * h.1)) • minkowskiMatrix D

/-- Trace reversal preserves the symmetric-matrix carrier. -/
private theorem traceReverse_isSymm (D : ℕ) (h : SymmetricPerturbation D) :
    (traceReverse D h).IsSymm := by
  let η := minkowskiMatrix D
  have hη : η.IsSymm := by
    ext i j
    by_cases hij : i = j
    · subst j
      rfl
    · change (minkowskiMatrix D) j i = (minkowskiMatrix D) i j
      rw [show (minkowskiMatrix D) i j = 0 by
        exact Matrix.diagonal_apply_ne _ hij,
        show (minkowskiMatrix D) j i = 0 by
        exact Matrix.diagonal_apply_ne _ (Ne.symm hij)]
  have hcore : (η * h.1 * η).IsSymm := by
    change (η * h.1 * η)ᵀ = η * h.1 * η
    simp only [Matrix.transpose_mul, hη.eq, h.2.eq]
    simp [Matrix.mul_assoc]
  unfold traceReverse
  exact hcore.sub (hη.smul _)

/-- The DeWitt pairing is the Frobenius trace pairing against trace reversal. -/
theorem pairing_eq_traceReverse_mul (D : ℕ) (h k : SymmetricPerturbation D) :
    pairing D h k = Matrix.trace (traceReverse D h * k.1) := by
  unfold pairing traceReverse
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul]
  ring

/-- Entrywise form of the DeWitt quadratic form. The sum keeps the full
ordered pair of matrix indices; no scalar or diagonal carrier is substituted. -/
theorem quadratic_entry_expansion (D : ℕ) (h : SymmetricPerturbation D) :
    quadratic D h =
      (∑ i : Fin D, ∑ j : Fin D,
        minkowskiSign i * minkowskiSign j * (h.1 i j) ^ 2) -
        ((1 : ℝ) / 2) *
          (∑ i : Fin D, minkowskiSign i * h.1 i i) ^ 2 := by
  let η := minkowskiMatrix D
  have hconj : η * h.1 * η = fun i j =>
      minkowskiSign i * h.1 i j * minkowskiSign j := by
    ext i j
    simp [η, minkowskiMatrix, minkowskiSign, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
  have hfirst : Matrix.trace (η * h.1 * η * h.1) =
      ∑ i : Fin D, ∑ j : Fin D,
        minkowskiSign i * minkowskiSign j * (h.1 i j) ^ 2 := by
    rw [show η * h.1 * η * h.1 = (η * h.1 * η) * h.1 by simp [mul_assoc], hconj]
    simp only [Matrix.trace]
    apply Finset.sum_congr rfl
    intro i hi
    change (∑ j : Fin D,
      (minkowskiSign i * h.1 i j * minkowskiSign j) * h.1 j i) = _
    apply Finset.sum_congr rfl
    intro j hj
    rw [h.2.apply j i]
    ring
  have hlinear : Matrix.trace (η * h.1) =
      ∑ i : Fin D, minkowskiSign i * h.1 i i := by
    simp [η, minkowskiMatrix, minkowskiSign, Matrix.trace, Matrix.diagonal_mul]
  unfold quadratic pairing
  change Matrix.trace (η * h.1 * η * h.1) -
    ((1 : ℝ) / 2) * Matrix.trace (η * h.1) * Matrix.trace (η * h.1) = _
  rw [hfirst, hlinear]
  ring

/-- Entrywise form of the full bilinear DeWitt pairing. It retains both
ordered matrix indices and exposes the cross terms needed to construct
orthogonal subspaces. -/
theorem pairing_entry_expansion (D : ℕ)
    (h k : SymmetricPerturbation D) :
    pairing D h k =
      (∑ i : Fin D, ∑ j : Fin D,
        minkowskiSign i * minkowskiSign j * (h.1 i j * k.1 i j)) -
        ((1 : ℝ) / 2) *
          (∑ i : Fin D, minkowskiSign i * h.1 i i) *
          (∑ i : Fin D, minkowskiSign i * k.1 i i) := by
  let η := minkowskiMatrix D
  have hconj : η * h.1 * η = fun i j =>
      minkowskiSign i * h.1 i j * minkowskiSign j := by
    ext i j
    simp [η, minkowskiMatrix, minkowskiSign, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
  have hfirst : Matrix.trace (η * h.1 * η * k.1) =
      ∑ i : Fin D, ∑ j : Fin D,
        minkowskiSign i * minkowskiSign j * (h.1 i j * k.1 i j) := by
    rw [show η * h.1 * η * k.1 = (η * h.1 * η) * k.1 by simp [mul_assoc], hconj]
    simp only [Matrix.trace]
    apply Finset.sum_congr rfl
    intro i hi
    change (∑ j : Fin D,
      (minkowskiSign i * h.1 i j * minkowskiSign j) * k.1 j i) = _
    apply Finset.sum_congr rfl
    intro j hj
    rw [k.2.apply j i]
    ring
  have htraceH : Matrix.trace (η * h.1) =
      ∑ i : Fin D, minkowskiSign i * h.1 i i := by
    simp [η, minkowskiMatrix, minkowskiSign, Matrix.trace, Matrix.diagonal_mul]
  have htraceK : Matrix.trace (η * k.1) =
      ∑ i : Fin D, minkowskiSign i * k.1 i i := by
    simp [η, minkowskiMatrix, minkowskiSign, Matrix.trace, Matrix.diagonal_mul]
  unfold pairing
  change Matrix.trace (η * h.1 * η * k.1) -
      ((1 : ℝ) / 2) * Matrix.trace (η * h.1) * Matrix.trace (η * k.1) = _
  rw [hfirst, htraceH, htraceK]

/-- The trace of the spatial block of a symmetric perturbation in dimension
`d + 1`. -/
def spatialTrace (d : ℕ) (h : SymmetricPerturbation (d + 1)) : ℝ :=
  ∑ i : Fin d, h.1 i.succ i.succ

/-- Sum of squares of the spatial diagonal entries. -/
def spatialDiagonalSquareSum (d : ℕ) (h : SymmetricPerturbation (d + 1)) : ℝ :=
  ∑ i : Fin d, (h.1 i.succ i.succ) ^ 2

/-- The spatial trace-free diagonal contribution is nonnegative. This is the
finite-dimensional Cauchy–Schwarz estimate on the actual spatial diagonal
coordinates. -/
theorem spatialDiagonalVariance_nonneg (d : ℕ)
    (h : SymmetricPerturbation (d + 1)) (hd : d ≠ 0) :
    0 ≤ spatialDiagonalSquareSum d h -
      (spatialTrace d h) ^ 2 / (d : ℝ) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hd)
  have hcs : (spatialTrace d h) ^ 2 ≤
      (d : ℝ) * spatialDiagonalSquareSum d h := by
    simpa [spatialTrace, spatialDiagonalSquareSum, Fintype.card_fin] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin d)))
        (f := fun i : Fin d => h.1 i.succ i.succ))
  have hdiv : (spatialTrace d h) ^ 2 / (d : ℝ) ≤
      spatialDiagonalSquareSum d h := by
    apply (div_le_iff₀ hdpos).2
    simpa [mul_comm] using hcs
  linarith

/-- Sum of squares of the spatial block entries, with both matrix indices
retained. -/
def spatialEntrySquareSum (d : ℕ) (h : SymmetricPerturbation (d + 1)) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, (h.1 i.succ j.succ) ^ 2

/-- Sum of squares of the off-diagonal entries of the spatial block. Both
orders of each off-diagonal pair are retained. -/
def spatialOffDiagonalSquareSum (d : ℕ) (h : SymmetricPerturbation (d + 1)) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    if i = j then 0 else (h.1 i.succ j.succ) ^ 2

/-- Off-diagonal spatial entries contribute a nonnegative sum of squares. -/
theorem spatialOffDiagonalSquareSum_nonneg (d : ℕ)
    (h : SymmetricPerturbation (d + 1)) :
    0 ≤ spatialOffDiagonalSquareSum d h := by
  unfold spatialOffDiagonalSquareSum
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  split_ifs <;> positivity

/-- The trace-free diagonal and off-diagonal spatial directions together have
nonnegative DeWitt contribution. -/
theorem spatialPositiveContribution_nonneg (d : ℕ)
    (h : SymmetricPerturbation (d + 1)) (hd : d ≠ 0) :
    0 ≤ spatialDiagonalSquareSum d h -
        (spatialTrace d h) ^ 2 / (d : ℝ) +
      spatialOffDiagonalSquareSum d h := by
  exact add_nonneg (spatialDiagonalVariance_nonneg d h hd)
    (spatialOffDiagonalSquareSum_nonneg d h)

/-- The spatial entry sum splits into its diagonal and off-diagonal squares. -/
theorem spatialEntrySquareSum_eq_diagonal_add_offDiagonal (d : ℕ)
    (h : SymmetricPerturbation (d + 1)) :
    spatialEntrySquareSum d h =
      spatialDiagonalSquareSum d h + spatialOffDiagonalSquareSum d h := by
  unfold spatialEntrySquareSum spatialDiagonalSquareSum spatialOffDiagonalSquareSum
  have hrow (i : Fin d) :
      (∑ j : Fin d, (h.1 i.succ j.succ) ^ 2) =
        (h.1 i.succ i.succ) ^ 2 +
          ∑ j : Fin d, if i = j then 0 else (h.1 i.succ j.succ) ^ 2 := by
    calc
      (∑ j : Fin d, (h.1 i.succ j.succ) ^ 2) =
          ∑ j : Fin d,
            ((if i = j then (h.1 i.succ j.succ) ^ 2 else 0) +
              (if i = j then 0 else (h.1 i.succ j.succ) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : i = j <;> simp [hij]
      _ = (h.1 i.succ i.succ) ^ 2 +
            ∑ j : Fin d, if i = j then 0 else (h.1 i.succ j.succ) ^ 2 := by
        rw [Finset.sum_add_distrib]
        simp
  calc
    (∑ i : Fin d, ∑ j : Fin d, (h.1 i.succ j.succ) ^ 2) =
        ∑ i : Fin d, ((h.1 i.succ i.succ) ^ 2 +
          ∑ j : Fin d, if i = j then 0 else (h.1 i.succ j.succ) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hrow i
    _ = (∑ i : Fin d, (h.1 i.succ i.succ) ^ 2) +
          ∑ i : Fin d, ∑ j : Fin d,
            if i = j then 0 else (h.1 i.succ j.succ) ^ 2 := by
      rw [Finset.sum_add_distrib]

/-- Sum of squares of the time-space entries. -/
def shiftSquareSum (d : ℕ) (h : SymmetricPerturbation (d + 1)) : ℝ :=
  ∑ i : Fin d, (h.1 0 i.succ) ^ 2

/-- Exact lapse/shift/spatial-block expansion of the DeWitt quadratic form.
This is an identity on the full symmetric-matrix carrier, not a diagonal
matrix restriction. -/
theorem quadratic_lapse_shift_spatial_expansion (d : ℕ)
    (h : SymmetricPerturbation (d + 1)) :
    quadratic (d + 1) h =
      (1 / 2 : ℝ) * (h.1 0 0 + spatialTrace d h) ^ 2 +
        spatialEntrySquareSum d h - (spatialTrace d h) ^ 2 -
        2 * shiftSquareSum d h := by
  have htrace : (∑ i : Fin (d + 1), minkowskiSign i * h.1 i i) =
      -h.1 0 0 + spatialTrace d h := by
    rw [Fin.sum_univ_succ]
    simp [minkowskiSign, spatialTrace]
  have hrows :
      ∀ i : Fin d,
        (∑ j : Fin (d + 1),
            minkowskiSign i.succ * minkowskiSign j * (h.1 i.succ j) ^ 2) =
          - (h.1 0 i.succ) ^ 2 +
            ∑ j : Fin d, (h.1 i.succ j.succ) ^ 2 := by
    intro i
    rw [Fin.sum_univ_succ]
    have hs : h.1 i.succ 0 = h.1 0 i.succ := h.2.apply 0 i.succ
    simp [minkowskiSign, hs]
  have hentry :
      (∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
          minkowskiSign i * minkowskiSign j * (h.1 i j) ^ 2) =
        (h.1 0 0) ^ 2 - 2 * shiftSquareSum d h + spatialEntrySquareSum d h := by
    rw [Fin.sum_univ_succ]
    have htop :
        (∑ j : Fin (d + 1),
            minkowskiSign (0 : Fin (d + 1)) * minkowskiSign j * (h.1 0 j) ^ 2) =
          (h.1 0 0) ^ 2 - shiftSquareSum d h := by
      rw [Fin.sum_univ_succ]
      simp [minkowskiSign, shiftSquareSum]
      ring
    rw [htop]
    have hsp :
        (∑ i : Fin d, ∑ j : Fin (d + 1),
            minkowskiSign i.succ * minkowskiSign j *
              (h.1 i.succ j) ^ 2) =
          - shiftSquareSum d h + spatialEntrySquareSum d h := by
      calc
        (∑ i : Fin d, ∑ j : Fin (d + 1),
            minkowskiSign i.succ * minkowskiSign j *
              (h.1 i.succ j) ^ 2) =
            ∑ i : Fin d, (-(h.1 0 i.succ) ^ 2 +
              ∑ j : Fin d, (h.1 i.succ j.succ) ^ 2) := by
                apply Finset.sum_congr rfl
                intro i hi
                exact hrows i
        _ = - shiftSquareSum d h + spatialEntrySquareSum d h := by
              rw [Finset.sum_add_distrib]
              simp only [shiftSquareSum, spatialEntrySquareSum,
                Finset.sum_neg_distrib]
    rw [hsp]
    ring
  rw [quadratic_entry_expansion, hentry, htrace]
  ring

/-- Exact sum-of-squares decomposition of the DeWitt form into lapse, the
trace-free spatial diagonal, spatial off-diagonal, shift, and spatial trace
terms. The identity holds for the full symmetric matrix. -/
theorem quadratic_variance_expansion (d : ℕ)
    (h : SymmetricPerturbation (d + 1)) (hd : d ≠ 0) :
    quadratic (d + 1) h =
      (1 / 2 : ℝ) * (h.1 0 0 + spatialTrace d h) ^ 2 +
        (spatialDiagonalSquareSum d h -
          (spatialTrace d h) ^ 2 / (d : ℝ)) +
        spatialOffDiagonalSquareSum d h - 2 * shiftSquareSum d h -
        ((d - 1 : ℝ) / d) * (spatialTrace d h) ^ 2 := by
  rw [quadratic_lapse_shift_spatial_expansion,
    spatialEntrySquareSum_eq_diagonal_add_offDiagonal]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  field_simp [hdR]
  ring

/-- Matrix representative of the negative lapse-trace and shift directions.
The first coordinate is the spatial trace; the spatial diagonal is its
constant-trace representative, and the remaining coordinates are the shifts. -/
private def negativeModeMatrix (d : ℕ) (v : Fin (d + 1) → ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Fin.cases
    (fun j => Fin.cases (-v 0) (fun i => v i.succ) j)
    (fun i => fun j => Fin.cases (v i.succ)
      (fun j => if i = j then v 0 / (d : ℝ) else 0) j)

private theorem negativeModeMatrix_isSymm (d : ℕ) (v : Fin (d + 1) → ℝ) :
    (negativeModeMatrix d v).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases <;> simp [negativeModeMatrix]
  | succ i =>
      cases j using Fin.cases with
      | zero => simp [negativeModeMatrix]
      | succ j => simp [negativeModeMatrix, eq_comm]

/-- The negative lapse/shift subspace, as a linear map into the actual
symmetric-matrix carrier. -/
def negativeModes (d : ℕ) :
    (Fin (d + 1) → ℝ) →ₗ[ℝ] SymmetricPerturbation (d + 1) where
  toFun v := ⟨negativeModeMatrix d v, negativeModeMatrix_isSymm d v⟩
  map_add' v w := by
    apply Subtype.ext
    ext i j
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp [negativeModeMatrix] <;> (try split_ifs) <;> ring
  map_smul' c v := by
    apply Subtype.ext
    ext i j
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp [negativeModeMatrix] <;> (try split_ifs) <;> ring

@[simp]
private theorem negativeModes_apply_00 (d : ℕ) (v : Fin (d + 1) → ℝ) :
    (negativeModes d v).1 0 0 = -v 0 := by
  rfl

@[simp]
private theorem negativeModes_apply_shift (d : ℕ) (v : Fin (d + 1) → ℝ)
    (i : Fin d) : (negativeModes d v).1 0 i.succ = v i.succ := by
  rfl

@[simp]
private theorem negativeModes_apply_spatial_diag (d : ℕ) (v : Fin (d + 1) → ℝ)
    (i : Fin d) :
    (negativeModes d v).1 i.succ i.succ = v 0 / (d : ℝ) := by
  simp [negativeModes, negativeModeMatrix]

private theorem negativeModes_apply_spatial_offdiag (d : ℕ) (v : Fin (d + 1) → ℝ)
    (i j : Fin d) (hij : i ≠ j) :
    (negativeModes d v).1 i.succ j.succ = 0 := by
  simp [negativeModes, negativeModeMatrix, hij]

/-- The trace/lapse coordinate plane inside the full matrix carrier. -/
def traceLapseMode (d : ℕ) (x y : ℝ) : SymmetricPerturbation (d + 1) :=
  ⟨Fin.cases
      (fun j => Fin.cases (x - y) (fun _ => 0) j)
      (fun i j => Fin.cases 0 (fun j => if i = j then y / (d : ℝ) else 0) j),
    by
      apply Matrix.IsSymm.ext
      intro i j
      cases i using Fin.cases with
      | zero => cases j using Fin.cases <;> simp
      | succ i =>
          cases j using Fin.cases with
          | zero => simp
          | succ j => simp [eq_comm]⟩

@[simp] private theorem traceLapseMode_apply_00 (d : ℕ) (x y : ℝ) :
    (traceLapseMode d x y).1 0 0 = x - y := rfl

@[simp] private theorem traceLapseMode_apply_timeSpace (d : ℕ) (x y : ℝ)
    (i : Fin d) : (traceLapseMode d x y).1 0 i.succ = 0 := rfl

@[simp] private theorem traceLapseMode_apply_spatial_diag (d : ℕ) (x y : ℝ)
    (i : Fin d) : (traceLapseMode d x y).1 i.succ i.succ = y / (d : ℝ) := by
  simp [traceLapseMode]

/-- The DeWitt form on the lapse/spatial-trace plane has one positive and one
negative direction for every `d ≥ 2`. -/
theorem quadratic_traceLapseMode (d : ℕ) (hd : 2 ≤ d) (x y : ℝ) :
    quadratic (d + 1) (traceLapseMode d x y) =
      (1 / 2 : ℝ) * x ^ 2 - ((d - 1 : ℝ) / d) * y ^ 2 := by
  have hdNe : d ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hd)
  rw [quadratic_variance_expansion d (traceLapseMode d x y) hdNe]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdNe
  have htrace : spatialTrace d (traceLapseMode d x y) = y := by
    unfold spatialTrace
    calc
      (∑ i : Fin d, (traceLapseMode d x y).1 i.succ i.succ) =
          ∑ i : Fin d, y / (d : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp
      _ = y := by
            rw [Finset.sum_const, Finset.card_fin]
            simp only [nsmul_eq_mul]
            field_simp [hdR]
  have hdiag : spatialDiagonalSquareSum d (traceLapseMode d x y) =
      y ^ 2 / (d : ℝ) := by
    unfold spatialDiagonalSquareSum
    calc
      (∑ i : Fin d, ((traceLapseMode d x y).1 i.succ i.succ) ^ 2) =
          ∑ i : Fin d, (y / (d : ℝ)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            simp
      _ = y ^ 2 / (d : ℝ) := by
            rw [Finset.sum_const, Finset.card_fin]
            simp only [nsmul_eq_mul]
            field_simp [hdR]
  have hoff : spatialOffDiagonalSquareSum d (traceLapseMode d x y) = 0 := by
    unfold spatialOffDiagonalSquareSum
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, traceLapseMode]
  have hshift : shiftSquareSum d (traceLapseMode d x y) = 0 := by
    simp [shiftSquareSum]
  rw [htrace, hdiag, hoff, hshift]
  simp only [traceLapseMode_apply_00]
  field_simp [hdR]
  ring_nf

/-- The bilinear pairing on the full matrix carrier restricts to the diagonal
trace/lapse plane with the same two coefficients as its quadratic form. -/
theorem pairing_traceLapseMode (d : ℕ) (hd : 2 ≤ d)
    (x₁ y₁ x₂ y₂ : ℝ) :
    pairing (d + 1) (traceLapseMode d x₁ y₁) (traceLapseMode d x₂ y₂) =
      (1 / 2 : ℝ) * x₁ * x₂ - ((d - 1 : ℝ) / d) * y₁ * y₂ := by
  rw [pairing_entry_expansion]
  have hdNe : d ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hd)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdNe
  have htrace (x y : ℝ) :
      (∑ i : Fin (d + 1), minkowskiSign i *
        (traceLapseMode d x y).1 i i) = -x + 2 * y := by
    rw [Fin.sum_univ_succ]
    simp [minkowskiSign]
    field_simp [hdR]
    ring_nf
  have hentry :
      (∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
        minkowskiSign i * minkowskiSign j *
          ((traceLapseMode d x₁ y₁).1 i j *
            (traceLapseMode d x₂ y₂).1 i j)) =
        (x₁ - y₁) * (x₂ - y₂) + y₁ * y₂ / (d : ℝ) := by
    simp [traceLapseMode, minkowskiSign, Fin.sum_univ_succ, Finset.sum_const,
      nsmul_eq_mul]
    field_simp [hdR]
  rw [hentry, htrace x₁ y₁, htrace x₂ y₂]
  field_simp [hdR]
  ring_nf

/-- The DeWitt lapse/trace plane contains an explicit pair of null vectors
with nonzero mutual pairing. This is an actual hyperbolic-plane witness in
the symmetric-matrix carrier, for every spatial dimension `d ≥ 2`. -/
theorem traceLapse_hyperbolic_pair (d : ℕ) (hd : 2 ≤ d) :
    let r := Real.sqrt (2 * ((d - 1 : ℝ) / d))
    let u := traceLapseMode d r 1
    let v := traceLapseMode d (-r) 1
    quadratic (d + 1) u = 0 ∧ quadratic (d + 1) v = 0 ∧
      pairing (d + 1) u v = -2 * ((d - 1 : ℝ) / d) := by
  let c : ℝ := (d - 1 : ℝ) / d
  let r : ℝ := Real.sqrt (2 * c)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hdgt : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (sub_pos.mpr hdgt) (by positivity)
  have hr2 : r ^ 2 = 2 * c := by
    dsimp [r]
    rw [Real.sq_sqrt (by positivity)]
  change quadratic (d + 1) (traceLapseMode d r 1) = 0 ∧
    quadratic (d + 1) (traceLapseMode d (-r) 1) = 0 ∧
      pairing (d + 1) (traceLapseMode d r 1) (traceLapseMode d (-r) 1) = -2 * c
  constructor
  · rw [quadratic_traceLapseMode d hd]
    rw [hr2]
    ring
  constructor
  · rw [quadratic_traceLapseMode d hd]
    rw [neg_sq, hr2]
    ring
  · rw [pairing_traceLapseMode d hd]
    rw [show (1 / 2 : ℝ) * r * (-r) = -(1 / 2 : ℝ) * r ^ 2 by ring, hr2]
    ring


/-- The lapse/shift parametrization is injective: its zero-zero entry and
time-space row recover every input coordinate. -/
theorem negativeModes_injective (d : ℕ) : Function.Injective (negativeModes d) := by
  intro v w h
  funext i
  cases i using Fin.cases with
  | zero =>
      have h00 := congrArg (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => M 0 0)
        (congrArg Subtype.val h)
      simpa using congrArg Neg.neg h00
  | succ i =>
      have h0i := congrArg (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => M 0 i.succ)
        (congrArg Subtype.val h)
      simpa using h0i

/-- Exact quadratic value on the trace-and-shift mode family. -/
theorem quadratic_negativeModes (d : ℕ)
    (v : Fin (d + 1) → ℝ) (hd : d ≠ 0) :
    quadratic (d + 1) (negativeModes d v) =
      -2 * (∑ i : Fin d, (v i.succ) ^ 2) -
        ((d - 1 : ℝ) / d) * (v 0) ^ 2 := by
  rw [quadratic_variance_expansion d (negativeModes d v) hd]
  simp only [spatialTrace, spatialDiagonalSquareSum, spatialOffDiagonalSquareSum,
    shiftSquareSum, negativeModes_apply_00, negativeModes_apply_shift,
    negativeModes_apply_spatial_diag]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have htrace : (∑ i : Fin d, v 0 / (d : ℝ)) = v 0 := by
    rw [Finset.sum_const, Finset.card_fin]
    simp only [nsmul_eq_mul]
    field_simp [hdR]
  have hdiag : (∑ i : Fin d, (v 0 / (d : ℝ)) ^ 2) =
      (v 0) ^ 2 / (d : ℝ) := by
    rw [Finset.sum_const, Finset.card_fin]
    simp only [nsmul_eq_mul]
    field_simp [hdR]
  have hoff : (∑ i : Fin d, ∑ j : Fin d,
      if i = j then 0 else ((negativeModes d v).1 i.succ j.succ) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hij : i = j
    · simp [hij]
    · rw [if_neg hij, negativeModes_apply_spatial_offdiag d v i j hij]
      simp
  rw [htrace, hdiag, hoff]
  field_simp [hdR]
  ring_nf

/-- In spacetime dimension at least three, every nonzero lapse/shift mode has
strictly negative DeWitt norm. -/
theorem quadratic_negativeModes_neg (d : ℕ) (hd : 2 ≤ d)
    (v : Fin (d + 1) → ℝ) (hv : v ≠ 0) :
    quadratic (d + 1) (negativeModes d v) < 0 := by
  have hdNe : d ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hd)
  rw [quadratic_negativeModes d v hdNe]
  have hd1 : 1 < d := lt_of_lt_of_le (by decide : 1 < 2) hd
  have hdR : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hcoeff : 0 < ((d : ℝ) - 1) / (d : ℝ) := by
    exact div_pos (by linarith) (by positivity)
  by_cases hv0 : v 0 = 0
  · have hshift : ∃ i : Fin d, v i.succ ≠ 0 := by
      by_contra h
      push_neg at h
      apply hv
      funext i
      cases i using Fin.cases with
      | zero => exact hv0
      | succ j => exact h j
    obtain ⟨i, hi⟩ := hshift
    have hsum : 0 < ∑ i : Fin d, (v i.succ) ^ 2 := by
      apply Finset.sum_pos' (fun j hj => sq_nonneg (v j.succ))
      exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
    nlinarith [hsum]
  · have hv0sq : 0 < (v 0) ^ 2 := sq_pos_of_ne_zero hv0
    have hsum : 0 ≤ ∑ i : Fin d, (v i.succ) ^ 2 :=
      Finset.sum_nonneg fun i hi => sq_nonneg (v i.succ)
    nlinarith

/-- Trace of the diagonal of a symmetric spatial block. -/
def blockTrace (d : ℕ) (S : SymmetricPerturbation d) : ℝ :=
  ∑ i : Fin d, S.1 i i

/-- The positive-mode embedding puts a symmetric spatial block in the spatial
corner, sets the shift to zero, and chooses lapse equal to its spatial trace. -/
private def positiveModeMatrix (d : ℕ) (S : SymmetricPerturbation d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Fin.cases
    (fun j => Fin.cases (blockTrace d S) (fun _ => 0) j)
    (fun i => fun j => Fin.cases 0 (fun j => S.1 i j) j)

private theorem positiveModeMatrix_isSymm (d : ℕ) (S : SymmetricPerturbation d) :
    (positiveModeMatrix d S).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  cases i using Fin.cases with
  | zero => cases j using Fin.cases <;> simp [positiveModeMatrix]
  | succ i =>
      cases j using Fin.cases with
      | zero => simp [positiveModeMatrix]
      | succ j => simpa [positiveModeMatrix] using S.2.apply i j

/-- Linear embedding of symmetric spatial matrices into spacetime symmetric
perturbations. -/
def positiveModes (d : ℕ) :
    SymmetricPerturbation d →ₗ[ℝ] SymmetricPerturbation (d + 1) where
  toFun S := ⟨positiveModeMatrix d S, positiveModeMatrix_isSymm d S⟩
  map_add' S T := by
    apply Subtype.ext
    ext i j
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp [positiveModeMatrix, blockTrace, Finset.sum_add_distrib]
  map_smul' c S := by
    apply Subtype.ext
    ext i j
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp [positiveModeMatrix, blockTrace, Finset.mul_sum]

@[simp]
private theorem positiveModes_apply_00 (d : ℕ) (S : SymmetricPerturbation d) :
    (positiveModes d S).1 0 0 = blockTrace d S := by
  rfl

@[simp]
private theorem positiveModes_apply_timeSpace (d : ℕ) (S : SymmetricPerturbation d)
    (i : Fin d) : (positiveModes d S).1 0 i.succ = 0 := by
  rfl

@[simp]
private theorem positiveModes_apply_spatial (d : ℕ) (S : SymmetricPerturbation d)
    (i j : Fin d) : (positiveModes d S).1 i.succ j.succ = S.1 i j := by
  rfl

/-- The DeWitt form on the embedded spatial block is the sum of its entry
squares plus the square of its trace. -/
theorem quadratic_positiveModes (d : ℕ) (S : SymmetricPerturbation d) :
    quadratic (d + 1) (positiveModes d S) =
      (blockTrace d S) ^ 2 + ∑ i : Fin d, ∑ j : Fin d, (S.1 i j) ^ 2 := by
  rw [quadratic_lapse_shift_spatial_expansion]
  simp only [spatialTrace, spatialEntrySquareSum, shiftSquareSum,
    positiveModes_apply_00, positiveModes_apply_timeSpace,
    positiveModes_apply_spatial, blockTrace]
  have hzero : (∑ i : Fin d, (0 : ℝ) ^ 2) = 0 := by simp
  rw [hzero]
  ring_nf

/-- The positive-mode embedding is injective because its spatial corner
recovers the input matrix. -/
theorem positiveModes_injective (d : ℕ) : Function.Injective (positiveModes d) := by
  intro S T h
  apply Subtype.ext
  ext i j
  have hij := congrArg
    (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => M i.succ j.succ)
    (congrArg Subtype.val h)
  simpa using hij

/-- The positive spatial-block image in the full spacetime perturbation space. -/
def positiveModeSubspace (d : ℕ) :
    Submodule ℝ (SymmetricPerturbation (d + 1)) :=
  LinearMap.range (positiveModes d)

/-- Every nonzero embedded spatial block has strictly positive DeWitt norm. -/
theorem quadratic_positiveModes_pos (d : ℕ) (S : SymmetricPerturbation d)
    (hS : S ≠ 0) : quadratic (d + 1) (positiveModes d S) > 0 := by
  rw [quadratic_positiveModes]
  have hexists : ∃ i j : Fin d, S.1 i j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hS
    apply Subtype.ext
    ext i j
    exact h i j
  obtain ⟨i, j, hij⟩ := hexists
  have hterm : 0 < (S.1 i j) ^ 2 := sq_pos_of_ne_zero hij
  have hrow : (S.1 i j) ^ 2 ≤ ∑ k : Fin d, (S.1 i k) ^ 2 :=
    Finset.single_le_sum (s := (Finset.univ : Finset (Fin d)))
      (f := fun k => (S.1 i k) ^ 2) (fun k hk => sq_nonneg (S.1 i k)) (Finset.mem_univ j)
  have htotal : (∑ l : Fin d, (S.1 i l) ^ 2) ≤
      ∑ k : Fin d, ∑ l : Fin d, (S.1 k l) ^ 2 :=
    Finset.single_le_sum (s := (Finset.univ : Finset (Fin d)))
      (f := fun k => ∑ l : Fin d, (S.1 k l) ^ 2)
      (fun k hk => Finset.sum_nonneg fun l hl => sq_nonneg (S.1 k l))
      (Finset.mem_univ i)
  have htrace : 0 ≤ (blockTrace d S) ^ 2 := sq_nonneg _
  nlinarith

/-- The actual image of the lapse/shift coordinates in the symmetric-matrix
space. -/
def negativeModeSubspace (d : ℕ) :
    Submodule ℝ (SymmetricPerturbation (d + 1)) :=
  LinearMap.range (negativeModes d)

/-- The spatial symmetric block of a spacetime perturbation, read from the
actual lower-right matrix corner. -/
def spatialBlock (d : ℕ) (h : SymmetricPerturbation (d + 1)) :
    SymmetricPerturbation d :=
  (symmetricPeel d h).2.2

/-- The time-space row of a perturbation, retaining all shift components. -/
def shiftCoordinates (d : ℕ) (h : SymmetricPerturbation (d + 1)) : Fin d → ℝ :=
  fun i => h.1 0 i.succ

/-- The identity operator in the symmetric spatial matrix space. -/
def spatialIdentity (d : ℕ) : SymmetricPerturbation d :=
  ⟨1, by
    change (1 : Matrix (Fin d) (Fin d) ℝ).IsSymm
    exact Matrix.isSymm_one⟩

/-- Spatial trace-free part, formed inside the symmetric-matrix space by
subtracting the scalar trace component. -/
def spatialTraceFreePart (d : ℕ) (S : SymmetricPerturbation d) :
    SymmetricPerturbation d :=
  S - (blockTrace d S / (d : ℝ)) • spatialIdentity d

theorem blockTrace_add (d : ℕ) (S T : SymmetricPerturbation d) :
    blockTrace d (S + T) = blockTrace d S + blockTrace d T := by
  simp [blockTrace, Finset.sum_add_distrib]

theorem blockTrace_sub (d : ℕ) (S T : SymmetricPerturbation d) :
    blockTrace d (S - T) = blockTrace d S - blockTrace d T := by
  simp [blockTrace, Finset.sum_sub_distrib]

theorem blockTrace_smul (d : ℕ) (c : ℝ) (S : SymmetricPerturbation d) :
    blockTrace d (c • S) = c * blockTrace d S := by
  simp [blockTrace, Finset.mul_sum]

theorem blockTrace_spatialTraceFreePart (d : ℕ) (S : SymmetricPerturbation d)
    (hd : d ≠ 0) : blockTrace d (spatialTraceFreePart d S) = 0 := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hone : blockTrace d (spatialIdentity d) = (d : ℝ) := by
    simp [blockTrace, spatialIdentity, Matrix.one_apply]
  rw [spatialTraceFreePart, blockTrace_sub, blockTrace_smul, hone]
  rw [show blockTrace d S / (d : ℝ) * (d : ℝ) = blockTrace d S by
    field_simp [hdR]]
  ring

theorem spatialTraceFreePart_add_scalar (d : ℕ) (S : SymmetricPerturbation d)
    (hd : d ≠ 0) :
    spatialTraceFreePart d S + (blockTrace d S / (d : ℝ)) •
      spatialIdentity d = S := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  apply Subtype.ext
  ext i j
  change (spatialTraceFreePart d S).1 i j +
    (blockTrace d S / (d : ℝ)) * (spatialIdentity d).1 i j = S.1 i j
  by_cases hij : i = j
  · subst j
    simp [spatialTraceFreePart, spatialIdentity, Matrix.one_apply]
  · simp [spatialTraceFreePart, spatialIdentity, Matrix.one_apply, hij]

private def shiftOnlyVector (d : ℕ) (h : SymmetricPerturbation (d + 1)) :
    Fin (d + 1) → ℝ :=
  Fin.cons 0 (shiftCoordinates d h)

/-- Every symmetric spacetime matrix is the sum of its lapse/trace plane,
its time-space shift matrix, and its trace-free spatial matrix. This is an
actual reconstruction identity on the full matrix carrier. -/
theorem symmetricPerturbation_lapse_shift_traceFree_decomposition
    (d : ℕ) (hd : d ≠ 0) (h : SymmetricPerturbation (d + 1)) :
    traceLapseMode d
        (h.1 0 0 + spatialTrace d h) (spatialTrace d h) +
      negativeModes d (shiftOnlyVector d h) +
      positiveModes d (spatialTraceFreePart d (spatialBlock d h)) = h := by
  have hspatial : spatialTrace d h = blockTrace d (spatialBlock d h) := by
    simp [spatialTrace, blockTrace, spatialBlock, symmetricPeel]
  have hsplit := spatialTraceFreePart_add_scalar d (spatialBlock d h) hd
  apply Subtype.ext
  ext i j
  change (traceLapseMode d (h.1 0 0 + spatialTrace d h) (spatialTrace d h)).1 i j +
      (negativeModes d (shiftOnlyVector d h)).1 i j +
      (positiveModes d (spatialTraceFreePart d (spatialBlock d h))).1 i j = h.1 i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero =>
          simp [traceLapseMode_apply_00, negativeModes_apply_00,
            shiftOnlyVector, positiveModes_apply_00,
            blockTrace_spatialTraceFreePart d (spatialBlock d h) hd]
      | succ j =>
          simp [traceLapseMode_apply_timeSpace, negativeModes_apply_shift,
            shiftOnlyVector, shiftCoordinates, positiveModes_apply_timeSpace]
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          have hs := h.2.apply 0 i.succ
          change 0 + (shiftOnlyVector d h) i.succ + 0 = h.1 i.succ 0
          simp [shiftOnlyVector, shiftCoordinates, hs]
      | succ j =>
          have hblock := congrArg (fun S : SymmetricPerturbation d => S.1 i j) hsplit
          have hpeel : (spatialBlock d h).1 i j = h.1 i.succ j.succ := by
            simp [spatialBlock, symmetricPeel]
          simp only [shiftOnlyVector, positiveModes_apply_spatial]
          rw [hspatial]
          rw [hpeel] at hblock
          by_cases hij : i = j
          · subst j
            rw [← hblock]
            simp [spatialTraceFreePart, spatialIdentity]
          · rw [← hblock]
            rw [negativeModes_apply_spatial_offdiag d
              (Fin.cons 0 (shiftCoordinates d h)) i j hij]
            simp [traceLapseMode, positiveModes, spatialTraceFreePart,
              spatialIdentity, Matrix.one_apply, blockTrace, hij]

private theorem minkowskiMatrix_sq (D : ℕ) :
    minkowskiMatrix D * minkowskiMatrix D = 1 := by
  rw [minkowskiMatrix, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val = 0 <;> simp [hi]
  · simp [hij]

/-- On a symmetric real matrix, the trace of its square is the sum of the
entrywise squares. This is the positivity input for the Frobenius pairing. -/
theorem trace_mul_self_eq_sum_sq (D : ℕ) (M : Matrix (Fin D) (Fin D) ℝ)
    (hM : M.IsSymm) :
    Matrix.trace (M * M) = ∑ i : Fin D, ∑ j : Fin D, (M i j) ^ 2 := by
  change (∑ i : Fin D, ∑ j : Fin D, M i j * M j i) = _
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show M j i = M i j from hM.apply i j]
  ring

/-- A symmetric real matrix with zero Frobenius square is zero. -/
theorem symmetric_eq_zero_of_trace_mul_self_eq_zero (D : ℕ)
    (M : Matrix (Fin D) (Fin D) ℝ) (hM : M.IsSymm)
    (hzero : Matrix.trace (M * M) = 0) : M = 0 := by
  rw [trace_mul_self_eq_sum_sq D M hM] at hzero
  have hentries : ∀ i j, M i j = 0 := by
    intro i j
    have hsum : (∑ i : Fin D, ∑ j : Fin D, (M i j) ^ 2) = 0 := hzero
    have hnonneg : ∀ i ∈ Finset.univ, 0 ≤ ∑ j : Fin D, (M i j) ^ 2 := by
      intro i hi
      exact Finset.sum_nonneg fun j hj => sq_nonneg (M i j)
    have hrow : ∑ j : Fin D, (M i j) ^ 2 = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum i (Finset.mem_univ i)
      exact this
    have hterm : (M i j) ^ 2 = 0 := by
      have hrow' := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj => sq_nonneg (M i j))).mp hrow j (Finset.mem_univ j)
      exact hrow'
    exact (sq_eq_zero_iff).mp hterm
  ext i j
  exact hentries i j

/-- The Frobenius trace pairing is nondegenerate on symmetric matrices. -/
theorem symmetric_frobenius_radical_eq_zero (D : ℕ)
    (M : Matrix (Fin D) (Fin D) ℝ) (hM : M.IsSymm)
    (horth : ∀ N : SymmetricPerturbation D,
      Matrix.trace (M * N.1) = 0) : M = 0 := by
  apply symmetric_eq_zero_of_trace_mul_self_eq_zero D M hM
  exact horth ⟨M, hM⟩

/-- Away from dimension two, trace reversal has no kernel on symmetric
perturbations. This is a dimension-uniform algebraic fact; it does not by
itself claim a signature for the bilinear form. -/
theorem traceReverse_eq_zero_imp_eq_zero {D : ℕ}
    (hD : (D : ℝ) ≠ 2) (h : SymmetricPerturbation D)
    (hh : traceReverse D h = 0) : h = 0 := by
  let η := minkowskiMatrix D
  let t := Matrix.trace (η * h.1)
  let α : ℝ := (1 / 2) * t
  have hη : η * η = 1 := by simpa [η] using minkowskiMatrix_sq D
  have hfactor : η * h.1 * η = α • η := by
    have h0 : η * h.1 * η - α • η = 0 := by
      simpa [traceReverse, t, α, η] using hh
    exact sub_eq_zero.mp h0
  have hmatrix : h.1 = α • η := by
    have hsandwich (M : Matrix (Fin D) (Fin D) ℝ) : η * (η * M * η) * η = M := by
      calc
        η * (η * M * η) * η = (η * η * M) * (η * η) := by
          simp only [Matrix.mul_assoc]
        _ = M := by rw [hη]; simp
    calc
      h.1 = η * (η * h.1 * η) * η := (hsandwich h.1).symm
      _ = η * (α • η) * η := by rw [hfactor]
      _ = α • η := by simp [hη]
  have ht : t = α * (D : ℝ) := by
    dsimp [t]
    rw [hmatrix]
    simp [η, minkowskiMatrix_sq, Matrix.trace_smul, Matrix.trace_one, α, mul_comm]
  have hprod : ((D : ℝ) - 2) * t = 0 := by
    dsimp [α] at ht
    nlinarith [ht]
  have htzero : t = 0 := by
    rcases mul_eq_zero.mp hprod with hD' | ht'
    · exact False.elim (hD (by linarith))
    · exact ht'
  have hα : α = 0 := by simp [α, htzero]
  apply Subtype.ext
  rw [hmatrix, hα]
  simp

/-- The two-dimensional Minkowski metric itself is a nonzero symmetric
perturbation annihilated by trace reversal. This exhibits the exceptional
dimension in the nondegeneracy theorem above. -/
def minkowskiTwo : SymmetricPerturbation 2 :=
  ⟨minkowskiMatrix 2, Matrix.isSymm_diagonal _⟩

theorem minkowskiTwo_ne_zero : minkowskiTwo ≠ 0 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) (congrArg Subtype.val h)
  norm_num [minkowskiTwo, minkowskiMatrix] at h00

theorem traceReverse_minkowskiTwo_eq_zero : traceReverse 2 minkowskiTwo = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [traceReverse, minkowskiTwo, minkowskiMatrix, Matrix.diagonal,
      Matrix.mul_apply, Matrix.trace]

/-- The DeWitt bilinear form is degenerate in dimension two, with an explicit
nonzero radical vector. -/
theorem pairing_degenerate_dimension_two :
    ∃ h : SymmetricPerturbation 2, h ≠ 0 ∧
      ∀ k : SymmetricPerturbation 2, pairing 2 h k = 0 := by
  refine ⟨minkowskiTwo, minkowskiTwo_ne_zero, ?_⟩
  intro k
  rw [pairing_eq_traceReverse_mul, traceReverse_minkowskiTwo_eq_zero]
  simp

/-- The DeWitt pairing is nondegenerate in every dimension other than two.
The proof tests a vector against its trace reverse, uses positivity of the
real Frobenius form on symmetric matrices, and then applies injectivity of
trace reversal. -/
theorem pairing_left_nondegenerate {D : ℕ} (hD : (D : ℝ) ≠ 2)
    (h : SymmetricPerturbation D)
    (hpair : ∀ k : SymmetricPerturbation D, pairing D h k = 0) :
    h = 0 := by
  let A := traceReverse D h
  have hAsymm : A.IsSymm := by
    exact traceReverse_isSymm D h
  have htrace : Matrix.trace (A * A) = 0 := by
    let hk : SymmetricPerturbation D := ⟨A, hAsymm⟩
    have hzero := hpair hk
    rw [pairing_eq_traceReverse_mul] at hzero
    simpa only [Submodule.coe_mk] using hzero
  have hAzero : A = 0 :=
    symmetric_eq_zero_of_trace_mul_self_eq_zero D A hAsymm htrace
  exact traceReverse_eq_zero_imp_eq_zero hD h hAzero

theorem pairing_swap (D : ℕ) (h k : SymmetricPerturbation D) :
    pairing D h k = pairing D k h := by
  unfold pairing
  have htrace :
      Matrix.trace (minkowskiMatrix D * h.1 * minkowskiMatrix D * k.1) =
        Matrix.trace (minkowskiMatrix D * k.1 * minkowskiMatrix D * h.1) := by
    rw [show minkowskiMatrix D * h.1 * minkowskiMatrix D * k.1 =
        (minkowskiMatrix D * h.1) * (minkowskiMatrix D * k.1) by simp [mul_assoc]]
    rw [show minkowskiMatrix D * k.1 * minkowskiMatrix D * h.1 =
        (minkowskiMatrix D * k.1) * (minkowskiMatrix D * h.1) by simp [mul_assoc]]
    exact Matrix.trace_mul_comm _ _
  rw [htrace]
  simp only [mul_assoc]
  rw [mul_comm (Matrix.trace (minkowskiMatrix D * h.1))
    (Matrix.trace (minkowskiMatrix D * k.1))]

theorem pairing_add_left (D : ℕ) (h₁ h₂ k : SymmetricPerturbation D) :
    pairing D (h₁ + h₂) k = pairing D h₁ k + pairing D h₂ k := by
  unfold pairing
  simp only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  ring_nf

theorem pairing_add_right (D : ℕ) (h k₁ k₂ : SymmetricPerturbation D) :
    pairing D h (k₁ + k₂) = pairing D h k₁ + pairing D h k₂ := by
  rw [pairing_swap, pairing_add_left, pairing_swap D k₁ h, pairing_swap D k₂ h]

/-- Polarization of the actual DeWitt quadratic form. The cross term is the
matrix-trace pairing itself, so this identity can be used to prove orthogonal
splittings of the full symmetric-matrix carrier. -/
theorem quadratic_add (D : ℕ) (h k : SymmetricPerturbation D) :
    quadratic D (h + k) =
      quadratic D h + 2 * pairing D h k + quadratic D k := by
  unfold quadratic
  calc
    pairing D (h + k) (h + k) =
        pairing D h (h + k) + pairing D k (h + k) := pairing_add_left D h k (h + k)
    _ = (pairing D h h + pairing D h k) +
        (pairing D k h + pairing D k k) := by
          rw [pairing_add_right, pairing_add_right]
    _ = pairing D h h + 2 * pairing D h k + pairing D k k := by
          rw [pairing_swap D k h]
          simp only [two_mul]
          abel

/-- Full bilinear form on the actual lapse/shift matrix subspace. In
particular, its `d` shift directions are pairwise orthogonal and have norm
`-2`; the remaining lapse/trace direction is orthogonal to them. -/
theorem pairing_negativeModes (d : ℕ) (v w : Fin (d + 1) → ℝ)
    (hd : d ≠ 0) :
    pairing (d + 1) (negativeModes d v) (negativeModes d w) =
      -2 * (∑ i : Fin d, v i.succ * w i.succ) -
        ((d - 1 : ℝ) / d) * (v 0 * w 0) := by
  have hsum := quadratic_negativeModes d (v + w) hd
  rw [(negativeModes d).map_add v w] at hsum
  rw [quadratic_add] at hsum
  have hv := quadratic_negativeModes d v hd
  have hw := quadratic_negativeModes d w hd
  have hcross : (∑ i : Fin d, (v i.succ + w i.succ) ^ 2) =
      (∑ i : Fin d, (v i.succ) ^ 2) +
        2 * (∑ i : Fin d, v i.succ * w i.succ) +
        ∑ i : Fin d, (w i.succ) ^ 2 := by
    calc
      _ = ∑ i : Fin d,
          ((v i.succ) ^ 2 + 2 * (v i.succ * w i.succ) + (w i.succ) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring_nf
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
  simp only [Pi.add_apply] at hsum
  rw [hv, hw, hcross] at hsum
  change pairing (d + 1) (negativeModes d v) (negativeModes d w) = _
  linear_combination hsum / 2

/-- Full bilinear form on the positive spatial-matrix embedding. It is the
Frobenius pairing of the spatial blocks plus the product of their traces;
this formula will certify mutual orthogonality of concrete positive partner
modes inside the original spacetime matrix carrier. -/
theorem pairing_positiveModes (d : ℕ) (S T : SymmetricPerturbation d) :
    pairing (d + 1) (positiveModes d S) (positiveModes d T) =
      blockTrace d S * blockTrace d T +
        ∑ i : Fin d, ∑ j : Fin d, S.1 i j * T.1 i j := by
  have hsum := quadratic_positiveModes d (S + T)
  rw [(positiveModes d).map_add S T] at hsum
  rw [quadratic_add] at hsum
  have hS := quadratic_positiveModes d S
  have hT := quadratic_positiveModes d T
  have htrace : blockTrace d (S + T) = blockTrace d S + blockTrace d T := by
    simp [blockTrace, Finset.sum_add_distrib]
  have hentryAux :
      (∑ i : Fin d, ∑ j : Fin d, (S.1 i j + T.1 i j) ^ 2) =
        (∑ i : Fin d, ∑ j : Fin d, (S.1 i j) ^ 2) +
          2 * (∑ i : Fin d, ∑ j : Fin d, S.1 i j * T.1 i j) +
          ∑ i : Fin d, ∑ j : Fin d, (T.1 i j) ^ 2 := by
    calc
      _ = ∑ i : Fin d, ∑ j : Fin d,
          ((S.1 i j) ^ 2 + 2 * (S.1 i j * T.1 i j) + (T.1 i j) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hentry :
      (∑ i : Fin d, ∑ j : Fin d, ((S + T).1 i j) ^ 2) =
        (∑ i : Fin d, ∑ j : Fin d, (S.1 i j) ^ 2) +
          2 * (∑ i : Fin d, ∑ j : Fin d, S.1 i j * T.1 i j) +
          ∑ i : Fin d, ∑ j : Fin d, (T.1 i j) ^ 2 := by
    simpa only [Submodule.coe_add, Matrix.add_apply] using hentryAux
  rw [hS, hT, htrace, hentry] at hsum
  change pairing (d + 1) (positiveModes d S) (positiveModes d T) = _
  nlinarith [hsum]

theorem quadratic_smul (D : ℕ) (c : ℝ) (h : SymmetricPerturbation D) :
    quadratic D (c • h) = c ^ 2 * quadratic D h := by
  unfold quadratic pairing
  simp only [Submodule.coe_smul_of_tower, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul]
  ring_nf

/-- The lapse/shift modes are orthogonal to the trace-free spatial block in
the full DeWitt pairing. This is the key orthogonality needed to turn the
separate positive and negative mode counts into an actual Witt splitting. -/
theorem negativeModes_orthogonal_traceFreePositiveModes (d : ℕ)
    (v : Fin (d + 1) → ℝ) (S : SymmetricPerturbation d)
    (hS : blockTrace d S = 0) :
    pairing (d + 1) (negativeModes d v) (positiveModes d S) = 0 := by
  rw [pairing_entry_expansion]
  have hdiag : (∑ i : Fin d, S.1 i i) = 0 := by
    simpa [blockTrace] using hS
  have hentry :
      (∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
        minkowskiSign i * minkowskiSign j *
          ((negativeModes d v).1 i j * (positiveModes d S).1 i j)) = 0 := by
    simp [minkowskiSign, negativeModes, negativeModeMatrix,
      positiveModes, positiveModeMatrix, blockTrace, hdiag,
      Fin.sum_univ_succ]
    rw [← Finset.mul_sum, hdiag]
    simp
  have htrace :
      (∑ i : Fin (d + 1), minkowskiSign i *
        (positiveModes d S).1 i i) = 0 := by
    rw [Fin.sum_univ_succ]
    simp [minkowskiSign, positiveModes_apply_00,
      positiveModes_apply_spatial, blockTrace, hdiag]
  rw [hentry, htrace]
  simp

/-- On a trace-free spatial block, adding the lapse/shift perturbation and the
spatial perturbation splits the DeWitt quadratic value without a cross term. -/
theorem quadratic_add_negativeModes_traceFreePositiveModes (d : ℕ)
    (v : Fin (d + 1) → ℝ) (S : SymmetricPerturbation d)
    (hS : blockTrace d S = 0) :
    quadratic (d + 1) (negativeModes d v + positiveModes d S) =
      quadratic (d + 1) (negativeModes d v) +
        quadratic (d + 1) (positiveModes d S) := by
  rw [quadratic_add, negativeModes_orthogonal_traceFreePositiveModes d v S hS]
  simp

theorem pairing_smul_left (D : ℕ) (c : ℝ) (h k : SymmetricPerturbation D) :
    pairing D (c • h) k = c * pairing D h k := by
  unfold pairing
  simp only [Submodule.coe_smul_of_tower, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul]
  ring_nf

theorem pairing_smul_right (D : ℕ) (c : ℝ) (h k : SymmetricPerturbation D) :
    pairing D h (c • k) = c * pairing D h k := by
  rw [pairing_swap, pairing_smul_left, pairing_swap]

theorem pairing_sub_left (D : ℕ) (h k z : SymmetricPerturbation D) :
    pairing D (h - k) z = pairing D h z - pairing D k z := by
  rw [sub_eq_add_neg, pairing_add_left, ← neg_one_smul ℝ k, pairing_smul_left]
  ring_nf

theorem pairing_sub_right (D : ℕ) (h z w : SymmetricPerturbation D) :
    pairing D h (z - w) = pairing D h z - pairing D h w := by
  rw [sub_eq_add_neg, pairing_add_right, ← neg_one_smul ℝ w, pairing_smul_right]
  ring_nf

/-- Opposite-norm orthogonal directions in the genuine symmetric-matrix
DeWitt carrier combine into a normalized hyperbolic pair. This is the
division-by-two change of basis from an orthogonal `(2,-2)` pair to two
isotropic vectors with mutual pairing one. -/
theorem normalizedWittPair_of_orthogonal_opposite_norms (D : ℕ)
    (u v : SymmetricPerturbation D)
    (hu : quadratic D u = 2) (hv : quadratic D v = -2)
    (huv : pairing D u v = 0) :
    quadratic D ((1 / 2 : ℝ) • (u + v)) = 0 ∧
      quadratic D ((1 / 2 : ℝ) • (u - v)) = 0 ∧
      pairing D ((1 / 2 : ℝ) • (u + v)) ((1 / 2 : ℝ) • (u - v)) = 1 := by
  have hvu : pairing D v u = 0 := by rw [pairing_swap, huv]
  have hsum : quadratic D (u + v) = 0 := by
    rw [quadratic_add, hu, huv, hv]
    ring
  have hdiff : quadratic D (u - v) = 0 := by
    rw [sub_eq_add_neg, ← neg_one_smul ℝ v]
    rw [quadratic_add, quadratic_smul, pairing_smul_right, huv, hu, hv]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [quadratic_smul, hsum]
    norm_num
  · rw [quadratic_smul, hdiff]
    norm_num
  · rw [pairing_smul_left, pairing_smul_right]
    have hexpand : pairing D (u + v) (u - v) = 4 := by
      rw [sub_eq_add_neg, ← neg_one_smul ℝ v,
        pairing_add_left, pairing_add_right, pairing_add_right,
        pairing_smul_right, pairing_smul_right, huv, hvu]
      unfold quadratic at hu hv
      rw [hu, ← pairing_swap D v v, hv]
      norm_num
    rw [hexpand]
    norm_num

/-- Coordinate vector for one of the independent spacetime shifts. -/
def shiftModeVector (d : ℕ) (i : Fin d) : Fin (d + 1) → ℝ :=
  Fin.cons 0 (fun j => if j = i then 1 else 0)

/-- Distinct spacetime shift coordinates are orthogonal in the full DeWitt
pairing, with exact negative norm `-2` on the diagonal. -/
theorem shiftModes_pairing (d : ℕ) (i j : Fin d) :
    pairing (d + 1) (negativeModes d (shiftModeVector d i))
        (negativeModes d (shiftModeVector d j)) =
      if i = j then -2 else 0 := by
  rw [pairing_negativeModes d _ _ (by have hi := i.isLt; omega)]
  simp [shiftModeVector, eq_comm]

/-- Any trace-free spatial mode of DeWitt norm two pairs with each unit shift
mode to give an actual normalized hyperbolic plane in the full matrix
carrier. The hypotheses name the spatial modes needed to assemble a fully
mutually orthogonal Witt basis. -/
theorem shiftWittPair_of_traceFreeSpatialUnit (d : ℕ) (hd : 2 ≤ d)
    (i : Fin d) (S : SymmetricPerturbation d)
    (htrace : blockTrace d S = 0)
    (hpos : quadratic (d + 1) (positiveModes d S) = 2) :
    quadratic (d + 1)
        ((1 / 2 : ℝ) • (positiveModes d S +
          negativeModes d (shiftModeVector d i))) = 0 ∧
      quadratic (d + 1)
        ((1 / 2 : ℝ) • (positiveModes d S -
          negativeModes d (shiftModeVector d i))) = 0 ∧
      pairing (d + 1)
        ((1 / 2 : ℝ) • (positiveModes d S +
          negativeModes d (shiftModeVector d i)))
        ((1 / 2 : ℝ) • (positiveModes d S -
          negativeModes d (shiftModeVector d i))) = 1 := by
  let v := shiftModeVector d i
  have hneg : quadratic (d + 1) (negativeModes d v) = -2 := by
    rw [quadratic_negativeModes d v (by omega)]
    simp [v, shiftModeVector]
  have hcross : pairing (d + 1) (positiveModes d S)
      (negativeModes d v) = 0 := by
    rw [pairing_swap]
    exact negativeModes_orthogonal_traceFreePositiveModes d v S htrace
  exact normalizedWittPair_of_orthogonal_opposite_norms (d + 1)
    (positiveModes d S) (negativeModes d v) hpos hneg hcross

/-- A spatial off-diagonal matrix supported on one unordered pair of
coordinates.  The two entries are kept in the actual symmetric matrix
carrier, rather than represented by a scalar coordinate. -/
def spatialEdgeMode (d : ℕ) (i j : Fin d) (hij : i ≠ j) :
    SymmetricPerturbation d :=
  ⟨Matrix.single i j (1 : ℝ) + Matrix.single j i 1, by
    apply Matrix.IsSymm.ext
    intro a b
    simp only [Matrix.add_apply, Matrix.single_apply]
    ac_rfl
  ⟩

/-- A trace-free diagonal direction in the actual spatial symmetric-matrix
carrier. The two selected diagonal entries have opposite signs. -/
def spatialDiagonalDifference (d : ℕ) (hd : 2 ≤ d) :
    SymmetricPerturbation d := by
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  exact ⟨Matrix.single i i (1 : ℝ) - Matrix.single j j 1, by
    apply Matrix.IsSymm.ext
    intro a b
    simp [Matrix.sub_apply, Matrix.single_apply, and_comm, eq_comm]⟩

/-- The diagonal difference has zero trace. -/
theorem blockTrace_spatialDiagonalDifference (d : ℕ) (hd : 2 ≤ d) :
    blockTrace d (spatialDiagonalDifference d hd) = 0 := by
  classical
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  unfold blockTrace spatialDiagonalDifference
  simp [i, j, Matrix.single_apply, hij]

/-- The diagonal difference has Frobenius norm squared two, hence its
spacetime embedding has DeWitt norm two. -/
theorem spatialDiagonalDifference_trace_and_norm (d : ℕ) (hd : 2 ≤ d) :
    blockTrace d (spatialDiagonalDifference d hd) = 0 ∧
      quadratic (d + 1)
        (positiveModes d (spatialDiagonalDifference d hd)) = 2 := by
  classical
  refine ⟨blockTrace_spatialDiagonalDifference d hd, ?_⟩
  rw [quadratic_positiveModes,
    blockTrace_spatialDiagonalDifference d hd]
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  have hsum : (∑ a : Fin d, ∑ b : Fin d,
      ((spatialDiagonalDifference d hd).1 a b) ^ 2) = 2 := by
    have hentry (a b : Fin d) :
        ((spatialDiagonalDifference d hd).1 a b) ^ 2 =
          if a = i then if b = i then 1 else 0
          else if a = j then if b = j then 1 else 0 else 0 := by
      by_cases hai : a = i
      · subst a
        simp [spatialDiagonalDifference, i, j, Matrix.single_apply, hij, eq_comm]
      · by_cases haj : a = j
        · subst a
          simp [spatialDiagonalDifference, i, j, Matrix.single_apply, hij,
            Ne.symm hij, eq_comm]
        · simp [spatialDiagonalDifference, i, j, Matrix.single_apply,
            hai, haj, eq_comm]
    simp_rw [hentry]
    calc
      (∑ a : Fin d, ∑ b : Fin d,
          (if a = i then if b = i then (1 : ℝ) else 0
           else if a = j then if b = j then 1 else 0 else 0)) =
        ∑ a : Fin d, ((if a = i then (1 : ℝ) else 0) +
          (if a = j then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases hai : a = i
            · subst a
              simp [hij]
            · by_cases haj : a = j
              · subst a
                simp [Ne.symm hij]
              · simp [hai, haj]
      _ = 2 := by
        rw [Finset.sum_add_distrib]
        simp
        <;> norm_num
  rw [hsum]
  norm_num

/-- The off-diagonal edge has zero spatial trace. -/
theorem blockTrace_spatialEdgeMode (d : ℕ) (i j : Fin d) (hij : i ≠ j) :
    blockTrace d (spatialEdgeMode d i j hij) = 0 := by
  unfold blockTrace
  apply Finset.sum_eq_zero
  intro a ha
  have h₁ : ¬ (i = a ∧ j = a) := by
    rintro ⟨hia, hja⟩
    exact hij (hia.trans hja.symm)
  have h₂ : ¬ (j = a ∧ i = a) := by
    rintro ⟨hja, hia⟩
    exact (Ne.symm hij) (hja.trans hia.symm)
  simp [spatialEdgeMode, Matrix.single_apply, h₁, h₂]

/-- The edge mode is trace-free and has Frobenius square two, hence its
embedded DeWitt norm is exactly two. -/
theorem spatialEdgeMode_trace_and_norm (d : ℕ) (i j : Fin d) (hij : i ≠ j) :
    blockTrace d (spatialEdgeMode d i j hij) = 0 ∧
      quadratic (d + 1) (positiveModes d (spatialEdgeMode d i j hij)) = 2 := by
  constructor
  · exact blockTrace_spatialEdgeMode d i j hij
  · rw [quadratic_positiveModes]
    rw [blockTrace_spatialEdgeMode]
    have hsum : (∑ a : Fin d, ∑ b : Fin d,
        ((spatialEdgeMode d i j hij).1 a b) ^ 2) = 2 := by
      classical
      have hentry (a b : Fin d) :
          (((spatialEdgeMode d i j hij).1 a b) ^ 2) =
            (if a = i then if b = j then 1 else 0
             else if a = j then if b = i then 1 else 0 else 0) := by
        by_cases hai : a = i
        · subst a
          simp [spatialEdgeMode, Matrix.single_apply, hij, Ne.symm hij, eq_comm]
        · by_cases haj : a = j
          · subst a
            simp [spatialEdgeMode, Matrix.single_apply, hij, Ne.symm hij, hai, eq_comm]
          · have hia : i ≠ a := fun h => hai h.symm
            have hja : j ≠ a := fun h => haj h.symm
            simp [spatialEdgeMode, Matrix.single_apply, hia, hja, eq_comm]
      simp_rw [hentry]
      calc
        (∑ a : Fin d, ∑ b : Fin d,
            (if a = i then if b = j then (1 : ℝ) else 0
             else if a = j then if b = i then 1 else 0 else 0)) =
            ∑ a : Fin d, ((if a = i then (1 : ℝ) else 0) + (if a = j then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro a ha
              by_cases hai : a = i
              · subst a
                simp [hij]
              · by_cases haj : a = j
                · subst a
                  simp [Ne.symm hij]
                · simp [hai, haj]
        _ = 2 := by
          rw [Finset.sum_add_distrib]
          have hi : (∑ x : Fin d, if x = i then (1 : ℝ) else 0) = 1 := by
            simp
          have hj : (∑ x : Fin d, if x = j then (1 : ℝ) else 0) = 1 := by
            simp
          rw [hi, hj]
          norm_num
    rw [hsum]
    norm_num

/-- Spatial edge modes with a common endpoint are mutually orthogonal in the
actual DeWitt pairing; matching edges have norm two. -/
theorem spatialEdgeMode_commonAnchor_pairing (d : ℕ) (i j k : Fin d)
    (hij : i ≠ j) (hik : i ≠ k) :
    pairing (d + 1) (positiveModes d (spatialEdgeMode d i j hij))
        (positiveModes d (spatialEdgeMode d i k hik)) =
      if j = k then 2 else 0 := by
  classical
  by_cases hjk : j = k
  · subst k
    rw [if_pos rfl]
    exact (spatialEdgeMode_trace_and_norm d i j hij).2
  · rw [if_neg hjk, pairing_positiveModes]
    rw [blockTrace_spatialEdgeMode d i j hij,
      blockTrace_spatialEdgeMode d i k hik]
    simp only [zero_mul, zero_add]
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hai : a = i
    · subst a
      simp [spatialEdgeMode, Matrix.single_apply, hij, hik, hjk,
        Ne.symm hjk, eq_comm] <;>
          (intro hb; subst b; exact hjk)
    · by_cases haj : a = j
      · subst a
        simp [spatialEdgeMode, Matrix.single_apply, hij, hik, hjk,
          Ne.symm hjk, eq_comm]
      · by_cases hak : a = k
        · subst a
          simp [spatialEdgeMode, Matrix.single_apply, hij, hik, hjk,
            Ne.symm hjk, eq_comm]
        · have hai' : i ≠ a := fun h => hai h.symm
          have haj' : j ≠ a := fun h => haj h.symm
          have hak' : k ≠ a := fun h => hak h.symm
          simp [spatialEdgeMode, Matrix.single_apply, hij, hik, hjk,
            hai', haj', hak', eq_comm]

/-- Every spatial off-diagonal edge supplies a genuine normalized Witt pair
with any unit shift direction. -/
theorem spatialEdge_shift_witt_pair (d : ℕ) (hd : 2 ≤ d)
    (i j shift : Fin d) (hij : i ≠ j) :
    let e := positiveModes d (spatialEdgeMode d i j hij)
    let n := negativeModes d (shiftModeVector d shift)
    quadratic (d + 1) ((1 / 2 : ℝ) • (e + n)) = 0 ∧
      quadratic (d + 1) ((1 / 2 : ℝ) • (e - n)) = 0 ∧
      pairing (d + 1) ((1 / 2 : ℝ) • (e + n))
        ((1 / 2 : ℝ) • (e - n)) = 1 := by
  have htrace := (spatialEdgeMode_trace_and_norm d i j hij).1
  have hpos := (spatialEdgeMode_trace_and_norm d i j hij).2
  exact shiftWittPair_of_traceFreeSpatialUnit d hd shift
    (spatialEdgeMode d i j hij) htrace hpos

/-- An explicit orthogonal family of `d` trace-free, norm-two spatial
partners for the `d` spacetime shifts. The first is a diagonal difference;
the others are distinct off-diagonal edges with a common endpoint. -/
private def spatialAnchorIndex (d : ℕ) (hd : 2 ≤ d) : Fin d :=
  ⟨0, by omega⟩

def spatialShiftPartner (d : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    SymmetricPerturbation d := by
  by_cases hi : i = spatialAnchorIndex d hd
  · exact spatialDiagonalDifference d hd
  · exact spatialEdgeMode d (spatialAnchorIndex d hd) i (fun h => hi h.symm)

theorem blockTrace_spatialShiftPartner (d : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    blockTrace d (spatialShiftPartner d hd i) = 0 := by
  by_cases hi : i = spatialAnchorIndex d hd
  · rw [show spatialShiftPartner d hd i = spatialDiagonalDifference d hd by
      simp [spatialShiftPartner, hi]]
    exact blockTrace_spatialDiagonalDifference d hd
  · rw [show spatialShiftPartner d hd i =
      spatialEdgeMode d (spatialAnchorIndex d hd) i (fun h => hi h.symm) by
        simp [spatialShiftPartner, hi]]
    exact blockTrace_spatialEdgeMode d _ _ (fun h => hi h.symm)

theorem quadratic_spatialShiftPartner (d : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    quadratic (d + 1) (positiveModes d (spatialShiftPartner d hd i)) = 2 := by
  by_cases hi : i = spatialAnchorIndex d hd
  · simpa [spatialShiftPartner, hi] using
      (spatialDiagonalDifference_trace_and_norm d hd).2
  · simpa [spatialShiftPartner, hi] using
      (spatialEdgeMode_trace_and_norm d (spatialAnchorIndex d hd) i
        (fun h => hi h.symm)).2

private theorem pairing_spatialDiagonalDifference_edge_zero (d : ℕ)
    (hd : 2 ≤ d) (j : Fin d) (hj : j ≠ spatialAnchorIndex d hd) :
    pairing (d + 1) (positiveModes d (spatialDiagonalDifference d hd))
      (positiveModes d (spatialEdgeMode d (spatialAnchorIndex d hd) j
        (fun h => hj h.symm))) = 0 := by
  rw [pairing_positiveModes,
    blockTrace_spatialDiagonalDifference d hd,
    blockTrace_spatialEdgeMode d (spatialAnchorIndex d hd) j
      (fun h => hj h.symm)]
  simp only [zero_mul, zero_add]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  by_cases hab : a = b
  · subst b
    have hEdge : spatialAnchorIndex d hd ≠ j := fun h => hj h.symm
    have hdiag : (spatialEdgeMode d (spatialAnchorIndex d hd) j hEdge).1 a a = 0 := by
      by_cases ha : a = spatialAnchorIndex d hd
      · subst a
        simp [spatialEdgeMode, Matrix.single_apply, Ne.symm hEdge]
      · by_cases haj : a = j
        · subst a
          simp [spatialEdgeMode, Matrix.single_apply, hEdge]
        · simp [spatialEdgeMode, Matrix.single_apply, ha, haj, eq_comm]
    rw [hdiag]
    simp
  · have hdiag : (spatialDiagonalDifference d hd).1 a b = 0 := by
      let i₀ : Fin d := ⟨0, by omega⟩
      have h₀ : ¬ (i₀ = a ∧ i₀ = b) := by
        rintro ⟨ha, hb⟩
        exact hab (ha.symm.trans hb)
      let j₁ : Fin d := ⟨1, by omega⟩
      have h₁ : ¬ (j₁ = a ∧ j₁ = b) := by
        rintro ⟨ha, hb⟩
        exact hab (ha.symm.trans hb)
      simp [spatialDiagonalDifference, Matrix.single_apply, h₀, h₁,
        i₀, j₁]
    rw [hdiag]
    simp

/-- The concrete positive spatial partners are mutually orthogonal and have
norm two in the full DeWitt matrix pairing. -/
theorem spatialShiftPartner_pairing (d : ℕ) (hd : 2 ≤ d) (i j : Fin d) :
    pairing (d + 1) (positiveModes d (spatialShiftPartner d hd i))
      (positiveModes d (spatialShiftPartner d hd j)) =
        if i = j then 2 else 0 := by
  by_cases hi : i = spatialAnchorIndex d hd <;>
    by_cases hj : j = spatialAnchorIndex d hd
  · rw [hi, hj]
    change quadratic (d + 1)
      (positiveModes d (spatialDiagonalDifference d hd)) = 2
    exact (spatialDiagonalDifference_trace_and_norm d hd).2
  · rw [hi]
    have hj' : j ≠ spatialAnchorIndex d hd := hj
    simp [spatialShiftPartner, hj, Ne.symm hj',
      pairing_spatialDiagonalDifference_edge_zero d hd j hj']
  · rw [hj]
    have hi' : i ≠ spatialAnchorIndex d hd := hi
    rw [pairing_swap]
    simp [spatialShiftPartner, hi,
      pairing_spatialDiagonalDifference_edge_zero d hd i hi']
  · have hij₀ : spatialAnchorIndex d hd ≠ i := fun h => hi h.symm
    have hj₀ : spatialAnchorIndex d hd ≠ j := fun h => hj h.symm
    simpa [spatialShiftPartner, hi, hj] using
      spatialEdgeMode_commonAnchor_pairing d (spatialAnchorIndex d hd) i j hij₀ hj₀

/-- Every lapse/shift negative direction has a concrete trace-free spatial
partner of norm two. Thus the displayed Witt pair lives in the original
symmetric spacetime-matrix carrier, with no coordinate surrogate. -/
theorem spatialShiftPartner_wittPair (d : ℕ) (hd : 2 ≤ d) (i : Fin d) :
    let e := positiveModes d (spatialShiftPartner d hd i)
    let n := negativeModes d (shiftModeVector d i)
    quadratic (d + 1) ((1 / 2 : ℝ) • (e + n)) = 0 ∧
      quadratic (d + 1) ((1 / 2 : ℝ) • (e - n)) = 0 ∧
      pairing (d + 1) ((1 / 2 : ℝ) • (e + n))
        ((1 / 2 : ℝ) • (e - n)) = 1 := by
  exact shiftWittPair_of_traceFreeSpatialUnit d hd i
    (spatialShiftPartner d hd i)
    (blockTrace_spatialShiftPartner d hd i)
    (quadratic_spatialShiftPartner d hd i)

/-- A trace-free spatial perturbation is orthogonal to the lapse/trace plane.
This supplies the cross-orthogonality needed to join the explicit lapse pair
to the shift-associated Witt frame. -/
theorem traceLapse_orthogonal_traceFreeSpatial (d : ℕ) (hd : 2 ≤ d)
    (x y : ℝ) (S : SymmetricPerturbation d)
    (hS : blockTrace d S = 0) :
    pairing (d + 1) (traceLapseMode d x y) (positiveModes d S) = 0 := by
  rw [pairing_entry_expansion]
  have hdNe : d ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hd)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdNe
  have htime : (∑ i : Fin (d + 1), minkowskiSign i *
      (traceLapseMode d x y).1 i i) = -x + 2 * y := by
    rw [Fin.sum_univ_succ]
    simp [minkowskiSign, traceLapseMode]
    field_simp [hdR]
    ring_nf
  have hspace : (∑ i : Fin (d + 1), minkowskiSign i *
      (positiveModes d S).1 i i) = 0 := by
    rw [Fin.sum_univ_succ]
    simp [minkowskiSign, positiveModes_apply_00, positiveModes_apply_spatial,
      blockTrace]
  have hfirst : (∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
      minkowskiSign i * minkowskiSign j *
        ((traceLapseMode d x y).1 i j * (positiveModes d S).1 i j)) = 0 := by
    have hformula : (∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
        minkowskiSign i * minkowskiSign j *
          ((traceLapseMode d x y).1 i j * (positiveModes d S).1 i j)) =
        (x - y) * blockTrace d S + (y / (d : ℝ)) * blockTrace d S := by
      simp [traceLapseMode, positiveModes, positiveModeMatrix, minkowskiSign,
        Fin.sum_univ_succ, Finset.sum_ite_eq', blockTrace]
      rw [← Finset.mul_sum]
    rw [hformula, hS]
    simp
  rw [hfirst, htime, hspace]
  simp

/-- The diagonal lapse/trace plane is orthogonal to each off-diagonal shift
direction in the full DeWitt pairing. -/
theorem traceLapse_orthogonal_shift (d : ℕ) (x y : ℝ) (i : Fin d) :
    pairing (d + 1) (traceLapseMode d x y)
      (negativeModes d (shiftModeVector d i)) = 0 := by
  rw [pairing_entry_expansion]
  have htrace : (∑ j : Fin (d + 1), minkowskiSign j *
      (negativeModes d (shiftModeVector d i)).1 j j) = 0 := by
    rw [Fin.sum_univ_succ]
    simp [minkowskiSign, negativeModes_apply_00, negativeModes_apply_spatial_diag,
      shiftModeVector]
  have hfirst : (∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
      minkowskiSign a * minkowskiSign b *
        ((traceLapseMode d x y).1 a b *
          (negativeModes d (shiftModeVector d i)).1 a b)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hab : a = b
    · subst b
      cases a using Fin.cases with
      | zero => simp [minkowskiSign, traceLapseMode, negativeModes,
          negativeModeMatrix, shiftModeVector]
      | succ a => simp [minkowskiSign, traceLapseMode, negativeModes,
          negativeModeMatrix, shiftModeVector]
    · cases a using Fin.cases with
      | zero =>
          cases b using Fin.cases with
          | zero => exact (hab rfl).elim
          | succ b => simp [traceLapseMode]
      | succ a =>
          cases b using Fin.cases with
          | zero => simp [traceLapseMode]
          | succ b =>
              have hab' : a ≠ b := fun h => hab (congrArg Fin.succ h)
              simp [traceLapseMode, hab']
  rw [hfirst, htrace]
  simp

/-- The positive and negative null vectors obtained from the spatial partner
and corresponding shift form an indexed orthogonal hyperbolic frame. The
pairing is Kronecker delta, while vectors of the same sign pair to zero.
All vectors are elements of the original symmetric spacetime-matrix carrier.
-/
theorem spatialShiftPartner_orthogonal_witt_frame (d : ℕ) (hd : 2 ≤ d)
    (i j : Fin d) :
    let eᵢ := positiveModes d (spatialShiftPartner d hd i)
    let eⱼ := positiveModes d (spatialShiftPartner d hd j)
    let nᵢ := negativeModes d (shiftModeVector d i)
    let nⱼ := negativeModes d (shiftModeVector d j)
    let pᵢ := (1 / 2 : ℝ) • (eᵢ + nᵢ)
    let qᵢ := (1 / 2 : ℝ) • (eᵢ - nᵢ)
    let pⱼ := (1 / 2 : ℝ) • (eⱼ + nⱼ)
    let qⱼ := (1 / 2 : ℝ) • (eⱼ - nⱼ)
    pairing (d + 1) pᵢ pⱼ = 0 ∧
      pairing (d + 1) qᵢ qⱼ = 0 ∧
      pairing (d + 1) pᵢ qⱼ = if i = j then 1 else 0 := by
  dsimp only
  have he : pairing (d + 1)
      (positiveModes d (spatialShiftPartner d hd i))
      (positiveModes d (spatialShiftPartner d hd j)) =
      if i = j then 2 else 0 := spatialShiftPartner_pairing d hd i j
  have hn : pairing (d + 1)
      (negativeModes d (shiftModeVector d i))
      (negativeModes d (shiftModeVector d j)) =
      if i = j then -2 else 0 := shiftModes_pairing d i j
  have hen : pairing (d + 1)
      (positiveModes d (spatialShiftPartner d hd i))
      (negativeModes d (shiftModeVector d j)) = 0 := by
    rw [pairing_swap]
    exact negativeModes_orthogonal_traceFreePositiveModes d
      (shiftModeVector d j) (spatialShiftPartner d hd i)
      (blockTrace_spatialShiftPartner d hd i)
  have hne : pairing (d + 1)
      (negativeModes d (shiftModeVector d i))
      (positiveModes d (spatialShiftPartner d hd j)) = 0 := by
    exact negativeModes_orthogonal_traceFreePositiveModes d
      (shiftModeVector d i) (spatialShiftPartner d hd j)
      (blockTrace_spatialShiftPartner d hd j)
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [pairing_smul_left, pairing_smul_right, pairing_add_left,
      pairing_add_right, pairing_sub_left, pairing_sub_right,
      he, hn, hen, hne] <;>
    by_cases hij : i = j <;> simp [hij] <;> ring

/-- Each normalized null vector in the shift-associated Witt planes is
orthogonal to the entire lapse/trace plane. -/
theorem traceLapse_orthogonal_spatialWittPair (d : ℕ) (hd : 2 ≤ d)
    (x y : ℝ) (i : Fin d) :
    let e := positiveModes d (spatialShiftPartner d hd i)
    let n := negativeModes d (shiftModeVector d i)
    pairing (d + 1) (traceLapseMode d x y)
        ((1 / 2 : ℝ) • (e + n)) = 0 ∧
      pairing (d + 1) (traceLapseMode d x y)
        ((1 / 2 : ℝ) • (e - n)) = 0 := by
  dsimp only
  have he : pairing (d + 1) (traceLapseMode d x y)
      (positiveModes d (spatialShiftPartner d hd i)) = 0 :=
    traceLapse_orthogonal_traceFreeSpatial d hd x y
      (spatialShiftPartner d hd i) (blockTrace_spatialShiftPartner d hd i)
  have hn : pairing (d + 1) (traceLapseMode d x y)
      (negativeModes d (shiftModeVector d i)) = 0 :=
    traceLapse_orthogonal_shift d x y i
  constructor
  · rw [pairing_smul_right, pairing_add_right, he, hn]
    simp
  · rw [pairing_smul_right, pairing_sub_right, he, hn]
    simp

/-- The DeWitt pairing as a bundled Mathlib bilinear map. -/
noncomputable def bilinear (D : ℕ) :
    SymmetricPerturbation D →ₗ[ℝ] SymmetricPerturbation D →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (pairing D)
    (fun h₁ h₂ k => pairing_add_left D h₁ h₂ k)
    (fun c h k => pairing_smul_left D c h k)
    (fun h k₁ k₂ => pairing_add_right D h k₁ k₂)
    (fun c h k => pairing_smul_right D c h k)

/-- The spatial trace bundled as a linear map on the actual symmetric-matrix
carrier. -/
noncomputable def blockTraceLinear (d : ℕ) :
    SymmetricPerturbation d →ₗ[ℝ] ℝ where
  toFun := blockTrace d
  map_add' := blockTrace_add d
  map_smul' := by
    intro c S
    rw [blockTrace_smul]
    rfl

@[simp] theorem blockTraceLinear_apply (d : ℕ) (S : SymmetricPerturbation d) :
    blockTraceLinear d S = blockTrace d S := rfl

/-- The bundled quadratic map induced by the actual DeWitt bilinear pairing. -/
noncomputable def quadraticForm (D : ℕ) : QuadraticForm ℝ (SymmetricPerturbation D) :=
  LinearMap.BilinMap.toQuadraticMap (bilinear D)

/-- The associated bilinear form of the DeWitt quadratic form is separating
in every dimension other than two. This connects the matrix-level
nondegeneracy proof to Mathlib's Sylvester inertia theorem. -/
theorem quadraticForm_associated_separatingLeft {D : ℕ} (hD : (D : ℝ) ≠ 2) :
    (QuadraticMap.associated (quadraticForm D)).SeparatingLeft := by
  have hAssoc : QuadraticMap.associated (quadraticForm D) = bilinear D := by
    rw [quadraticForm]
    exact QuadraticMap.associated_left_inverse ℝ
      (fun x y => pairing_swap D x y)
  rw [LinearMap.separatingLeft_iff_ker_eq_bot]
  rw [LinearMap.ker_eq_bot]
  intro h k hEq
  have hzero : QuadraticMap.associated (quadraticForm D) (h - k) = 0 := by
    rw [map_sub, hEq, sub_self]
  rw [hAssoc] at hzero
  have hsubzero : h - k = 0 := by
    apply pairing_left_nondegenerate hD (h - k)
    intro x
    have hx := LinearMap.congr_fun hzero x
    have hpairdiff : pairing D (h - k) x = pairing D h x - pairing D k x := by
      rw [show h - k = h + -k by abel, pairing_add_left]
      rw [← neg_one_smul ℝ k, pairing_smul_left]
      ring
    rw [hpairdiff]
    simpa [bilinear] using hx
  exact sub_eq_zero.mp hsubzero

/-- Sylvester's theorem supplies a genuine weighted-square normal form for the
DeWitt quadratic form on the symmetric-matrix carrier. This statement records
existence of the normal form; it does not claim the weights' multiplicities. -/
theorem quadraticForm_equivalent_weighted_signs {D : ℕ} (hD : (D : ℝ) ≠ 2) :
    ∃ w : Fin (Module.finrank ℝ (SymmetricPerturbation D)) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
        QuadraticMap.Equivalent (quadraticForm D)
          (QuadraticMap.weightedSumSquares ℝ w) := by
  exact QuadraticForm.equivalent_one_neg_one_weighted_sum_squared
    (quadraticForm D) (quadraticForm_associated_separatingLeft hD)

/-- The DeWitt form is positive definite on the embedded spatial block. -/
theorem positiveModeSubspace_posDef (d : ℕ) :
    (quadraticForm (d + 1)).restrict (positiveModeSubspace d) |>.PosDef := by
  intro x hx
  rcases x with ⟨x, ⟨S, hS⟩⟩
  have hSne : S ≠ 0 := by
    intro hSzero
    have hxval : x = 0 := by
      calc
        x = positiveModes d S := hS.symm
        _ = 0 := by simp [hSzero]
    apply hx
    exact Subtype.ext hxval
  change 0 < quadratic (d + 1) x
  rw [← hS]
  exact quadratic_positiveModes_pos d S hSne

/-- The positive signature index contains at least all independent symmetric
spatial-block directions. -/
theorem quadraticForm_sigPos_ge_spatialFinrank (d : ℕ) :
    _root_.sigPos (quadraticForm (d + 1)) ≥
      Module.finrank ℝ (SymmetricPerturbation d) := by
  have hbound := _root_.le_sigPos_of_posDef
    (quadraticForm (d + 1)) (positiveModeSubspace_posDef d)
  change Module.finrank ℝ (LinearMap.range (positiveModes d)) ≤ _ at hbound
  have hrank : Module.finrank ℝ (LinearMap.range (positiveModes d)) =
      Module.finrank ℝ (SymmetricPerturbation d) :=
    LinearMap.finrank_range_of_inj (positiveModes_injective d)
  omega

/-- The negative DeWitt quadratic form is positive definite on the constructed
lapse/shift image. -/
theorem negativeModeSubspace_posDef (d : ℕ) (hd : 2 ≤ d) :
    ((-quadraticForm (d + 1)).restrict (negativeModeSubspace d)).PosDef := by
  intro x hx
  rcases x with ⟨x, ⟨v, hv⟩⟩
  have hvne : v ≠ 0 := by
    intro hvzero
    have hxval : x = 0 := by
      calc
        x = negativeModes d v := hv.symm
        _ = 0 := by simp [hvzero]
    apply hx
    exact Subtype.ext hxval
  change 0 < -quadratic (d + 1) x
  rw [← hv]
  exact neg_pos.mpr (quadratic_negativeModes_neg d hd v hvne)

/-- The negative index of the genuine DeWitt quadratic form is at least the
spacetime dimension: the independent lapse and shift directions already
provide that many negative directions. -/
theorem quadraticForm_sigNeg_ge_spacetimeDim (d : ℕ) (hd : 2 ≤ d) :
    _root_.sigNeg (quadraticForm (d + 1)) ≥ d + 1 := by
  have hbound := _root_.le_sigNeg_of_negDef
    (quadraticForm (d + 1)) (negativeModeSubspace_posDef d hd)
  change Module.finrank ℝ (LinearMap.range (negativeModes d)) ≤ _ at hbound
  have hrank : Module.finrank ℝ (LinearMap.range (negativeModes d)) = d + 1 := by
    rw [LinearMap.finrank_range_of_inj (negativeModes_injective d)]
    simp [Module.finrank_fintype_fun_eq_card]
  omega

/-- Exact inertia of the Lorentzian DeWitt form in every spacetime dimension
`D = d + 1 ≥ 3`. The explicit positive spatial-block and negative lapse/shift
subspaces exhaust the dimension; nondegeneracy removes any radical. -/
theorem quadraticForm_signature (d : ℕ) (hd : 2 ≤ d) :
    _root_.sigPos (quadraticForm (d + 1)) = Nat.choose (d + 1) 2 ∧
      _root_.sigNeg (quadraticForm (d + 1)) = d + 1 := by
  have hD : ((d + 1 : ℕ) : ℝ) ≠ 2 := by
    exact_mod_cast (show d + 1 ≠ 2 by omega)
  have hrad : (quadraticForm (d + 1)).radical = ⊥ := by
    rw [QuadraticMap.radical_eq_ker_associated]
    exact LinearMap.separatingLeft_iff_ker_eq_bot.mp
      (quadraticForm_associated_separatingLeft hD)
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := quadraticForm (d + 1))
  rw [hrad] at hsum
  simp only [finrank_bot, add_zero] at hsum
  rw [finrank_symmetricPerturbation_succ] at hsum
  have hpos := quadraticForm_sigPos_ge_spatialFinrank d
  have hneg := quadraticForm_sigNeg_ge_spacetimeDim d hd
  have hposExact :
      _root_.sigPos (quadraticForm (d + 1)) =
        Module.finrank ℝ (SymmetricPerturbation d) := by omega
  have hnegExact :
      _root_.sigNeg (quadraticForm (d + 1)) = d + 1 := by omega
  constructor
  · simpa only [finrank_symmetricPerturbation] using hposExact
  · exact hnegExact

/-- The signed Sylvester normal form of the actual matrix DeWitt pairing has
exactly the positive and negative multiplicities computed by
`quadraticForm_signature`. This records the full inertia in the normal-form
coordinates, rather than only asserting that all coefficients are signs. -/
theorem quadraticForm_weighted_sign_counts (d : ℕ) (hd : 2 ≤ d) :
    ∃ w : Fin (Module.finrank ℝ (SymmetricPerturbation (d + 1))) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
      QuadraticMap.Equivalent (quadraticForm (d + 1))
        (QuadraticMap.weightedSumSquares ℝ w) ∧
      {i | 0 < w i}.ncard = Nat.choose (d + 1) 2 ∧
      {i | w i < 0}.ncard = d + 1 := by
  obtain ⟨w, hw, hequiv⟩ := quadraticForm_equivalent_weighted_signs
    (D := d + 1) (by
      exact_mod_cast (show d + 1 ≠ 2 by omega))
  have hsig := quadraticForm_signature d hd
  have hpos : _root_.sigPos (quadraticForm (d + 1)) =
      {i | 0 < w i}.ncard :=
    QuadraticForm.sigPos_of_equiv_weightedSumSquares hequiv
  have hneg : _root_.sigNeg (quadraticForm (d + 1)) =
      {i | w i < 0}.ncard :=
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares hequiv
  exact ⟨w, hw, hequiv, by omega, by omega⟩

/-- Rescale the explicit lapse/trace null pair so its mutual DeWitt pairing
is exactly one. This gives a normalized hyperbolic plane in the actual
symmetric-matrix carrier, not merely a nonzero pairing. -/
theorem traceLapse_normalized_hyperbolic_pair (d : ℕ) (hd : 2 ≤ d) :
    let c : ℝ := (d - 1 : ℝ) / d
    let r : ℝ := Real.sqrt (2 * c)
    let u := traceLapseMode d r 1
    let v := (-(1 / (2 * c))) • traceLapseMode d (-r) 1
    quadratic (d + 1) u = 0 ∧ quadratic (d + 1) v = 0 ∧
      pairing (d + 1) u v = 1 := by
  let c : ℝ := (d - 1 : ℝ) / d
  let r : ℝ := Real.sqrt (2 * c)
  let u := traceLapseMode d r 1
  let v₀ := traceLapseMode d (-r) 1
  let α : ℝ := -(1 / (2 * c))
  change quadratic (d + 1) u = 0 ∧ quadratic (d + 1) (α • v₀) = 0 ∧
    pairing (d + 1) u (α • v₀) = 1
  have hp := traceLapse_hyperbolic_pair d hd
  change quadratic (d + 1) u = 0 ∧ quadratic (d + 1) v₀ = 0 ∧
    pairing (d + 1) u v₀ = -2 * c at hp
  rcases hp with ⟨hu, hv, huv⟩
  have hdR : (d : ℝ) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 by omega)
  have hdgt : (1 : ℝ) < d := by
    exact_mod_cast (show 1 < d by omega)
  have hc : c ≠ 0 := ne_of_gt (div_pos (sub_pos.mpr hdgt) (by positivity))
  refine ⟨hu, ?_, ?_⟩
  · rw [quadratic_smul, hv]
    simp
  · rw [pairing_smul_right, huv]
    dsimp [α]
    field_simp [hc]

/-- The first positive null vector in the normalized lapse/trace pair. -/
def traceLapseWittPlus (d : ℕ) : SymmetricPerturbation (d + 1) :=
  traceLapseMode d (Real.sqrt (2 * ((d - 1 : ℝ) / d))) 1

/-- The second null vector in the normalized lapse/trace pair. -/
def traceLapseWittMinus (d : ℕ) : SymmetricPerturbation (d + 1) :=
  (-(1 / (2 * ((d - 1 : ℝ) / d)))) •
    traceLapseMode d (-Real.sqrt (2 * ((d - 1 : ℝ) / d))) 1

/-- Positive null vectors for the full lapse/shift Witt frame. -/
def deWittWittPlus (d : ℕ) (hd : 2 ≤ d) :
    Fin (d + 1) → SymmetricPerturbation (d + 1) :=
  Fin.cases (traceLapseWittPlus d) (fun i =>
    (1 / 2 : ℝ) • (positiveModes d (spatialShiftPartner d hd i) +
      negativeModes d (shiftModeVector d i)))

/-- Negative null vectors for the full lapse/shift Witt frame. -/
def deWittWittMinus (d : ℕ) (hd : 2 ≤ d) :
    Fin (d + 1) → SymmetricPerturbation (d + 1) :=
  Fin.cases (traceLapseWittMinus d) (fun i =>
    (1 / 2 : ℝ) • (positiveModes d (spatialShiftPartner d hd i) -
      negativeModes d (shiftModeVector d i)))

/-- The actual symmetric-matrix DeWitt carrier contains `d+1` pairwise
orthogonal normalized hyperbolic planes, including the lapse/trace plane and
the `d` shift planes. The bilinear Gram matrix has zero diagonal blocks and
identity cross-block. -/
theorem deWitt_lapse_shift_orthogonal_witt_frame (d : ℕ) (hd : 2 ≤ d)
    (i j : Fin (d + 1)) :
    pairing (d + 1) (deWittWittPlus d hd i) (deWittWittPlus d hd j) = 0 ∧
      pairing (d + 1) (deWittWittMinus d hd i) (deWittWittMinus d hd j) = 0 ∧
      pairing (d + 1) (deWittWittPlus d hd i) (deWittWittMinus d hd j) =
        if i = j then 1 else 0 := by
  have hl := traceLapse_normalized_hyperbolic_pair d hd
  change quadratic (d + 1) (traceLapseWittPlus d) = 0 ∧
      quadratic (d + 1) (traceLapseWittMinus d) = 0 ∧
      pairing (d + 1) (traceLapseWittPlus d) (traceLapseWittMinus d) = 1 at hl
  rcases hl with ⟨hlp, hlm, hlcross⟩
  have hpp : pairing (d + 1) (traceLapseWittPlus d)
      (traceLapseWittPlus d) = 0 := hlp
  have hmm : pairing (d + 1) (traceLapseWittMinus d)
      (traceLapseWittMinus d) = 0 := hlm
  have hpm : pairing (d + 1) (traceLapseWittPlus d)
      (traceLapseWittMinus d) = 1 := hlcross
  have hplusCross (k : Fin d) :
      pairing (d + 1) (traceLapseWittPlus d)
        ((1 / 2 : ℝ) • (positiveModes d (spatialShiftPartner d hd k) +
          negativeModes d (shiftModeVector d k))) = 0 ∧
      pairing (d + 1) (traceLapseWittPlus d)
        ((1 / 2 : ℝ) • (positiveModes d (spatialShiftPartner d hd k) -
          negativeModes d (shiftModeVector d k))) = 0 := by
    simpa [traceLapseWittPlus] using
      traceLapse_orthogonal_spatialWittPair d hd
        (Real.sqrt (2 * ((d - 1 : ℝ) / d))) 1 k
  have hminusCross (k : Fin d) :
      pairing (d + 1) (traceLapseWittMinus d)
        ((1 / 2 : ℝ) • (positiveModes d (spatialShiftPartner d hd k) +
          negativeModes d (shiftModeVector d k))) = 0 ∧
      pairing (d + 1) (traceLapseWittMinus d)
        ((1 / 2 : ℝ) • (positiveModes d (spatialShiftPartner d hd k) -
          negativeModes d (shiftModeVector d k))) = 0 := by
    have hraw := traceLapse_orthogonal_spatialWittPair d hd
      (-Real.sqrt (2 * ((d - 1 : ℝ) / d))) 1 k
    constructor
    · rw [traceLapseWittMinus, pairing_smul_left, hraw.1]
      simp
    · rw [traceLapseWittMinus, pairing_smul_left, hraw.2]
      simp
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero =>
          simpa [deWittWittPlus, deWittWittMinus, quadratic] using
            (And.intro hpp (And.intro hmm hpm))
      | succ j =>
          simp only [deWittWittPlus, deWittWittMinus, Fin.cases_zero,
            Fin.cases_succ]
          exact ⟨(hplusCross j).1, (hminusCross j).2,
            by calc
              _ = 0 := (hplusCross j).2
              _ = if (0 : Fin (d + 1)) = j.succ then 1 else 0 := by
                rw [if_neg (Fin.succ_ne_zero j).symm]⟩
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          simp only [deWittWittPlus, deWittWittMinus, Fin.cases_succ,
            Fin.cases_zero]
          refine ⟨?_, ?_, ?_⟩
          · rw [pairing_swap]
            exact (hplusCross i).1
          · rw [pairing_swap]
            exact (hminusCross i).2
          · rw [pairing_swap]
            exact (hminusCross i).1
      | succ j =>
          have hsucc : i.succ = j.succ ↔ i = j := by
            constructor
            · intro h
              apply Fin.ext
              have hv := congrArg Fin.val h
              simp at hv
              omega
            · rintro rfl
              rfl
          simpa only [deWittWittPlus, deWittWittMinus, Fin.cases_succ,
            hsucc] using
            spatialShiftPartner_orthogonal_witt_frame d hd i j

/-- Recover the spatial positive and lapse/shift negative generators from each
normalized shift Witt pair. Thus the Witt-frame span contains both coordinate
directions used by the spatial section and the negative shift mode. -/
theorem deWittWitt_shift_pair_reconstruction (d : ℕ) (hd : 2 ≤ d)
    (i : Fin d) :
    deWittWittPlus d hd i.succ + deWittWittMinus d hd i.succ =
        positiveModes d (spatialShiftPartner d hd i) ∧
      deWittWittPlus d hd i.succ - deWittWittMinus d hd i.succ =
        negativeModes d (shiftModeVector d i) := by
  constructor
  · change (1 / 2 : ℝ) •
        (positiveModes d (spatialShiftPartner d hd i) +
          negativeModes d (shiftModeVector d i)) +
      (1 / 2 : ℝ) •
        (positiveModes d (spatialShiftPartner d hd i) -
          negativeModes d (shiftModeVector d i)) = _
    module
  · change (1 / 2 : ℝ) •
        (positiveModes d (spatialShiftPartner d hd i) +
          negativeModes d (shiftModeVector d i)) -
      (1 / 2 : ℝ) •
        (positiveModes d (spatialShiftPartner d hd i) -
          negativeModes d (shiftModeVector d i)) = _
    module

/- The full Witt frame will be paired with its opposite null generator. -/
def deWittWittFrame (d : ℕ) (hd : 2 ≤ d) :
    (Fin (d + 1) ⊕ Fin (d + 1)) → SymmetricPerturbation (d + 1) :=
  Sum.elim (deWittWittPlus d hd) (deWittWittMinus d hd)

def deWittWittDualIndex {n : ℕ} : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n)
  | Sum.inl i => Sum.inr i
  | Sum.inr i => Sum.inl i

/-- Pairing a frame vector against the opposite generator of a second frame
vector gives the Kronecker pairing. -/
theorem deWittWittFrame_dual_pairing (d : ℕ) (hd : 2 ≤ d)
    (i j : Fin (d + 1) ⊕ Fin (d + 1)) :
    pairing (d + 1) (deWittWittFrame d hd i)
      (deWittWittFrame d hd (deWittWittDualIndex j)) =
        if i = j then 1 else 0 := by
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp only [deWittWittFrame, Sum.elim_inl, deWittWittDualIndex,
            Sum.elim_inr]
          simpa using (deWitt_lapse_shift_orthogonal_witt_frame d hd i j).2.2
      | inr j =>
          simp only [deWittWittFrame, Sum.elim_inl, deWittWittDualIndex,
            Sum.elim_inl]
          simpa using (deWitt_lapse_shift_orthogonal_witt_frame d hd i j).1
  | inr i =>
      cases j with
      | inl j =>
          simp only [deWittWittFrame, Sum.elim_inr, deWittWittDualIndex,
            Sum.elim_inr]
          rw [pairing_swap]
          simpa using (deWitt_lapse_shift_orthogonal_witt_frame d hd j i).2.1
      | inr j =>
          simp only [deWittWittFrame, Sum.elim_inr, deWittWittDualIndex,
            Sum.elim_inl]
          rw [pairing_swap]
          simpa [eq_comm] using
            (deWitt_lapse_shift_orthogonal_witt_frame d hd j i).2.2

private def deWittPairingFunctional (D : ℕ) (k : SymmetricPerturbation D) :
    SymmetricPerturbation D →ₗ[ℝ] ℝ where
  toFun h := pairing D h k
  map_add' h₁ h₂ := pairing_add_left D h₁ h₂ k
  map_smul' c h := pairing_smul_left D c h k

/-- The full `2(d+1)` null generators are linearly independent. The proof
uses the actual DeWitt pairing as a dual-coordinate system, rather than a
dimension count or a named-frame assumption. -/
theorem deWittWittFrame_linearIndependent (d : ℕ) (hd : 2 ≤ d) :
    LinearIndependent ℝ (deWittWittFrame d hd) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hp := congrArg
    (deWittPairingFunctional (d + 1)
      (deWittWittFrame d hd (deWittWittDualIndex i))) hc
  simp only [map_sum, map_smul, map_zero] at hp
  change (∑ j : Fin (d + 1) ⊕ Fin (d + 1),
      c j * pairing (d + 1) (deWittWittFrame d hd j)
        (deWittWittFrame d hd (deWittWittDualIndex i))) = 0 at hp
  simp_rw [deWittWittFrame_dual_pairing d hd] at hp
  rw [Finset.sum_eq_single i] at hp
  · simpa using hp
  · intro j hj hji
    simp [hji]
  · simp

/-- The hyperbolic span generated by the full lapse/shift Witt frame. -/
def deWittWittFrameSubspace (d : ℕ) (hd : 2 ≤ d) :
    Submodule ℝ (SymmetricPerturbation (d + 1)) :=
  Submodule.span ℝ (Set.range (deWittWittFrame d hd))

/-- The explicit full Witt frame spans exactly `2(d+1)` dimensions. -/
theorem deWittWittFrameSubspace_finrank (d : ℕ) (hd : 2 ≤ d) :
    Module.finrank ℝ (deWittWittFrameSubspace d hd) = 2 * (d + 1) := by
  rw [deWittWittFrameSubspace, finrank_span_eq_card
    (deWittWittFrame_linearIndependent d hd)]
  simp [deWittWittFrame, Fintype.card_sum, Fintype.card_fin]
  omega
/-- Coordinates of the DeWitt pairing of a spatial block against the `d`
explicit diagonal/off-diagonal positive partners of the shift modes. -/
noncomputable def spatialPartnerCoordinates (d : ℕ) (hd : 2 ≤ d) :
    SymmetricPerturbation d →ₗ[ℝ] (Fin (d + 1) → ℝ) :=
  LinearMap.pi fun i => Fin.cases (blockTraceLinear d)
    (fun i => IsLinearMap.mk'
      (fun S => pairing (d + 1)
        (positiveModes d (spatialShiftPartner d hd i)) (positiveModes d S))
      (IsLinearMap.mk
        (fun S T => by rw [(positiveModes d).map_add, pairing_add_right])
        (fun c S => by
          rw [(positiveModes d).map_smul, pairing_smul_right]
          simp [smul_eq_mul]))) i

@[simp] theorem spatialPartnerCoordinates_zero (d : ℕ) (hd : 2 ≤ d)
    (S : SymmetricPerturbation d) :
    spatialPartnerCoordinates d hd S 0 = blockTrace d S := by
  simp [spatialPartnerCoordinates]

@[simp] theorem spatialPartnerCoordinates_succ (d : ℕ) (hd : 2 ≤ d)
    (S : SymmetricPerturbation d) (i : Fin d) :
    spatialPartnerCoordinates d hd S i.succ =
      pairing (d + 1) (positiveModes d (spatialShiftPartner d hd i))
        (positiveModes d S) := by
  simp [spatialPartnerCoordinates]

/-- The spatial anisotropic candidate consists of blocks orthogonal to every
shift-partner spatial direction. This is a subspace of the actual symmetric
matrix carrier, defined as the kernel of the pairing-coordinate map. -/
def spatialAnisotropicSubspace (d : ℕ) (hd : 2 ≤ d) :
    Submodule ℝ (SymmetricPerturbation d) :=
  LinearMap.ker (spatialPartnerCoordinates d hd)

/-- Every element of the spatial anisotropic candidate is orthogonal in the
full spacetime DeWitt form to all shift-partner directions. -/
theorem spatialAnisotropic_orthogonal_shiftPartners (d : ℕ) (hd : 2 ≤ d)
    (S : spatialAnisotropicSubspace d hd) (i : Fin d) :
    pairing (d + 1) (positiveModes d S.1)
      (positiveModes d (spatialShiftPartner d hd i)) = 0 := by
  have hker : spatialPartnerCoordinates d hd S.1 = 0 := S.2
  have hi := congrFun hker i.succ
  simp only [spatialPartnerCoordinates_succ] at hi
  have hi' : pairing (d + 1) (positiveModes d
      (spatialShiftPartner d hd i)) (positiveModes d S.1) = 0 := by
    simpa [bilinear] using hi
  rw [pairing_swap] at hi'
  exact hi'

/-- Kernel elements also have zero spatial trace, so their embedded matrices
are orthogonal to the lapse/trace Witt plane. -/
theorem spatialAnisotropic_trace_zero (d : ℕ) (hd : 2 ≤ d)
    (S : spatialAnisotropicSubspace d hd) : blockTrace d S.1 = 0 := by
  have hker : spatialPartnerCoordinates d hd S.1 = 0 := S.2
  have hi := congrFun hker 0
  simpa only [spatialPartnerCoordinates_zero, Pi.zero_apply] using hi

/-- Strict positivity on every nonzero vector in the spatial anisotropic
candidate, measured by the full spacetime DeWitt quadratic form after its
canonical embedding. -/
theorem spatialAnisotropic_positive (d : ℕ) (hd : 2 ≤ d)
    (S : spatialAnisotropicSubspace d hd) (hS : S.1 ≠ 0) :
    quadratic (d + 1) (positiveModes d S.1) > 0 := by
  have _htrace : blockTrace d S.1 = 0 := spatialAnisotropic_trace_zero d hd S
  exact quadratic_positiveModes_pos d S.1 hS

/-- A shift partner is orthogonal to the spatial identity direction. -/
theorem spatialShiftPartner_orthogonal_identity (d : ℕ) (hd : 2 ≤ d)
    (i : Fin d) :
    pairing (d + 1) (positiveModes d (spatialShiftPartner d hd i))
      (positiveModes d (spatialIdentity d)) = 0 := by
  rw [pairing_positiveModes, blockTrace_spatialShiftPartner d hd i]
  have hdiag : (∑ a : Fin d, ∑ b : Fin d,
      (spatialShiftPartner d hd i).1 a b * (spatialIdentity d).1 a b) =
      blockTrace d (spatialShiftPartner d hd i) := by
    simp [blockTrace, spatialIdentity, Matrix.one_apply]
  rw [hdiag, blockTrace_spatialShiftPartner d hd i]
  simp

/-- The trace/shift coordinates of the spatial identity are exactly its trace
coordinate, with no component along any shift partner. -/
theorem spatialPartnerCoordinates_spatialIdentity (d : ℕ) (hd : 2 ≤ d) :
    spatialPartnerCoordinates d hd (spatialIdentity d) =
      fun i => Fin.cases (d : ℝ) (fun _ => 0) i := by
  funext i
  cases i using Fin.cases with
  | zero =>
      simp only [spatialPartnerCoordinates_zero]
      simp [blockTrace, spatialIdentity]
  | succ i =>
      simp only [spatialPartnerCoordinates_succ,
        spatialShiftPartner_orthogonal_identity]
      rfl

/-- Each spatial shift partner is read by its own coordinate and annihilated
by every other shift coordinate. The diagonal value is the nonzero scalar `2`. -/
theorem spatialPartnerCoordinates_shiftPartner (d : ℕ) (hd : 2 ≤ d)
    (j : Fin d) :
    spatialPartnerCoordinates d hd (spatialShiftPartner d hd j) =
      fun i => Fin.cases 0 (fun i => if i = j then 2 else 0) i := by
  funext i
  cases i using Fin.cases with
  | zero =>
      simp only [spatialPartnerCoordinates_zero]
      rw [blockTrace_spatialShiftPartner]
      rfl
  | succ i =>
      rw [spatialPartnerCoordinates_succ, spatialShiftPartner_pairing]
      simp [eq_comm]

/-- The coordinate map is onto because its identity and shift-partner
preimages give the standard basis after rescaling by `d` and `2`. -/
theorem spatialPartnerCoordinates_surjective (d : ℕ) (hd : 2 ≤ d) :
    Function.Surjective (spatialPartnerCoordinates d hd) := by
  intro f
  refine ⟨(f 0 / (d : ℝ)) • spatialIdentity d +
    ∑ j : Fin d, (f j.succ / 2) • spatialShiftPartner d hd j, ?_⟩
  have hmap : spatialPartnerCoordinates d hd
      ((f 0 / (d : ℝ)) • spatialIdentity d +
        ∑ j : Fin d, (f j.succ / 2) • spatialShiftPartner d hd j) = f := by
    rw [(spatialPartnerCoordinates d hd).map_add,
      (spatialPartnerCoordinates d hd).map_smul,
      map_sum (spatialPartnerCoordinates d hd)
        (fun j : Fin d => (f j.succ / 2) • spatialShiftPartner d hd j)
        Finset.univ]
    funext i
    cases i using Fin.cases with
    | zero =>
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Finset.sum_apply, spatialPartnerCoordinates_zero,
          spatialPartnerCoordinates_spatialIdentity,
          spatialPartnerCoordinates_shiftPartner]
        simp only [Fin.cases_zero, mul_zero, add_zero]
        have hzero : (∑ x : Fin d,
            blockTrace d ((f x.succ / 2) • spatialShiftPartner d hd x)) = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          rw [blockTrace_smul, blockTrace_spatialShiftPartner]
          simp
        rw [hzero, add_zero]
        have hdR : (d : ℝ) ≠ 0 := by
          exact_mod_cast (show d ≠ 0 by omega)
        field_simp [hdR]
    | succ i =>
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Finset.sum_apply, spatialPartnerCoordinates_zero,
          spatialPartnerCoordinates_succ,
          spatialPartnerCoordinates_spatialIdentity,
          spatialPartnerCoordinates_shiftPartner, Fin.cases_succ,
          mul_zero, zero_add]
        rw [Finset.sum_eq_single i]
        · rw [(positiveModes d).map_smul, pairing_smul_right,
            spatialShiftPartner_pairing]
          simp
        · intro j hj hji
          rw [(positiveModes d).map_smul, pairing_smul_right,
            spatialShiftPartner_pairing]
          simp [Ne.symm hji]
        · simp
  exact hmap

/-- A linear section of the trace/shift coordinate map, built from the spatial
identity and the mutually orthogonal shift partners. -/
noncomputable def spatialPartnerSection (d : ℕ) (hd : 2 ≤ d) :
    (Fin (d + 1) → ℝ) →ₗ[ℝ] SymmetricPerturbation d where
  toFun f := (f 0 / (d : ℝ)) • spatialIdentity d +
    ∑ j : Fin d, (f j.succ / 2) • spatialShiftPartner d hd j
  map_add' f g := by
    simp only [Pi.add_apply, add_div, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_div_assoc, smul_add,
      Finset.smul_sum, smul_smul]
    simp only [RingHom.id_apply]

/-- The explicit linear section is a right inverse to the trace/shift
coordinate map. -/
theorem spatialPartnerCoordinates_section_apply (d : ℕ) (hd : 2 ≤ d)
    (f : Fin (d + 1) → ℝ) :
    spatialPartnerCoordinates d hd (spatialPartnerSection d hd f) = f := by
  change spatialPartnerCoordinates d hd
      ((f 0 / (d : ℝ)) • spatialIdentity d +
        ∑ j : Fin d, (f j.succ / 2) • spatialShiftPartner d hd j) = f
  rw [(spatialPartnerCoordinates d hd).map_add,
    (spatialPartnerCoordinates d hd).map_smul,
    map_sum (spatialPartnerCoordinates d hd)
      (fun j : Fin d => (f j.succ / 2) • spatialShiftPartner d hd j)
      Finset.univ]
  funext i
  cases i using Fin.cases with
  | zero =>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_apply, spatialPartnerCoordinates_zero,
        spatialPartnerCoordinates_spatialIdentity,
        spatialPartnerCoordinates_shiftPartner]
      simp only [Fin.cases_zero, mul_zero, add_zero]
      have hzero : (∑ x : Fin d,
          blockTrace d ((f x.succ / 2) • spatialShiftPartner d hd x)) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        rw [blockTrace_smul, blockTrace_spatialShiftPartner]
        simp
      rw [hzero, add_zero]
      have hdR : (d : ℝ) ≠ 0 := by
        exact_mod_cast (show d ≠ 0 by omega)
      field_simp [hdR]
  | succ i =>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_apply, spatialPartnerCoordinates_zero,
        spatialPartnerCoordinates_succ,
        spatialPartnerCoordinates_spatialIdentity,
        spatialPartnerCoordinates_shiftPartner, Fin.cases_succ,
        mul_zero, zero_add]
      rw [Finset.sum_eq_single i]
      · rw [(positiveModes d).map_smul, pairing_smul_right,
          spatialShiftPartner_pairing]
        simp
      · intro j hj hji
        rw [(positiveModes d).map_smul, pairing_smul_right,
          spatialShiftPartner_pairing]
        simp [Ne.symm hji]
      · simp

/-- The spatial anisotropic kernel and the explicit section image have zero
intersection. -/
theorem spatialAnisotropic_inf_sectionRange_eq_bot (d : ℕ) (hd : 2 ≤ d) :
    spatialAnisotropicSubspace d hd ⊓
      LinearMap.range (spatialPartnerSection d hd) = ⊥ := by
  apply le_antisymm
  · intro S hS
    rcases hS with ⟨hker, ⟨f, hf⟩⟩
    have hcoordinates := LinearMap.mem_ker.mp hker
    rw [← hf, spatialPartnerCoordinates_section_apply] at hcoordinates
    have hfzero : f = 0 := by
      funext i
      exact congrFun hcoordinates i
    subst f
    simpa using hf.symm
  · exact bot_le

/-- The anisotropic kernel together with the selected trace/shift directions
spans every actual symmetric spatial block. -/
theorem spatialAnisotropic_sup_sectionRange_eq_top (d : ℕ) (hd : 2 ≤ d) :
    spatialAnisotropicSubspace d hd ⊔
      LinearMap.range (spatialPartnerSection d hd) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro S
  apply Submodule.mem_sup.mpr
  refine ⟨S - spatialPartnerSection d hd (spatialPartnerCoordinates d hd S), ?_,
    spatialPartnerSection d hd (spatialPartnerCoordinates d hd S), ?_, ?_⟩
  · apply LinearMap.mem_ker.mpr
    rw [map_sub, spatialPartnerCoordinates_section_apply]
    simp
  · exact ⟨spatialPartnerCoordinates d hd S, rfl⟩
  · abel

/-- The spatial symmetric-matrix carrier is the internal direct sum of the
trace/shift-coordinate kernel and its explicit section image. -/
theorem spatialAnisotropic_isCompl_sectionRange (d : ℕ) (hd : 2 ≤ d) :
    IsCompl (spatialAnisotropicSubspace d hd)
      (LinearMap.range (spatialPartnerSection d hd)) := by
  rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  exact ⟨spatialAnisotropic_inf_sectionRange_eq_bot d hd,
    spatialAnisotropic_sup_sectionRange_eq_top d hd⟩

/-- The anisotropic kernel has the expected dimension by rank-nullity: its
dimension plus the trace coordinate and `d` independent shift coordinates
equals the dimension of the spatial symmetric-matrix carrier. -/
theorem spatialAnisotropic_finrank_add_codimension (d : ℕ) (hd : 2 ≤ d) :
    Module.finrank ℝ (spatialAnisotropicSubspace d hd) + (d + 1) =
      Nat.choose (d + 1) 2 := by
  have hrank :=
    (spatialAnisotropicSubspace d hd).finrank_quotient_add_finrank
  rw [show spatialAnisotropicSubspace d hd =
      LinearMap.ker (spatialPartnerCoordinates d hd) by rfl] at hrank
  rw [LinearEquiv.finrank_eq
    (spatialPartnerCoordinates d hd).quotKerEquivRange] at hrank
  have hsurj : LinearMap.range (spatialPartnerCoordinates d hd) = ⊤ :=
    LinearMap.range_eq_top.mpr (spatialPartnerCoordinates_surjective d hd)
  rw [hsurj, finrank_top, finrank_symmetricPerturbation] at hrank
  have hcard : Module.finrank ℝ (Fin (d + 1) → ℝ) = d + 1 := by
    simp [Module.finrank_fintype_fun_eq_card]
  rw [hcard] at hrank
  change Module.finrank ℝ (LinearMap.ker (spatialPartnerCoordinates d hd)) +
      (d + 1) = Nat.choose (d + 1) 2
  omega

/-- The same rank computation in closed form: the spatial anisotropic part has
dimension `choose d 2 - 1`, i.e. `(d+1)(d-2)/2` in spacetime dimension `d+1`. -/
theorem spatialAnisotropic_finrank (d : ℕ) (hd : 2 ≤ d) :
    Module.finrank ℝ (spatialAnisotropicSubspace d hd) =
      Nat.choose d 2 - 1 := by
  have hchoose : Nat.choose (d + 1) 2 = d + Nat.choose d 2 := by
    rw [Nat.choose_succ_succ' d 1]
    simp
  have hdim := spatialAnisotropic_finrank_add_codimension d hd
  rw [hchoose] at hdim
  have hpos : 1 ≤ Nat.choose d 2 := by
    exact Nat.succ_le_of_lt (Nat.choose_pos (by omega))
  omega

/-- The anisotropic kernel is orthogonal to the complete explicit Witt frame:
trace zero handles the lapse pair and its defining coordinates handle shifts. -/
theorem spatialAnisotropic_orthogonal_wittFrame (d : ℕ) (hd : 2 ≤ d)
    (S : spatialAnisotropicSubspace d hd) (i : Fin (d + 1)) :
    pairing (d + 1) (positiveModes d S.1) (deWittWittPlus d hd i) = 0 ∧
      pairing (d + 1) (positiveModes d S.1) (deWittWittMinus d hd i) = 0 := by
  cases i using Fin.cases with
  | zero =>
      have ht := spatialAnisotropic_trace_zero d hd S
      have hplus := traceLapse_orthogonal_traceFreeSpatial d hd
        (Real.sqrt (2 * ((d - 1 : ℝ) / d))) 1 S.1 ht
      have hminus := traceLapse_orthogonal_traceFreeSpatial d hd
        (-Real.sqrt (2 * ((d - 1 : ℝ) / d))) 1 S.1 ht
      constructor
      · change pairing (d + 1) (positiveModes d S.1)
          (traceLapseWittPlus d) = 0
        calc
          _ = pairing (d + 1) (traceLapseMode d
              (Real.sqrt (2 * ((d - 1 : ℝ) / d))) 1) (positiveModes d S.1) :=
                pairing_swap _ _ _
          _ = 0 := hplus
      · change pairing (d + 1) (positiveModes d S.1)
          (traceLapseWittMinus d) = 0
        rw [traceLapseWittMinus, pairing_smul_right, pairing_swap, hminus]
        simp
  | succ i =>
      have h := spatialAnisotropic_orthogonal_shiftPartners d hd S i
      have htrace := spatialAnisotropic_trace_zero d hd S
      have hshift : pairing (d + 1) (negativeModes d (shiftModeVector d i))
          (positiveModes d S.1) = 0 :=
        negativeModes_orthogonal_traceFreePositiveModes d
          (shiftModeVector d i) S.1 htrace
      constructor
      · simp only [deWittWittPlus, Fin.cases_succ]
        rw [pairing_smul_right, pairing_add_right, h, pairing_swap, hshift]
        simp
      · simp only [deWittWittMinus, Fin.cases_succ]
        rw [pairing_smul_right, pairing_sub_right, h, pairing_swap, hshift]
        simp

/-- Embed the spatial anisotropic kernel into the full spacetime perturbation
carrier. -/
def spacetimeAnisotropicEmbedding (d : ℕ) (hd : 2 ≤ d) :
    spatialAnisotropicSubspace d hd →ₗ[ℝ]
      SymmetricPerturbation (d + 1) :=
  (positiveModes d).comp (spatialAnisotropicSubspace d hd).subtype

/-- The full spacetime anisotropic subspace is the image of the spatial
trace/shift kernel under the genuine symmetric-matrix block embedding. -/
def spacetimeAnisotropicSubspace (d : ℕ) (hd : 2 ≤ d) :
    Submodule ℝ (SymmetricPerturbation (d + 1)) :=
  LinearMap.range (spacetimeAnisotropicEmbedding d hd)

/-- The anisotropic subspace and the explicit hyperbolic frame have trivial
intersection. Orthogonality to every frame vector forces an element of their
intersection to have zero DeWitt norm, while anisotropic positivity forces it
to vanish. -/
theorem spacetimeAnisotropic_inf_wittFrame_eq_bot (d : ℕ) (hd : 2 ≤ d) :
    spacetimeAnisotropicSubspace d hd ⊓ deWittWittFrameSubspace d hd = ⊥ := by
  apply le_antisymm
  · intro x hx
    rcases Submodule.mem_inf.mp hx with ⟨⟨S, hS⟩, hframe⟩
    have hframe' : spacetimeAnisotropicEmbedding d hd S ∈
        deWittWittFrameSubspace d hd := by
      rw [hS]
      exact hframe
    have horth : ∀ y ∈ deWittWittFrameSubspace d hd,
        pairing (d + 1) (spacetimeAnisotropicEmbedding d hd S) y = 0 := by
      intro y hy
      refine Submodule.span_induction
        (p := fun y _ =>
          pairing (d + 1) (spacetimeAnisotropicEmbedding d hd S) y = 0)
        ?_ ?_ ?_ ?_ hy
      · intro z hz
        rcases hz with ⟨i, rfl⟩
        cases i with
        | inl i => exact (spatialAnisotropic_orthogonal_wittFrame d hd S i).1
        | inr i => exact (spatialAnisotropic_orthogonal_wittFrame d hd S i).2
      · rw [pairing_swap]
        exact (deWittPairingFunctional (d + 1)
          (spacetimeAnisotropicEmbedding d hd S)).map_zero
      · intro y₁ y₂ hy₁ hy₂ h₁ h₂
        rw [pairing_add_right, h₁, h₂]
        ring
      · intro c y hy h_y
        rw [pairing_smul_right, h_y]
        simp
    have hqzero : quadratic (d + 1) (spacetimeAnisotropicEmbedding d hd S) = 0 := by
      simpa [quadratic] using horth _ hframe'
    have hSzero : S.1 = 0 := by
      by_contra hSne
      have hpos := spatialAnisotropic_positive d hd S hSne
      have hpos' : quadratic (d + 1)
          (spacetimeAnisotropicEmbedding d hd S) > 0 := by
        simpa [spacetimeAnisotropicEmbedding] using hpos
      rw [hqzero] at hpos'
      linarith
    have hxzero : x = 0 := by
      rw [← hS]
      simp [spacetimeAnisotropicEmbedding, hSzero]
    simpa [Submodule.mem_bot] using hxzero
  · exact bot_le

/-- The spacetime embedding of the anisotropic kernel is injective because
its spatial block recovers the original symmetric matrix. -/
theorem spacetimeAnisotropicEmbedding_injective (d : ℕ) (hd : 2 ≤ d) :
    Function.Injective (spacetimeAnisotropicEmbedding d hd) := by
  intro S T h
  change positiveModes d (S : spatialAnisotropicSubspace d hd) =
    positiveModes d (T : spatialAnisotropicSubspace d hd) at h
  apply Subtype.ext
  exact positiveModes_injective d h

/-- The anisotropic spacetime image has the expected transverse dimension. -/
theorem spacetimeAnisotropicSubspace_finrank (d : ℕ) (hd : 2 ≤ d) :
    Module.finrank ℝ (spacetimeAnisotropicSubspace d hd) = Nat.choose d 2 - 1 := by
  rw [spacetimeAnisotropicSubspace,
    LinearMap.finrank_range_of_inj (spacetimeAnisotropicEmbedding_injective d hd),
    spatialAnisotropic_finrank]

/-- The hyperbolic frame and positive anisotropic image span the entire
symmetric spacetime perturbation carrier. The proof combines the proved
trivial intersection with their exact dimensions. -/
theorem deWitt_full_witt_anisotropic_sup_eq_top (d : ℕ) (hd : 2 ≤ d) :
    spacetimeAnisotropicSubspace d hd ⊔ deWittWittFrameSubspace d hd = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (spacetimeAnisotropicSubspace d hd) (deWittWittFrameSubspace d hd)
  rw [spacetimeAnisotropic_inf_wittFrame_eq_bot d hd] at hsum
  rw [finrank_bot, add_zero] at hsum
  rw [spacetimeAnisotropicSubspace_finrank d hd,
    deWittWittFrameSubspace_finrank d hd] at hsum
  have hc1 : Nat.choose (d + 1) 2 = d + Nat.choose d 2 := by
    rw [Nat.choose_succ_succ' d 1]
    simp
  have hc2 : Nat.choose (d + 2) 2 = d + 1 + Nat.choose (d + 1) 2 := by
    rw [Nat.choose_succ_succ' (d + 1) 1]
    simp
  have hcpos : 1 ≤ Nat.choose d 2 := Nat.choose_pos (by omega)
  have hdimension : Nat.choose d 2 - 1 + 2 * (d + 1) = Nat.choose (d + 2) 2 := by
    rw [hc2, hc1]
    have hminus : Nat.choose d 2 - 1 + 1 = Nat.choose d 2 :=
      Nat.sub_add_cancel hcpos
    omega
  rw [hsum, finrank_symmetricPerturbation]
  exact hdimension

/-- The actual full spacetime perturbation carrier is the internal direct sum
of the positive anisotropic subspace and the explicit hyperbolic-frame span. -/
theorem deWitt_full_witt_anisotropic_isCompl (d : ℕ) (hd : 2 ≤ d) :
    IsCompl (spacetimeAnisotropicSubspace d hd)
      (deWittWittFrameSubspace d hd) := by
  rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  exact ⟨spacetimeAnisotropic_inf_wittFrame_eq_bot d hd,
    deWitt_full_witt_anisotropic_sup_eq_top d hd⟩

/-- The restriction of the full DeWitt quadratic form to the plane generated
by the normalized explicit null pair is the split binary form `2 a b`. This proves
the Witt-plane structure, including its bilinear cross term, inside
`SymmetricPerturbation (d + 1)`. -/
theorem traceLapse_hyperbolic_form (d : ℕ) (hd : 2 ≤ d) (a b : ℝ) :
    let r := Real.sqrt (2 * ((d - 1 : ℝ) / d))
    let u := traceLapseMode d r 1
    let c : ℝ := (d - 1 : ℝ) / d
    let v := (-(1 / (2 * c))) • traceLapseMode d (-r) 1
    quadratic (d + 1) (a • u + b • v) =
      2 * a * b := by
  let r : ℝ := Real.sqrt (2 * ((d - 1 : ℝ) / d))
  let u := traceLapseMode d r 1
  let c : ℝ := (d - 1 : ℝ) / d
  let v := (-(1 / (2 * c))) • traceLapseMode d (-r) 1
  have hp := traceLapse_normalized_hyperbolic_pair d hd
  change quadratic (d + 1) u = 0 ∧ quadratic (d + 1) v = 0 ∧
    pairing (d + 1) u v = 1 at hp
  rcases hp with ⟨hu, hv, huv⟩
  change quadratic (d + 1) (a • u + b • v) =
    2 * a * b
  rw [quadratic_add, quadratic_smul, quadratic_smul, hu, hv,
    pairing_smul_left, pairing_smul_right, huv]
  ring_nf

end InfoGeometry.Geometry.DeWittMatrixForm
