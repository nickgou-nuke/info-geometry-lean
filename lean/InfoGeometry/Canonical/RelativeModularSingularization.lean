import InfoGeometry.Canonical.RelativeModularOperator
import InfoGeometry.Canonical.Singular
import InfoGeometry.Meta.Architecture
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

open scoped BigOperators

/-!
# Relative Modular Singularization

Nontrivial singular support truncation for the finite relative modular operator.

The full finite owner `relativeModularOperator q q0` is strictly positive and
therefore invertible, so its Drazin and Moore-Penrose projectors collapse to the
identity. The genuinely singular regime appears only after support truncation:

- keep the modular ratio on a chosen support `s`,
- set the operator to zero off-support,
- use the reciprocal ratio on the same support as the generalized inverse.

This produces proper support projectors, a nontrivial Moore-Penrose/Drazin
package, and pseudo-determinant style scalar shadows.
-/

namespace RelativeModularSingularization

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Canonical.PositiveRayCore
open RelativeModularCore
open RelativePotentialCore
open RelativeModularOperator
open _root_.JaynesInfoStatMech.ThermalDiagonal

section Finite

variable {n : ℕ} [Nonempty (Fin n)]

private theorem relativeDensity_mul_reverse
    (q q0 : PositiveRay (Fin n)) (i : Fin n) :
    relativeDensity (α := Fin n) q q0 i * relativeDensity (α := Fin n) q0 q i = 1 := by
  have h := relativeDensity_cocycle (q := q) (q0 := q0) (q1 := q) i
  rw [relativeDensity_self] at h
  exact h.symm

private theorem reverse_relativeDensity_mul
    (q q0 : PositiveRay (Fin n)) (i : Fin n) :
    relativeDensity (α := Fin n) q0 q i * relativeDensity (α := Fin n) q q0 i = 1 := by
  have h := relativeDensity_cocycle (q := q0) (q0 := q) (q1 := q0) i
  rw [relativeDensity_self] at h
  exact h.symm

/-- Diagonal projector onto a chosen support subset. -/
@[rep_depth operator]
def supportProjector (s : Finset (Fin n)) : FinMat n :=
  diagMatrix (fun i => if i ∈ s then 1 else 0)

omit [Nonempty (Fin n)] in
@[simp] theorem supportProjector_diag
    (s : Finset (Fin n)) (i : Fin n) :
    supportProjector (n := n) s i i = if i ∈ s then 1 else 0 := by
  simp only [supportProjector, diagMatrix, Matrix.diagonal_apply_eq]

omit [Nonempty (Fin n)] in
@[simp] theorem supportProjector_offdiag
    (s : Finset (Fin n)) {i j : Fin n} (hij : i ≠ j) :
    supportProjector (n := n) s i j = 0 := by
  simp only [supportProjector, diagMatrix, Matrix.diagonal_apply_ne _ hij]

omit [Nonempty (Fin n)] in
@[simp] theorem supportProjector_idempotent
    (s : Finset (Fin n)) :
    supportProjector (n := n) s * supportProjector (n := n) s =
      supportProjector (n := n) s := by
  unfold supportProjector diagMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr
  funext i
  by_cases hi : i ∈ s <;> simp only [hi, if_true, if_false, one_mul, zero_mul]

omit [Nonempty (Fin n)] in
@[simp] theorem supportProjector_star
    (s : Finset (Fin n)) :
    star (supportProjector (n := n) s) = supportProjector (n := n) s := by
  unfold supportProjector diagMatrix
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  simp only [star_trivial]

omit [Nonempty (Fin n)] in
theorem supportProjector_ne_zero_of_mem
    (s : Finset (Fin n)) {i : Fin n} (hi : i ∈ s) :
    supportProjector (n := n) s ≠ 0 := by
  intro h
  have hDiag : (1 : ℝ) = 0 := by
    simpa [supportProjector, diagMatrix, hi] using congrArg (fun M : FinMat n => M i i) h
  exact one_ne_zero hDiag

omit [Nonempty (Fin n)] in
theorem supportProjector_ne_one_of_not_mem
    (s : Finset (Fin n)) {i : Fin n} (hi : i ∉ s) :
    supportProjector (n := n) s ≠ (1 : FinMat n) := by
  intro h
  have hDiag : (0 : ℝ) = 1 := by
    simpa [supportProjector, diagMatrix, hi] using congrArg (fun M : FinMat n => M i i) h
  exact zero_ne_one hDiag

/--
Support-truncated relative modular operator: keep the modular ratio on `s` and
force zero off-support.
-/
@[rep_depth operator]
noncomputable def singularRelativeModularOperator
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) : FinMat n :=
  diagMatrix (fun i =>
    if i ∈ s then relativeDensity (α := Fin n) q q0 i else 0)

/--
Support-truncated reciprocal modular operator. This is the generalized inverse
for `singularRelativeModularOperator`.
-/
@[rep_depth operator]
noncomputable def singularRelativeModularPseudoInverse
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) : FinMat n :=
  diagMatrix (fun i =>
    if i ∈ s then relativeDensity (α := Fin n) q0 q i else 0)

@[simp] theorem singularRelativeModularOperator_diag
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) (i : Fin n) :
    singularRelativeModularOperator (n := n) s q q0 i i =
      if i ∈ s then relativeDensity (α := Fin n) q q0 i else 0 := by
  simp only [singularRelativeModularOperator, diagMatrix, Matrix.diagonal_apply_eq]

@[simp] theorem singularRelativeModularOperator_offdiag
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) {i j : Fin n} (hij : i ≠ j) :
    singularRelativeModularOperator (n := n) s q q0 i j = 0 := by
  simp only [singularRelativeModularOperator, diagMatrix, Matrix.diagonal_apply_ne _ hij]

@[simp] theorem singularRelativeModularPseudoInverse_diag
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) (i : Fin n) :
    singularRelativeModularPseudoInverse (n := n) s q q0 i i =
      if i ∈ s then relativeDensity (α := Fin n) q0 q i else 0 := by
  simp only [singularRelativeModularPseudoInverse, diagMatrix, Matrix.diagonal_apply_eq]

@[simp] theorem singularRelativeModularPseudoInverse_offdiag
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) {i j : Fin n} (hij : i ≠ j) :
    singularRelativeModularPseudoInverse (n := n) s q q0 i j = 0 := by
  simp only [singularRelativeModularPseudoInverse, diagMatrix, Matrix.diagonal_apply_ne _ hij]

/-- The singular operator is exactly the support projection of the full owner. -/
@[rep_depth operator]
theorem singularRelativeModularOperator_eq_supportProjector_mul_relativeModularOperator
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    singularRelativeModularOperator (n := n) s q q0 =
      supportProjector (n := n) s * relativeModularOperator (n := n) q q0 := by
  unfold singularRelativeModularOperator supportProjector relativeModularOperator
  rw [RelativeStatePair.modularOperator_eq_diagMatrix_density]
  unfold RelativeStatePair.density diagMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr
  funext i
  by_cases hi : i ∈ s <;> simp only [hi, if_true, if_false, one_mul, zero_mul]

@[rep_depth operator]
theorem singularRelativeModularOperator_eq_relativeModularOperator_mul_supportProjector
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    singularRelativeModularOperator (n := n) s q q0 =
      relativeModularOperator (n := n) q q0 * supportProjector (n := n) s := by
  unfold singularRelativeModularOperator supportProjector relativeModularOperator
  rw [RelativeStatePair.modularOperator_eq_diagMatrix_density]
  unfold RelativeStatePair.density diagMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr
  funext i
  by_cases hi : i ∈ s <;> simp only [hi, if_true, if_false, mul_one, mul_zero]

@[rep_depth operator]
theorem singularRelativeModularPseudoInverse_eq_supportProjector_mul_relativeModularOperator
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    singularRelativeModularPseudoInverse (n := n) s q q0 =
      supportProjector (n := n) s * relativeModularOperator (n := n) q0 q := by
  unfold singularRelativeModularPseudoInverse supportProjector relativeModularOperator
  rw [RelativeStatePair.modularOperator_eq_diagMatrix_density]
  unfold RelativeStatePair.density diagMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr
  funext i
  by_cases hi : i ∈ s <;> simp only [hi, if_true, if_false, one_mul, zero_mul]

@[rep_depth operator]
theorem singularRelativeModularPseudoInverse_eq_relativeModularOperator_mul_supportProjector
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    singularRelativeModularPseudoInverse (n := n) s q q0 =
      relativeModularOperator (n := n) q0 q * supportProjector (n := n) s := by
  unfold singularRelativeModularPseudoInverse supportProjector relativeModularOperator
  rw [RelativeStatePair.modularOperator_eq_diagMatrix_density]
  unfold RelativeStatePair.density diagMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr
  funext i
  by_cases hi : i ∈ s <;> simp only [hi, if_true, if_false, mul_one, mul_zero]

@[simp] theorem supportProjector_mul_singularRelativeModularOperator
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    supportProjector (n := n) s * singularRelativeModularOperator (n := n) s q q0 =
      singularRelativeModularOperator (n := n) s q q0 := by
  unfold supportProjector singularRelativeModularOperator diagMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr
  funext i
  by_cases hi : i ∈ s <;> simp only [hi, if_true, if_false, one_mul, zero_mul]

@[simp] theorem singularRelativeModularOperator_mul_supportProjector
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    singularRelativeModularOperator (n := n) s q q0 * supportProjector (n := n) s =
      singularRelativeModularOperator (n := n) s q q0 := by
  unfold supportProjector singularRelativeModularOperator diagMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr
  funext i
  by_cases hi : i ∈ s <;> simp only [hi, if_true, if_false, mul_one, mul_zero]

@[simp] theorem supportProjector_mul_singularRelativeModularPseudoInverse
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    supportProjector (n := n) s * singularRelativeModularPseudoInverse (n := n) s q q0 =
      singularRelativeModularPseudoInverse (n := n) s q q0 := by
  unfold supportProjector singularRelativeModularPseudoInverse diagMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr
  funext i
  by_cases hi : i ∈ s <;> simp only [hi, if_true, if_false, one_mul, zero_mul]

@[simp] theorem singularRelativeModularPseudoInverse_mul_supportProjector
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    singularRelativeModularPseudoInverse (n := n) s q q0 * supportProjector (n := n) s =
      singularRelativeModularPseudoInverse (n := n) s q q0 := by
  unfold supportProjector singularRelativeModularPseudoInverse diagMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr
  funext i
  by_cases hi : i ∈ s <;> simp only [hi, if_true, if_false, mul_one, mul_zero]

/-- The spectral/range projection of the singular pair is the support projector. -/
@[rep_depth operator]
theorem singularRelativeModularOperator_mul_pseudoInverse_eq_supportProjector
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    singularRelativeModularOperator (n := n) s q q0
        * singularRelativeModularPseudoInverse (n := n) s q q0 =
      supportProjector (n := n) s := by
  unfold singularRelativeModularOperator singularRelativeModularPseudoInverse supportProjector diagMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr
  funext i
  by_cases hi : i ∈ s
  · rw [if_pos hi, if_pos hi, if_pos hi, relativeDensity_mul_reverse]
  · rw [if_neg hi, if_neg hi, if_neg hi]
    simp

/-- The domain/co-range projection of the singular pair is the same support projector. -/
@[rep_depth operator]
theorem singularRelativeModularPseudoInverse_mul_operator_eq_supportProjector
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    singularRelativeModularPseudoInverse (n := n) s q q0
        * singularRelativeModularOperator (n := n) s q q0 =
      supportProjector (n := n) s := by
  unfold singularRelativeModularOperator singularRelativeModularPseudoInverse supportProjector diagMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr
  funext i
  by_cases hi : i ∈ s
  · rw [if_pos hi, if_pos hi, if_pos hi, reverse_relativeDensity_mul]
  · rw [if_neg hi, if_neg hi, if_neg hi]
    simp

/-- Support-truncated modular pair satisfies the Moore-Penrose equations. -/
@[rep_depth operator]
theorem isMoorePenroseInverse_singularRelativeModularOperator
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    IsMoorePenroseInverse
      (singularRelativeModularOperator (n := n) s q q0)
      (singularRelativeModularPseudoInverse (n := n) s q q0) := by
  refine IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · calc
      singularRelativeModularOperator (n := n) s q q0
          * singularRelativeModularPseudoInverse (n := n) s q q0
          * singularRelativeModularOperator (n := n) s q q0
          = supportProjector (n := n) s
              * singularRelativeModularOperator (n := n) s q q0 := by
              rw [singularRelativeModularOperator_mul_pseudoInverse_eq_supportProjector]
      _ = singularRelativeModularOperator (n := n) s q q0 := by
        rw [supportProjector_mul_singularRelativeModularOperator]
  · calc
      singularRelativeModularPseudoInverse (n := n) s q q0
          * singularRelativeModularOperator (n := n) s q q0
          * singularRelativeModularPseudoInverse (n := n) s q q0
          = supportProjector (n := n) s
              * singularRelativeModularPseudoInverse (n := n) s q q0 := by
              rw [singularRelativeModularPseudoInverse_mul_operator_eq_supportProjector]
      _ = singularRelativeModularPseudoInverse (n := n) s q q0 := by
        rw [supportProjector_mul_singularRelativeModularPseudoInverse]
  · rw [singularRelativeModularOperator_mul_pseudoInverse_eq_supportProjector]
    exact supportProjector_star (n := n) s
  · rw [singularRelativeModularPseudoInverse_mul_operator_eq_supportProjector]
    exact supportProjector_star (n := n) s

/-- Support-truncated modular pair satisfies the Drazin equations with index `1`. -/
@[rep_depth operator]
theorem isDrazinInverse_singularRelativeModularOperator
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    IsDrazinInverse
      (singularRelativeModularOperator (n := n) s q q0)
      (singularRelativeModularPseudoInverse (n := n) s q q0) 1 := by
  refine IsDrazinInverse.mk ?_ ?_ ?_
  · rw [singularRelativeModularOperator_mul_pseudoInverse_eq_supportProjector,
      singularRelativeModularPseudoInverse_mul_operator_eq_supportProjector]
  · calc
      singularRelativeModularPseudoInverse (n := n) s q q0
          * singularRelativeModularOperator (n := n) s q q0
          * singularRelativeModularPseudoInverse (n := n) s q q0
          = supportProjector (n := n) s
              * singularRelativeModularPseudoInverse (n := n) s q q0 := by
              rw [singularRelativeModularPseudoInverse_mul_operator_eq_supportProjector]
      _ = singularRelativeModularPseudoInverse (n := n) s q q0 := by
        rw [supportProjector_mul_singularRelativeModularPseudoInverse]
  · calc
      singularRelativeModularOperator (n := n) s q q0 ^ (1 + 1)
          * singularRelativeModularPseudoInverse (n := n) s q q0
          = singularRelativeModularOperator (n := n) s q q0
              * (singularRelativeModularOperator (n := n) s q q0
                  * singularRelativeModularPseudoInverse (n := n) s q q0) := by
                    simp [pow_succ, mul_assoc]
      _ = singularRelativeModularOperator (n := n) s q q0
              * supportProjector (n := n) s := by
                rw [singularRelativeModularOperator_mul_pseudoInverse_eq_supportProjector]
      _ = singularRelativeModularOperator (n := n) s q q0 := by
        rw [singularRelativeModularOperator_mul_supportProjector]
      _ = singularRelativeModularOperator (n := n) s q q0 ^ 1 := by
        simp

@[simp] theorem drazinProjection_eq_supportProjector
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    IsDrazinInverse.projection
        (singularRelativeModularOperator (n := n) s q q0)
        (singularRelativeModularPseudoInverse (n := n) s q q0)
      = supportProjector (n := n) s := by
  exact singularRelativeModularOperator_mul_pseudoInverse_eq_supportProjector
    (n := n) s q q0

@[simp] theorem moorePenroseRightProjector_eq_supportProjector
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    IsMoorePenroseInverse.rightProjector
        (singularRelativeModularOperator (n := n) s q q0)
        (singularRelativeModularPseudoInverse (n := n) s q q0)
      = supportProjector (n := n) s := by
  exact singularRelativeModularOperator_mul_pseudoInverse_eq_supportProjector
    (n := n) s q q0

@[simp] theorem moorePenroseLeftProjector_eq_supportProjector
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    IsMoorePenroseInverse.leftProjector
        (singularRelativeModularOperator (n := n) s q q0)
        (singularRelativeModularPseudoInverse (n := n) s q q0)
      = supportProjector (n := n) s := by
  exact singularRelativeModularPseudoInverse_mul_operator_eq_supportProjector
    (n := n) s q q0

theorem drazinProjection_ne_zero_of_mem
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) {i : Fin n} (hi : i ∈ s) :
    IsDrazinInverse.projection
        (singularRelativeModularOperator (n := n) s q q0)
        (singularRelativeModularPseudoInverse (n := n) s q q0) ≠ 0 := by
  rw [drazinProjection_eq_supportProjector]
  exact supportProjector_ne_zero_of_mem (n := n) s hi

theorem drazinProjection_ne_one_of_not_mem
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) {i : Fin n} (hi : i ∉ s) :
    IsDrazinInverse.projection
        (singularRelativeModularOperator (n := n) s q q0)
        (singularRelativeModularPseudoInverse (n := n) s q q0) ≠ (1 : FinMat n) := by
  rw [drazinProjection_eq_supportProjector]
  exact supportProjector_ne_one_of_not_mem (n := n) s hi

theorem moorePenroseRightProjector_ne_zero_of_mem
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) {i : Fin n} (hi : i ∈ s) :
    IsMoorePenroseInverse.rightProjector
        (singularRelativeModularOperator (n := n) s q q0)
        (singularRelativeModularPseudoInverse (n := n) s q q0) ≠ 0 := by
  rw [moorePenroseRightProjector_eq_supportProjector]
  exact supportProjector_ne_zero_of_mem (n := n) s hi

theorem moorePenroseRightProjector_ne_one_of_not_mem
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) {i : Fin n} (hi : i ∉ s) :
    IsMoorePenroseInverse.rightProjector
        (singularRelativeModularOperator (n := n) s q q0)
        (singularRelativeModularPseudoInverse (n := n) s q q0) ≠ (1 : FinMat n) := by
  rw [moorePenroseRightProjector_eq_supportProjector]
  exact supportProjector_ne_one_of_not_mem (n := n) s hi

theorem moorePenroseLeftProjector_ne_zero_of_mem
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) {i : Fin n} (hi : i ∈ s) :
    IsMoorePenroseInverse.leftProjector
        (singularRelativeModularOperator (n := n) s q q0)
        (singularRelativeModularPseudoInverse (n := n) s q q0) ≠ 0 := by
  rw [moorePenroseLeftProjector_eq_supportProjector]
  exact supportProjector_ne_zero_of_mem (n := n) s hi

theorem moorePenroseLeftProjector_ne_one_of_not_mem
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) {i : Fin n} (hi : i ∉ s) :
    IsMoorePenroseInverse.leftProjector
        (singularRelativeModularOperator (n := n) s q q0)
        (singularRelativeModularPseudoInverse (n := n) s q q0) ≠ (1 : FinMat n) := by
  rw [moorePenroseLeftProjector_eq_supportProjector]
  exact supportProjector_ne_one_of_not_mem (n := n) s hi

/-- Pseudo-determinant style volume shadow on the surviving support. -/
@[rep_depth operator]
noncomputable def relativeModularPseudoVolumeShadow
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) : ℝ :=
  s.prod (fun i => relativeDensity (α := Fin n) q q0 i)

@[simp] theorem relativeModularPseudoVolumeShadow_pos
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    0 < relativeModularPseudoVolumeShadow (n := n) s q q0 := by
  unfold relativeModularPseudoVolumeShadow
  refine Finset.prod_pos ?_
  intro i hi
  rw [relativeDensity_eq_exp_relativeLogDensity]
  positivity

@[simp] theorem relativeModularPseudoVolumeShadow_self
    (s : Finset (Fin n)) (q : PositiveRay (Fin n)) :
    relativeModularPseudoVolumeShadow (n := n) s q q = 1 := by
  unfold relativeModularPseudoVolumeShadow
  refine Finset.prod_eq_one ?_
  intro i hi
  rw [relativeDensity_self]

@[simp] theorem relativeModularPseudoVolumeShadow_univ
    (q q0 : PositiveRay (Fin n)) :
    relativeModularPseudoVolumeShadow (n := n) Finset.univ q q0 =
      relativeModularVolumeShadow (n := n) q q0 := by
  unfold relativeModularPseudoVolumeShadow
  rw [relativeModularVolumeShadow_eq_prod_relativeDensity]

/-- Negative logarithmic pseudo-volume readout on the surviving support. -/
@[rep_depth operator]
noncomputable def relativeModularPseudoVolumePotential
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) : ℝ :=
  -Real.log (relativeModularPseudoVolumeShadow (n := n) s q q0)

@[rep_depth thermo, capstone]
theorem log_relativeModularPseudoVolumeShadow_eq_sum_relativeLogDensity
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    Real.log (relativeModularPseudoVolumeShadow (n := n) s q q0)
      = s.sum (fun i => relativeLogDensity (α := Fin n) q q0 i) := by
  rw [relativeModularPseudoVolumeShadow]
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    rw [relativeDensity_eq_exp_relativeLogDensity, Real.log_exp]
  · intro i hi
    rw [relativeDensity_eq_exp_relativeLogDensity]
    positivity

@[rep_depth thermo, capstone]
theorem relativeModularPseudoVolumePotential_eq_sum_relativeModularPotential
    (s : Finset (Fin n)) (q q0 : PositiveRay (Fin n)) :
    relativeModularPseudoVolumePotential (n := n) s q q0
      = s.sum (fun i => relativeModularPotential (α := Fin n) q q0 i) := by
  unfold relativeModularPseudoVolumePotential
  rw [log_relativeModularPseudoVolumeShadow_eq_sum_relativeLogDensity]
  rw [show
      s.sum (fun i => relativeModularPotential (α := Fin n) q q0 i) =
        s.sum (fun i => -relativeLogDensity (α := Fin n) q q0 i) by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [relativeModularPotential_eq_neg_relativeLogDensity]]
  rw [Finset.sum_neg_distrib]

@[simp] theorem relativeModularPseudoVolumePotential_univ
    (q q0 : PositiveRay (Fin n)) :
    relativeModularPseudoVolumePotential (n := n) Finset.univ q q0 =
      relativeModularVolumePotential (n := n) q q0 := by
  unfold relativeModularPseudoVolumePotential relativeModularVolumePotential
  rw [relativeModularPseudoVolumeShadow_univ]

/--
Berezinian-style pseudo-supervolume shadow obtained from plus/minus surviving
supports.
-/
@[rep_depth operator]
noncomputable def relativeModularPseudoBerezinianShadow
    (sPlus sMinus : Finset (Fin n))
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) : ℝ :=
  relativeModularPseudoVolumeShadow (n := n) sPlus qPlus q0Plus
    / relativeModularPseudoVolumeShadow (n := n) sMinus qMinus q0Minus

/-- Compatibility alias for the pseudo-supervolume scalar shadow. -/
@[rep_depth operator]
noncomputable abbrev relativeModularPseudoSupervolumeShadow
    (sPlus sMinus : Finset (Fin n))
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) : ℝ :=
  relativeModularPseudoBerezinianShadow (n := n) sPlus sMinus qPlus q0Plus qMinus q0Minus

@[simp] theorem relativeModularPseudoBerezinianShadow_pos
    (sPlus sMinus : Finset (Fin n))
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    0 < relativeModularPseudoBerezinianShadow (n := n) sPlus sMinus qPlus q0Plus qMinus q0Minus := by
  unfold relativeModularPseudoBerezinianShadow
  exact div_pos
    (relativeModularPseudoVolumeShadow_pos (n := n) sPlus qPlus q0Plus)
    (relativeModularPseudoVolumeShadow_pos (n := n) sMinus qMinus q0Minus)

/-- Negative logarithmic pseudo-Berezinian readout. -/
@[rep_depth operator]
noncomputable def relativeModularPseudoBerezinianPotential
    (sPlus sMinus : Finset (Fin n))
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) : ℝ :=
  -Real.log
    (relativeModularPseudoBerezinianShadow (n := n) sPlus sMinus qPlus q0Plus qMinus q0Minus)

/-- Compatibility alias for the pseudo-supervolume negative-log readout. -/
@[rep_depth operator]
noncomputable abbrev relativeModularPseudoSupervolumePotential
    (sPlus sMinus : Finset (Fin n))
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) : ℝ :=
  relativeModularPseudoBerezinianPotential (n := n) sPlus sMinus qPlus q0Plus qMinus q0Minus

@[rep_depth thermo, capstone]
theorem log_relativeModularPseudoBerezinianShadow_eq_volumeLog_sub_volumeLog
    (sPlus sMinus : Finset (Fin n))
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    Real.log
        (relativeModularPseudoBerezinianShadow (n := n) sPlus sMinus qPlus q0Plus qMinus q0Minus)
      = Real.log (relativeModularPseudoVolumeShadow (n := n) sPlus qPlus q0Plus)
          - Real.log (relativeModularPseudoVolumeShadow (n := n) sMinus qMinus q0Minus) := by
  unfold relativeModularPseudoBerezinianShadow
  rw [Real.log_div
    (ne_of_gt (relativeModularPseudoVolumeShadow_pos (n := n) sPlus qPlus q0Plus))
    (ne_of_gt (relativeModularPseudoVolumeShadow_pos (n := n) sMinus qMinus q0Minus))]

@[rep_depth thermo, capstone]
theorem relativeModularPseudoBerezinianPotential_eq_volumePotential_sub_volumePotential
    (sPlus sMinus : Finset (Fin n))
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    relativeModularPseudoBerezinianPotential (n := n) sPlus sMinus qPlus q0Plus qMinus q0Minus
      = relativeModularPseudoVolumePotential (n := n) sPlus qPlus q0Plus
          - relativeModularPseudoVolumePotential (n := n) sMinus qMinus q0Minus := by
  unfold relativeModularPseudoBerezinianPotential relativeModularPseudoVolumePotential
  rw [log_relativeModularPseudoBerezinianShadow_eq_volumeLog_sub_volumeLog]
  ring

@[rep_depth thermo, capstone]
theorem relativeModularPseudoBerezinianPotential_eq_sum_relativeModularPotential_sub_sum_relativeModularPotential
    (sPlus sMinus : Finset (Fin n))
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    relativeModularPseudoBerezinianPotential (n := n) sPlus sMinus qPlus q0Plus qMinus q0Minus
      = sPlus.sum (fun i => relativeModularPotential (α := Fin n) qPlus q0Plus i)
          - sMinus.sum (fun i => relativeModularPotential (α := Fin n) qMinus q0Minus i) := by
  rw [relativeModularPseudoBerezinianPotential_eq_volumePotential_sub_volumePotential]
  rw [relativeModularPseudoVolumePotential_eq_sum_relativeModularPotential]
  rw [relativeModularPseudoVolumePotential_eq_sum_relativeModularPotential]

@[simp] theorem relativeModularPseudoBerezinianShadow_univ
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    relativeModularPseudoBerezinianShadow
        (n := n) Finset.univ Finset.univ qPlus q0Plus qMinus q0Minus
      = relativeModularBerezinianShadow (n := n) qPlus q0Plus qMinus q0Minus := by
  unfold relativeModularPseudoBerezinianShadow relativeModularBerezinianShadow
  rw [relativeModularPseudoVolumeShadow_univ, relativeModularPseudoVolumeShadow_univ]

@[simp] theorem relativeModularPseudoBerezinianPotential_univ
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    relativeModularPseudoBerezinianPotential
        (n := n) Finset.univ Finset.univ qPlus q0Plus qMinus q0Minus
      = relativeModularBerezinianPotential (n := n) qPlus q0Plus qMinus q0Minus := by
  unfold relativeModularPseudoBerezinianPotential relativeModularBerezinianPotential
  rw [relativeModularPseudoBerezinianShadow_univ]

end Finite

end RelativeModularSingularization
