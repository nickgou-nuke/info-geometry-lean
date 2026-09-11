import InfoGeometry.Canonical.SplitCliffordHeadLift
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitCliffordHeadPhaseFlip
import InfoGeometry.Meta.Architecture
import Mathlib.Tactic.Module

/-!
# InfoGeometry.Canonical.SplitCliffordHeadPolarization

Thin translator layer for the split `Cl(1,1)` head null pair on the Bott tensor
side.

This file does not introduce a new projector framework. It only packages the
two mixed null-mode products already present in the head algebra as the local
`ε`-sector idempotents:

- `u_- u_+ = (1 - ε)/2`,
- `u_+ u_- = (1 + ε)/2`,
- they are complementary idempotents,
- `ε` acts on them with eigenvalues `-1` and `+1`,
- the head `K`-flip swaps the two sectors.
-/

namespace InfoGeometry.Canonical.SplitCliffordHeadPolarization

open InfoGeometry.Canonical.SplitCliffordHeadLift
open InfoGeometry.Canonical.SplitCliffordHeadPhaseFlip
open InfoGeometry.Canonical.SplitCliffordTensorBridge

/-- The `ε = -1` head-sector idempotent cut out by the ordered null pair `u_- u_+`. -/
@[rep_depth krein]
noncomputable def headMinusSectorTensor (n : ℕ) : SplitClNNTensorStep n :=
  headNullMinusTensor n * headNullPlusTensor n

/-- The `ε = +1` head-sector idempotent cut out by the ordered null pair `u_+ u_-`. -/
@[rep_depth krein]
noncomputable def headPlusSectorTensor (n : ℕ) : SplitClNNTensorStep n :=
  headNullPlusTensor n * headNullMinusTensor n

@[rep_depth krein, simp] theorem headMinusSectorTensor_eq_formula (n : ℕ) :
    headMinusSectorTensor n
      = (1 / 2 : ℝ) • ((1 : SplitClNNTensorStep n) - headEpsTensor n) := by
  unfold headMinusSectorTensor
  rw [headNullMinusTensor_eq_formula, headNullPlusTensor_eq_formula]
  simp [sub_eq_add_neg, add_mul, mul_add, smul_add,
    headEpsTensor, headJTensor_sq, headKTensor_sq, headKTensor_mul_headJTensor]
  module

@[rep_depth krein, simp] theorem headPlusSectorTensor_eq_formula (n : ℕ) :
    headPlusSectorTensor n
      = (1 / 2 : ℝ) • ((1 : SplitClNNTensorStep n) + headEpsTensor n) := by
  unfold headPlusSectorTensor
  rw [headNullPlusTensor_eq_formula, headNullMinusTensor_eq_formula]
  simp [sub_eq_add_neg, add_mul, mul_add, smul_add,
    headEpsTensor, headJTensor_sq, headKTensor_sq, headKTensor_mul_headJTensor]
  module

@[rep_depth krein, simp] theorem headMinusSectorTensor_add_headPlusSectorTensor (n : ℕ) :
    headMinusSectorTensor n + headPlusSectorTensor n = 1 := by
  rw [headMinusSectorTensor_eq_formula, headPlusSectorTensor_eq_formula]
  simp [sub_eq_add_neg]
  module

@[rep_depth krein, simp] theorem headMinusSectorTensor_mul_headPlusSectorTensor (n : ℕ) :
    headMinusSectorTensor n * headPlusSectorTensor n = 0 := by
  unfold headMinusSectorTensor headPlusSectorTensor
  calc
    (headNullMinusTensor n * headNullPlusTensor n) * (headNullPlusTensor n * headNullMinusTensor n)
      = ((headNullMinusTensor n * headNullPlusTensor n) * headNullPlusTensor n) * headNullMinusTensor n := by
          simp [mul_assoc]
    _ = (headNullMinusTensor n * (headNullPlusTensor n * headNullPlusTensor n)) * headNullMinusTensor n := by
          simp [mul_assoc]
    _ = 0 := by
          rw [headNullPlusTensor_sq]
          simp

@[rep_depth krein, simp] theorem headPlusSectorTensor_mul_headMinusSectorTensor (n : ℕ) :
    headPlusSectorTensor n * headMinusSectorTensor n = 0 := by
  unfold headMinusSectorTensor headPlusSectorTensor
  calc
    (headNullPlusTensor n * headNullMinusTensor n) * (headNullMinusTensor n * headNullPlusTensor n)
      = ((headNullPlusTensor n * headNullMinusTensor n) * headNullMinusTensor n) * headNullPlusTensor n := by
          simp [mul_assoc]
    _ = (headNullPlusTensor n * (headNullMinusTensor n * headNullMinusTensor n)) * headNullPlusTensor n := by
          simp [mul_assoc]
    _ = 0 := by
          rw [headNullMinusTensor_sq]
          simp

@[rep_depth krein, simp] theorem headMinusSectorTensor_idempotent (n : ℕ) :
    headMinusSectorTensor n * headMinusSectorTensor n = headMinusSectorTensor n := by
  calc
    headMinusSectorTensor n * headMinusSectorTensor n
      = headMinusSectorTensor n * headMinusSectorTensor n + 0 := by simp
    _ = headMinusSectorTensor n * headMinusSectorTensor n
          + headMinusSectorTensor n * headPlusSectorTensor n := by
            rw [headMinusSectorTensor_mul_headPlusSectorTensor]
    _ = headMinusSectorTensor n * (headMinusSectorTensor n + headPlusSectorTensor n) := by
            rw [mul_add]
    _ = headMinusSectorTensor n * 1 := by
            rw [headMinusSectorTensor_add_headPlusSectorTensor]
    _ = headMinusSectorTensor n := by simp

@[rep_depth krein, simp] theorem headPlusSectorTensor_idempotent (n : ℕ) :
    headPlusSectorTensor n * headPlusSectorTensor n = headPlusSectorTensor n := by
  calc
    headPlusSectorTensor n * headPlusSectorTensor n
      = headPlusSectorTensor n * headPlusSectorTensor n + 0 := by simp
    _ = headPlusSectorTensor n * headPlusSectorTensor n
          + headPlusSectorTensor n * headMinusSectorTensor n := by
            rw [headPlusSectorTensor_mul_headMinusSectorTensor]
    _ = headPlusSectorTensor n * (headPlusSectorTensor n + headMinusSectorTensor n) := by
            rw [mul_add]
    _ = headPlusSectorTensor n * 1 := by
            rw [add_comm, headMinusSectorTensor_add_headPlusSectorTensor]
    _ = headPlusSectorTensor n := by simp

@[rep_depth krein, simp] theorem headEpsTensor_mul_headNullMinusTensor (n : ℕ) :
    headEpsTensor n * headNullMinusTensor n = -(headNullMinusTensor n) := by
  rw [headNullMinusTensor_eq_formula]
  simp [mul_add, headEpsTensor_mul_headJTensor, headEpsTensor_mul_headKTensor]

@[rep_depth krein, simp] theorem headNullMinusTensor_mul_headEpsTensor (n : ℕ) :
    headNullMinusTensor n * headEpsTensor n = headNullMinusTensor n := by
  rw [headNullMinusTensor_eq_formula]
  simp [add_mul, headJTensor_mul_headEpsTensor, headKTensor_mul_headEpsTensor, add_comm]

@[rep_depth krein, simp] theorem headEpsTensor_mul_headNullPlusTensor (n : ℕ) :
    headEpsTensor n * headNullPlusTensor n = headNullPlusTensor n := by
  rw [headNullPlusTensor_eq_formula]
  simp [sub_eq_add_neg, mul_add, headEpsTensor_mul_headJTensor, headEpsTensor_mul_headKTensor, add_comm]

@[rep_depth krein, simp] theorem headNullPlusTensor_mul_headEpsTensor (n : ℕ) :
    headNullPlusTensor n * headEpsTensor n = -(headNullPlusTensor n) := by
  rw [headNullPlusTensor_eq_formula]
  simp [sub_eq_add_neg, add_mul, headJTensor_mul_headEpsTensor, headKTensor_mul_headEpsTensor]

@[rep_depth krein, simp] theorem headEpsTensor_mul_headMinusSectorTensor (n : ℕ) :
    headEpsTensor n * headMinusSectorTensor n = -(headMinusSectorTensor n) := by
  calc
    headEpsTensor n * headMinusSectorTensor n
      = (headEpsTensor n * headNullMinusTensor n) * headNullPlusTensor n := by
          simp [headMinusSectorTensor, mul_assoc]
    _ = (-(headNullMinusTensor n)) * headNullPlusTensor n := by
          rw [headEpsTensor_mul_headNullMinusTensor]
    _ = -(headNullMinusTensor n * headNullPlusTensor n) := by
          simp only [neg_mul]
    _ = -(headMinusSectorTensor n) := by rfl

@[rep_depth krein, simp] theorem headMinusSectorTensor_mul_headEpsTensor (n : ℕ) :
    headMinusSectorTensor n * headEpsTensor n = -(headMinusSectorTensor n) := by
  calc
    headMinusSectorTensor n * headEpsTensor n
      = headNullMinusTensor n * (headNullPlusTensor n * headEpsTensor n) := by
          simp [headMinusSectorTensor, mul_assoc]
    _ = headNullMinusTensor n * (-(headNullPlusTensor n)) := by
          rw [headNullPlusTensor_mul_headEpsTensor]
    _ = -(headNullMinusTensor n * headNullPlusTensor n) := by simp
    _ = -(headMinusSectorTensor n) := by rfl

@[rep_depth krein, simp] theorem headEpsTensor_mul_headPlusSectorTensor (n : ℕ) :
    headEpsTensor n * headPlusSectorTensor n = headPlusSectorTensor n := by
  calc
    headEpsTensor n * headPlusSectorTensor n
      = (headEpsTensor n * headNullPlusTensor n) * headNullMinusTensor n := by
          simp [headPlusSectorTensor, mul_assoc]
    _ = headNullPlusTensor n * headNullMinusTensor n := by
          rw [headEpsTensor_mul_headNullPlusTensor]
    _ = headPlusSectorTensor n := by rfl

@[rep_depth krein, simp] theorem headPlusSectorTensor_mul_headEpsTensor (n : ℕ) :
    headPlusSectorTensor n * headEpsTensor n = headPlusSectorTensor n := by
  calc
    headPlusSectorTensor n * headEpsTensor n
      = headNullPlusTensor n * (headNullMinusTensor n * headEpsTensor n) := by
          simp [headPlusSectorTensor, mul_assoc]
    _ = headNullPlusTensor n * headNullMinusTensor n := by
          rw [headNullMinusTensor_mul_headEpsTensor]
    _ = headPlusSectorTensor n := by rfl

@[rep_depth krein, simp] theorem headKFlipTensor_apply_headMinusSectorTensor (n : ℕ) :
    headKFlipTensor n (headMinusSectorTensor n) = headPlusSectorTensor n := by
  unfold headMinusSectorTensor headPlusSectorTensor
  rw [map_mul, headKFlipTensor_apply_headNullMinusTensor, headKFlipTensor_apply_headNullPlusTensor]

@[rep_depth krein, simp] theorem headKFlipTensor_apply_headPlusSectorTensor (n : ℕ) :
    headKFlipTensor n (headPlusSectorTensor n) = headMinusSectorTensor n := by
  unfold headMinusSectorTensor headPlusSectorTensor
  rw [map_mul, headKFlipTensor_apply_headNullPlusTensor, headKFlipTensor_apply_headNullMinusTensor]

/--
Particle-hole symmetry resolves the mixed chiral-sector anomaly at the split
head: the `K`-flip exchanges the two `ε` sectors, while both mixed products
vanish.
-/
@[rep_depth krein]
theorem headKFlipTensor_particleHole_resolves_mixedSectorAnomaly (n : ℕ) :
    headKFlipTensor n (headMinusSectorTensor n) = headPlusSectorTensor n ∧
      headKFlipTensor n (headPlusSectorTensor n) = headMinusSectorTensor n ∧
        headMinusSectorTensor n * headPlusSectorTensor n = 0 ∧
          headPlusSectorTensor n * headMinusSectorTensor n = 0 := by
  exact ⟨headKFlipTensor_apply_headMinusSectorTensor n,
    headKFlipTensor_apply_headPlusSectorTensor n,
    headMinusSectorTensor_mul_headPlusSectorTensor n,
    headPlusSectorTensor_mul_headMinusSectorTensor n⟩

end InfoGeometry.Canonical.SplitCliffordHeadPolarization
