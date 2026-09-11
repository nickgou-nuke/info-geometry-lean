import InfoGeometry.Canonical.SplitCliffordHeadPolarization
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.SplitCliffordHeadProjectors

Public projector-facing names for the head `ε`-sector algebra on the Bott tensor
side.

The owned algebra lives in `SplitCliffordHeadPolarization`. This file is a thin
renaming layer that exposes the same surface with projector terminology.
-/

namespace InfoGeometry.Canonical.SplitCliffordHeadProjectors

open InfoGeometry.Canonical.SplitCliffordHeadLift
open InfoGeometry.Canonical.SplitCliffordHeadPhaseFlip
open InfoGeometry.Canonical.SplitCliffordHeadPolarization
open InfoGeometry.Canonical.SplitCliffordTensorBridge

/-- The head `ε = -1` projector on the Bott tensor side. -/
@[rep_depth krein]
noncomputable abbrev headEpsMinusProjectorTensor (n : ℕ) : SplitClNNTensorStep n :=
  headMinusSectorTensor n

/-- The head `ε = +1` projector on the Bott tensor side. -/
@[rep_depth krein]
noncomputable abbrev headEpsPlusProjectorTensor (n : ℕ) : SplitClNNTensorStep n :=
  headPlusSectorTensor n

@[rep_depth krein, simp] theorem headEpsMinusProjectorTensor_eq_formula (n : ℕ) :
    headEpsMinusProjectorTensor n
      = (1 / 2 : ℝ) • ((1 : SplitClNNTensorStep n) - headEpsTensor n) :=
  headMinusSectorTensor_eq_formula n

@[rep_depth krein, simp] theorem headEpsPlusProjectorTensor_eq_formula (n : ℕ) :
    headEpsPlusProjectorTensor n
      = (1 / 2 : ℝ) • ((1 : SplitClNNTensorStep n) + headEpsTensor n) :=
  headPlusSectorTensor_eq_formula n

@[rep_depth krein, simp] theorem headEpsProjectorTensor_sum (n : ℕ) :
    headEpsMinusProjectorTensor n + headEpsPlusProjectorTensor n
      = (1 : SplitClNNTensorStep n) :=
  headMinusSectorTensor_add_headPlusSectorTensor n

@[rep_depth krein, simp] theorem headEpsMinusProjectorTensor_mul_headEpsPlusProjectorTensor
    (n : ℕ) :
    headEpsMinusProjectorTensor n * headEpsPlusProjectorTensor n = 0 :=
  headMinusSectorTensor_mul_headPlusSectorTensor n

@[rep_depth krein, simp] theorem headEpsPlusProjectorTensor_mul_headEpsMinusProjectorTensor
    (n : ℕ) :
    headEpsPlusProjectorTensor n * headEpsMinusProjectorTensor n = 0 :=
  headPlusSectorTensor_mul_headMinusSectorTensor n

@[rep_depth krein, simp] theorem headEpsMinusProjectorTensor_idempotent (n : ℕ) :
    headEpsMinusProjectorTensor n * headEpsMinusProjectorTensor n
      = headEpsMinusProjectorTensor n :=
  headMinusSectorTensor_idempotent n

@[rep_depth krein, simp] theorem headEpsPlusProjectorTensor_idempotent (n : ℕ) :
    headEpsPlusProjectorTensor n * headEpsPlusProjectorTensor n
      = headEpsPlusProjectorTensor n :=
  headPlusSectorTensor_idempotent n

@[rep_depth krein, simp] theorem headEpsTensor_mul_headEpsMinusProjectorTensor (n : ℕ) :
    headEpsTensor n * headEpsMinusProjectorTensor n = -headEpsMinusProjectorTensor n :=
  headEpsTensor_mul_headMinusSectorTensor n

@[rep_depth krein, simp] theorem headEpsMinusProjectorTensor_mul_headEpsTensor (n : ℕ) :
    headEpsMinusProjectorTensor n * headEpsTensor n = -headEpsMinusProjectorTensor n :=
  headMinusSectorTensor_mul_headEpsTensor n

@[rep_depth krein, simp] theorem headEpsTensor_mul_headEpsPlusProjectorTensor (n : ℕ) :
    headEpsTensor n * headEpsPlusProjectorTensor n = headEpsPlusProjectorTensor n :=
  headEpsTensor_mul_headPlusSectorTensor n

@[rep_depth krein, simp] theorem headEpsPlusProjectorTensor_mul_headEpsTensor (n : ℕ) :
    headEpsPlusProjectorTensor n * headEpsTensor n = headEpsPlusProjectorTensor n :=
  headPlusSectorTensor_mul_headEpsTensor n

@[rep_depth krein, simp] theorem headKFlipTensor_apply_headEpsMinusProjectorTensor
    (n : ℕ) :
    headKFlipTensor n (headEpsMinusProjectorTensor n) = headEpsPlusProjectorTensor n :=
  headKFlipTensor_apply_headMinusSectorTensor n

@[rep_depth krein, simp] theorem headKFlipTensor_apply_headEpsPlusProjectorTensor
    (n : ℕ) :
    headKFlipTensor n (headEpsPlusProjectorTensor n) = headEpsMinusProjectorTensor n :=
  headKFlipTensor_apply_headPlusSectorTensor n

@[rep_depth krein, simp] theorem headKFlipTensor_apply_headEpsProjectorTensor_sum
    (n : ℕ) :
    headKFlipTensor n (headEpsMinusProjectorTensor n + headEpsPlusProjectorTensor n)
      = headEpsMinusProjectorTensor n + headEpsPlusProjectorTensor n := by
  rw [map_add, headKFlipTensor_apply_headEpsMinusProjectorTensor,
    headKFlipTensor_apply_headEpsPlusProjectorTensor, add_comm]

@[rep_depth krein, simp] theorem headKFlipTensor_apply_headEpsProjectorTensor_diff
    (n : ℕ) :
    headKFlipTensor n (headEpsMinusProjectorTensor n - headEpsPlusProjectorTensor n)
      = -(headEpsMinusProjectorTensor n - headEpsPlusProjectorTensor n) := by
  rw [sub_eq_add_neg, map_add, map_neg,
    headKFlipTensor_apply_headEpsMinusProjectorTensor,
    headKFlipTensor_apply_headEpsPlusProjectorTensor]
  abel_nf

/--
Projector-facing particle-hole cancellation law at the split head: the `K`-flip
exchanges the two `ε` projectors, and both mixed-sector products vanish.
-/
@[rep_depth krein]
theorem headKFlipTensor_particleHole_resolves_projectorAnomaly (n : ℕ) :
    headKFlipTensor n (headEpsMinusProjectorTensor n) = headEpsPlusProjectorTensor n ∧
      headKFlipTensor n (headEpsPlusProjectorTensor n) = headEpsMinusProjectorTensor n ∧
        headEpsMinusProjectorTensor n * headEpsPlusProjectorTensor n = 0 ∧
          headEpsPlusProjectorTensor n * headEpsMinusProjectorTensor n = 0 := by
  exact ⟨headKFlipTensor_apply_headEpsMinusProjectorTensor n,
    headKFlipTensor_apply_headEpsPlusProjectorTensor n,
    headEpsMinusProjectorTensor_mul_headEpsPlusProjectorTensor n,
    headEpsPlusProjectorTensor_mul_headEpsMinusProjectorTensor n⟩

end InfoGeometry.Canonical.SplitCliffordHeadProjectors
