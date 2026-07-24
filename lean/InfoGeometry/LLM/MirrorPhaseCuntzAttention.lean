import Mathlib
import InfoGeometry.Canonical.CantorKMSCylinderState

/-!
# Mirror Phase: finite Cuntz attention row

This module starts Epoch 4 with a deliberately small theorem surface: a
two-branch attention row is identified with the depth-one dyadic KMS cylinder
weights of the Cuntz/Cantor boundary.

It does not claim anything about a trained neural network, transformer
interpretability, alignment, or global routing dynamics.  It proves only the
finite row-normalization and dyadic readback facts Lean can own directly.

#### BUCKET 1: CLOSED FINITE THEOREMS

* `twoBranchAttentionWeight_nonneg`
* `twoBranchAttentionWeight_sum_one`
* `twoBranchAttentionWeight_eq_depthOne_cylinderKMSWeight`
* `twoBranchAttentionRow_exactness_defect_zero`
* `leftBranchAttentionWeight_eq_cylinderKMSWeight`
* `rightBranchAttentionWeight_eq_cylinderKMSWeight`
* `mirrorAttentionMatrix_row_sum_one`
* `mirrorAttentionMatrix_entry_nonneg`
* `mirrorAttentionMatrix_idempotent`
* `applyMirrorAttention_eq_average`
* `mirrorAttention_kills_branchAnomaly`
* `applyMirrorAttention_idempotent`
* `applyMirrorAttention_preserves_total`
* `branchAnomaly_eq_zero_iff`
* `applyMirrorAttention_eq_self_iff_branchAnomaly_eq_zero`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

* Relating real transformer attention matrices to this exact dyadic row.
* Proving that learned routing obeys Cuntz exactness.
* Extending from one two-branch row to multi-token, multi-head, trained-model
  attention dynamics.
-/

noncomputable section

namespace InfoGeometry.LLM.MirrorPhaseCuntzAttention

open scoped BigOperators
open InfoGeometry.Canonical.CantorCuntzBasis
open InfoGeometry.Canonical.CantorKMSCylinderState

/-- The exact two-branch attention row used for the first Mirror Phase corridor. -/
def twoBranchAttentionWeight (_i : Fin 2) : ℝ :=
  1 / 2

/-- Index `0` is the left/false Cuntz branch, index `1` is the right/true branch. -/
def depthOneBranchWord (i : Fin 2) : BinaryWord :=
  if i = 0 then [false] else [true]

/-- Every weight in the exact two-branch attention row is nonnegative. -/
theorem twoBranchAttentionWeight_nonneg (i : Fin 2) :
    0 ≤ twoBranchAttentionWeight i := by
  norm_num [twoBranchAttentionWeight]

/-- The exact two-branch attention row is normalized. -/
theorem twoBranchAttentionWeight_sum_one :
    (∑ i : Fin 2, twoBranchAttentionWeight i) = 1 := by
  simp [twoBranchAttentionWeight]

/--
The exact two-branch attention row is precisely the depth-one dyadic KMS
cylinder row.
-/
theorem twoBranchAttentionWeight_eq_depthOne_cylinderKMSWeight (i : Fin 2) :
    twoBranchAttentionWeight i = cylinderKMSWeight (depthOneBranchWord i) := by
  fin_cases i <;> norm_num [twoBranchAttentionWeight, depthOneBranchWord, cylinderKMSWeight]

/-- The row-normalization defect of the exact two-branch attention row vanishes. -/
theorem twoBranchAttentionRow_exactness_defect_zero :
    (∑ i : Fin 2, twoBranchAttentionWeight i) - 1 = 0 := by
  rw [twoBranchAttentionWeight_sum_one]
  ring

/-- The left attention branch is the left depth-one Cuntz/KMS cylinder weight. -/
theorem leftBranchAttentionWeight_eq_cylinderKMSWeight :
    twoBranchAttentionWeight 0 = cylinderKMSWeight [false] := by
  simpa [depthOneBranchWord] using
    twoBranchAttentionWeight_eq_depthOne_cylinderKMSWeight 0

/-- The right attention branch is the right depth-one Cuntz/KMS cylinder weight. -/
theorem rightBranchAttentionWeight_eq_cylinderKMSWeight :
    twoBranchAttentionWeight 1 = cylinderKMSWeight [true] := by
  simpa [depthOneBranchWord] using
    twoBranchAttentionWeight_eq_depthOne_cylinderKMSWeight 1

/-! ## Finite attention operator and branch-anomaly cancellation -/

/-- A two-branch real value vector. -/
abbrev TwoBranchVector := Fin 2 → ℝ

/--
The exact Mirror Phase attention operator: every query averages the two Cuntz
branches with dyadic weights.
-/
def mirrorAttentionMatrix : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => (1 / 2 : ℝ)

/-- Applying the exact Mirror Phase attention operator to a two-branch vector. -/
def applyMirrorAttention (v : TwoBranchVector) : TwoBranchVector :=
  fun i => ∑ j : Fin 2, mirrorAttentionMatrix i j * v j

/-- The branch anomaly/imbalance readout: right value minus left value. -/
def branchAnomaly (v : TwoBranchVector) : ℝ :=
  v 1 - v 0

/-- Every row of the exact Mirror Phase attention matrix is stochastic. -/
theorem mirrorAttentionMatrix_row_sum_one (i : Fin 2) :
    (∑ j : Fin 2, mirrorAttentionMatrix i j) = 1 := by
  simp [mirrorAttentionMatrix]

/-- Every entry of the exact Mirror Phase attention matrix is nonnegative. -/
theorem mirrorAttentionMatrix_entry_nonneg (i j : Fin 2) :
    0 ≤ mirrorAttentionMatrix i j := by
  norm_num [mirrorAttentionMatrix]

/--
The exact Mirror Phase attention matrix is an idempotent projection.  This is a
finite matrix identity, not a claim about trained transformer dynamics.
-/
theorem mirrorAttentionMatrix_idempotent :
    mirrorAttentionMatrix * mirrorAttentionMatrix = mirrorAttentionMatrix := by
  ext i j
  simp [Matrix.mul_apply, mirrorAttentionMatrix]

/-- Applying exact Mirror Phase attention replaces a vector by its branch average. -/
theorem applyMirrorAttention_eq_average (v : TwoBranchVector) (i : Fin 2) :
    applyMirrorAttention v i = (v 0 + v 1) / 2 := by
  fin_cases i <;>
    simp [applyMirrorAttention, mirrorAttentionMatrix, Fin.sum_univ_two] <;>
    ring_nf

/-- Exact Mirror Phase attention kills the finite branch-anomaly readout. -/
theorem mirrorAttention_kills_branchAnomaly (v : TwoBranchVector) :
    branchAnomaly (applyMirrorAttention v) = 0 := by
  simp [branchAnomaly, applyMirrorAttention_eq_average]

/-- Applying exact Mirror Phase attention twice is the same as applying it once. -/
theorem applyMirrorAttention_idempotent (v : TwoBranchVector) :
    applyMirrorAttention (applyMirrorAttention v) = applyMirrorAttention v := by
  ext i
  rw [applyMirrorAttention_eq_average (applyMirrorAttention v) i]
  rw [applyMirrorAttention_eq_average v 0,
    applyMirrorAttention_eq_average v 1,
    applyMirrorAttention_eq_average v i]
  ring

/-- Exact Mirror Phase attention preserves total branch mass. -/
theorem applyMirrorAttention_preserves_total (v : TwoBranchVector) :
    (∑ i : Fin 2, applyMirrorAttention v i) = ∑ i : Fin 2, v i := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  rw [applyMirrorAttention_eq_average v 0, applyMirrorAttention_eq_average v 1]
  ring

/-- Zero branch anomaly is exactly equality of the two branch values. -/
theorem branchAnomaly_eq_zero_iff (v : TwoBranchVector) :
    branchAnomaly v = 0 ↔ v 0 = v 1 := by
  unfold branchAnomaly
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- The exact Mirror Phase attention fixes exactly branch-balanced vectors. -/
theorem applyMirrorAttention_eq_self_iff_branchAnomaly_eq_zero (v : TwoBranchVector) :
    applyMirrorAttention v = v ↔ branchAnomaly v = 0 := by
  constructor
  · intro h
    rw [← h]
    exact mirrorAttention_kills_branchAnomaly v
  · intro h
    ext i
    have hv : v 0 = v 1 := (branchAnomaly_eq_zero_iff v).1 h
    fin_cases i
    · rw [applyMirrorAttention_eq_average]
      have h0 : (v 0 + v 1) / 2 = v 0 := by linarith
      simpa using h0
    · rw [applyMirrorAttention_eq_average]
      have h1 : (v 0 + v 1) / 2 = v 1 := by linarith
      simpa using h1

end InfoGeometry.LLM.MirrorPhaseCuntzAttention

end noncomputable section
