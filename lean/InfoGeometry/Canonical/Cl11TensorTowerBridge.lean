import InfoGeometry.Clifford.Cl11TensorTowerIteration
import InfoGeometry.Canonical.FiniteDeterminantTower
import InfoGeometry.Canonical.NormalizedLogDetTower

set_option autoImplicit false

/-!
# InfoGeometry.Canonical.Cl11TensorTowerBridge

Finite tensor-tower readouts for the real `Cl(1,1)` matrix tower.

This file packages only the finite recurrence laws that are already owned by
`Cl11TensorTower`, `Cl11TensorTowerIteration`, and the finite determinant
normalization lemmas.

It does **not** prove a hyperfinite `II₁` factor theorem, a Type `III`
classification theorem, or any general Jones-subfactor completeness claim.
-/

namespace InfoGeometry.Canonical.Cl11TensorTowerBridge

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerIteration
open InfoGeometry.Clifford.Cl11TensorTowerLimit

/-- One-step determinant squaring along the `Cl(1,1)` tensor tower. -/
theorem det_stageEmbed (n : ℕ) (A : MatStage n) :
    Matrix.det (stageEmbed n A) = Matrix.det A ^ (2 : ℕ) := by
  simpa [stageEmbed_apply] using matStageEmbed_det (n := n) A

/-- One-step normalized trace stability along the `Cl(1,1)` tensor tower. -/
theorem normalizedTrace_stageEmbed (n : ℕ) (A : MatStage n) :
    normalizedTrace (n + 1) (stageEmbed n A) = normalizedTrace n A := by
  simpa [stageEmbed_apply] using normalizedTrace_matStageEmbed (n := n) A

/-- One-step normalized log-absolute-determinant stability along the tower. -/
theorem normalizedLogAbsDet_stageEmbed (n : ℕ) (A : MatStage n) :
    normalizedLogAbsDet (n + 1) (stageEmbed n A) = normalizedLogAbsDet n A := by
  simpa [stageEmbed_apply] using normalizedLogAbsDet_matStageEmbed (n := n) A

/-- Determinant squaring along a compatible stage sequence. -/
theorem det_square_along_compatible_sequence
    (F : ∀ n : ℕ, MatStage n)
    (hF : ∀ n : ℕ, stageEmbed n (F n) = F (n + 1)) :
    ∀ n : ℕ, Matrix.det (F (n + 1)) = Matrix.det (F n) ^ 2 := by
  intro n
  rw [← hF n]
  exact det_stageEmbed n (F n)

/-- Normalized trace is constant along a compatible stage sequence. -/
theorem normalizedTrace_constant_along_compatible_sequence
    (F : ∀ n : ℕ, MatStage n)
    (hF : ∀ n : ℕ, stageEmbed n (F n) = F (n + 1)) :
    ∀ n : ℕ, normalizedTrace n (F n) = normalizedTrace 0 (F 0) := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        normalizedTrace (n + 1) (F (n + 1))
            = normalizedTrace (n + 1) (stageEmbed n (F n)) := by
                rw [← hF n]
        _ = normalizedTrace n (F n) := normalizedTrace_stageEmbed n (F n)
        _ = normalizedTrace 0 (F 0) := ih

/-- Normalized log-absolute-determinant is constant along a compatible stage sequence. -/
theorem normalizedLogAbsDet_constant_along_compatible_sequence
    (F : ∀ n : ℕ, MatStage n)
    (hF : ∀ n : ℕ, stageEmbed n (F n) = F (n + 1)) :
    ∀ n : ℕ, normalizedLogAbsDet n (F n) = normalizedLogAbsDet 0 (F 0) := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        normalizedLogAbsDet (n + 1) (F (n + 1))
            = normalizedLogAbsDet (n + 1) (stageEmbed n (F n)) := by
                rw [← hF n]
        _ = normalizedLogAbsDet n (F n) := normalizedLogAbsDet_stageEmbed n (F n)
        _ = normalizedLogAbsDet 0 (F 0) := ih

/-- The direct-limit image of a compatible sequence is constant. -/
theorem stageSequence_constant_in_limit
    (F : ∀ n : ℕ, MatStage n)
    (hF : ∀ n : ℕ, stageEmbed n (F n) = F (n + 1)) :
    ∀ n : ℕ, ofStage n (F n) = ofStage 0 (F 0) := by
  exact finite_sequence_constant_in_limit F hF

/-- Scalar binary-tower normalized log-determinant stabilization. -/
theorem scalar_normalizedLogDet_binaryTower_step
    (N : ℕ)
    {detA : ℝ}
    (hdetA : 0 < detA) :
    (1 / ((2 : ℝ) ^ (N + 1))) * Real.log (detA ^ 2)
      =
    (1 / ((2 : ℝ) ^ N)) * Real.log detA := by
  exact NormalizedLogDetTower.normalizedLogDet_binaryTower_step N hdetA

/-- Scalar determinant-squaring normalization in the finite tower. -/
theorem scalar_normalizedLogDet_tensorId2_step
    (N : ℕ)
    {detA detTensor : ℝ}
    (hdetA : 0 < detA)
    (hdetTensor : detTensor = detA ^ 2) :
    (1 / ((2 : ℝ) ^ (N + 1))) * Real.log detTensor
      =
    (1 / ((2 : ℝ) ^ N)) * Real.log detA := by
  exact NormalizedLogDetTower.normalizedLogDet_tensorId2_step N hdetA hdetTensor

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
[det_stageEmbed, normalizedTrace_stageEmbed,
 normalizedLogAbsDet_stageEmbed,
 det_square_along_compatible_sequence,
 normalizedTrace_constant_along_compatible_sequence,
 normalizedLogAbsDet_constant_along_compatible_sequence,
 stageSequence_constant_in_limit,
 scalar_normalizedLogDet_binaryTower_step,
 scalar_normalizedLogDet_tensorId2_step]

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
[The recurrence property `hF` is the explicit finite compatibility property.]

#### BUCKET 3: OPEN CLOSURE DEBT
[No hyperfinite `II₁` factor theorem, no Type `III` classification theorem,
and no general Jones-subfactor theorem are proved here.]
-/

end InfoGeometry.Canonical.Cl11TensorTowerBridge
