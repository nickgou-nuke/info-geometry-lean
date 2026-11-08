/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry
import InfoGeometry.Clifford.Cl11TensorTowerLimit

/-!
# Exact CE connections along the native matrix tensor stages

An operator `P` defines an exact CE one-form on the full matrix derivation
lane. We evaluate its curvature on inner derivations, prove that the actual
stage embedding transports this curvature, and identify its two images in
the existing algebraic direct limit. No connection on the limit is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorStageExactConnection

open InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-- The actual tensor embedding intertwines the action of inner derivations. -/
theorem stageEmbed_inner_action (n : ℕ) (X T : Stage n) :
    (matrixInnerLieHom ℝ (Idx (n + 1)) (stageEmbed n X) :
      Module.End ℝ (Stage (n + 1))) (stageEmbed n T) =
    stageEmbed n ((matrixInnerLieHom ℝ (Idx n) X : Module.End ℝ (Stage n)) T) := by
  simp only [matrixInnerLieHom_apply, map_sub, map_mul]

/-- The exact one-form `d P` is compatible with the native tensor embedding
when evaluated on the corresponding inner derivations. -/
theorem stageEmbed_exactOneForm (n : ℕ) (P X : Stage n) :
    exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx (n + 1))) (stageEmbed n P)
        (matrixInnerLieHom ℝ (Idx (n + 1)) (stageEmbed n X)) =
      stageEmbed n (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx n)) P
        (matrixInnerLieHom ℝ (Idx n) X)) := by
  exact stageEmbed_inner_action n X P

/-- The covariant Leibniz derivation associated with `d P` also intertwines
with the tensor embedding on the represented inner directions. -/
theorem stageEmbed_exactCovariantDerivative (n : ℕ) (P X T : Stage n) :
    covariantDerivative (matrixDerivationsLane ℝ (Idx (n + 1)))
        (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx (n + 1))) (stageEmbed n P))
        (matrixInnerLieHom ℝ (Idx (n + 1)) (stageEmbed n X)) (stageEmbed n T) =
      stageEmbed n (covariantDerivative (matrixDerivationsLane ℝ (Idx n))
        (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx n)) P)
        (matrixInnerLieHom ℝ (Idx n) X) T) := by
  change (stageEmbed n X * stageEmbed n T - stageEmbed n T * stageEmbed n X) +
    (stageEmbed n X * stageEmbed n P - stageEmbed n P * stageEmbed n X) * stageEmbed n T -
    stageEmbed n T * (stageEmbed n X * stageEmbed n P - stageEmbed n P * stageEmbed n X) =
    stageEmbed n ((X * T - T * X) + (X * P - P * X) * T - T * (X * P - P * X))
  simp only [map_sub, map_add, map_mul]

/-- Every iterated tensor-tower bonding map transports the exact CE
covariant derivative on represented inner directions. -/
theorem bondMap_exactCovariantDerivative {n m : ℕ} (hnm : n ≤ m)
    (P X T : Stage n) :
    covariantDerivative (matrixDerivationsLane ℝ (Idx m))
        (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx m))
          (bondMap stageBond n m hnm P))
        (matrixInnerLieHom ℝ (Idx m) (bondMap stageBond n m hnm X))
        (bondMap stageBond n m hnm T) =
      bondMap stageBond n m hnm
        (covariantDerivative (matrixDerivationsLane ℝ (Idx n))
          (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx n)) P)
          (matrixInnerLieHom ℝ (Idx n) X) T) := by
  refine Nat.le_induction
    (m := n)
    (P := fun m hnm =>
      covariantDerivative (matrixDerivationsLane ℝ (Idx m))
          (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx m))
            (bondMap stageBond n m hnm P))
          (matrixInnerLieHom ℝ (Idx m) (bondMap stageBond n m hnm X))
          (bondMap stageBond n m hnm T) =
        bondMap stageBond n m hnm
          (covariantDerivative (matrixDerivationsLane ℝ (Idx n))
            (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx n)) P)
            (matrixInnerLieHom ℝ (Idx n) X) T))
    ?base ?succ m hnm
  · simp [bondMap_refl]
  · intro k hnk ih
    rw [bondMap_succ stageBond n k hnk]
    simp only [RingHom.comp_apply]
    rw [← ih]
    exact stageEmbed_exactCovariantDerivative k
      (bondMap stageBond n k hnk P)
      (bondMap stageBond n k hnk X)
      (bondMap stageBond n k hnk T)

/-- Curvature of the exact one-form `d P`, evaluated on inner directions. -/
def exactCutCurvature (n : ℕ) (P X Y : Stage n) : Stage n :=
  connectionCurvature (matrixDerivationsLane ℝ (Idx n))
    (exteriorDerivativeZero (matrixDerivationsLane ℝ (Idx n)) P)
    (matrixInnerLieHom ℝ (Idx n) X) (matrixInnerLieHom ℝ (Idx n) Y)

/-- The curvature remains a genuinely ordered matrix commutator. -/
theorem exactCutCurvature_apply (n : ℕ) (P X Y : Stage n) :
    exactCutCurvature n P X Y =
      (X * P - P * X) * (Y * P - P * Y) -
        (Y * P - P * Y) * (X * P - P * X) := by
  unfold exactCutCurvature
  rw [matrixExactOneForm_curvature]
  rfl

/-- The native one-step tensor embedding transports this concrete CE
curvature on the corresponding inner directions. -/
theorem stageEmbed_exactCutCurvature (n : ℕ) (P X Y : Stage n) :
    stageEmbed n (exactCutCurvature n P X Y) =
      exactCutCurvature (n + 1) (stageEmbed n P) (stageEmbed n X) (stageEmbed n Y) := by
  rw [exactCutCurvature_apply, exactCutCurvature_apply]
  simp only [map_sub, map_mul]

/-- Every iterated bonding map transports the finite-stage exact CE
curvature, not just its one-step representative. -/
theorem bondMap_exactCutCurvature {n m : ℕ} (hnm : n ≤ m)
    (P X Y : Stage n) :
    bondMap stageBond n m hnm (exactCutCurvature n P X Y) =
      exactCutCurvature m
        (bondMap stageBond n m hnm P)
        (bondMap stageBond n m hnm X)
        (bondMap stageBond n m hnm Y) := by
  refine Nat.le_induction
    (m := n)
    (P := fun m hnm =>
      bondMap stageBond n m hnm (exactCutCurvature n P X Y) =
        exactCutCurvature m
          (bondMap stageBond n m hnm P)
          (bondMap stageBond n m hnm X)
          (bondMap stageBond n m hnm Y))
    ?base ?succ m hnm
  · simp [bondMap_refl]
  · intro k hnk ih
    rw [bondMap_succ stageBond n k hnk]
    simp only [RingHom.comp_apply]
    rw [ih]
    exact stageEmbed_exactCutCurvature k
      (bondMap stageBond n k hnk P)
      (bondMap stageBond n k hnk X)
      (bondMap stageBond n k hnk Y)

/-- The two stage representatives define the same element of the existing
direct limit. This is an algebraic descent statement. -/
theorem ofStage_exactCutCurvature_bond (n : ℕ) (P X Y : Stage n) :
    ofStage (n + 1)
        (exactCutCurvature (n + 1) (stageEmbed n P) (stageEmbed n X) (stageEmbed n Y)) =
      ofStage n (exactCutCurvature n P X Y) := by
  rw [← stageEmbed_exactCutCurvature]
  exact ofStage_apply_bond n _

end InfoGeometry.Canonical.TensorStageExactConnection

end
