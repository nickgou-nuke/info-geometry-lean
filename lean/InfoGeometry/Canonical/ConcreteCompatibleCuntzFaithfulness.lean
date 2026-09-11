import InfoGeometry.Canonical.ConcreteCompatibleCuntzRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixFaithfulness

/-!
# Faithfulness of the concrete compatible Cuntz cone

The finite coefficient probe is transported through the real-to-complex
matrix equivalence and the concrete compatible stage maps.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConcreteCompatibleCuntzFaithfulness

open InfoGeometry.Canonical.ConcreteCompatibleCuntzRepresentation
open InfoGeometry.Canonical.CuntzBoundaryMatrixStageBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixFaithfulness
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11InfiniteCarrier
open InfoGeometry.Algebra.CliffordBitWordEquivalence

theorem complexify_star (n : ℕ) (A : UHFStage n) :
    complexify n (star A) = star (complexify n A) := by
  ext i j
  simp [complexify, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

theorem clStageEquiv_star (n : ℕ) (A : ClStage n) :
    clStageEquiv n (star A) = star (clStageEquiv n A) := by
  ext i j
  simp [clStageEquiv_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Matrix.reindex]

theorem stageMap_star (n : ℕ) (A : ClStage n) :
    stageMap n (star A) = star (stageMap n A) := by
  change boundaryRep n (complexify n (clStageEquiv n (star A))) = _
  rw [clStageEquiv_star, complexify_star, map_star]
  rfl

theorem complexify_injective (n : ℕ) :
    Function.Injective (complexify n) := by
  intro A B h
  ext i j
  apply Complex.ofReal_injective
  simpa [complexify] using congrArg Complex.re (congrFun (congrFun h i) j)

theorem boundaryRep_injective (n : ℕ) :
    Function.Injective (boundaryRep n) := by
  intro A B h
  change bitWordMatrixLinearRepresentation n A =
    bitWordMatrixLinearRepresentation n B at h
  exact bitWordMatrixLinearRepresentation_injective n h

theorem stageMap_injective (n : ℕ) :
    Function.Injective (stageMap n) := by
  intro A B h
  apply (clStageEquiv n).injective
  apply complexify_injective n
  apply boundaryRep_injective n
  exact h

theorem representation_injective_of_stage_maps
    (hstage : ∀ n : ℕ, Function.Injective (stageMap n)) :
    Function.Injective colimitRepresentation := by
  intro x y hxy
  induction x, y using DirectLimit.induction₂ with
  | _ n A B =>
      have hstageAB : stageMap n A = stageMap n B := by
        simpa [colimitRepresentation_stage] using hxy
      have hAB : A = B := (hstage n) hstageAB
      subst B
      rfl

theorem colimitRepresentation_injective :
    Function.Injective colimitRepresentation := by
  exact representation_injective_of_stage_maps stageMap_injective

end InfoGeometry.Canonical.ConcreteCompatibleCuntzFaithfulness
