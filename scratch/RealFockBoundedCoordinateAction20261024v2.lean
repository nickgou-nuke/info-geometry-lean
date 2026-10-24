/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.RealFockCoordinateTransport
import InfoGeometry.Clifford.RealFockHilbertCompletion
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentationLinearityWave16

/-! # Bounded coordinate actions on the existing algebraic Fock colimit

Pending dependency: native RealFockCoordinateTransport. This bundles the actual
splitCliffordFockAction and proves bounds by common-stage readback. No new action,
colimit, assumed compatible family, or completed operator is constructed.
-/
noncomputable section
namespace InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace
attribute [local instance] fockInfinityInnerProductCore fockInfinityPreInnerProductCore
  fockInfinityNormedAddCommGroup fockInfinityInnerProductSpace fockInfinityNormedSpace
  fockInfinityUniformContinuousConstSMul

/-- Use exactly the accepted norm's uniform structure on the root quotient. -/
local instance fockInfinityMetricUniformSpace : UniformSpace FockInfinity :=
  fockInfinityNormedAddCommGroup.toMetricSpace.toUniformSpace

/-- Pin CLM signatures to the metric topology, rather than the quotient fallback. -/
local instance fockInfinityMetricTopology : TopologicalSpace FockInfinity :=
  fockInfinityNormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace

local notation "ofC" => DirectLimit.Algebra.of SplitClNNAlg
  (fun m n h => splitCliffordMap m n h)

/-- Bundle the existing colimit action using its already proved right-linearity. -/
def splitCliffordFockActionLinearMap (a : SplitCliffordInfinity) :
    FockInfinity →ₗ[ℝ] FockInfinity where
  toFun := splitCliffordFockAction a
  map_add' := splitCliffordFockAction_add_right a
  map_smul' r ψ := splitCliffordFockAction_smul_right r a ψ

/-- The linear bundle is exactly the original action on every algebraic spinor. -/
theorem splitCliffordFockActionLinearMap_apply (a : SplitCliffordInfinity)
    (ψ : FockInfinity) :
    splitCliffordFockActionLinearMap a ψ = splitCliffordFockAction a ψ := rfl

/-- Arbitrary mixed-stage inputs are evaluated at their common upper stage. -/
theorem splitCliffordFockAction_mixed_stage (m n : ℕ)
    (a : SplitClNNAlg m) (ψ : FockStage n) :
    splitCliffordFockAction (ofC m a) (fockToInfinity n ψ) =
      fockToInfinity (max m n)
        (towerSpinorRep (max m n)
          (splitCliffordMap m (max m n) (le_max_left m n) a)
          (fockStageMap n (max m n) (le_max_right m n) ψ)) := by
  have ha : ofC (max m n) (splitCliffordMap m (max m n) (le_max_left m n) a) =
      ofC m a := DirectLimit.Algebra.of_f
        (f := fun i j h => splitCliffordMap i j h) (le_max_left m n) a
  have hψ : fockToInfinity (max m n)
      (fockStageMap n (max m n) (le_max_right m n) ψ) = fockToInfinity n ψ :=
    fockToInfinity_transition (le_max_right m n) ψ
  calc
    _ = splitCliffordFockAction
        (ofC (max m n) (splitCliffordMap m (max m n) (le_max_left m n) a))
        (fockToInfinity (max m n) (fockStageMap n (max m n) (le_max_right m n) ψ)) :=
      congrArg₂ splitCliffordFockAction ha.symm hψ.symm
    _ = _ := splitCliffordFockAction_of (max m n) _ _

/-- The actual fixed creation element is contractive on every algebraic spinor. -/
theorem splitCliffordFockAction_creation_norm_le (m : ℕ) (i : Fin m)
    (ψ : FockInfinity) :
    ‖splitCliffordFockAction (ofC m (fockCreationGenerator m i)) ψ‖ ≤ ‖ψ‖ := by
  obtain ⟨n, x, hx⟩ := DirectLimit.exists_eq_mk
    (f := fun j k h => fockStageMap j k h) ψ
  have hx' : ψ = fockToInfinity n x := hx
  rw [hx', splitCliffordFockAction_mixed_stage]
  simp only [fockToInfinity_norm]
  calc
    _ ≤ ‖fockStageMap n (max m n) (le_max_right m n) x‖ :=
      transported_creation_norm_le m (max m n) (le_max_left m n) i _
    _ = ‖x‖ := fockStageMap_norm n (max m n) (le_max_right m n) x

/-- The actual fixed contraction element has the same derived global bound. -/
theorem splitCliffordFockAction_contraction_norm_le (m : ℕ) (i : Fin m)
    (ψ : FockInfinity) :
    ‖splitCliffordFockAction (ofC m (fockContractionGenerator m i)) ψ‖ ≤ ‖ψ‖ := by
  obtain ⟨n, x, hx⟩ := DirectLimit.exists_eq_mk
    (f := fun j k h => fockStageMap j k h) ψ
  have hx' : ψ = fockToInfinity n x := hx
  rw [hx', splitCliffordFockAction_mixed_stage]
  simp only [fockToInfinity_norm]
  calc
    _ ≤ ‖fockStageMap n (max m n) (le_max_right m n) x‖ :=
      transported_contraction_norm_le m (max m n) (le_max_left m n) i _
    _ = ‖x‖ := fockStageMap_norm n (max m n) (le_max_right m n) x

/-- The existing creation action, made continuous by its proved bound. -/
def fockInfinityCreationCLM (m : ℕ) (i : Fin m) : FockInfinity →L[ℝ] FockInfinity :=
  (splitCliffordFockActionLinearMap (ofC m (fockCreationGenerator m i))).mkContinuous 1
    (fun ψ => by simpa only [one_mul, splitCliffordFockActionLinearMap_apply] using
      splitCliffordFockAction_creation_norm_le m i ψ)

/-- The existing contraction action, made continuous by its proved bound. -/
def fockInfinityContractionCLM (m : ℕ) (i : Fin m) : FockInfinity →L[ℝ] FockInfinity :=
  (splitCliffordFockActionLinearMap (ofC m (fockContractionGenerator m i))).mkContinuous 1
    (fun ψ => by simpa only [one_mul, splitCliffordFockActionLinearMap_apply] using
      splitCliffordFockAction_contraction_norm_le m i ψ)

/-- Creation CLM application is definitionally the actual colimit action. -/
theorem fockInfinityCreationCLM_apply (m : ℕ) (i : Fin m) (ψ : FockInfinity) :
    fockInfinityCreationCLM m i ψ =
      splitCliffordFockAction (ofC m (fockCreationGenerator m i)) ψ := rfl

/-- Contraction CLM application is definitionally the actual colimit action. -/
theorem fockInfinityContractionCLM_apply (m : ℕ) (i : Fin m) (ψ : FockInfinity) :
    fockInfinityContractionCLM m i ψ =
      splitCliffordFockAction (ofC m (fockContractionGenerator m i)) ψ := rfl

/-- The creation operator norm follows from the bound used in its construction. -/
theorem fockInfinityCreationCLM_norm_le (m : ℕ) (i : Fin m) :
    ‖fockInfinityCreationCLM m i‖ ≤ 1 := by
  unfold fockInfinityCreationCLM
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The contraction operator norm follows from its proved pointwise bound. -/
theorem fockInfinityContractionCLM_norm_le (m : ℕ) (i : Fin m) :
    ‖fockInfinityContractionCLM m i‖ ≤ 1 := by
  unfold fockInfinityContractionCLM
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
