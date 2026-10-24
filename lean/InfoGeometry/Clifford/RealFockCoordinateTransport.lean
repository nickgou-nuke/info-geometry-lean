/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
import InfoGeometry.Clifford.FockTailExteriorBasis
import InfoGeometry.Clifford.FiniteRealFockNormBounds

/-! # Fixed coordinate modes in the native split Clifford/Fock tower

Old modes move by Fin.succ at each zero-head inclusion. Generator identities
hold in the actual split Clifford algebra, so their action readbacks and norm
bounds hold on every later-stage spinor, not merely on an earlier-stage image.
No new action, colimit, or completed operator is introduced.
-/
noncomputable section

namespace InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

/-- Extending a coordinate covector by zero shifts its index past the new head. -/
theorem dualTailMap_proj (n : ℕ) (i : Fin n) :
    dualTailMap n (LinearMap.proj i : Module.Dual ℝ (Vector n)) =
      (LinearMap.proj i.succ : Module.Dual ℝ (Vector (n+1))) := by
  apply LinearMap.ext
  intro x
  rfl

end InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

namespace InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Algebra.SuperGrassmannianClifford
attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

/-- The actual fixed mode shifts once for every inserted head coordinate. -/
def fockModeShift (m n : ℕ) (h : m ≤ n) (i : Fin m) : Fin n :=
  Nat.leRecOn h (C := fun n => Fin n) (fun {_k} j => j.succ) i

@[simp] theorem fockModeShift_refl (m : ℕ) (i : Fin m) :
    fockModeShift m m le_rfl i = i := by
  simpa [fockModeShift] using
    (Nat.leRecOn_self (C := fun n => Fin n) (next := fun {_k} j => j.succ) (x := i))

theorem fockModeShift_succ (m n : ℕ) (h : m ≤ n) (i : Fin m) :
    fockModeShift m (n+1) (h.trans (Nat.le_succ n)) i =
      (fockModeShift m n h i).succ := by
  unfold fockModeShift
  rw [Nat.leRecOn_trans h (Nat.le_succ n), Nat.leRecOn_succ']

/-- The creation coordinate as an element of the existing split Clifford algebra. -/
def fockCreationGenerator (n : ℕ) (i : Fin n) : SplitClNNAlg n :=
  CliffordAlgebra.ι (TowerForm n)
    (neutralToSplit n ((Pi.basisFun ℝ (Fin n)) i, 0))

/-- The contraction coordinate as an element of the same split Clifford algebra. -/
def fockContractionGenerator (n : ℕ) (i : Fin n) : SplitClNNAlg n :=
  CliffordAlgebra.ι (TowerForm n)
    (neutralToSplit n (0, (LinearMap.proj i : Module.Dual ℝ (Vector n))))

/-- The actual algebra step sends a neutral generator to its native tail generator. -/
theorem splitCliffordStep_neutral_generator (n : ℕ) (X : Neutral n) :
    splitCliffordStep n (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n X)) =
      CliffordAlgebra.ι (TowerForm (n+1))
        (neutralToSplit (n+1) (neutralTailMap n X)) := by
  rw [splitCliffordStep_eq_splitStageCliffordMap, splitStageCliffordMap,
    CliffordAlgebra.map_apply_ι, splitStageIsometry_apply, ← neutralToSplit_tail]

/-- Creation coordinates are shifted by exactly one under the actual algebra step. -/
theorem fockCreationGenerator_step (n : ℕ) (i : Fin n) :
    splitCliffordStep n (fockCreationGenerator n i) =
      fockCreationGenerator (n+1) i.succ := by
  unfold fockCreationGenerator
  rw [splitCliffordStep_neutral_generator]
  have htail : neutralTailMap n ((Pi.basisFun ℝ (Fin n)) i, 0) =
      ((Pi.basisFun ℝ (Fin (n+1))) i.succ, 0) := by
    apply Prod.ext
    · exact vectorHeadZero_basisFun n i
    · change dualTailMap n 0 = 0
      exact map_zero _
  rw [htail]

/-- Contraction coordinates follow the same successor shift. -/
theorem fockContractionGenerator_step (n : ℕ) (i : Fin n) :
    splitCliffordStep n (fockContractionGenerator n i) =
      fockContractionGenerator (n+1) i.succ := by
  unfold fockContractionGenerator
  rw [splitCliffordStep_neutral_generator]
  have htail : neutralTailMap n (0, (LinearMap.proj i : Module.Dual ℝ (Vector n))) =
      (0, (LinearMap.proj i.succ : Module.Dual ℝ (Vector (n+1)))) := by
    apply Prod.ext
    · change vectorHeadZero n 0 = 0
      exact map_zero _
    · exact dualTailMap_proj n i
  rw [htail]

/-- All-index creation transport is an equality in the native Clifford algebra. -/
theorem splitCliffordMap_creation (m n : ℕ) (h : m ≤ n) (i : Fin m) :
    splitCliffordMap m n h (fockCreationGenerator m i) =
      fockCreationGenerator n (fockModeShift m n h i) := by
  induction n, h using Nat.le_induction with
  | base => simp only [splitCliffordMap_refl, AlgHom.id_apply, fockModeShift_refl]
  | succ n h ih =>
      rw [splitCliffordMap_succ m n h]
      change splitCliffordStep n (splitCliffordMap m n h (fockCreationGenerator m i)) = _
      rw [ih, fockCreationGenerator_step, fockModeShift_succ]

/-- All-index contraction transport is an equality in that same algebra. -/
theorem splitCliffordMap_contraction (m n : ℕ) (h : m ≤ n) (i : Fin m) :
    splitCliffordMap m n h (fockContractionGenerator m i) =
      fockContractionGenerator n (fockModeShift m n h i) := by
  induction n, h using Nat.le_induction with
  | base => simp only [splitCliffordMap_refl, AlgHom.id_apply, fockModeShift_refl]
  | succ n h ih =>
      rw [splitCliffordMap_succ m n h]
      change splitCliffordStep n (splitCliffordMap m n h (fockContractionGenerator m i)) = _
      rw [ih, fockContractionGenerator_step, fockModeShift_succ]

/-- Native Chevalley readback of one finite creation coordinate. -/
theorem towerSpinorRep_creation (n : ℕ) (i : Fin n) (ψ : FockStage n) :
    towerSpinorRep n (fockCreationGenerator n i) ψ = fockExtActionCLM n i ψ := by
  unfold fockCreationGenerator
  rw [towerSpinorRep_generator, LinearEquiv.symm_apply_apply]
  change InfoGeometry.Clifford.spinorAction ((Pi.basisFun ℝ (Fin n)) i, 0) ψ =
    InfoGeometry.Clifford.extAction ((Pi.basisFun ℝ (Fin n)) i) ψ
  simp [InfoGeometry.Clifford.spinorAction, InfoGeometry.Clifford.intAction]

/-- Native Chevalley readback of one finite contraction coordinate. -/
theorem towerSpinorRep_contraction (n : ℕ) (i : Fin n) (ψ : FockStage n) :
    towerSpinorRep n (fockContractionGenerator n i) ψ = fockIntActionCLM n i ψ := by
  unfold fockContractionGenerator
  rw [towerSpinorRep_generator, LinearEquiv.symm_apply_apply]
  change InfoGeometry.Clifford.spinorAction
    (0, (LinearMap.proj i : Module.Dual ℝ (Vector n))) ψ =
      InfoGeometry.Clifford.intAction (LinearMap.proj i) ψ
  simp [InfoGeometry.Clifford.spinorAction, InfoGeometry.Clifford.extAction]

/-- Creation readback holds on every later-stage spinor, with no image hypothesis. -/
theorem towerSpinorRep_transported_creation (m n : ℕ) (h : m ≤ n)
    (i : Fin m) (ψ : FockStage n) :
    towerSpinorRep n (splitCliffordMap m n h (fockCreationGenerator m i)) ψ =
      fockExtActionCLM n (fockModeShift m n h i) ψ := by
  rw [splitCliffordMap_creation, towerSpinorRep_creation]

/-- Contraction readback also holds on every later-stage spinor. -/
theorem towerSpinorRep_transported_contraction (m n : ℕ) (h : m ≤ n)
    (i : Fin m) (ψ : FockStage n) :
    towerSpinorRep n (splitCliffordMap m n h (fockContractionGenerator m i)) ψ =
      fockIntActionCLM n (fockModeShift m n h i) ψ := by
  rw [splitCliffordMap_contraction, towerSpinorRep_contraction]

/-- The fixed creation mode is contractive on all later stages. -/
theorem transported_creation_norm_le (m n : ℕ) (h : m ≤ n)
    (i : Fin m) (ψ : FockStage n) :
    ‖towerSpinorRep n (splitCliffordMap m n h (fockCreationGenerator m i)) ψ‖ ≤ ‖ψ‖ := by
  rw [towerSpinorRep_transported_creation, fockExtActionCLM_apply]
  exact fock_extAction_norm_le n (fockModeShift m n h i) ψ

/-- The fixed contraction mode has the same genuine uniform bound. -/
theorem transported_contraction_norm_le (m n : ℕ) (h : m ≤ n)
    (i : Fin m) (ψ : FockStage n) :
    ‖towerSpinorRep n (splitCliffordMap m n h (fockContractionGenerator m i)) ψ‖ ≤ ‖ψ‖ := by
  rw [towerSpinorRep_transported_contraction, fockIntActionCLM_apply]
  exact fock_intAction_norm_le n (fockModeShift m n h i) ψ

/-- Existing representation naturality gives creation intertwining on old spinors. -/
theorem fockStageMap_creation (m n : ℕ) (h : m ≤ n) (i : Fin m) (ψ : FockStage m) :
    fockStageMap m n h (fockExtActionCLM m i ψ) =
      fockExtActionCLM n (fockModeShift m n h i) (fockStageMap m n h ψ) := by
  have he := towerSpinorRep_stageMap m n h (fockCreationGenerator m i) ψ
  rw [towerSpinorRep_creation, towerSpinorRep_transported_creation] at he
  exact he

/-- The same existing representation naturality gives contraction intertwining. -/
theorem fockStageMap_contraction (m n : ℕ) (h : m ≤ n) (i : Fin m) (ψ : FockStage m) :
    fockStageMap m n h (fockIntActionCLM m i ψ) =
      fockIntActionCLM n (fockModeShift m n h i) (fockStageMap m n h ψ) := by
  have he := towerSpinorRep_stageMap m n h (fockContractionGenerator m i) ψ
  rw [towerSpinorRep_contraction, towerSpinorRep_transported_contraction] at he
  exact he

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
