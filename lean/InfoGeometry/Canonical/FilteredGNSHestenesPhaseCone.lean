/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FilteredGNSGlobalStageRepresentation
import InfoGeometry.Canonical.SouriauOnsagerBKMHestenesAnalyticColimit

/-!
# Native filtered GNS spaces as a Hestenes--Krein cone

This is an instantiation of the existing phase and doubled-cone owners by the
actual GNS stage spaces, their proved isometric transition maps, and their
canonical maps into the completed Hilbert direct limit.  The cone equations
and phase laws are derived from those maps; no new ambient carrier, arbitrary
compatibility field, or scalar replacement is introduced.

The doubled representation of each finite observable intertwines the actual
stage inclusion and preserves the native clock axis.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSHestenesPhaseCone

open FilteredGNS FilteredGNSHilbertColimit FilteredGNSTailRepresentation
open FilteredGNSGlobalStageRepresentation
open InfoGeometry.Krein
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Canonical.HestenesAnalyticity
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.SouriauOnsagerBKMHestenesAnalyticColimit

variable (Stage : ℕ → Type) [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)] [∀ n, StarOrderedRing (Stage n)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)

/-- The actual complex GNS Hilbert direct limit, viewed through its real
phase structure. -/
def gnsPhaseCone : FilteredPhaseCone where
  Stage := GNSStage Stage sys ω
  stageNormedAddCommGroup := fun _ => inferInstance
  stageNormedSpace := fun _ => inferInstance
  phase := fun n => complexModulePhase (GNSStage Stage sys ω n)
  bond := fun n => (filteredGNSMapCLM Stage sys ω (Nat.le_succ n)).restrictScalars ℝ
  bond_phase := fun n =>
    complexLinearMap_isPhaseLinear (filteredGNSMapCLM Stage sys ω (Nat.le_succ n))
  Limit := GNSHilbertColimit Stage sys ω
  limitNormedAddCommGroup := inferInstance
  limitNormedSpace := inferInstance
  limitPhase := complexModulePhase (GNSHilbertColimit Stage sys ω)
  ι := fun n => (gnsStageToHilbertColimit Stage sys ω n).toContinuousLinearMap.restrictScalars ℝ
  ι_phase := fun n =>
    complexLinearMap_isPhaseLinear (gnsStageToHilbertColimit Stage sys ω n).toContinuousLinearMap
  ι_bond := by
    intro n
    apply ContinuousLinearMap.ext
    intro x
    change gnsStageToHilbertColimit Stage sys ω (n + 1)
      (filteredGNSMapCLM Stage sys ω (Nat.le_succ n) x) =
        gnsStageToHilbertColimit Stage sys ω n x
    rw [filteredGNSMapCLM_apply]
    exact gnsStageToHilbertColimit_transition Stage sys ω (Nat.le_succ n) x

/-- The phase carrier retains the proved density of genuine GNS stage images. -/
theorem gnsPhaseCone_dense :
    Dense (⋃ n : ℕ, Set.range ((gnsPhaseCone Stage sys ω).ι n)) := by
  exact dense_iUnion_range_gnsStageToHilbertColimit Stage sys ω

local instance gnsStageRealInnerProduct (n : ℕ) :
    InnerProductSpace ℝ (GNSStage Stage sys ω n) :=
  InnerProductSpace.complexToReal

local instance gnsColimitRealInnerProduct :
    InnerProductSpace ℝ (GNSHilbertColimit Stage sys ω) :=
  InnerProductSpace.complexToReal

/-- Doubling of the native GNS transition after real scalar restriction. -/
def doubledGNSBond (n : ℕ) :
    DoubledSpace (GNSStage Stage sys ω n) →L[ℝ]
      DoubledSpace (GNSStage Stage sys ω (n + 1)) :=
  doubledContinuousLinearMap
    ((filteredGNSMapCLM Stage sys ω (Nat.le_succ n)).restrictScalars ℝ)

/-- Doubling of the native isometric inclusion into the Hilbert colimit. -/
def doubledGNSInclusion (n : ℕ) :
    DoubledSpace (GNSStage Stage sys ω n) →L[ℝ]
      DoubledSpace (GNSHilbertColimit Stage sys ω) :=
  doubledContinuousLinearMap
    ((gnsStageToHilbertColimit Stage sys ω n).toContinuousLinearMap.restrictScalars ℝ)

theorem doubledGNSBond_isHestenes (n : ℕ) :
    IsHestenesHolomorphicDifferential
      (E := GNSStage Stage sys ω n) (F := GNSStage Stage sys ω (n + 1))
      (doubledGNSBond Stage sys ω n) :=
  doubledContinuousLinearMap_isHestenes
    ((filteredGNSMapCLM Stage sys ω (Nat.le_succ n)).restrictScalars ℝ)

theorem doubledGNSInclusion_isHestenes (n : ℕ) :
    IsHestenesHolomorphicDifferential
      (E := GNSStage Stage sys ω n) (F := GNSHilbertColimit Stage sys ω)
      (doubledGNSInclusion Stage sys ω n) :=
  doubledContinuousLinearMap_isHestenes
    ((gnsStageToHilbertColimit Stage sys ω n).toContinuousLinearMap.restrictScalars ℝ)

/-- Native inclusion compatibility, proved before packaging either cone. -/
theorem doubledGNSInclusion_bond (n : ℕ) :
    (doubledGNSInclusion Stage sys ω (n + 1)).comp
        (doubledGNSBond Stage sys ω n) =
      doubledGNSInclusion Stage sys ω n := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext
  · change gnsStageToHilbertColimit Stage sys ω (n + 1)
      (filteredGNSMapCLM Stage sys ω (Nat.le_succ n) (WithLp.fst x)) =
        gnsStageToHilbertColimit Stage sys ω n (WithLp.fst x)
    rw [filteredGNSMapCLM_apply]
    exact gnsStageToHilbertColimit_transition Stage sys ω (Nat.le_succ n) (WithLp.fst x)
  · change gnsStageToHilbertColimit Stage sys ω (n + 1)
      (filteredGNSMapCLM Stage sys ω (Nat.le_succ n) (WithLp.snd x)) =
        gnsStageToHilbertColimit Stage sys ω n (WithLp.snd x)
    rw [filteredGNSMapCLM_apply]
    exact gnsStageToHilbertColimit_transition Stage sys ω (Nat.le_succ n) (WithLp.snd x)

/-- Double the actual GNS maps using the existing canonical real construction.
The concrete maps and their laws are elaborated independently of cone projections. -/
def gnsHestenesKreinCone : HestenesKreinCone where
  Base := GNSStage Stage sys ω
  baseNormedAddCommGroup := fun _ => inferInstance
  baseInnerProductSpace := fun _ => inferInstance
  baseCompleteSpace := fun _ => inferInstance
  LimitBase := GNSHilbertColimit Stage sys ω
  limitNormedAddCommGroup := inferInstance
  limitInnerProductSpace := inferInstance
  limitCompleteSpace := inferInstance
  bond := doubledGNSBond Stage sys ω
  bond_hestenes := doubledGNSBond_isHestenes Stage sys ω
  ι := doubledGNSInclusion Stage sys ω
  ι_hestenes := doubledGNSInclusion_isHestenes Stage sys ω
  ι_bond := doubledGNSInclusion_bond Stage sys ω

@[simp] theorem gnsHestenesInclude_fst (n : ℕ)
    (x : DoubledSpace (GNSStage Stage sys ω n)) :
    WithLp.fst ((gnsHestenesKreinCone Stage sys ω).ι n x) =
      gnsStageToHilbertColimit Stage sys ω n (WithLp.fst x) := rfl

@[simp] theorem gnsHestenesInclude_snd (n : ℕ)
    (x : DoubledSpace (GNSStage Stage sys ω n)) :
    WithLp.snd ((gnsHestenesKreinCone Stage sys ω).ι n x) =
      gnsStageToHilbertColimit Stage sys ω n (WithLp.snd x) := rfl

/-- Actual finite-observable readback through the Hilbert colimit inclusion. -/
theorem gnsStageAction_intertwines (n : ℕ) (a : Stage n)
    (x : GNSStage Stage sys ω n) :
    globalStageRepresentationStarAlgHom Stage sys ω n a
        (gnsStageToHilbertColimit Stage sys ω n x) =
      gnsStageToHilbertColimit Stage sys ω n
        ((ω.state n).functional.gnsStarAlgHom a x) := by
  simpa only [tailGNSOperator, tailObservable, sys.map_id, StarAlgHom.coe_id, id_eq] using
    globalStageRepresentation_stage Stage sys ω a ⟨n, le_refl n⟩ x

def doubledStageAction (n : ℕ) (a : Stage n) :
    DoubledSpace (GNSStage Stage sys ω n) →L[ℝ]
      DoubledSpace (GNSStage Stage sys ω n) :=
  doubledContinuousLinearMap (((ω.state n).functional.gnsStarAlgHom a).restrictScalars ℝ)

def doubledGlobalStageAction (n : ℕ) (a : Stage n) :
    DoubledSpace (GNSHilbertColimit Stage sys ω) →L[ℝ]
      DoubledSpace (GNSHilbertColimit Stage sys ω) :=
  doubledContinuousLinearMap
    ((globalStageRepresentationStarAlgHom Stage sys ω n a).restrictScalars ℝ)

theorem doubledGlobalStageAction_isHestenes (n : ℕ) (a : Stage n) :
    IsHestenesHolomorphicDifferential (doubledGlobalStageAction Stage sys ω n a) :=
  doubledContinuousLinearMap_isHestenes _

/-- Both physical and ghost components use the same actual represented
observable, and intertwining is inherited from the native GNS action. -/
theorem doubledStageAction_intertwines (n : ℕ) (a : Stage n)
    (x : DoubledSpace (GNSStage Stage sys ω n)) :
    doubledGlobalStageAction Stage sys ω n a
        ((gnsHestenesKreinCone Stage sys ω).ι n x) =
      (gnsHestenesKreinCone Stage sys ω).ι n
        (doubledStageAction Stage sys ω n a x) := by
  apply DoubledSpace.ext
  · change globalStageRepresentationStarAlgHom Stage sys ω n a
      (gnsStageToHilbertColimit Stage sys ω n (WithLp.fst x)) =
        gnsStageToHilbertColimit Stage sys ω n
          ((ω.state n).functional.gnsStarAlgHom a (WithLp.fst x))
    exact gnsStageAction_intertwines Stage sys ω n a (WithLp.fst x)
  · change globalStageRepresentationStarAlgHom Stage sys ω n a
      (gnsStageToHilbertColimit Stage sys ω n (WithLp.snd x)) =
        gnsStageToHilbertColimit Stage sys ω n
          ((ω.state n).functional.gnsStarAlgHom a (WithLp.snd x))
    exact gnsStageAction_intertwines Stage sys ω n a (WithLp.snd x)

end CStarStateColimit.Native.FilteredGNSHestenesPhaseCone
