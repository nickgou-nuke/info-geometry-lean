import Lean
import InfoGeometry.Canonical.BlackBookIntegration
import InfoGeometry.Canonical.GenerativeInferenceCore
import InfoGeometry.Canonical.CognitiveArchetype
import InfoGeometry.Canonical.CognitiveShadow
import InfoGeometry.Canonical.ProofCausalityBridge
import InfoGeometry.Causal.ProofCone
import InfoGeometry.SelfReference.ShadowCone
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.HiveSelfModel

Canonical self-model scaffold for the repo-native cognitive architecture.

This file packages the five pillars discussed in the architecture notes as
data, not as proof authority:

* logos: theorem inventory;
* sensing: proof-causality cone readout;
* reflex: generative-inference state;
* memory: lineage/manifests;
* conscience/shadow: vacuity and debt markers;
* dream: conjectural seed list.

No metaphysical or psychological claim is made here. This is a repository
state schema with explicit proof-causality readouts.
-/

noncomputable section

namespace InfoGeometry.Canonical.HiveSelfModel

open InfoGeometry.Canonical.GenerativeInferenceCore
open InfoGeometry.Canonical.ProofCausalityBridge
open InfoGeometry.Causal.Algebra

section Core

variable {n : Nat}
variable {E α : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]
variable [CausalGraph α]

abbrev ShadowBoundary (α : Type*) := InfoGeometry.SelfReference.ShadowCone α

/--
Repo-native self-model state.

The structure is intentionally shallow: it records the current cognitive
surface of the system without pretending to be an ontology.
-/
structure CognitiveSelfModel (n : Nat) (E α : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [CausalGraph α] where
  /-- Conscious theorem inventory. -/
  logosTheorems : Array Lean.Name

  /-- Proof-causality focus node. -/
  focus : α

  /-- Generative-inference reflex core. -/
  inference : GenerativeInferenceDatum n E

  /-- Memory/lineage manifests. -/
  memoryManifests : Array String

  /-- Black-book source-to-lineage packets. -/
  blackBooks : Array InfoGeometry.Canonical.BlackBookIntegration.BlackBookPacket

  /-- Open debt and shadow content. -/
  shadowDebt : Array String

  /-- Incidence-aware shadow cones. -/
  shadowCones : Array (ShadowBoundary α)

  /-- Rejection or vacuity patterns. -/
  rejectionPatterns : Array String

  /-- Dream or conjecture seeds. -/
  dreamSeeds : Array String

  /-- Recognized archetype names / motifs. -/
  archetypes : Array InfoGeometry.Canonical.CognitiveArchetype.ArchetypeTemplate

  /-- Recognized shadow modes / critic-lane refusals. -/
  shadows : Array InfoGeometry.Canonical.CognitiveShadow.ShadowTemplate

  /-- Current proof-causality operator analogue. -/
  causalProjection : InfoGeometry.Causal.ProofCone.CausalMat2

namespace Model

variable {n : Nat} {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [CausalGraph α]
variable (M : CognitiveSelfModel n E α)

/-- The number of recorded theorems. -/
def logosCount : Nat :=
  Array.size (α := Lean.Name) (CognitiveSelfModel.logosTheorems M)

/-- The number of open shadow debts. -/
def shadowDebtCount : Nat :=
  Array.size (α := String) (CognitiveSelfModel.shadowDebt M)

/-- The number of incidence-aware shadow cones. -/
def shadowBoundaryCount : Nat :=
  Array.size
    (α := ShadowBoundary α)
    (CognitiveSelfModel.shadowCones M)

/-- The number of lineage manifests. -/
def memoryCount : Nat :=
  Array.size (α := String) (CognitiveSelfModel.memoryManifests M)

/-- The number of black-book packets. -/
def blackBookCount : Nat :=
  Array.size
    (α := InfoGeometry.Canonical.BlackBookIntegration.BlackBookPacket)
    (CognitiveSelfModel.blackBooks M)

/-- The number of rejection patterns. -/
def rejectionPatternCount : Nat :=
  Array.size (α := String) (CognitiveSelfModel.rejectionPatterns M)

/-- The number of conjectural dream seeds. -/
def dreamSeedCount : Nat :=
  Array.size (α := String) (CognitiveSelfModel.dreamSeeds M)

/-- The number of recognized archetypes. -/
def archetypeCount : Nat :=
  Array.size
    (α := InfoGeometry.Canonical.CognitiveArchetype.ArchetypeTemplate)
    (CognitiveSelfModel.archetypes M)

/-- The number of recognized shadow modes. -/
def shadowPatternCount : Nat :=
  Array.size
    (α := InfoGeometry.Canonical.CognitiveShadow.ShadowTemplate)
    (CognitiveSelfModel.shadows M)

/-- Forward cone sensed from the current focus node. -/
def sensedForwardCone : Set α :=
  CausalGraph.forwardCone (CognitiveSelfModel.focus M)

/-- Backward cone sensed from the current focus node. -/
def sensedBackwardCone : Set α :=
  CausalGraph.backwardCone (CognitiveSelfModel.focus M)

/-- The current focus belongs to its own sensed forward cone. -/
theorem focus_mem_sensedForwardCone :
    CognitiveSelfModel.focus M ∈ sensedForwardCone M := by
  simpa [sensedForwardCone] using
    forwardCone_self (a := CognitiveSelfModel.focus M)

/-- The current focus belongs to its own sensed backward cone. -/
theorem focus_mem_sensedBackwardCone :
    CognitiveSelfModel.focus M ∈ sensedBackwardCone M := by
  simpa [sensedBackwardCone] using
    backwardCone_self (a := CognitiveSelfModel.focus M)

/-- The sensed cones intersect only at the focus node. -/
theorem sensedCone_intersection_eq_singleton :
    sensedForwardCone M ∩ sensedBackwardCone M =
      {CognitiveSelfModel.focus M} := by
  simpa [sensedForwardCone, sensedBackwardCone] using
    cones_intersect_self_iff_antisymm (a := CognitiveSelfModel.focus M)

/-- No two-way causal loop survives away from the focus node. -/
theorem no_two_way_loop_except_focus
    (a : α)
    (hf : a ∈ sensedForwardCone M)
    (hb : a ∈ sensedBackwardCone M) :
    a = CognitiveSelfModel.focus M := by
  simpa [sensedForwardCone, sensedBackwardCone] using
    (acyclic_no_two_way_except_self (a := CognitiveSelfModel.focus M) (b := a) hf hb).symm

/-- A compact readout of the current self-model. -/
structure Summary where
  logosCount : Nat
  shadowDebtCount : Nat
  shadowConeCount : Nat
  memoryCount : Nat
  blackBookCount : Nat
  rejectionPatternCount : Nat
  dreamSeedCount : Nat
  archetypeCount : Nat
  shadowPatternCount : Nat

/-- The current summary of the self-model. -/
def summary : Summary :=
  { logosCount := logosCount M
    shadowDebtCount := shadowDebtCount M
    shadowConeCount := shadowBoundaryCount M
    memoryCount := memoryCount M
    blackBookCount := blackBookCount M
    rejectionPatternCount := rejectionPatternCount M
    dreamSeedCount := dreamSeedCount M
    archetypeCount := archetypeCount M
    shadowPatternCount := shadowPatternCount M }

end Model

end Core

end InfoGeometry.Canonical.HiveSelfModel
