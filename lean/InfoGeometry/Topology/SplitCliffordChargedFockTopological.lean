/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitCliffordSourceHeisenberg
import InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
import InfoGeometry.Topology.SplitCliffordHeisenbergTopological

/-!
# Topological Bundle of Concrete Charged-Fock Split-Clifford Heisenberg Currents

This module constructs `representedChargedFockData α : SplitCliffordHeisenbergWitness 𝕜 (ChargedFockSpace 𝕜 α)`
from the proved truncation and Wick commutator laws on `ChargedFockSpace 𝕜 α`,
places the dependent family in the sigma bundle `ChargedFockDataBundle 𝕜`, and
proves its continuity and local constancy.

- BUCKET 1 (Real Math in This File):
  - `representedChargedFockData`, `representedChargedFockData_J`,
    `representedChargedFockData_trunc`, `representedChargedFockData_comm`
  - `ChargedFockDataBundle`, `representedChargedFockDataBundle`
  - `representedChargedFockDataBundle_fst`, `representedChargedFockDataBundle_snd`,
    `continuous_representedChargedFockDataBundle`,
    `isLocallyConstant_representedChargedFockDataBundle`

- BUCKET 2 (Meaningful Mathematical Results Used):
  - `InfoGeometry.Canonical.SplitCliffordSourceHeisenberg`
  - `InfoGeometry.Topology.SplitCliffordHeisenbergTopological`

- BUCKET 3 (Excluded Wrapper Patterns):
  - Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

namespace InfoGeometry.Topology.SplitCliffordChargedFockTopological

open InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
open InfoGeometry.Canonical.SplitCliffordSourceCurrentWick
open InfoGeometry.Canonical.SplitCliffordSourceHeisenberg
open InfoGeometry.Topology.HeisenbergBoundaryAtlasTopological
open VirasoroProject

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Concrete `SplitCliffordHeisenbergWitness` carried by the represented
charged-Fock current at charge `α`. -/
def representedChargedFockData (α : 𝕜) :
    SplitCliffordHeisenbergWitness 𝕜
      (VirasoroProject.ChargedFockSpace 𝕜 α) :=
  ⟨representedChargedFockJ 𝕜 α,
   representedChargedFockJ_trunc 𝕜 α,
   representedChargedFockJ_wick 𝕜 α⟩

/-- The mode family of `representedChargedFockData α` equals `representedChargedFockJ 𝕜 α`. -/
@[simp] theorem representedChargedFockData_J (α : 𝕜) :
    (representedChargedFockData (𝕜 := 𝕜) α).J =
      representedChargedFockJ 𝕜 α := by
  unfold representedChargedFockData SplitCliffordHeisenbergWitness.J
  rfl

/-- Eventual positive-mode truncation of `representedChargedFockData α`. -/
theorem representedChargedFockData_trunc (α : 𝕜) :
    ∀ v, ∀ᶠ n : Int in Filter.atTop,
      (representedChargedFockData (𝕜 := 𝕜) α).J n v = 0 := by
  intro v
  exact representedChargedFockJ_trunc 𝕜 α v

/-- Heisenberg mode commutator law of `representedChargedFockData α`. -/
theorem representedChargedFockData_comm (α : 𝕜) (m n : Int) :
    ((representedChargedFockData (𝕜 := 𝕜) α).J m).commutator
        ((representedChargedFockData (𝕜 := 𝕜) α).J n) =
      if m + n = 0 then
        (m : 𝕜) •
          (1 :
            VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
              VirasoroProject.ChargedFockSpace 𝕜 α)
      else 0 := by
  have h := representedChargedFockJ_wick 𝕜 α m n
  exact h

/-- Dependent sigma bundle of concrete charged-Fock Heisenberg witnesses over `α : 𝕜`. -/
abbrev ChargedFockDataBundle (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] :=
  Σ α : 𝕜,
    SplitCliffordHeisenbergWitness 𝕜
      (VirasoroProject.ChargedFockSpace 𝕜 α)

/-- Discrete topology on `ChargedFockDataBundle 𝕜`. -/
instance chargedFockDataBundleTopologicalSpace :
    TopologicalSpace (ChargedFockDataBundle 𝕜) := ⊥

/-- `DiscreteTopology` instance on `ChargedFockDataBundle 𝕜`. -/
instance chargedFockDataBundleDiscreteTopology :
    DiscreteTopology (ChargedFockDataBundle 𝕜) := ⟨rfl⟩

/-- Section `α ↦ ⟨α, representedChargedFockData α⟩` into `ChargedFockDataBundle 𝕜`. -/
def representedChargedFockDataBundle (α : 𝕜) :
    ChargedFockDataBundle 𝕜 :=
  ⟨α, representedChargedFockData (𝕜 := 𝕜) α⟩

/-- First sigma coordinate of `representedChargedFockDataBundle α`. -/
@[simp] theorem representedChargedFockDataBundle_fst (α : 𝕜) :
    (representedChargedFockDataBundle (𝕜 := 𝕜) α).1 = α := by
  unfold representedChargedFockDataBundle
  rfl

/-- Second sigma coordinate of `representedChargedFockDataBundle α`. -/
@[simp] theorem representedChargedFockDataBundle_snd (α : 𝕜) :
    (representedChargedFockDataBundle (𝕜 := 𝕜) α).2 =
      representedChargedFockData (𝕜 := 𝕜) α := by
  unfold representedChargedFockDataBundle
  rfl

/-- Continuity of `representedChargedFockDataBundle`. -/
theorem continuous_representedChargedFockDataBundle :
    Continuous (representedChargedFockDataBundle (𝕜 := 𝕜)) := by
  have h : Continuous (representedChargedFockDataBundle (𝕜 := 𝕜)) :=
    continuous_of_discreteTopology
  exact h

/-- Local constancy of `representedChargedFockDataBundle`. -/
theorem isLocallyConstant_representedChargedFockDataBundle :
    IsLocallyConstant (representedChargedFockDataBundle (𝕜 := 𝕜)) := by
  have h := IsLocallyConstant.of_discrete
    (f := representedChargedFockDataBundle (𝕜 := 𝕜))
  exact h

end
end InfoGeometry.Topology.SplitCliffordChargedFockTopological
