import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentModularFlowHomeomorphTopCat

/-!
# Topological readout of the symbolic-latent modular flow

This file keeps the native flow data from `SymbolicLatentModularFlow` and
exposes it as continuous maps and homeomorphisms.  It does not add a new flow
law or any operator-algebraic structure.
-/

namespace InfoGeometry.Topology.SymbolicLatentModularFlowTopological

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The joint modular action `(\u211d × X) → X` as a topological readout. -/
def topologicalModularFlowAction
    (Φ : SymbolicLatentModularFlow X) : ℝ × X → X :=
  fun p => Φ.act p.1 p.2

@[simp] theorem topologicalModularFlowAction_apply
    (Φ : SymbolicLatentModularFlow X) (p : ℝ × X) :
    topologicalModularFlowAction Φ p = Φ.act p.1 p.2 :=
  rfl

theorem continuous_topologicalModularFlowAction
    (Φ : SymbolicLatentModularFlow X) :
    Continuous (topologicalModularFlowAction Φ) := by
  simpa [topologicalModularFlowAction] using Φ.continuous_act

/-- The time-`t` slice of the modular flow as a topological map. -/
def topologicalModularTimeSlice
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) : X → X :=
  Φ.act t

@[simp] theorem topologicalModularTimeSlice_apply
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) (x : X) :
    topologicalModularTimeSlice Φ t x = Φ.act t x :=
  rfl

theorem continuous_topologicalModularTimeSlice
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) :
    Continuous (topologicalModularTimeSlice Φ t) := by
  simpa [topologicalModularTimeSlice] using
    (Φ.continuous_act.comp (continuous_const.prodMk continuous_id))

/-- The orbit map of a fixed point under the modular flow. -/
def topologicalModularOrbitMap
    (Φ : SymbolicLatentModularFlow X) (x : X) : ℝ → X :=
  fun t => Φ.act t x

@[simp] theorem topologicalModularOrbitMap_apply
    (Φ : SymbolicLatentModularFlow X) (x : X) (t : ℝ) :
    topologicalModularOrbitMap Φ x t = Φ.act t x :=
  rfl

theorem continuous_topologicalModularOrbitMap
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    Continuous (topologicalModularOrbitMap Φ x) := by
  simpa [topologicalModularOrbitMap] using
    Φ.continuous_orbit x

/-- The modular time slice as a homeomorphism, re-exposed in the topology lane. -/
def topologicalModularHomeomorph
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) : X ≃ₜ X :=
  SymbolicLatentModularFlow.actHomeomorph (X := X) Φ t

@[simp] theorem topologicalModularHomeomorph_apply
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) (x : X) :
    topologicalModularHomeomorph Φ t x = Φ.act t x :=
  rfl

theorem topologicalModularHomeomorph_zero
    (Φ : SymbolicLatentModularFlow X) :
    topologicalModularHomeomorph Φ 0 = Homeomorph.refl X := by
  ext x
  simpa [topologicalModularHomeomorph] using
    (SymbolicLatentModularFlow.actHomeomorph_zero_apply (X := X) Φ x)

theorem topologicalModularHomeomorph_comp
    (Φ : SymbolicLatentModularFlow X) (s t : ℝ) :
    (topologicalModularHomeomorph Φ t).trans
      (topologicalModularHomeomorph Φ s) =
        topologicalModularHomeomorph Φ (t + s) := by
  simpa [topologicalModularHomeomorph, add_comm] using
    (SymbolicLatentModularFlow.actHomeomorph_trans (X := X) Φ t s)

end
end InfoGeometry.Topology.SymbolicLatentModularFlowTopological
