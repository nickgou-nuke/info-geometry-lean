/-
InfoGeometry/OperatorAlgebra/TopologicalSnap.lean

Topological obstruction to flattening.

An admissible modular, Bogoliubov, or symmetry-preserving flow cannot relax a
nontrivial topological/anomaly sector into a flat sector when the obstruction
invariant is conserved and every flat state has trivial obstruction.
-/

import Mathlib

noncomputable section

namespace TopologicalSnap

/-! ## 1. Conserved obstruction flows -/

/--
A symmetry-preserving flow with a conserved obstruction invariant.

`Flat` is the flat/trivial sector.

`invariant` is the topological, anomaly, residue, or index readout.

`flow` is the admissible relaxation, modular, or Bogoliubov flow.
-/
structure ConservedObstructionFlow
    (State Charge : Type*) [Zero Charge] where
  /-- Topological/anomaly obstruction readout. -/
  invariant : State → Charge

  /-- Flat/trivial sector. -/
  Flat : Set State

  /-- Admissible flow. -/
  flow : ℝ → State → State

  /-- Every flat state has trivial obstruction. -/
  flat_invariant_zero :
    ∀ x : State, x ∈ Flat → invariant x = 0

  /-- The flow preserves the obstruction invariant. -/
  flow_preserves_invariant :
    ∀ (t : ℝ) (x : State), invariant (flow t x) = invariant x

namespace ConservedObstructionFlow

variable {State Charge : Type*} [Zero Charge]
variable (F : ConservedObstructionFlow State Charge)

/--
A state is obstruction-trivial when its invariant vanishes.
-/
def IsTrivial
    (x : State) : Prop :=
  F.invariant x = 0

/--
A state is obstruction-nontrivial when its invariant is nonzero.
-/
def IsNontrivial
    (x : State) : Prop :=
  F.invariant x ≠ 0

/--
Flat states are obstruction-trivial.
-/
theorem trivial_of_flat
    {x : State}
    (hx : x ∈ F.Flat) :
    F.IsTrivial x :=
  F.flat_invariant_zero x hx

/--
A nontrivial state is not flat.
-/
theorem nontrivial_not_flat
    {x : State}
    (hx : F.IsNontrivial x) :
    x ∉ F.Flat := by
  intro hflat
  exact hx (F.trivial_of_flat hflat)

/--
The flow preserves obstruction-triviality.
-/
theorem flow_preserves_trivial
    {x : State}
    (hx : F.IsTrivial x)
    (t : ℝ) :
    F.IsTrivial (F.flow t x) := by
  dsimp [IsTrivial] at hx ⊢
  rw [F.flow_preserves_invariant t x]
  exact hx

/--
The flow preserves obstruction-nontriviality.
-/
theorem flow_preserves_nontrivial
    {x : State}
    (hx : F.IsNontrivial x)
    (t : ℝ) :
    F.IsNontrivial (F.flow t x) := by
  dsimp [IsNontrivial] at hx ⊢
  intro hzero
  have hpres :
      F.invariant (F.flow t x) = F.invariant x :=
    F.flow_preserves_invariant t x
  exact hx (by
    rw [← hpres]
    exact hzero)

/--
If a target sector has invariant `q`, then any state that flows into that
sector must already have invariant `q`.
-/
theorem invariant_eq_of_flows_to_sector
    {Target : Set State}
    {q : Charge}
    (hTarget : ∀ y : State, y ∈ Target → F.invariant y = q)
    {x : State}
    {t : ℝ}
    (hmem : F.flow t x ∈ Target) :
    F.invariant x = q := by
  have hq :
      F.invariant (F.flow t x) = q :=
    hTarget (F.flow t x) hmem
  have hpres :
      F.invariant (F.flow t x) = F.invariant x :=
    F.flow_preserves_invariant t x
  rw [← hpres]
  exact hq

/--
If a target sector has trivial obstruction, then a nontrivial state cannot flow
into it.
-/
theorem nontrivial_cannot_flow_to_trivial_sector
    {Target : Set State}
    (hTarget : ∀ y : State, y ∈ Target → F.invariant y = 0)
    {x : State}
    (hx : F.invariant x ≠ 0)
    (t : ℝ) :
    F.flow t x ∉ Target := by
  intro hmem
  have hzero :
      F.invariant x = 0 :=
    F.invariant_eq_of_flows_to_sector hTarget hmem
  exact hx hzero

/--
A state with nonzero obstruction cannot flow into the flat sector.
-/
theorem nontrivial_cannot_flow_to_flat
    {x : State}
    (hx : F.invariant x ≠ 0)
    (t : ℝ) :
    F.flow t x ∉ F.Flat := by
  intro hflat
  have hzero :
      F.invariant (F.flow t x) = 0 :=
    F.flat_invariant_zero (F.flow t x) hflat
  have hpres :
      F.invariant (F.flow t x) = F.invariant x :=
    F.flow_preserves_invariant t x
  exact hx (by
    rw [← hpres]
    exact hzero)

/--
Equivalent phrasing: landing in the flat sector forces the initial obstruction
to be trivial.
-/
theorem invariant_zero_of_flows_to_flat
    {x : State}
    {t : ℝ}
    (hflat : F.flow t x ∈ F.Flat) :
    F.invariant x = 0 := by
  have hzero :
      F.invariant (F.flow t x) = 0 :=
    F.flat_invariant_zero (F.flow t x) hflat
  have hpres :
      F.invariant (F.flow t x) = F.invariant x :=
    F.flow_preserves_invariant t x
  rw [← hpres]
  exact hzero

/--
The flow of a nontrivial state remains outside the flat sector.
-/
theorem flow_nontrivial_not_flat
    {x : State}
    (hx : F.IsNontrivial x)
    (t : ℝ) :
    F.flow t x ∉ F.Flat :=
  F.nontrivial_cannot_flow_to_flat hx t

/--
The preimage of the flat sector under any admissible flow time is contained in
the trivial obstruction sector.
-/
theorem flow_flat_preimage_subset_trivial
    (t : ℝ) :
    {x : State | F.flow t x ∈ F.Flat}
      ⊆
    {x : State | F.IsTrivial x} := by
  intro x hx
  exact F.invariant_zero_of_flows_to_flat hx

/--
There is no admissible finite-time flattening of a nontrivial obstruction
sector.
-/
theorem no_nontrivial_flattening :
    ¬ ∃ (x : State) (t : ℝ),
      F.IsNontrivial x ∧ F.flow t x ∈ F.Flat := by
  intro h
  rcases h with ⟨x, t, hx_nontrivial, hx_flat⟩
  exact (F.flow_nontrivial_not_flat hx_nontrivial t) hx_flat

end ConservedObstructionFlow

end TopologicalSnap
