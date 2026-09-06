import Mathlib

/-!
# Continuous Kantorovich pairing

This file adds the topological interface for a fixed-observable pairing.  It
does not define a Wasserstein distance: no supremum over Lipschitz
observables is taken here.
-/

namespace InfoGeometry.Topology.ContinuousKantorovichPairing

abbrev ContinuousExpectation (State : Type*) [TopologicalSpace State] :=
  C(State, (State → ℝ) → ℝ)

namespace ContinuousExpectation

abbrev value
    {State : Type*} [TopologicalSpace State]
    (E : ContinuousExpectation State) : State → (State → ℝ) → ℝ := E

abbrev continuous_value
    {State : Type*} [TopologicalSpace State]
    (E : ContinuousExpectation State) (f : State → ℝ) :
    Continuous (fun ρ => E.value ρ f) :=
  (continuous_apply f).comp E.continuous

end ContinuousExpectation

def pairing
    {State : Type*} [TopologicalSpace State]
    (E : ContinuousExpectation State) (f : State → ℝ) :
  State × State → ℝ :=
  fun p => abs (E.value p.1 f - E.value p.2 f)

theorem pairing_apply
    {State : Type*} [TopologicalSpace State]
    (E : ContinuousExpectation State) (f : State → ℝ)
    (ρ σ : State) :
    pairing E f (ρ, σ) = abs (E.value ρ f - E.value σ f) :=
  rfl

theorem continuous_pairing
    {State : Type*} [TopologicalSpace State]
    (E : ContinuousExpectation State) (f : State → ℝ) :
    Continuous (pairing E f) := by
  have hleft : Continuous (fun p : State × State => E.value p.1 f) :=
    (E.continuous_value f).comp continuous_fst
  have hright : Continuous (fun p : State × State => E.value p.2 f) :=
    (E.continuous_value f).comp continuous_snd
  exact (hleft.sub hright).abs

def toTopCatHom
    {State : Type} [TopologicalSpace State]
    (E : ContinuousExpectation State) (f : State → ℝ) :
    TopCat.of (State × State) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := pairing E f
      continuous_toFun := continuous_pairing E f }

@[simp] theorem toTopCatHom_apply
    {State : Type} [TopologicalSpace State]
    (E : ContinuousExpectation State) (f : State → ℝ)
    (p : State × State) :
    toTopCatHom E f p = pairing E f p :=
  rfl

theorem pairing_symm
    {State : Type*} [TopologicalSpace State]
    (E : ContinuousExpectation State) (f : State → ℝ)
    (ρ σ : State) :
    pairing E f (ρ, σ) = pairing E f (σ, ρ) := by
  simp only [pairing]
  exact abs_sub_comm (E.value ρ f) (E.value σ f)

theorem pairing_triangle
    {State : Type*} [TopologicalSpace State]
    (E : ContinuousExpectation State) (f : State → ℝ)
    (ρ σ τ : State) :
    pairing E f (ρ, τ) ≤
      pairing E f (ρ, σ) + pairing E f (σ, τ) := by
  simp only [pairing]
  exact abs_sub_le (E.value ρ f) (E.value σ f) (E.value τ f)

end InfoGeometry.Topology.ContinuousKantorovichPairing
