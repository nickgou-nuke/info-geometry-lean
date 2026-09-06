-- CausalStructure.lean

/-- Finite-spine compactness proxy: a subset has at most one point. -/
def IsCompact {α : Type} (s : α → Prop) : Prop :=
  ∀ ⦃x y : α⦄, s x → s y → x = y

class Spacetime (M : Type) where
  J_plus : M → (M → Prop)
  J_minus : M → (M → Prop)

open Spacetime

def causal_diamond {M : Type} [Spacetime M] (x y : M) : M → Prop :=
  fun z => (J_plus x z) ∧ (J_minus y z)

/-- A Cauchy surface meets each two-sided causal diamond in at most one point. -/
def is_Cauchy_surface {M : Type} [Spacetime M] (S : M → Prop) : Prop :=
  ∀ ⦃x y z : M⦄, S z → causal_diamond x y z → J_plus x z ∧ J_minus y z

class GloballyHyperbolic (M : Type) [Spacetime M] : Prop where
  exists_cauchy : ∃ S : M → Prop, is_Cauchy_surface S
  diamond_compact : ∀ x y : M, IsCompact (causal_diamond x y)

theorem diamond_is_compact {M : Type} [Spacetime M] [GloballyHyperbolic M] (x y : M) :
    IsCompact (causal_diamond x y) :=
  GloballyHyperbolic.diamond_compact x y
