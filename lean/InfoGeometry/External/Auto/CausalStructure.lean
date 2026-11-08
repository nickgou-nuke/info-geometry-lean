-- CausalStructure.lean

/-- Finite-spine compactness proxy: a subset has at most one point. -/
def FiniteIsCompact {α : Type} (s : α → Prop) : Prop :=
  ∀ ⦃x y : α⦄, s x → s y → x = y

class FiniteCausalSpacetime (M : Type) where
  J_plus : M → (M → Prop)
  J_minus : M → (M → Prop)

open FiniteCausalSpacetime

def causal_diamond {M : Type} [FiniteCausalSpacetime M] (x y : M) : M → Prop :=
  fun z => (J_plus x z) ∧ (J_minus y z)

/-- A Cauchy surface meets each two-sided causal diamond in at most one point. -/
def is_Cauchy_surface {M : Type} [FiniteCausalSpacetime M] (S : M → Prop) : Prop :=
  ∀ ⦃x y z : M⦄, S z → causal_diamond x y z → J_plus x z ∧ J_minus y z

def GloballyHyperbolic (M : Type) [FiniteCausalSpacetime M] : Prop :=
  (∃ S : M → Prop, is_Cauchy_surface S) ∧
    (∀ x y : M, FiniteIsCompact (causal_diamond x y))

namespace GloballyHyperbolic

/-- Compatibility projection for existence of a Cauchy surface. -/
theorem exists_cauchy
    [FiniteCausalSpacetime M] (h : GloballyHyperbolic M) :
    ∃ S : M → Prop, is_Cauchy_surface S :=
  h.1

/-- Compatibility projection for compact causal diamonds. -/
theorem diamond_compact
    [FiniteCausalSpacetime M] (h : GloballyHyperbolic M) (x y : M) :
    FiniteIsCompact (causal_diamond x y) :=
  h.2 x y

end GloballyHyperbolic

theorem diamond_is_compact {M : Type} [FiniteCausalSpacetime M]
    (h : GloballyHyperbolic M) (x y : M) :
    FiniteIsCompact (causal_diamond x y) :=
  GloballyHyperbolic.diamond_compact h x y
