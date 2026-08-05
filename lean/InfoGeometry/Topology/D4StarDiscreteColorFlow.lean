import InfoGeometry.Topology.D4StarObservationalQuotient

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical
open InfoGeometry.Topology.ContinuousQuotientDescent

/-! A discrete modular-time flow of color permutations and its quotient. -/

structure ColorPermutationFlow where
  permutation : ℤ → Equiv.Perm ColorChannel
  zero_law : permutation 0 = 1
  add_law : ∀ s t, permutation (s + t) =
    permutation s * permutation t

def inducedQuotientFlow (F : ColorPermutationFlow) :
    ContinuousFlow D4StarQuotient where
  flow := fun t q => quotientColorAction (F.permutation t) q
  zero_law := by
    intro q
    rw [F.zero_law]
    exact quotientColorAction_identity q
  add_law := by
    intro s t q
    rw [F.add_law]
    exact (quotientColorAction_comp (F.permutation s) (F.permutation t) q).symm
  continuous := by
    intro t
    exact continuous_quotientColorAction (F.permutation t)

theorem inducedQuotientFlow_is_trivial
    (F : ColorPermutationFlow) (t : ℤ) (q : D4StarQuotient) :
    (inducedQuotientFlow F).flow t q = q := by
  simp [inducedQuotientFlow]
  <;> rw [quotientColorAction_eq_id (F.permutation t)]
  <;> rfl

theorem inducedQuotientFlow_descends_to_bool
    (F : ColorPermutationFlow) (t : ℤ) (q : D4StarQuotient) :
    quotientToBool ((inducedQuotientFlow F).flow t q) =
      quotientToBool q := by
  exact congrArg quotientToBool (inducedQuotientFlow_is_trivial F t q)

theorem inducedQuotientFlow_flow_eq_starQuotientFlow
    (F : ColorPermutationFlow) :
    (inducedQuotientFlow F).flow = starQuotientFlow.flow := by
  funext t q
  exact inducedQuotientFlow_is_trivial F t q

def inducedBoolFlow (F : ColorPermutationFlow) :
    ContinuousFlow Bool where
  flow := fun _ b => b
  zero_law := by intro b; rfl
  add_law := by intro s t b; rfl
  continuous := by intro t; exact continuous_id

theorem inducedBoolFlow_is_observable_factor
    (F : ColorPermutationFlow) (t : ℤ) (q : D4StarQuotient) :
    quotientToBool ((inducedQuotientFlow F).flow t q) =
      (inducedBoolFlow F).flow t (quotientToBool q) := by
  exact inducedQuotientFlow_descends_to_bool F t q

@[simp] theorem inducedBoolFlow_flow_eq_id
    (F : ColorPermutationFlow) :
    (inducedBoolFlow F).flow = fun _ b => b := by
  rfl

end InfoGeometry.Topology.PauliJungD4Star
