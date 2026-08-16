import InfoGeometry.Topology.D4StarObservationalQuotient

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical
open InfoGeometry.Topology.ContinuousQuotientDescent

/-! A discrete modular-time flow of color permutations and its quotient. -/

structure ColorPermutationFlow where
  /-- A genuine representation of discrete time by color permutations. -/
  representation : Multiplicative ℤ →* Equiv.Perm ColorChannel

namespace ColorPermutationFlow

def permutation (F : ColorPermutationFlow) (t : ℤ) : Equiv.Perm ColorChannel :=
  F.representation (Multiplicative.ofAdd t)

@[simp] theorem permutation_zero (F : ColorPermutationFlow) :
    F.permutation 0 = 1 := by
  exact F.representation.map_one

theorem permutation_add (F : ColorPermutationFlow) (s t : ℤ) :
    F.permutation (s + t) = F.permutation s * F.permutation t := by
  exact F.representation.map_mul (Multiplicative.ofAdd s) (Multiplicative.ofAdd t)

end ColorPermutationFlow

def trivialColorPermutationFlow : ColorPermutationFlow where
  representation :=
    { toFun := fun _ => 1
      map_one' := rfl
      map_mul' := by intro s t; simp }

def inducedQuotientFlow (F : ColorPermutationFlow) :
    ContinuousFlow D4StarQuotient where
  flow := fun t q => quotientColorAction (F.permutation t) q
  zero_law := by
    intro q
    rw [F.permutation_zero]
    exact quotientColorAction_identity q
  add_law := by
    intro s t q
    rw [F.permutation_add]
    exact (quotientColorAction_comp (F.permutation s) (F.permutation t) q).symm
  continuous := by
    intro t
    exact continuous_quotientColorAction (F.permutation t)

theorem inducedQuotientFlow_is_trivial
    (F : ColorPermutationFlow) (t : ℤ) (q : D4StarQuotient) :
    (inducedQuotientFlow F).flow t q = q := by
  change quotientColorAction (F.permutation t) q = q
  rw [quotientColorAction_eq_id]
  rfl

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
