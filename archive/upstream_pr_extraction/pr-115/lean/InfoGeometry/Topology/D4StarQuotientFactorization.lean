import InfoGeometry.Topology.D4StarQuotientClopen

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-! Color permutations factor through the two-class observable quotient. -/

theorem quotientToBool_quotientColorAction
    (σ : Equiv.Perm ColorChannel) (q : D4StarQuotient) :
    quotientToBool (quotientColorAction σ q) = quotientToBool q := by
  induction q using Quotient.inductionOn with
  | _ v =>
      cases v <;> rfl

def boolFactorAction (σ : Equiv.Perm ColorChannel) : Bool → Bool :=
  id

theorem quotient_factorization
    (σ : Equiv.Perm ColorChannel) (q : D4StarQuotient) :
    quotientToBool (quotientColorAction σ q) =
      boolFactorAction σ (quotientToBool q) := by
  exact quotientToBool_quotientColorAction σ q

theorem continuous_boolFactorAction
    (σ : Equiv.Perm ColorChannel) :
    Continuous (boolFactorAction σ) := by
  exact continuous_id

theorem quotient_action_is_topologically_trivial
    (σ : Equiv.Perm ColorChannel) :
    quotientColorAction σ = id := by
  exact quotientColorAction_eq_id σ

end InfoGeometry.Topology.PauliJungD4Star
