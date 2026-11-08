/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Omega.Conclusion.C6JacobianNotSimple

/-!
# Exact scope of the C₆ type-level Jacobian model

`C6JacobianNotSimple` defines every Jacobian carrier to be `PUnit` and defines
isogeny as type equivalence.  In that model the nonsimplicity conclusion is
independent of the supplied isogeny premise: `PUnit` is equivalent to
`PUnit × PUnit`.  This companion records that exact consequence and makes no
claim about geometric Jacobians or isogenies of abelian varieties.
-/

namespace Omega.Conclusion

def pUnitProductEquiv : PUnit ≃ PUnit × PUnit where
  toFun := fun _ => (PUnit.unit, PUnit.unit)
  invFun := fun _ => PUnit.unit
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

/-- In the owner's concrete `PUnit` carrier, the defined type-level
nonsimplicity predicate already fails, without any isogeny hypothesis. -/
theorem c6_type_model_not_simple_without_isogeny :
    ¬ IsSimpleOverQ (Jacobian C6) := by
  intro hs
  exact hs ⟨PUnit, PUnit, ⟨pUnitProductEquiv⟩⟩

/-- Consequently the source theorem's premise is redundant in its current
type model. -/
theorem c6_type_model_conclusion_for_all_isogeny_inputs :
    ∀ _h : IsogenousOverQ (Jacobian C6)
      (Jacobian C × Jacobian R × Jacobian R),
      ¬ IsSimpleOverQ (Jacobian C6) := by
  intro _h
  exact c6_type_model_not_simple_without_isogeny

end Omega.Conclusion
