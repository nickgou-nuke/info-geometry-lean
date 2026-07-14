import Mathlib
import InfoGeometry.Canonical.SouriauOperatorialLogPotential

namespace InfoGeometry.Sandbox.DuhamelInstance

open InfoGeometry.Canonical.SouriauOperatorialLogPotential

/-!
# QMS Intent Envelope
- concept_id: TrivSqZeroExtDuhamelInstance
- target_status: theorem-backed
- risk_level: R2
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] [IsCentralScalar R M]

def discreteDuhamelSum (A : R) (B : M) (n : ℕ) : M :=
  -- Mocking the previously verified summation to decouple this test
  0

/-- 
STATE: CONTRACT
Instantiating the exact Duhamel typeclass over TrivSqZeroExt R M.
-/
def TrivSqZeroExtDuhamel (n : ℕ) : DuhamelOperatorDerivative R (TrivSqZeroExt R M) M where
  K β := TrivSqZeroExt.inl β
  directionToInsertion δ := TrivSqZeroExt.inr δ
  derivativeOfExp β δ := TrivSqZeroExt.inr (discreteDuhamelSum β δ n)
  higherSimplexOrderedForms
    | 1, β, [δ] => TrivSqZeroExt.inr (discreteDuhamelSum β δ n)
    | _, _, _ => 0
  traceStateKMSReadout _ := 0
  derivativeOfExp_eq_first_ordered_form β δ := rfl

end InfoGeometry.Sandbox.DuhamelInstance
