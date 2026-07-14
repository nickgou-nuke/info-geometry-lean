import Mathlib.Tactic

namespace Omega.GU

/-- The audited Zeckendorf data for `12 = 8 + 3 + 1`. -/
def Window6SMZeckendorfAudit : Prop :=
  12 = Nat.fib 6 + Nat.fib 4 + Nat.fib 2 ∧
    Nat.fib 2 + Nat.fib 4 + Nat.fib 6 = 12 ∧
    Nat.fib 2 = 1 ∧ Nat.fib 4 = 3 ∧ Nat.fib 6 = 8 ∧
    4 - 2 ≥ 2 ∧ 6 - 4 ≥ 2

/-- The Zeckendorf audit at dimension `12` matches the finite decomposition `1 + 3 + 8`.

This theorem proves only the finite arithmetic/readout facts supplied by
`ZeckendorfSignature`; compactness of an operator model is not asserted here.
-/
theorem paper_window6_sm_zeckendorf_audit :
    Window6SMZeckendorfAudit := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, by omega, by omega⟩

end Omega.GU
