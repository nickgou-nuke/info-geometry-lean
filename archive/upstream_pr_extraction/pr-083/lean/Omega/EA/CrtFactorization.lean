import Mathlib.Data.ZMod.Basic
import Omega.Folding.FiberRing

namespace Omega.EA

/-- Paper label: `cor:crt-factorization`. The stable-value map already identifies `X m` with
`ZMod (F_{m+2})`, and the existing CRT equivalence transports any coprime factorization of
`F_{m+2}` to a product decomposition of the folded ring. -/
theorem paper_crt_factorization (m : ℕ) :
    Nonempty (Omega.X m ≃+* ZMod (Nat.fib (m + 2))) ∧
      ∀ p q : ℕ, Nat.fib (m + 2) = p * q → Nat.Coprime p q →
        Nonempty (Omega.X m ≃+* ZMod p × ZMod q) := by
  refine ⟨⟨Omega.X.stableValueRingEquiv m⟩, ?_⟩
  intro p q hpq hcop
  exact ⟨Omega.X.crtDecomposition m p q hpq hcop⟩

end Omega.EA
