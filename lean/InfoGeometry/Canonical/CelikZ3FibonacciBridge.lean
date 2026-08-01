import Mathlib.Logic.Equiv.Basic

namespace InfoGeometry.Canonical.CelikZ3FibonacciBridge

/-- Abstract representation of a braid label at stage `n`.

This owner carries no braid relation or stage-dependent invariant, so its
native carrier is the underlying natural-number label. -/
abbrev ArtinBraid (n : ℕ) := ℕ

namespace ArtinBraid
abbrev val {n : ℕ} (β : ArtinBraid n) : ℕ := β
end ArtinBraid

/--
Bridge carrier between the Z3 graded calculus and the Fibonacci anyon lane.

The structure records an intertwining/projection map rather than an equality
theorem between the two carriers.
-/
structure Z3ParafermionToFibonacciBridge where
  z3Carrier : ℕ → Type
  fibCarrier : ℕ → Type
  project : (n : ℕ) → z3Carrier n → fibCarrier n

  braidZ3 : (n : ℕ) → ArtinBraid n → (z3Carrier n → z3Carrier n)
  braidFib : (n : ℕ) → ArtinBraid n → (fibCarrier n → fibCarrier n)

theorem project_intertwines
    (B : Z3ParafermionToFibonacciBridge)
    (hintertwines :
      ∀ n β,
        B.project n ∘ B.braidZ3 n β =
          B.braidFib n β ∘ B.project n)
    (n : ℕ) (β : ArtinBraid n) :
    B.project n ∘ B.braidZ3 n β =
      B.braidFib n β ∘ B.project n :=
  hintertwines n β

end InfoGeometry.Canonical.CelikZ3FibonacciBridge
