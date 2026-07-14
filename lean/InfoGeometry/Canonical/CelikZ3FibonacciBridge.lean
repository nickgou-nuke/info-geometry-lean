import Mathlib.Logic.Equiv.Basic

namespace CelikZ3FibonacciBridge

/-- Abstract representation of the B_n elements -/
structure ArtinBraid (n : ℕ) where
  val : ℕ

/--
The true formal categorical relationship between the Z3 graded calculus
and the Fibonacci anyons. 

WARNING: Do not define this as an equality theorem. The Z3 parafermion 
substrate does not equate dimension-for-dimension with the Fibonacci fusion 
sector. The theorem is properly an Intertwining/Projection topological map.
-/
structure Z3ParafermionToFibonacciBridge where
  z3Carrier : ℕ → Type
  fibCarrier : ℕ → Type
  project : (n : ℕ) → z3Carrier n → fibCarrier n

  braidZ3 : (n : ℕ) → ArtinBraid n → (z3Carrier n → z3Carrier n)
  braidFib : (n : ℕ) → ArtinBraid n → (fibCarrier n → fibCarrier n)

  intertwines :
    ∀ n β,
      project n ∘ braidZ3 n β =
      braidFib n β ∘ project n

end CelikZ3FibonacciBridge
