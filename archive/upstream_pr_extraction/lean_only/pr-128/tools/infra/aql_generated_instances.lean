/- Auto-generated from AQL query -/
/- Content hash: f14818a476be7210 -/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic


/-- Prime numbers from ArangoDB -/
inductive AQLPrime : Type
| mk (val : ℕ) (h_prime : Nat.Prime val) : AQLPrime
deriving DecidableEq

def AQLPrime.val : AQLPrime → ℕ
| mk v _ => v

theorem AQLPrime.val_spec (p : AQLPrime) : Nat.Prime (p.val) :=
  match p with
  | mk _ h => h


/-- Prime 2 (key: prime-2) -/
def prime_2 : AQLPrime := AQLPrime.mk 2 (by decide)


/-- Prime 3 (key: prime-3) -/
def prime_3 : AQLPrime := AQLPrime.mk 3 (by decide)


/-- Prime 5 (key: prime-5) -/
def prime_5 : AQLPrime := AQLPrime.mk 5 (by decide)

/-- Divides relation on vertices -/
def divides : AQLPrime → AQLPrime → Prop :=
  fun p q => ∃ k : ℕ, q.val = p.val * k

/-- Divisibility graph from ArangoDB -/
structure DivisibilityGraph where
  vertices : Finset AQLPrime
  divides : AQLPrime → AQLPrime → Prop
  
def graphInstance : DivisibilityGraph :=
  { vertices := {prime_2, prime_3, prime_5},
    divides := divides }
