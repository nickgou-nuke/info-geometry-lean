/-
InfoGeometry/Algebra/LightConePair.lean

A theorem-safe local lightcone compensation socket.

This file proves only the finite associative-algebra identities following from
nilpotent generators `ePlus`, `eMinus` with anticommutator one.  It does not
construct a Clifford module, a `Pin(5,5)` action, a physical Witten index, or a
global orbit/classification theorem.
-/

import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Algebra

/--
A lightcone compensation pair in an associative ring.

The hypotheses are the local algebraic engine
`e₊² = e₋² = 0` and `e₊e₋ + e₋e₊ = 1`.
-/
def LightConePair (R : Type*) [Ring R] :=
  Subtype (fun p : R × R =>
    p.1 * p.1 = 0 ∧ p.2 * p.2 = 0 ∧ p.1 * p.2 + p.2 * p.1 = 1)

namespace LightConePair

variable {R : Type*} [Ring R]
variable (P : LightConePair R)

abbrev ePlus : R := P.1.1

abbrev eMinus : R := P.1.2

def ePlus_sq : ePlus P * ePlus P = 0 := P.2.1

def eMinus_sq : eMinus P * eMinus P = 0 := P.2.2.1

def anticomm : ePlus P * eMinus P + eMinus P * ePlus P = 1 := P.2.2.2

/-- The positive lightcone projector `p₊ = e₊e₋`. -/
def pPlus : R := P.ePlus * P.eMinus

/-- The negative lightcone projector `p₋ = e₋e₊`. -/
def pMinus : R := P.eMinus * P.ePlus

/-- `p₊` is idempotent. -/
theorem pPlus_idem : P.pPlus * P.pPlus = P.pPlus := by
  dsimp [pPlus]
  have h : P.eMinus * P.ePlus = 1 - P.ePlus * P.eMinus := by
    rw [eq_sub_iff_add_eq]
    rw [add_comm]
    exact P.anticomm
  calc
    (P.ePlus * P.eMinus) * (P.ePlus * P.eMinus)
        = P.ePlus * ((P.eMinus * P.ePlus) * P.eMinus) := by noncomm_ring
    _ = P.ePlus * ((1 - P.ePlus * P.eMinus) * P.eMinus) := by rw [h]
    _ = P.ePlus * P.eMinus := by
        noncomm_ring [P.ePlus_sq, P.eMinus_sq]

/-- `p₋` is idempotent. -/
theorem pMinus_idem : P.pMinus * P.pMinus = P.pMinus := by
  dsimp [pMinus]
  have h : P.ePlus * P.eMinus = 1 - P.eMinus * P.ePlus := by
    rw [eq_sub_iff_add_eq]
    exact P.anticomm
  calc
    (P.eMinus * P.ePlus) * (P.eMinus * P.ePlus)
        = P.eMinus * ((P.ePlus * P.eMinus) * P.ePlus) := by noncomm_ring
    _ = P.eMinus * ((1 - P.eMinus * P.ePlus) * P.ePlus) := by rw [h]
    _ = P.eMinus * P.ePlus := by
        noncomm_ring [P.ePlus_sq, P.eMinus_sq]

/-- The two lightcone projectors are orthogonal in one order. -/
theorem pPlus_mul_pMinus : P.pPlus * P.pMinus = 0 := by
  dsimp [pPlus, pMinus]
  rw [mul_assoc, ← mul_assoc P.eMinus P.eMinus P.ePlus, P.eMinus_sq]
  simp

/-- The two lightcone projectors are orthogonal in the other order. -/
theorem pMinus_mul_pPlus : P.pMinus * P.pPlus = 0 := by
  dsimp [pPlus, pMinus]
  rw [mul_assoc, ← mul_assoc P.ePlus P.ePlus P.eMinus, P.ePlus_sq]
  simp

/-- The lightcone projectors add to the identity. -/
theorem pPlus_add_pMinus_eq_one : P.pPlus + P.pMinus = 1 :=
  P.anticomm

/-- Convenience packet for the local compensation algebra. -/
theorem lightcone_compensation_packet :
    P.pPlus * P.pPlus = P.pPlus ∧
    P.pMinus * P.pMinus = P.pMinus ∧
    P.pPlus * P.pMinus = 0 ∧
    P.pMinus * P.pPlus = 0 ∧
    P.pPlus + P.pMinus = 1 :=
  ⟨P.pPlus_idem, P.pMinus_idem, P.pPlus_mul_pMinus,
    P.pMinus_mul_pPlus, P.pPlus_add_pMinus_eq_one⟩

end LightConePair

end InfoGeometry.Algebra
