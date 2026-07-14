import Mathlib
import InfoGeometry.Arithmetic.MobiusFermionBosonization
import InfoGeometry.Meta.SocketTarget

/-!
# InfoGeometry.Arithmetic.PrimeMajoranaBitFlip

Finite real Majorana bit-flip layer for square-free prime registers.

The real Majorana operator attached to a prime mode is modeled as a toggle on
the square-free/Cantor occupation register:

* if the mode is absent, it is inserted;
* if the mode is present, it is erased;
* toggling twice is the identity.

This is the finite real algebraic content of the "Majorana is a bit-flipper"
picture.  Kitaev-chain, Pfaffian zero-mode, and RH interpretations remain
in the separate CAR, Clifford/Fock, and zero-mode owner files.
-/

noncomputable section

namespace PrimeMajoranaBitFlip

/-! ## 1. Real Majorana toggle on square-free states -/

/--
Majorana bit-flip on a finite square-free occupation state.

It toggles the presence of the mode `p`.
-/
def majoranaFlip
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    (p : PrimeLabel)
    (S : Finset PrimeLabel) : Finset PrimeLabel :=
  if p ∈ S then S.erase p else insert p S

/-- The flipped mode is absent exactly when it was present before. -/
@[simp]
theorem mem_majoranaFlip_self
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    (p : PrimeLabel)
    (S : Finset PrimeLabel) :
    p ∈ majoranaFlip p S ↔ p ∉ S := by
  by_cases h : p ∈ S <;> simp [majoranaFlip, h]

/-- Other modes are unaffected by a Majorana flip. -/
@[simp]
theorem mem_majoranaFlip_of_ne
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    {p q : PrimeLabel}
    (hqp : q ≠ p)
    (S : Finset PrimeLabel) :
    q ∈ majoranaFlip p S ↔ q ∈ S := by
  by_cases hp : p ∈ S <;> simp [majoranaFlip, hp, hqp]

/-- Majorana bit-flip is involutive. -/
@[simp]
theorem majoranaFlip_involutive
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    (p : PrimeLabel)
    (S : Finset PrimeLabel) :
    majoranaFlip p (majoranaFlip p S) = S := by
  ext q
  by_cases hqp : q = p
  · subst hqp
    simp
  · simp [mem_majoranaFlip_of_ne hqp]

/-- Majorana bit-flips on finite occupation states commute. -/
theorem majoranaFlip_commute
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    (p q : PrimeLabel)
    (S : Finset PrimeLabel) :
    majoranaFlip p (majoranaFlip q S) = majoranaFlip q (majoranaFlip p S) := by
  ext r
  by_cases hrp : r = p
  · subst r
    by_cases hpq : p = q
    · subst q
      simp
    · simp [mem_majoranaFlip_self, mem_majoranaFlip_of_ne hpq]
  · by_cases hrq : r = q
    · subst r
      simp [mem_majoranaFlip_self, mem_majoranaFlip_of_ne hrp]
    · simp [mem_majoranaFlip_of_ne hrp, mem_majoranaFlip_of_ne hrq]

/-- Cardinality increases by one when the flipped mode was absent. -/
theorem card_majoranaFlip_of_not_mem
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    {p : PrimeLabel}
    {S : Finset PrimeLabel}
    (h : p ∉ S) :
    (majoranaFlip p S).card = S.card + 1 := by
  simp [majoranaFlip, h, Finset.card_insert_of_notMem]

/-- Cardinality decreases by one when the flipped mode was present. -/
theorem card_majoranaFlip_add_one_of_mem
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    {p : PrimeLabel}
    {S : Finset PrimeLabel}
    (h : p ∈ S) :
    (majoranaFlip p S).card + 1 = S.card := by
  simpa [majoranaFlip, h] using Finset.card_erase_add_one h

end PrimeMajoranaBitFlip
