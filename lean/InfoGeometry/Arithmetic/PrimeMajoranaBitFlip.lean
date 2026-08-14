import Mathlib.Tactic
import InfoGeometry.Arithmetic.MobiusFermionBosonization
import InfoGeometry.Meta.SocketTarget


noncomputable section

namespace InfoGeometry.Arithmetic.PrimeMajoranaBitFlip

def majoranaFlip
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    (p : PrimeLabel)
    (S : Finset PrimeLabel) : Finset PrimeLabel :=
  if p ∈ S then S.erase p else insert p S

@[simp]
theorem mem_majoranaFlip_self
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    (p : PrimeLabel)
    (S : Finset PrimeLabel) :
    p ∈ majoranaFlip p S ↔ p ∉ S := by
  by_cases h : p ∈ S <;> simp [majoranaFlip, h]

@[simp]
theorem mem_majoranaFlip_of_ne
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    {p q : PrimeLabel}
    (hqp : q ≠ p)
    (S : Finset PrimeLabel) :
    q ∈ majoranaFlip p S ↔ q ∈ S := by
  by_cases hp : p ∈ S <;> simp [majoranaFlip, hp, hqp]

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

theorem card_majoranaFlip_of_not_mem
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    {p : PrimeLabel}
    {S : Finset PrimeLabel}
    (h : p ∉ S) :
    (majoranaFlip p S).card = S.card + 1 := by
  simp [majoranaFlip, h, Finset.card_insert_of_notMem]

theorem card_majoranaFlip_add_one_of_mem
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    {p : PrimeLabel}
    {S : Finset PrimeLabel}
    (h : p ∈ S) :
    (majoranaFlip p S).card + 1 = S.card := by
  simpa [majoranaFlip, h] using Finset.card_erase_add_one h

end InfoGeometry.Arithmetic.PrimeMajoranaBitFlip
