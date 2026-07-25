import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.Cl44FockParity

/-!
# Finite Parity Pairing — Witten-Möbius Index Cancellation

A finite algebraic structure for parity cancellation: given a finite
type with a fixed-point-free involution flipping parity, the Witten
index (even count minus odd count) is exactly zero.

This is the algebraic kernel of the Witten-Möbius chiral parity
theorem. The Cl(4,4) CAR algebra provides the local 16-state
occupation sheet; the `FiniteParityPairing` structure abstracts
the toggle involution proof. The Möbius recursion then globalizes.

## Architecture

```
  Cl(4,4) CAR ──→ 16 occupation states (Cl44FockParity)
       │
       ▼
  FiniteParityPairing (this file)
       │
       ▼
  MobiusChiralClosure / WittenParityAnomalyBridge
```
-/

namespace InfoGeometry.Arithmetic.WittenMobius

/--
A finite type with a parity-flipping bijection between an even and
an odd sector. The involution must be fixed-point-free so that every
state has a partner of opposite parity.
-/
structure FiniteParityPairing where
  Carrier : Type u
  [fintype : Fintype Carrier]
  /-- A fixed-point-free involution on the carrier. -/
  flip : Carrier → Carrier
  flip_involutive : Function.Involutive flip
  flip_fixed_point_free : ∀ x, flip x ≠ x
  /-- Even predicate: true on one half of each paired orbit. -/
  isEven : Carrier → Bool
  /-- flip toggles the isEven predicate. -/
  flip_toggles_parity : ∀ x, isEven (flip x) = !(isEven x)

attribute [instance] FiniteParityPairing.fintype

namespace FiniteParityPairing

/-- The even sector (elements where isEven = true). -/
def EvenSector (P : FiniteParityPairing) : Type :=
  {x : P.Carrier // P.isEven x = true}

/-- The odd sector (elements where isEven = false). -/
def OddSector (P : FiniteParityPairing) : Type :=
  {x : P.Carrier // P.isEven x = false}

instance (P : FiniteParityPairing) : Fintype P.EvenSector :=
  Subtype.fintype _

instance (P : FiniteParityPairing) : Fintype P.OddSector :=
  Subtype.fintype _

/-- The flip induces a bijection between even and odd sectors. -/
def parityEquiv (P : FiniteParityPairing) : P.EvenSector ≃ P.OddSector where
  toFun x := ⟨P.flip x.val, by
    have h1 := P.flip_toggles_parity x.val
    have h2 := x.property
    rw [h2] at h1
    exact h1⟩
  invFun x := ⟨P.flip x.val, by
    have h1 := P.flip_toggles_parity x.val
    have h2 := x.property
    rw [h2] at h1
    exact h1⟩
  left_inv := fun x => Subtype.ext (P.flip_involutive x.val)
  right_inv := fun x => Subtype.ext (P.flip_involutive x.val)

/-- The finite Witten index: card(even) - card(odd). -/
def wittenIndex (P : FiniteParityPairing) : ℤ :=
  (Fintype.card P.EvenSector : ℤ) - (Fintype.card P.OddSector : ℤ)

/-- Parity pairing forces the Witten index to zero. -/
theorem wittenIndex_zero (P : FiniteParityPairing) :
    P.wittenIndex = 0 := by
  dsimp [wittenIndex]
  have h := Fintype.card_congr (P.parityEquiv)
  omega

end FiniteParityPairing

/-! ## Instantiation: 4-mode Cl(4,4) Fock parity -/

open InfoGeometry.OperatorAlgebra.Cl44FockParity

/-- Toggling mode 0 on the 4-mode Fock space provides a finite parity pairing. -/
def fourModeParityPairing : FiniteParityPairing where
  Carrier := Occ4
  fintype := inferInstance
  flip := toggle0
  flip_involutive := toggle0_involutive
  flip_fixed_point_free := by
    intro w; intro h
    have h0 := congr_fun h 0
    simp [toggle0] at h0
  isEven := fun w => decide (Even (fermionNumber w))
  flip_toggles_parity := by
    -- This requires a combinatorial argument that toggle0 flips parity.
    -- The toggle adds/removes mode 0 from the occupied set, changing
    -- the cardinality by ±1, which flips the parity.
    -- This is a finite check: there are only 16 occupation states.
    decide

/-- The Witten index for 4 fermionic modes is zero. -/
theorem fourModeWittenIndexZero : (fourModeParityPairing.wittenIndex : ℤ) = 0 :=
  FiniteParityPairing.wittenIndex_zero _

end InfoGeometry.Arithmetic.WittenMobius
