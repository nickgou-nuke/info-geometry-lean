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
witness-gated.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeMajoranaBitFlip

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

/-! ## 2. Witness gates for Majorana chains and zero modes -/

/--
Finite Majorana Clifford/CAR gate.

Concrete anticommutation and self-adjointness laws are supplied by an owner
operator model.  The finite register theorem above only proves the bit-flip
shadow.
-/
@[socket_debt_tag]
structure PrimeMajoranaCARGate
  (PrimeLabel Operator : Type*) where
  majorana : PrimeLabel → Operator
  IsSelfAdjoint : Operator → Prop
  CliffordPair : Operator → Operator → Prop
  ImplementsBitFlip : PrimeLabel → Operator → Prop
  is_self_adjoint_law : ∀ p, IsSelfAdjoint (majorana p)
  clifford_pair_law : ∀ p q, CliffordPair (majorana p) (majorana q)
  implements_bit_flip_law : ∀ p, ImplementsBitFlip p (majorana p)

namespace PrimeMajoranaCARGate

/-- Explicit debt: the generic operator carrier has no owner CAR proof here. -/
theorem clifford_holds
    {PrimeLabel Operator : Type*}
    (G : PrimeMajoranaCARGate PrimeLabel Operator)
    (p q : PrimeLabel) :
    G.CliffordPair (G.majorana p) (G.majorana q) :=
    G.clifford_pair_law p q

/-- Explicit debt: matching an abstract operator to the finite flip needs an owner model. -/
theorem bit_flip_model
    {PrimeLabel Operator : Type*}
    (G : PrimeMajoranaCARGate PrimeLabel Operator)
    (p : PrimeLabel) :
    G.ImplementsBitFlip p (G.majorana p) :=
    G.implements_bit_flip_law p

/-- Explicit debt: self-adjointness needs a concrete adjoint/operator owner. -/
theorem self_adjoint
    {PrimeLabel Operator : Type*}
    (G : PrimeMajoranaCARGate PrimeLabel Operator)
    (p : PrimeLabel) :
    G.IsSelfAdjoint (G.majorana p) :=
    G.is_self_adjoint_law p

end PrimeMajoranaCARGate

/--
Majorana zero-mode interpretation gate.

This is deliberately a witness interface.  It does not assert that zeta zeros
are Majorana zero modes or prove RH.
-/
@[socket_debt_tag]
structure MajoranaZeroModeGate
    (Hamiltonian ZeroMode ZeroReadout : Type*) where
  hamiltonian : Hamiltonian
  zeroMode : ZeroMode
  zeroReadout : ZeroReadout
  CommutesWithHamiltonian : Hamiltonian → ZeroMode → Prop
  HasZeroEnergy : Hamiltonian → ZeroMode → Prop
  ReadoutMatchesZeroMode : ZeroReadout → ZeroMode → Prop
  zero_energy_law : HasZeroEnergy hamiltonian zeroMode
  readout_matches_zero_mode_law : ReadoutMatchesZeroMode zeroReadout zeroMode
  commutes_with_hamiltonian_law : CommutesWithHamiltonian hamiltonian zeroMode

namespace MajoranaZeroModeGate

/-- Explicit debt: zero energy needs a concrete Hamiltonian/zero-mode owner. -/
theorem zero_energy
    {Hamiltonian ZeroMode ZeroReadout : Type*}
    (G : MajoranaZeroModeGate Hamiltonian ZeroMode ZeroReadout) :
    G.HasZeroEnergy G.hamiltonian G.zeroMode :=
    G.zero_energy_law

/-- Explicit debt: comparing a readout to a zero mode needs a concrete owner. -/
theorem zero_readout_comparison
    {Hamiltonian ZeroMode ZeroReadout : Type*}
    (G : MajoranaZeroModeGate Hamiltonian ZeroMode ZeroReadout) :
    G.ReadoutMatchesZeroMode G.zeroReadout G.zeroMode :=
    G.readout_matches_zero_mode_law

/-- Explicit debt: Hamiltonian commutation needs a concrete operator owner. -/
theorem commutes_with_hamiltonian
    {Hamiltonian ZeroMode ZeroReadout : Type*}
    (G : MajoranaZeroModeGate Hamiltonian ZeroMode ZeroReadout) :
    G.CommutesWithHamiltonian G.hamiltonian G.zeroMode :=
    G.commutes_with_hamiltonian_law

end MajoranaZeroModeGate

end InfoGeometry.Arithmetic.PrimeMajoranaBitFlip
