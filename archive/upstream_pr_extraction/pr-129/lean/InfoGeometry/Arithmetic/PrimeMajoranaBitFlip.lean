import Mathlib
import InfoGeometry.Arithmetic.MobiusFermionBosonization

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
structure PrimeMajoranaCARGate
    (PrimeLabel Operator : Type*) where
  majorana : PrimeLabel → Operator
  self_adjoint_True : Prop
  clifford_True : Prop
  bit_flip_model_True : Prop
  certificate :
    self_adjoint_True ∧ clifford_True ∧ bit_flip_model_True

namespace PrimeMajoranaCARGate

/-- Re-export of the supplied Clifford/CAR law. -/
theorem clifford
    {PrimeLabel Operator : Type*}
    (G : PrimeMajoranaCARGate PrimeLabel Operator) :
    G.clifford_True :=
  G.certificate.2.1

/-- Re-export of the supplied bit-flip model law. -/
theorem bit_flip_model
    {PrimeLabel Operator : Type*}
    (G : PrimeMajoranaCARGate PrimeLabel Operator) :
    G.bit_flip_model_True :=
  G.certificate.2.2

end PrimeMajoranaCARGate

/--
Majorana zero-mode interpretation gate.

This is deliberately a witness interface.  It does not assert that zeta zeros
are Majorana zero modes or prove RH.
-/
structure MajoranaZeroModeGate
    (Hamiltonian ZeroMode ZeroReadout : Type*) where
  hamiltonian : Hamiltonian
  zeroMode : ZeroMode
  zeroReadout : ZeroReadout
  commutes_with_hamiltonian_True : Prop
  zero_energy_True : Prop
  zero_readout_comparison_True : Prop
  certificate :
    commutes_with_hamiltonian_True ∧
      zero_energy_True ∧
        zero_readout_comparison_True

namespace MajoranaZeroModeGate

/-- Re-export of the supplied zero-energy law. -/
theorem zero_energy
    {Hamiltonian ZeroMode ZeroReadout : Type*}
    (G : MajoranaZeroModeGate Hamiltonian ZeroMode ZeroReadout) :
    G.zero_energy_True :=
  G.certificate.2.1

/-- Re-export of the supplied zero-readout comparison law. -/
theorem zero_readout_comparison
    {Hamiltonian ZeroMode ZeroReadout : Type*}
    (G : MajoranaZeroModeGate Hamiltonian ZeroMode ZeroReadout) :
    G.zero_readout_comparison_True :=
  G.certificate.2.2

end MajoranaZeroModeGate

end InfoGeometry.Arithmetic.PrimeMajoranaBitFlip
