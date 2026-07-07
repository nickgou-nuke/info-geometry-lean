import Mathlib
import InfoGeometry.Meta.SocketTarget
import InfoGeometry.Arithmetic.PrimeMajoranaBitFlip

namespace InfoGeometry.Arithmetic.PrimeMajoranaBitFlip

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
