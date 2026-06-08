import InfoGeometry.Arithmetic.PrimeSuperalgebraReadback
import InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection
import InfoGeometry.Meta.SocketTarget

/-!
# InfoGeometry.Canonical.PrimeSUSYVacuum

Witness-gated SUSY vacuum capstone for the prime Lee--Yang architecture.

This module keeps the finite arithmetic facts separate from the analytic
spectral laws:

* finite Mobius parity is owned by
  `InfoGeometry.Arithmetic.PrimeSuperalgebraReadback`;
* defect-free Lee--Yang and Mertens/LDP hypotheses are owned by the canonical
  witness packets;
* the interpretation of completed-`xi` zeros as protected Majorana zero modes
  remains supplied data.

It does not prove RH, does not assert a completed-`xi` determinant identity, and
does not identify inverse-zeta Witten poles with zero modes.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeSUSYVacuum

open InfoGeometry.Arithmetic.PrimeSuperalgebraReadback
open InfoGeometry.Canonical.PrimeMertensDefectBoundary
open InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection

/-! ## Finite arithmetic parity readback -/

/-- Finite fermion parity readout from the arithmetic prime-superalgebra layer. -/
abbrev finiteFermionParity
    (P : FermionicPrimeRegister)
    (psi : FermionicPrimeState P) : ℤ :=
  fermionParity P psi

/-- Mobius equals finite fermion parity on represented square-free prime-bit states. -/
theorem finite_mobius_eq_fermionParity
    (P : FermionicPrimeRegister)
    (psi : FermionicPrimeState P) :
    ArithmeticFunction.moebius (representedSquarefreeNat P psi) =
      finiteFermionParity P psi := by
  exact mobius_eq_fermionParity P psi

/-- Finite Witten-index cancellation over a nonempty prime register. -/
theorem finite_wittenIndex_cancel
    (P : FermionicPrimeRegister)
    (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 :=
  finiteBooleanWittenIndex_cancel P hP

/-! ## SUSY vacuum packet -/

/--
Prime SUSY vacuum packet.

The infinite, spectral, and topological assertions are explicit fields. This
keeps the module proof-safe: assembling a packet requires supplying the laws
rather than manufacturing global theorems in this file.
-/
@[socket_debt_tag]
structure PrimeSUSYVacuumPacket
    (CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout
      VacuumReadout : Type) where
  /-- Mertens/random-walk defect boundary witness. -/
  mertensBoundary :
    MertensDefectBoundary

  /-- Protected zero-mode packet downstream of the defect-free Lee--Yang limit. -/
  zeroModeProtection :
    ZeroModeProtectionPacket
      CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout

  /-- Extra readout for the SUSY vacuum state. -/
  vacuumReadout :
    VacuumReadout

  /-- Witten-index law for the SUSY vacuum lane. -/
  wittenIndex_True : Prop

  /-- Boson/fermion pairing and cancellation law away from zero energy. -/
  bosonFermionCancellation_True : Prop

  /-- Zero macroscopic vacuum energy law. -/
  zeroVacuumEnergy_True : Prop

  /-- Unbroken arithmetic SUSY law. -/
  unbrokenSUSY_True : Prop

  /--
  Equivalence law between unbroken SUSY and the Mertens/LDP defect boundary in
  the chosen analytic model.
  -/
  unbrokenSUSY_iff_mertensBoundary_True : Prop

  /--
  Conditional spectral law: protected SUSY zero modes match the completed-`xi`
  zero readout.
  -/
  susyZeroModes_eq_completedXiZeros_True : Prop

  /-- Guardrail law: this packet does not prove RH unconditionally. -/
  no_unconditional_RH_claim : Prop

  /-- Guardrail law: the Witten/inverse-zeta channel is not itself the `xi` determinant. -/
  wittenIndex_not_completedXiDeterminant : Prop

namespace PrimeSUSYVacuumPacket

variable {CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout
    VacuumReadout : Type}
variable
  (_S : PrimeSUSYVacuumPacket
    CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout VacuumReadout)

end PrimeSUSYVacuumPacket

/--
Bridge data needed to assemble a SUSY vacuum packet from the existing Mertens
and zero-mode protection layers.
-/
structure PrimeSUSYVacuumBridge
    (VacuumReadout : Type) where
  vacuumReadout : VacuumReadout
  wittenIndex_True : Prop
  bosonFermionCancellation_True : Prop
  zeroVacuumEnergy_True : Prop
  unbrokenSUSY_True : Prop
  unbrokenSUSY_iff_mertensBoundary_True : Prop
  susyZeroModes_eq_completedXiZeros_True : Prop
  no_unconditional_RH_claim : Prop
  wittenIndex_not_completedXiDeterminant : Prop

/--
Assemble a theorem-safe SUSY vacuum packet from a Mertens boundary, a protected
zero-mode packet, and supplied SUSY bridge laws.
-/
def primeSUSYVacuum_of_zeroModeProtection
    {CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout
      VacuumReadout : Type}
    (M : MertensDefectBoundary)
    (P : ZeroModeProtectionPacket
      CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout)
    (B : PrimeSUSYVacuumBridge VacuumReadout) :
    PrimeSUSYVacuumPacket
      CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout VacuumReadout where
  mertensBoundary := M
  zeroModeProtection := P
  vacuumReadout := B.vacuumReadout
  wittenIndex_True := B.wittenIndex_True
  bosonFermionCancellation_True := B.bosonFermionCancellation_True
  zeroVacuumEnergy_True := B.zeroVacuumEnergy_True
  unbrokenSUSY_True := B.unbrokenSUSY_True
  unbrokenSUSY_iff_mertensBoundary_True := B.unbrokenSUSY_iff_mertensBoundary_True
  susyZeroModes_eq_completedXiZeros_True := B.susyZeroModes_eq_completedXiZeros_True
  no_unconditional_RH_claim := B.no_unconditional_RH_claim
  wittenIndex_not_completedXiDeterminant :=
    B.wittenIndex_not_completedXiDeterminant

/-- Owner readout: the assembled SUSY packet re-exports its supplied law predicates. -/
def primeSUSYVacuum_of_zeroModeProtection_reexports
    {CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout
      VacuumReadout : Type}
    (_M : MertensDefectBoundary)
    (_P : ZeroModeProtectionPacket
      CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout)
    (B : PrimeSUSYVacuumBridge VacuumReadout) : Prop :=
  B.wittenIndex_True ∧
    B.bosonFermionCancellation_True ∧
      B.zeroVacuumEnergy_True ∧ B.unbrokenSUSY_True ∧ B.susyZeroModes_eq_completedXiZeros_True

end InfoGeometry.Canonical.PrimeSUSYVacuum
