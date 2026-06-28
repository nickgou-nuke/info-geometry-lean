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

/-- Finite Witten-index sum over all fermionic prime subsets. -/
def finiteWittenIndexSum (P : FermionicPrimeRegister) : ℤ :=
  ∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card

/-- Lemma 1: the finite Witten-index sum is exactly the powerset parity sum. -/
theorem finiteWittenIndexSum_eq_powerset_sum
    (P : FermionicPrimeRegister) :
    finiteWittenIndexSum P =
      ∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card := by
  rfl

/-- Lemma 2: a nonempty finite fermion register has a cancelling parity powerset sum. -/
theorem powerset_parity_sum_cancel_of_nonempty
    (P : FermionicPrimeRegister)
    (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 := by
  exact finiteBooleanWittenIndex_cancel P hP

/-- Lemma 3: therefore the named finite Witten-index sum vanishes. -/
theorem finiteWittenIndexSum_cancel_of_nonempty
    (P : FermionicPrimeRegister)
    (hP : P.primes.Nonempty) :
    finiteWittenIndexSum P = 0 := by
  rw [finiteWittenIndexSum_eq_powerset_sum]
  exact powerset_parity_sum_cancel_of_nonempty P hP

/-- Theorem: finite SUSY vacuum cancellation is a theorem of finite fermion parity. -/
theorem finiteSUSYVacuum_wittenIndexCancellation
    (P : FermionicPrimeRegister)
    (hP : P.primes.Nonempty) :
    finiteWittenIndexSum P = 0 ∧
      (∑ S ∈ P.primes.powerset, (-1 : ℤ) ^ S.card) = 0 := by
  exact ⟨finiteWittenIndexSum_cancel_of_nonempty P hP,
    powerset_parity_sum_cancel_of_nonempty P hP⟩

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

  /-- Predicate expressing the Witten-index law for a vacuum readout. -/
  IsWittenIndex : VacuumReadout → Prop

  /-- Predicate expressing boson/fermion pairing away from zero energy. -/
  BosonFermionCancellation : VacuumReadout → Prop

  /-- Predicate expressing zero macroscopic vacuum energy. -/
  ZeroVacuumEnergy : VacuumReadout → Prop

  /-- Predicate expressing unbroken arithmetic SUSY. -/
  UnbrokenSUSY : VacuumReadout → Prop

  /--
  Predicate expressing the chosen model's link between unbroken SUSY and the
  Mertens/LDP defect boundary.
  -/
  UnbrokenSUSYIffMertensBoundary : VacuumReadout → MertensDefectBoundary → Prop

  /--
  Predicate expressing the conditional spectral comparison between protected
  SUSY zero modes and completed-`xi` zeros.
  -/
  SusyZeroModesMatchCompletedXiZeros :
    VacuumReadout →
      ZeroModeProtectionPacket
        CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout →
        Prop

  /-- Guardrail predicate: this packet does not prove RH unconditionally. -/
  NoUnconditionalRHClaim : VacuumReadout → Prop

  /-- Guardrail predicate: the Witten/inverse-zeta channel is not the `xi` determinant. -/
  WittenIndexNotCompletedXiDeterminant : VacuumReadout → Prop

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
    (CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout
      VacuumReadout : Type) where
  vacuumReadout : VacuumReadout
  IsWittenIndex : VacuumReadout → Prop
  BosonFermionCancellation : VacuumReadout → Prop
  ZeroVacuumEnergy : VacuumReadout → Prop
  UnbrokenSUSY : VacuumReadout → Prop
  UnbrokenSUSYIffMertensBoundary : VacuumReadout → MertensDefectBoundary → Prop
  SusyZeroModesMatchCompletedXiZeros :
    VacuumReadout →
      ZeroModeProtectionPacket
        CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout →
        Prop
  NoUnconditionalRHClaim : VacuumReadout → Prop
  WittenIndexNotCompletedXiDeterminant : VacuumReadout → Prop

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
    (B : PrimeSUSYVacuumBridge
      CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout VacuumReadout) :
    PrimeSUSYVacuumPacket
      CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout VacuumReadout where
  mertensBoundary := M
  zeroModeProtection := P
  vacuumReadout := B.vacuumReadout
  IsWittenIndex := B.IsWittenIndex
  BosonFermionCancellation := B.BosonFermionCancellation
  ZeroVacuumEnergy := B.ZeroVacuumEnergy
  UnbrokenSUSY := B.UnbrokenSUSY
  UnbrokenSUSYIffMertensBoundary := B.UnbrokenSUSYIffMertensBoundary
  SusyZeroModesMatchCompletedXiZeros := B.SusyZeroModesMatchCompletedXiZeros
  NoUnconditionalRHClaim := B.NoUnconditionalRHClaim
  WittenIndexNotCompletedXiDeterminant := B.WittenIndexNotCompletedXiDeterminant

/--
Explicit debt: these SUSY/spectral interpretation predicates need concrete
owners.  The finite Witten-index cancellation above is proved; this bridge is
not.
-/
theorem primeSUSYVacuum_of_zeroModeProtection_reexports
    {CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout
      VacuumReadout : Type}
    (M : MertensDefectBoundary)
    (P : ZeroModeProtectionPacket
      CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout)
    (B : PrimeSUSYVacuumBridge
      CompletedXiReadout Hamiltonian ZeroMode ZeroReadout ProtectionReadout VacuumReadout) :
    B.IsWittenIndex B.vacuumReadout →
      B.BosonFermionCancellation B.vacuumReadout →
        B.ZeroVacuumEnergy B.vacuumReadout →
          B.UnbrokenSUSY B.vacuumReadout →
            B.UnbrokenSUSYIffMertensBoundary B.vacuumReadout M →
              B.SusyZeroModesMatchCompletedXiZeros B.vacuumReadout P →
    B.IsWittenIndex B.vacuumReadout ∧
      B.BosonFermionCancellation B.vacuumReadout ∧
        B.ZeroVacuumEnergy B.vacuumReadout ∧
          B.UnbrokenSUSY B.vacuumReadout ∧
            B.UnbrokenSUSYIffMertensBoundary B.vacuumReadout M ∧
              B.SusyZeroModesMatchCompletedXiZeros B.vacuumReadout P := by
  intro hWitten hCancel hZero hSUSY hBoundary hModes
  exact ⟨hWitten, ⟨hCancel, ⟨hZero, ⟨hSUSY, ⟨hBoundary, hModes⟩⟩⟩⟩⟩

end InfoGeometry.Canonical.PrimeSUSYVacuum
