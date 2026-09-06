import InfoGeometry.Arithmetic.PrimeSuperalgebraReadback
import InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection

/-!
# InfoGeometry.Canonical.PrimeSUSYVacuum

Theorem-honest SUSY vacuum owner for the prime Lee--Yang architecture.

This module keeps only genuine finite arithmetic theorems and a data-only
assembly packet:

* finite Möbius/fermion-parity readback is owned by
  `InfoGeometry.Arithmetic.PrimeSuperalgebraReadback`;
* defect-free Lee--Yang approximation data are owned by
  `InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection`.

This file does not store arbitrary SUSY/RH/`xi`-zero laws as packet fields and
does not claim a completed-`xi` determinant identity.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeSUSYVacuum

open InfoGeometry.Arithmetic.PrimeSuperalgebraReadback
open InfoGeometry.Canonical.PrimeMertensDefectBoundary
open InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection

/-! ## 1. Finite arithmetic parity readback -/

/-- Finite fermion parity readout from the arithmetic prime-superalgebra layer. -/
abbrev finiteFermionParity
    (P : FermionicPrimeRegister)
    (psi : FermionicPrimeState P) : ℤ :=
  fermionParity P psi

/-- Möbius equals finite fermion parity on represented square-free prime-bit states. -/
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

/-- Finite divisor Möbius cancellation over a nonempty prime register. -/
theorem finite_divisorMobius_cancel
    (P : FermionicPrimeRegister)
    (hP : P.primes.Nonempty) :
    (∑ S ∈ P.primes.powerset,
      ArithmeticFunction.moebius (∏ p ∈ S, p)) = 0 :=
  finiteDivisorMobius_cancel P hP

/-! ## 2. Data-only SUSY vacuum assembly -/

/--
Data-only prime SUSY vacuum packet.

It combines the Mertens/random-walk defect boundary, the defect-free zero-mode
protection packet, and an extra vacuum readout. No grand SUSY/RH/`xi` laws are
stored here; those remain separate theorem obligations in their concrete owner
files.
-/
structure PrimeSUSYVacuumPacket
    (CompletedXiReadout VacuumReadout : Type) where
  /-- Mertens/random-walk defect boundary data. -/
  mertensBoundary : MertensDefectBoundary
  /-- Defect-free Lee--Yang zero-mode protection data. -/
  zeroModeProtection : ZeroModeProtectionPacket CompletedXiReadout
  /-- Extra vacuum-sector readout. -/
  vacuumReadout : VacuumReadout

namespace PrimeSUSYVacuumPacket

variable {CompletedXiReadout VacuumReadout : Type}

/-- The Lee--Yang approximation carried by the SUSY vacuum packet. -/
def approximation
    (S : PrimeSUSYVacuumPacket CompletedXiReadout VacuumReadout) :
    InfoGeometry.Canonical.CayleyCriticalLineCircleBridge.LeeYangPrimeApproximation
      CompletedXiReadout :=
  S.zeroModeProtection.approximation

/-- The large-deviation witness carried by the SUSY vacuum packet. -/
def largeDeviation
    (S : PrimeSUSYVacuumPacket CompletedXiReadout VacuumReadout) :
    InfoGeometry.Canonical.PrimeLeeYangLargeDeviation.PrimeChainLargeDeviationWitness :=
  S.zeroModeProtection.largeDeviation

variable (S : PrimeSUSYVacuumPacket CompletedXiReadout VacuumReadout)

@[simp] theorem approximation_eq :
    S.approximation = S.zeroModeProtection.approximation := rfl

@[simp] theorem largeDeviation_eq :
    S.largeDeviation = S.zeroModeProtection.largeDeviation := rfl

end PrimeSUSYVacuumPacket

/--
Assemble a prime SUSY vacuum packet from a Mertens boundary, a defect-free
zero-mode packet, and an auxiliary vacuum readout.
-/
def primeSUSYVacuum_of_zeroModeProtection
    {CompletedXiReadout VacuumReadout : Type}
    (M : MertensDefectBoundary)
    (P : ZeroModeProtectionPacket CompletedXiReadout)
    (R : VacuumReadout) :
    PrimeSUSYVacuumPacket CompletedXiReadout VacuumReadout where
  mertensBoundary := M
  zeroModeProtection := P
  vacuumReadout := R

@[simp] theorem primeSUSYVacuum_of_zeroModeProtection_mertensBoundary
    {CompletedXiReadout VacuumReadout : Type}
    (M : MertensDefectBoundary)
    (P : ZeroModeProtectionPacket CompletedXiReadout)
    (R : VacuumReadout) :
    (primeSUSYVacuum_of_zeroModeProtection M P R).mertensBoundary = M := rfl

@[simp] theorem primeSUSYVacuum_of_zeroModeProtection_zeroModeProtection
    {CompletedXiReadout VacuumReadout : Type}
    (M : MertensDefectBoundary)
    (P : ZeroModeProtectionPacket CompletedXiReadout)
    (R : VacuumReadout) :
    (primeSUSYVacuum_of_zeroModeProtection M P R).zeroModeProtection = P := rfl

@[simp] theorem primeSUSYVacuum_of_zeroModeProtection_vacuumReadout
    {CompletedXiReadout VacuumReadout : Type}
    (M : MertensDefectBoundary)
    (P : ZeroModeProtectionPacket CompletedXiReadout)
    (R : VacuumReadout) :
    (primeSUSYVacuum_of_zeroModeProtection M P R).vacuumReadout = R := rfl

end PrimeSUSYVacuum
