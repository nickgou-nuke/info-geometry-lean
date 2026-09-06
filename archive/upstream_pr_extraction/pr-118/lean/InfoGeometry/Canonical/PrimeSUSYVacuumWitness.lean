import InfoGeometry.Canonical.PrimeMertensDefectBoundary
import InfoGeometry.Canonical.PrimeSUSYVacuum
import InfoGeometry.Canonical.PrimeLeeYangLargeDeviation
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection

/-!
# InfoGeometry.Canonical.PrimeSUSYVacuumWitness

Minimal concrete data assembly for `PrimeSUSYVacuumPacket`.

This file follows the theorem-honest owner surface of
`InfoGeometry.Canonical.PrimeSUSYVacuum`: it builds only the data-only packet
and proves only definitional readback lemmas.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeSUSYVacuumWitness

open InfoGeometry.Canonical.PrimeMertensDefectBoundary
open InfoGeometry.Canonical.PrimeSUSYVacuum
open InfoGeometry.Canonical.PrimeLeeYangLargeDeviation
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.PrimeLeeYangZeroModeProtection

/-! ## 1. Trivial finite data -/

/-- A trivial finite Mertens defect boundary datum. -/
def trivialMertensDefectBoundary : MertensDefectBoundary :=
  (fun _ => 0, (fun _ => 1, fun _ => False))

/-- A trivial zero-mode protection packet built from supplied finite data. -/
def trivialZeroModeProtectionPacket
    {CompletedXiReadout : Type}
    (approx : LeeYangPrimeApproximation CompletedXiReadout)
    (ld : PrimeChainLargeDeviationWitness) :
    ZeroModeProtectionPacket CompletedXiReadout :=
  { approximation := approx
    largeDeviation := ld }

/-! ## 2. Main assembly -/

/-- Assemble the data-only prime SUSY vacuum packet from trivial finite data. -/
def trivialPrimeSUSYVacuumPacket
    {CompletedXiReadout : Type}
    (approx : LeeYangPrimeApproximation CompletedXiReadout)
    (ld : PrimeChainLargeDeviationWitness) :
    PrimeSUSYVacuumPacket CompletedXiReadout Unit :=
  primeSUSYVacuum_of_zeroModeProtection
    trivialMertensDefectBoundary
    (trivialZeroModeProtectionPacket approx ld)
    ()

/-! ## 3. Definitional readback lemmas -/

@[simp] theorem trivialPrimeSUSYVacuumPacket_mertensBoundary
    {CompletedXiReadout : Type}
    (approx : LeeYangPrimeApproximation CompletedXiReadout)
    (ld : PrimeChainLargeDeviationWitness) :
    (trivialPrimeSUSYVacuumPacket approx ld).mertensBoundary =
      trivialMertensDefectBoundary := rfl

@[simp] theorem trivialPrimeSUSYVacuumPacket_zeroModeProtection
    {CompletedXiReadout : Type}
    (approx : LeeYangPrimeApproximation CompletedXiReadout)
    (ld : PrimeChainLargeDeviationWitness) :
    (trivialPrimeSUSYVacuumPacket approx ld).zeroModeProtection =
      trivialZeroModeProtectionPacket approx ld := rfl

@[simp] theorem trivialPrimeSUSYVacuumPacket_vacuumReadout
    {CompletedXiReadout : Type}
    (approx : LeeYangPrimeApproximation CompletedXiReadout)
    (ld : PrimeChainLargeDeviationWitness) :
    (trivialPrimeSUSYVacuumPacket approx ld).vacuumReadout = () := rfl

@[simp] theorem trivialPrimeSUSYVacuumPacket_approximation
    {CompletedXiReadout : Type}
    (approx : LeeYangPrimeApproximation CompletedXiReadout)
    (ld : PrimeChainLargeDeviationWitness) :
    (trivialPrimeSUSYVacuumPacket approx ld).approximation = approx := rfl

@[simp] theorem trivialPrimeSUSYVacuumPacket_largeDeviation
    {CompletedXiReadout : Type}
    (approx : LeeYangPrimeApproximation CompletedXiReadout)
    (ld : PrimeChainLargeDeviationWitness) :
    (trivialPrimeSUSYVacuumPacket approx ld).largeDeviation = ld := rfl

end PrimeSUSYVacuumWitness
