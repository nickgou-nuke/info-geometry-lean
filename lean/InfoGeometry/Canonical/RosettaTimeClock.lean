import InfoGeometry.Canonical.HolographicEntanglementSymmetry
import InfoGeometry.Arithmetic.PrimeParafermionGrandCanonicalClock


/-!
# RosettaTimeClock

Research-facing façade for the positive-branch thermal-time/monodromy clock.

This file does not introduce new axioms or global identifications. It re-exports
both:

* the theorem-honest forward-time/holographic capstone surface already proved in
  `HolographicEntanglementSymmetry`; and
* the arithmetic parafermion clock bridge showing how the `κ`-truncated
  log-partition / Massieu readout plugs into that same positive-branch thermal
  time theorem surface.
-/

noncomputable section

namespace InfoGeometry.Canonical.RosettaTimeClock

export InfoGeometry.Canonical.HolographicEntanglementSymmetry (
  ForwardTimeHolographicTrialityPacket
  canonical_forward_time_holographic_triality_packet
  forward_time_equals_positive_winding_readout
  sector_forward_time_triality_readout
  positive_branch_time_clock_theorem
  thermal_time_is_positive_branch_monodromy_clock
  time_is_positive_branch_winding
)


export InfoGeometry.Arithmetic.PrimeParafermionGrandCanonicalClock (
  LogQClockCalibration
)

namespace PrimeParafermionRosettaBridge

open InfoGeometry.Arithmetic.PrimeParafermionGrandCanonicalClock

open InfoGeometry.Canonical.YangMillsContinuum
open InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData
open InfoGeometry.Canonical.TrialitySpin8Permutations
open InfoGeometry.Canonical.HolographicEntanglementSymmetry
open InfoGeometry.Canonical.RyuTakayanagiEntanglementBridge
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy

/--
Rosetta-facing readout: once the parafermion Massieu potential is calibrated as
`log Q`, the same positive-branch theorem surface reads its modular evolution as
thermal time.
-/
theorem parafermion_massieu_reads_as_rosetta_time
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E))
    {s : TrialitySector}
    {n N : ℕ} {A : EndH E}
    (P : ForwardTimeHolographicTrialityPacket (E := E) B s n N A) :
    modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding (n : ℤ)) A =
        B.modularData.toAdditiveModularFlow (B.calibration.timeOfWinding (n : ℤ)) A ∧
      ((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z) = logarithmicPhase (n : ℤ) ∧
      Complex.exp (((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z)) = (1 : ℂ) ∧
      subtreeEntropy n = minimalSurfaceArea n / (4 * effectiveNewtonConstant) := by
  exact positive_branch_time_clock_theorem (B := B) P

/--
Rosetta-facing semantic capstone: the `κ`-truncated parafermion Massieu
log-generator feeds the same positive-branch winding clock.
-/
theorem parafermion_statistics_are_read_by_positive_branch_time
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E))
    {s : TrialitySector}
    {n N : ℕ} {A : EndH E}
    (P : ForwardTimeHolographicTrialityPacket (E := E) B s n N A) :
    modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding (n : ℤ)) A =
        B.modularData.toAdditiveModularFlow (B.calibration.timeOfWinding (n : ℤ)) A ∧
      ((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z) = logarithmicPhase (n : ℤ) ∧
      Complex.exp (((n : ℤ) : ℂ) * (∮ z in C((0 : ℂ), B.radius), poleForm z)) = (1 : ℂ) := by
  exact thermal_time_is_positive_branch_monodromy_clock (B := B) P

/--
Canonical arithmetic Rosetta bridge: a calibrated finite prime parafermion
partition feeds the same positive-branch thermal-time clock, now read directly
through the chosen `d log Q` one-form.
-/
theorem parafermion_logQ_reads_as_rosetta_time
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {S : Finset Nat.Primes} {z s0 : ℂ} {κ : ℕ}
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E))
    (C : LogQClockCalibration S z s0 κ)
    {s : TrialitySector}
    {n N : ℕ} {A : EndH E}
    (P : ForwardTimeHolographicTrialityPacket (E := E) B s n N A) :
    Complex.log C.Q = InfoGeometry.Arithmetic.PrimeParafermionGrandCanonicalClock.parafermionMassieu S z s0 κ ∧
      modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding (n : ℤ)) A =
        B.modularData.toAdditiveModularFlow (B.calibration.timeOfWinding (n : ℤ)) A ∧
      (((n : ℤ) : ℂ) * (∮ w in C((0 : ℂ), B.radius), C.dlogQ w)) = logarithmicPhase (n : ℤ) ∧
      Complex.exp ((((n : ℤ) : ℂ) * (∮ w in C((0 : ℂ), B.radius), C.dlogQ w))) = (1 : ℂ) ∧
      subtreeEntropy n = minimalSurfaceArea n / (4 * effectiveNewtonConstant) := by
  refine ⟨C.logQ_eq_massieu, ?_, ?_, ?_, ?_⟩
  · exact (positive_branch_time_clock_theorem (B := B) P).1
  · exact C.dlogQ_deRhamClass_of_winding B.radius B.radius_pos (n : ℤ)
  · exact C.positive_branch_time_clock B.radius B.radius_pos n
  · exact (positive_branch_time_clock_theorem (B := B) P).2.2.2

/--
Capstone wording: Rosetta thermal time reads the modular flow of the arithmetic
`κ`-parafermion gas through the winding of its calibrated Massieu differential.
-/
theorem parafermion_massieu_differential_drives_rosetta_time
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {S : Finset Nat.Primes} {z s0 : ℂ} {κ : ℕ}
    (B : ThermalTimeMonodromyBridge.BridgeData (E := E))
    (C : LogQClockCalibration S z s0 κ)
    {s : TrialitySector}
    {n N : ℕ} {A : EndH E}
    (P : ForwardTimeHolographicTrialityPacket (E := E) B s n N A) :
    modularAutomorphismGroup B.modularData (B.calibration.timeOfWinding (n : ℤ)) A =
        B.modularData.toAdditiveModularFlow (B.calibration.timeOfWinding (n : ℤ)) A ∧
      (((n : ℤ) : ℂ) * (∮ w in C((0 : ℂ), B.radius), C.dlogQ w)) = logarithmicPhase (n : ℤ) ∧
      Complex.exp ((((n : ℤ) : ℂ) * (∮ w in C((0 : ℂ), B.radius), C.dlogQ w))) = (1 : ℂ) := by
  exact ⟨
    (parafermion_logQ_reads_as_rosetta_time (B := B) C P).2.1,
    (parafermion_logQ_reads_as_rosetta_time (B := B) C P).2.2.1,
    (parafermion_logQ_reads_as_rosetta_time (B := B) C P).2.2.2.1
  ⟩

end PrimeParafermionRosettaBridge

end InfoGeometry.Canonical.RosettaTimeClock
