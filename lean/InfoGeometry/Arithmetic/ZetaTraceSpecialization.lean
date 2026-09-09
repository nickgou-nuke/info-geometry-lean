/- 
InfoGeometry/Arithmetic/ZetaTraceSpecialization.lean

Finite prime-vielbein / zeta-trace specialization.

No infinite products.
No analytic continuation.
No Ray–Singer terminology.

The finite prime cutoff gives the Weyl/Euler denominator as a parity trace.
The finite prime-gas partition is the inverse of that denominator.
The finite supervolume is the same denominator read as a volume factor.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Canonical.SouriauThermalEvaluation
import InfoGeometry.Canonical.PrimeGasPartitions

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.ZetaTraceSpecialization

open InfoGeometry.Canonical.FormalPrimeRootSystem
open InfoGeometry.Canonical.SouriauThermalEvaluation
open InfoGeometry.Canonical.PrimeGasPartitions

/-! ### 0. Finite exterior/Fock compatibility layer -/

/-- Finite exterior prime state as a subset of the cutoff prime set. -/
abbrev PrimeExteriorState (L : FormalPrimeRootLattice) : Type :=
  {S : Finset ℕ // S ⊆ L.primes}

/-- Finite exterior prime Fock space as real-valued functions on states. -/
abbrev PrimeFockSpace (L : FormalPrimeRootLattice) : Type :=
  PrimeExteriorState L → ℝ

/-- Parity sign of a finite exterior state. -/
def stateParity {L : FormalPrimeRootLattice} (S : PrimeExteriorState L) : ℤ :=
  (-1 : ℤ) ^ S.1.card

/-- Occupied-state eigenvalue of the finite prime Fock lift. -/
def stateWeight {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) (S : PrimeExteriorState L) : ℝ :=
  ∏ p ∈ S.1, E.p_neg_beta p

/-- Diagonal operator on the finite exterior prime Fock space. -/
def diagonalFockEnd
    (L : FormalPrimeRootLattice)
    (w : PrimeExteriorState L → ℝ) :
    Module.End ℝ (PrimeFockSpace L) where
  toFun ψ := fun S => w S * ψ S
  map_add' ψ φ := by
    ext S
    exact mul_add (w S) (ψ S) (φ S)
  map_smul' a ψ := by
    ext S
    exact mul_left_comm (w S) a (ψ S)

/-- The finite unnormalized thermal prime-vielbein on Fock space. -/
def thermalPrimeVielbein
    (L : FormalPrimeRootLattice)
    (E : SouriauThermalEvaluation L) :
    Module.End ℝ (PrimeFockSpace L) :=
  diagonalFockEnd L (stateWeight E)

/-! ### 1. Finite denominator and supertrace -/

/-- Finite prime-vielbein supertrace readout. -/
def finiteZetaTraceSupertrace {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) : ℝ :=
  finiteEvaluatedAlternatingSum E

/-- Finite Weyl/Euler denominator readout. -/
def finiteZetaTraceDenominator {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) : ℝ :=
  finiteEvaluatedDenominator E

/--
Finite prime-gas partition.

This is the inverse of the finite denominator.
-/
def finitePrimeGasPartition {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) : ℝ :=
  (finiteZetaTraceDenominator E)⁻¹

/-- Finite supervolume readout, identified with the Weyl/Euler denominator. -/
def finiteZetaTraceSupervolume {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) : ℝ :=
  finiteZetaTraceDenominator E

@[simp]
theorem finiteZetaTraceSupertrace_eq_supervolume
    {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) :
    finiteZetaTraceSupertrace E = finiteZetaTraceSupervolume E := by
  simp [finiteZetaTraceSupertrace, finiteZetaTraceSupervolume, finiteZetaTraceDenominator]
  exact (finite_euler_weyl_identity E).symm

@[simp]
theorem finitePrimeGasPartition_eq_denominator_inv
    {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) :
    finitePrimeGasPartition E = (finiteZetaTraceDenominator E)⁻¹ :=
  rfl

/-- Compatibility alias for the finite Fock/parity supertrace denominator. -/
theorem primeFockSupertrace_eq_finiteEulerDenominator
    {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) :
    finiteZetaTraceSupertrace E = finiteZetaTraceDenominator E := by
  simp [finiteZetaTraceSupertrace]
  exact (finite_euler_weyl_identity E).symm

/-- Finite prime Fock supertrace equals the finite Weyl/Euler denominator. -/
theorem finitePrimeSupertrace_eq_weylDenominator
    {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) :
    finiteZetaTraceSupertrace E = finiteZetaTraceDenominator E :=
  primeFockSupertrace_eq_finiteEulerDenominator E

/-- Compatibility alias for the inverse finite prime-gas partition. -/
theorem finitePrimeGasPartition_eq_supertrace_inv
    {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) :
    finitePrimeGasPartition E = (finiteZetaTraceSupertrace E)⁻¹ := by
  rw [finitePrimeGasPartition_eq_denominator_inv, primeFockSupertrace_eq_finiteEulerDenominator]

/-- Finite prime-gas partition is the inverse of the Weyl/Euler denominator. -/
theorem finitePrimeGasPartition_eq_weylDenominator_inv
    {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) :
    finitePrimeGasPartition E = (finiteZetaTraceDenominator E)⁻¹ :=
  finitePrimeGasPartition_eq_denominator_inv E

/-! ### 2. Readout package -/

/--
Finite zeta-trace readout.

The supertrace is the alternating sum, the denominator is the finite Weyl
product, the partition is its inverse, and the supervolume is the denominator
viewed as a volume factor.
-/
structure FiniteZetaTraceReadout (L : FormalPrimeRootLattice) where
  evaluation : SouriauThermalEvaluation L
  supertraceReadout : ℝ
  denominatorReadout : ℝ
  partitionReadout : ℝ
  supervolumeReadout : ℝ
  supertrace_eq_denominator : supertraceReadout = denominatorReadout
  partition_eq_denominator_inv : partitionReadout = denominatorReadout⁻¹
  supervolume_eq_denominator : supervolumeReadout = denominatorReadout

namespace FiniteZetaTraceReadout

variable {L : FormalPrimeRootLattice}

/-- Canonical finite zeta-trace readout. -/
def canonical (E : SouriauThermalEvaluation L) : FiniteZetaTraceReadout L where
  evaluation := E
  supertraceReadout := finiteZetaTraceSupertrace E
  denominatorReadout := finiteZetaTraceDenominator E
  partitionReadout := finitePrimeGasPartition E
  supervolumeReadout := finiteZetaTraceSupervolume E
  supertrace_eq_denominator := by
    simp [finiteZetaTraceSupertrace, finiteZetaTraceDenominator]
    exact (finite_euler_weyl_identity E).symm
  partition_eq_denominator_inv := rfl
  supervolume_eq_denominator := rfl

@[simp]
theorem canonical_supertrace_eq_denominator
    (E : SouriauThermalEvaluation L) :
    (canonical E).supertraceReadout = (canonical E).denominatorReadout :=
  (canonical E).supertrace_eq_denominator

@[simp]
theorem canonical_partition_eq_denominator_inv
    (E : SouriauThermalEvaluation L) :
    (canonical E).partitionReadout = ((canonical E).denominatorReadout)⁻¹ :=
  (canonical E).partition_eq_denominator_inv

@[simp]
theorem canonical_supervolume_eq_denominator
    (E : SouriauThermalEvaluation L) :
    (canonical E).supervolumeReadout = (canonical E).denominatorReadout :=
  (canonical E).supervolume_eq_denominator

end FiniteZetaTraceReadout

/-- Finite negative log-supervolume potential. -/
def finiteZetaTraceEffectiveAction {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L)
    (_hpos : 0 < finiteZetaTraceSupervolume E) : ℝ :=
  - Real.log (finiteZetaTraceSupervolume E)

@[simp]
theorem finiteZetaTraceEffectiveAction_def
    {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L)
    (hpos : 0 < finiteZetaTraceSupervolume E) :
    finiteZetaTraceEffectiveAction E hpos =
      - Real.log (finiteZetaTraceSupervolume E) :=
  rfl

end InfoGeometry.Arithmetic.ZetaTraceSpecialization
