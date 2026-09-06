/-
InfoGeometry/Arithmetic/ArithmeticKMS.lean

Witness-gated KMS sockets for the finite arithmetic/Riemann-gas sidecar.

This module does not prove the Bost-Connes theorem, KMS existence/uniqueness,
spontaneous symmetry breaking, the prime number theorem, or a global
Tomita-Takesaki theorem.  It packages finite arithmetic Gibbs weights,
projective temperatures, modular-flow readouts, and model-supplied KMS
certificates as proof-carrying data.
-/

import InfoGeometry.Arithmetic.ProjectivePrimePartition
import InfoGeometry.Arithmetic.ProjectiveWeylGauge
import InfoGeometry.Thermodynamics.SouriauTemperatureProjective

noncomputable section

namespace InfoGeometry.Arithmetic.ArithmeticKMS

open InfoGeometry.Arithmetic
open InfoGeometry.Arithmetic.ProjectivePrimePartition
open InfoGeometry.Arithmetic.ProjectiveWeylGauge
open InfoGeometry.Thermodynamics
open InfoGeometry.Thermodynamics.ProjectiveTemperature

/-! ## 1. Finite arithmetic Gibbs/KMS readouts -/

/--
Finite arithmetic Gibbs weight at inverse temperature `β`.

This is exactly the guarded Mellin kernel `n ↦ n^(-β)` from
`PrimitiveSetsAbove`.
-/
def arithmeticGibbsWeight (β : ℝ) (n : ℕ) : ℝ :=
  primitiveMellinKernel n β

/-- Finite arithmetic Gibbs partition on a chosen support. -/
def arithmeticGibbsPartition (A : Finset ℕ) (β : ℝ) : ℝ :=
  Finset.sum A (fun n => arithmeticGibbsWeight β n)

/-- Projective-temperature Gibbs weight, evaluated at `β = u⁻¹`. -/
def projectiveArithmeticGibbsWeight (u : ℝ) (n : ℕ) : ℝ :=
  arithmeticGibbsWeight (betaInvert u) n

/-- Projective-temperature Gibbs partition on a chosen finite support. -/
def projectiveArithmeticGibbsPartition (A : Finset ℕ) (u : ℝ) : ℝ :=
  arithmeticGibbsPartition A (betaInvert u)

/-- Arithmetic Gibbs weights are nonnegative. -/
theorem arithmeticGibbsWeight_nonneg (β : ℝ) (n : ℕ) :
    0 ≤ arithmeticGibbsWeight β n :=
  primitiveMellinKernel_nonneg n β

/-- Arithmetic Gibbs partitions on finite supports are nonnegative. -/
theorem arithmeticGibbsPartition_nonneg (A : Finset ℕ) (β : ℝ) :
    0 ≤ arithmeticGibbsPartition A β := by
  unfold arithmeticGibbsPartition
  refine Finset.sum_nonneg ?_
  intro n hn
  exact arithmeticGibbsWeight_nonneg β n

/-- Projective arithmetic Gibbs partitions are nonnegative. -/
theorem projectiveArithmeticGibbsPartition_nonneg (A : Finset ℕ) (u : ℝ) :
    0 ≤ projectiveArithmeticGibbsPartition A u :=
  arithmeticGibbsPartition_nonneg A (betaInvert u)

/-- In the compact cold sector `u ∈ (0, 1)`, the corresponding `β` satisfies `1 < β`. -/
theorem one_lt_beta_of_projective_cold {u : ℝ}
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    1 < betaInvert u :=
  one_lt_betaInvert_of_mem_Ioo_zero_one hu

/-! ## 2. Phase labels as conservative data -/

/--
Finite phase label for the arithmetic KMS sidecar.

These are labels for model routing and certificates, not theorems asserting
phase transition or uniqueness.
-/
inductive ArithmeticKMSPhase where
  /-- Hot/critical side, usually represented by `β ≤ 1`. -/
  | hotOrCritical
  /-- Cold finite side, represented in this sidecar by `1 < β`. -/
  | cold
deriving DecidableEq, Repr

/-- Predicate assigning a conservative phase label to a finite inverse temperature. -/
def PhaseAtBeta (β : ℝ) : ArithmeticKMSPhase → Prop
  | ArithmeticKMSPhase.hotOrCritical => β ≤ 1
  | ArithmeticKMSPhase.cold => 1 < β

/-- Predicate assigning a conservative phase label to compact projective temperature. -/
def PhaseAtProjectiveTemperature (u : ℝ) : ArithmeticKMSPhase → Prop :=
  PhaseAtBeta (betaInvert u)

/-- Compact temperatures `u ∈ (0,1)` lie in the cold finite side. -/
theorem cold_phase_of_projective_Ioo
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    PhaseAtProjectiveTemperature u ArithmeticKMSPhase.cold :=
  one_lt_beta_of_projective_cold hu

/-! ## 3. Witness-gated modular/KMS socket -/

/--
Finite arithmetic KMS witness.

`State` is an arbitrary model carrier.  The KMS law is supplied as a predicate
and certificate rather than derived from AQFT or a C*-dynamical system.
-/
structure ArithmeticKMSWitness
    (State : Type*) where
  /-- Encode a finite arithmetic support as a model state. -/
  stateOfFinset : Finset ℕ → State

  /-- Model-specific modular-flow readout. -/
  modularFlowReadout : State → ℝ → ℝ

  /-- Model-specific equilibrium/KMS predicate. -/
  IsKMSAt : State → ℝ → Prop

  /-- Gibbs partition calibration on finite supports. -/
  modularFlow_eq_gibbsPartition :
    ∀ A : Finset ℕ, ∀ β : ℝ,
      modularFlowReadout (stateOfFinset A) β =
        arithmeticGibbsPartition A β

  /-- Supplied KMS certificate for the encoded finite support at `β`. -/
  kms_certificate :
    ∀ A : Finset ℕ, ∀ β : ℝ,
      IsKMSAt (stateOfFinset A) β

namespace ArithmeticKMSWitness

variable {State : Type*}
variable (K : ArithmeticKMSWitness State)

/-- Re-export the finite Gibbs partition calibration. -/
theorem modularFlowReadout_eq_gibbsPartition
    (A : Finset ℕ) (β : ℝ) :
    K.modularFlowReadout (K.stateOfFinset A) β =
      arithmeticGibbsPartition A β :=
  K.modularFlow_eq_gibbsPartition A β

/-- Encoded finite supports are KMS at the supplied inverse temperature. -/
theorem isKMSAt
    (A : Finset ℕ) (β : ℝ) :
    K.IsKMSAt (K.stateOfFinset A) β :=
  K.kms_certificate A β

/-- The calibrated modular-flow readout is nonnegative. -/
theorem modularFlowReadout_nonneg
    (A : Finset ℕ) (β : ℝ) :
    0 ≤ K.modularFlowReadout (K.stateOfFinset A) β := by
  rw [K.modularFlow_eq_gibbsPartition A β]
  exact arithmeticGibbsPartition_nonneg A β

end ArithmeticKMSWitness

/-! ## 4. Projective KMS witness -/

/--
Projective-temperature version of the finite arithmetic KMS witness.

The compact variable `u` is restricted by explicit hypotheses in the theorem
payload.  No global analytic continuation through the critical point is
claimed.
-/
structure ProjectiveArithmeticKMSWitness
    (State : Type*) where
  /-- Encode a finite arithmetic support as a model state. -/
  stateOfFinset : Finset ℕ → State

  /-- Model-specific modular-flow readout in compact temperature. -/
  projectiveModularFlowReadout : State → ℝ → ℝ

  /-- Model-specific projective KMS predicate. -/
  IsProjectiveKMSAt : State → ℝ → Prop

  /-- Projective Gibbs partition calibration on finite supports. -/
  projectiveFlow_eq_gibbsPartition :
    ∀ A : Finset ℕ, ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 →
      projectiveModularFlowReadout (stateOfFinset A) u =
        projectiveArithmeticGibbsPartition A u

  /-- Supplied projective KMS certificate in the compact cold sector. -/
  projective_kms_certificate :
    ∀ A : Finset ℕ, ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 →
      IsProjectiveKMSAt (stateOfFinset A) u

namespace ProjectiveArithmeticKMSWitness

variable {State : Type*}
variable (K : ProjectiveArithmeticKMSWitness State)

/-- Re-export the projective Gibbs partition calibration. -/
theorem projectiveModularFlowReadout_eq_gibbsPartition
    (A : Finset ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    K.projectiveModularFlowReadout (K.stateOfFinset A) u =
      projectiveArithmeticGibbsPartition A u :=
  K.projectiveFlow_eq_gibbsPartition A u hu

/-- Encoded finite supports are projective KMS in the compact cold sector. -/
theorem isProjectiveKMSAt
    (A : Finset ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    K.IsProjectiveKMSAt (K.stateOfFinset A) u :=
  K.projective_kms_certificate A u hu

/-- The calibrated projective modular-flow readout is nonnegative. -/
theorem projectiveModularFlowReadout_nonneg
    (A : Finset ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ K.projectiveModularFlowReadout (K.stateOfFinset A) u := by
  rw [K.projectiveFlow_eq_gibbsPartition A u hu]
  exact projectiveArithmeticGibbsPartition_nonneg A u

end ProjectiveArithmeticKMSWitness

/-! ## 5. Prime/projective-flow compatibility -/

/--
Compatibility between a projective KMS witness and the finite von Mangoldt
prime-flow calibration.
-/
structure ProjectiveKMSPrimeCompatibility
    (State : Type*) where
  /-- Projective arithmetic KMS witness. -/
  kms : ProjectiveArithmeticKMSWitness State

  /-- Projective prime-flow calibration. -/
  prime : ProjectivePrimeCalibration State

  /-- The two encodings agree on finite supports. -/
  state_agrees :
    ∀ A : Finset ℕ,
      prime.stateOfFinset A = kms.stateOfFinset A

  /--
  Supplied compatibility between the prime modular-flow readout and the KMS
  projective readout.  This is model data, not an analytic theorem.
  -/
  prime_flow_eq_kms_flow :
    ∀ A : Finset ℕ, ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 →
      prime.modularFlowReadout (prime.stateOfFinset A) u =
        kms.projectiveModularFlowReadout (kms.stateOfFinset A) u

namespace ProjectiveKMSPrimeCompatibility

variable {State : Type*}
variable (C : ProjectiveKMSPrimeCompatibility State)

/-- Prime flow and projective KMS flow agree by the supplied compatibility law. -/
theorem primeFlow_eq_kmsFlow
    (A : Finset ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    C.prime.modularFlowReadout (C.prime.stateOfFinset A) u =
      C.kms.projectiveModularFlowReadout (C.kms.stateOfFinset A) u :=
  C.prime_flow_eq_kms_flow A u hu

/-- The compatible prime flow is nonnegative in the compact cold sector. -/
theorem primeFlow_nonneg
    (A : Finset ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ C.prime.modularFlowReadout (C.prime.stateOfFinset A) u := by
  rw [C.primeFlow_eq_kmsFlow A hu]
  exact C.kms.projectiveModularFlowReadout_nonneg A hu

end ProjectiveKMSPrimeCompatibility

end InfoGeometry.Arithmetic.ArithmeticKMS
