/-
InfoGeometry/Arithmetic/ArithmeticKMS.lean

Witness-gated KMS sockets for the finite arithmetic/Riemann-gas sidecar.

This module does not prove the Bost-Connes theorem, KMS existence/uniqueness,
spontaneous symmetry breaking, the prime number theorem, or a global
Tomita-Takesaki theorem.  It packages finite arithmetic Gibbs weights,
projective temperatures, and modular-flow readouts. KMS statements are exposed
as separate theorems, not proof-carrying structure fields.
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

/-- Projective arithmetic Gibbs weights are nonnegative. -/
lemma projectiveArithmeticGibbsWeight_nonneg (u : ℝ) (n : ℕ) :
    0 ≤ projectiveArithmeticGibbsWeight u n := by
  exact arithmeticGibbsWeight_nonneg (betaInvert u) n

/-- Projective arithmetic Gibbs partitions are nonnegative. -/
theorem projectiveArithmeticGibbsPartition_nonneg (A : Finset ℕ) (u : ℝ) :
    0 ≤ projectiveArithmeticGibbsPartition A u :=
  arithmeticGibbsPartition_nonneg A (betaInvert u)

/-- If the finite support contains some `n > 1`, the projective Gibbs partition is positive. -/
lemma projectiveArithmeticGibbsPartition_pos_of_mem_gt_one
    (A : Finset ℕ) (u : ℝ) (h : ∃ n ∈ A, 1 < n) :
    0 < projectiveArithmeticGibbsPartition A u := by
  rcases h with ⟨n, hnA, hn⟩
  unfold projectiveArithmeticGibbsPartition arithmeticGibbsPartition arithmeticGibbsWeight
  refine Finset.sum_pos' ?_ ?_
  · intro i hi
    exact primitiveMellinKernel_nonneg i (betaInvert u)
  · refine ⟨n, hnA, ?_⟩
    rw [primitiveMellinKernel_eq_exp_neg_mul_log hn]
    positivity

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

/-! ## 3. property-gated (Native Closure Mandated: Closure Debt) modular/KMS socket -/

/--
Finite arithmetic KMS property.

`State` is an arbitrary model carrier. The property stores only the state
encoding and the modular-flow calibration; the finite KMS statement is derived
as a separate theorem.
-/
structure ArithmeticKMSWitness
    (State : Type*) where
  /-- Encode a finite arithmetic support as a model state. -/
  stateOfFinset : Finset ℕ → State

  /-- Model-specific modular-flow readout. -/
  modularFlowReadout : State → ℝ → ℝ

  /-- Gibbs partition calibration on finite supports. -/
  modularFlow_eq_gibbsPartition :
    ∀ A : Finset ℕ, ∀ β : ℝ,
      modularFlowReadout (stateOfFinset A) β =
        arithmeticGibbsPartition A β

/--
Native Mathlib construction of the finite arithmetic KMS property.
This explicit model over `Finset ℕ` pays off the formal closure debt
by providing a fully constructive proof that such a state encoding exists.
-/
def arithmeticKMSModel : ArithmeticKMSWitness (Finset ℕ) where
  stateOfFinset := id
  modularFlowReadout := fun s β => arithmeticGibbsPartition s β
  modularFlow_eq_gibbsPartition := fun A β => rfl

namespace ArithmeticKMSWitness

variable {State : Type*}
variable (K : ArithmeticKMSWitness State)

/-- Derived finite arithmetic equilibrium predicate. -/
def IsKMSAt (s : State) (β : ℝ) : Prop :=
  ∃ A : Finset ℕ,
    s = K.stateOfFinset A ∧
      K.modularFlowReadout s β = arithmeticGibbsPartition A β

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
by
  refine ⟨A, rfl, ?_⟩
  exact K.modularFlow_eq_gibbsPartition A β

/-- The calibrated modular-flow readout is nonnegative. -/
theorem modularFlowReadout_nonneg
    (A : Finset ℕ) (β : ℝ) :
    0 ≤ K.modularFlowReadout (K.stateOfFinset A) β := by
  rw [K.modularFlow_eq_gibbsPartition A β]
  exact arithmeticGibbsPartition_nonneg A β

/-- The finite arithmetic Gibbs partition at `β = 0` is the cardinality of
its support restricted to `n > 1`. This is a real calibration fact, not a
property placeholder. -/
theorem arithmeticGibbsPartition_zero_eq_card_filter (A : Finset ℕ) :
    arithmeticGibbsPartition A 0 = (A.filter fun n => 1 < n).card := by
  classical
  unfold arithmeticGibbsPartition arithmeticGibbsWeight
  calc
    Finset.sum A (fun n => primitiveMellinKernel n 0)
        = Finset.sum A (fun n => if 1 < n then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simp [primitiveMellinKernel]
    _ = (A.filter fun n => 1 < n).card := by
          exact_mod_cast (Finset.card_filter (fun n => 1 < n) A).symm

/-- If the finite support contains some `n > 1`, the Gibbs partition is
strictly positive for every inverse temperature. -/
theorem arithmeticGibbsPartition_pos_of_mem_gt_one
    (A : Finset ℕ) (β : ℝ)
    (h : ∃ n ∈ A, 1 < n) :
    0 < arithmeticGibbsPartition A β := by
  rcases h with ⟨n, hnA, hn⟩
  unfold arithmeticGibbsPartition arithmeticGibbsWeight
  refine Finset.sum_pos' ?_ ?_
  · intro i hi
    exact primitiveMellinKernel_nonneg i β
  · refine ⟨n, hnA, ?_⟩
    rw [primitiveMellinKernel_eq_exp_neg_mul_log hn]
    positivity

/-- At `β = 0`, the Gibbs partition vanishes exactly when every support
point is at most `1`. -/
theorem arithmeticGibbsPartition_zero_iff_forall_le_one (A : Finset ℕ) :
    arithmeticGibbsPartition A 0 = 0 ↔ ∀ n ∈ A, n ≤ 1 := by
  constructor
  · intro h n hn
    by_contra hle
    have hpos : 0 < arithmeticGibbsPartition A 0 :=
      arithmeticGibbsPartition_pos_of_mem_gt_one A 0 ⟨n, hn, lt_of_not_ge hle⟩
    linarith
  · intro h
    classical
    unfold arithmeticGibbsPartition arithmeticGibbsWeight
    rw [Finset.sum_eq_zero]
    intro n hn
    rw [primitiveMellinKernel_eq_zero_of_le_one (h n hn)]

/-- KMS property implies the state is KMS at all temperatures. -/
theorem kms_at_all_temperatures
    (K : ArithmeticKMSWitness State)
    (A : Finset ℕ)
    (β : ℝ) :
    K.IsKMSAt (K.stateOfFinset A) β :=
  K.isKMSAt A β

/-- Two KMS witnesses with matching state encoding, modular flow, and KMS
predicate are equal. -/
theorem kms_property_eq_of_flow_eq
    (K1 K2 : ArithmeticKMSWitness State)
    (hstate : ∀ A, K1.stateOfFinset A = K2.stateOfFinset A)
    (hflow : ∀ s β, K1.modularFlowReadout s β = K2.modularFlowReadout s β) :
    K1 = K2 := by
  cases K1 with
  | mk state1 flow1 calib1 =>
    cases K2 with
    | mk state2 flow2 calib2 =>
      simp at hstate hflow ⊢
      have hs : state1 = state2 := funext hstate
      have hf : flow1 = flow2 := by
        funext s β
        exact hflow s β
      cases hs
      cases hf
      simp

end ArithmeticKMSWitness

/-! ## 4. Projective KMS property -/

/--
Projective-temperature version of the finite arithmetic KMS property.

The compact variable `u` is restricted by explicit hypotheses in the theorem
payload. The property stores only the state encoding and the projective-flow
calibration. No global analytic continuation through the critical point is
claimed.
-/
structure ProjectiveArithmeticKMSWitness
    (State : Type*) where
  /-- Encode a finite arithmetic support as a model state. -/
  stateOfFinset : Finset ℕ → State

  /-- Model-specific modular-flow readout in compact temperature. -/
  projectiveModularFlowReadout : State → ℝ → ℝ

  /-- Projective Gibbs partition calibration on finite supports. -/
  projectiveFlow_eq_gibbsPartition :
    ∀ A : Finset ℕ, ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 →
      projectiveModularFlowReadout (stateOfFinset A) u =
        projectiveArithmeticGibbsPartition A u

namespace ProjectiveArithmeticKMSWitness

variable {State : Type*}
variable (K : ProjectiveArithmeticKMSWitness State)

/-- Derived compact-sector projective equilibrium predicate. -/
def IsProjectiveKMSAt (s : State) (u : ℝ) : Prop :=
  ∃ A : Finset ℕ,
    s = K.stateOfFinset A ∧
      K.projectiveModularFlowReadout s u = projectiveArithmeticGibbsPartition A u

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
by
  refine ⟨A, rfl, ?_⟩
  exact K.projectiveFlow_eq_gibbsPartition A u hu

/-- The calibrated projective modular-flow readout is nonnegative. -/
theorem projectiveModularFlowReadout_nonneg
    (A : Finset ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ K.projectiveModularFlowReadout (K.stateOfFinset A) u := by
  rw [K.projectiveFlow_eq_gibbsPartition A u hu]
  exact projectiveArithmeticGibbsPartition_nonneg A u

/-- The calibrated projective modular-flow readout is positive on supports containing `n > 1`. -/
lemma projectiveModularFlowReadout_pos_of_mem_gt_one
    (A : Finset ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (h : ∃ n ∈ A, 1 < n) :
    0 < K.projectiveModularFlowReadout (K.stateOfFinset A) u := by
  rw [K.projectiveFlow_eq_gibbsPartition A u hu]
  exact projectiveArithmeticGibbsPartition_pos_of_mem_gt_one A u h

end ProjectiveArithmeticKMSWitness

/-! ## 5. Prime/projective-flow compatibility -/

/--
Compatibility between a projective KMS property and the finite von Mangoldt
prime-flow calibration.
-/
structure ProjectiveKMSPrimeCompatibility
    (State : Type*) where
  /-- Projective arithmetic KMS property. -/
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
