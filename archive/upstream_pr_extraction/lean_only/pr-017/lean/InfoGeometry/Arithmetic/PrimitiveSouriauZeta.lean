import InfoGeometry.Arithmetic.PrimitiveSetsAbove

/-!
InfoGeometry/Arithmetic/PrimitiveSouriauZeta.lean

Witness-gated bridge between primitive-set arithmetic, finite Riemann-gas
partition readouts, and Souriau-style thermodynamic calibration.

This module does not prove the Erdős primitive-set theorem, the Riemann
hypothesis, analytic continuation of `ζ`, or an infinite Euler product.  It
formalizes the conservative finite bridge:

* energy level `E_n = log n`;
* finite restricted partition `∑ n∈A, exp (-β log n)`;
* primitive weight as the integral of that restricted partition over `β > 1`;
* model-specific Souriau free-energy/entropy readouts calibrated to the
  primitive arithmetic readouts by explicit witness fields.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimitiveSouriauZeta

open InfoGeometry.Arithmetic

/-! ## 1. Finite primitive Riemann-gas partition -/

/-- Logarithmic energy level of the arithmetic state `n`. -/
def primitiveEnergy (n : ℕ) : ℝ :=
  Real.log (n : ℝ)

/--
Finite Riemann-gas partition restricted to a finite support `A`.

This is the finite, support-restricted shadow of the zeta partition function.
It is not an infinite Euler product or analytic continuation statement.
-/
def primitiveFiniteZetaPartition (A : Finset ℕ) (β : ℝ) : ℝ :=
  Finset.sum A (fun n => primitiveMellinKernel n β)

/-- The finite restricted partition is a sum over the Mellin/Gibbs kernel. -/
theorem primitiveFiniteZetaPartition_eq_sum
    (A : Finset ℕ) (β : ℝ) :
    primitiveFiniteZetaPartition A β =
      Finset.sum A (fun n => primitiveMellinKernel n β) :=
  rfl

/-- The finite restricted partition is nonnegative. -/
theorem primitiveFiniteZetaPartition_nonneg
    (A : Finset ℕ) (β : ℝ) :
    0 ≤ primitiveFiniteZetaPartition A β := by
  unfold primitiveFiniteZetaPartition
  refine Finset.sum_nonneg ?_
  intro n hn
  exact primitiveMellinKernel_nonneg n β

/--
On positive-weight states, the finite restricted partition is the ordinary
Gibbs sum `∑ exp (-β log n)`.
-/
theorem primitiveFiniteZetaPartition_eq_exp_sum_of_supportedAbove_two
    {A : Finset ℕ}
    (hA : SupportedAboveFinset 2 A)
    (β : ℝ) :
    primitiveFiniteZetaPartition A β =
      Finset.sum A (fun n => Real.exp (-β * primitiveEnergy n)) := by
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn1 : 1 < n := lt_of_lt_of_le Nat.one_lt_two (hA hn)
  simp [primitiveMellinKernel, primitiveEnergy, hn1]

/--
The primitive-weight sum is the integral over inverse temperature `β > 1` of
the finite restricted zeta/Riemann-gas partition.
-/
theorem primitiveWeightSum_eq_integral_finiteZetaPartition
    (A : Finset ℕ) :
    primitiveWeightSum A =
      ∫ β : ℝ in Set.Ioi 1, primitiveFiniteZetaPartition A β := by
  simpa [primitiveFiniteZetaPartition] using
    primitiveWeightSum_eq_integral_mellinKernel A

/-! ## 2. Primitive admissibility and MaxEnt witness -/

/-- A finite primitive configuration supported above a threshold. -/
structure PrimitiveAdmissibleFinset where
  support : Finset ℕ
  threshold : ℕ
  primitive : PrimitiveFinset support
  supportedAbove : SupportedAboveFinset threshold support

namespace PrimitiveAdmissibleFinset

/-- The primitive-weight objective of an admissible finite configuration. -/
def objective (A : PrimitiveAdmissibleFinset) : ℝ :=
  primitiveWeightSum A.support

/-- The restricted finite zeta partition of an admissible configuration. -/
def partition (A : PrimitiveAdmissibleFinset) (β : ℝ) : ℝ :=
  primitiveFiniteZetaPartition A.support β

/-- Admissible finite partitions are nonnegative. -/
theorem partition_nonneg
    (A : PrimitiveAdmissibleFinset) (β : ℝ) :
    0 ≤ A.partition β :=
  primitiveFiniteZetaPartition_nonneg A.support β

/-- The admissible objective is the integrated finite partition. -/
theorem objective_eq_integral_partition
    (A : PrimitiveAdmissibleFinset) :
    A.objective = ∫ β : ℝ in Set.Ioi 1, A.partition β := by
  simpa [objective, partition] using
    primitiveWeightSum_eq_integral_finiteZetaPartition A.support

end PrimitiveAdmissibleFinset

/--
Finite MaxEnt-style optimizer witness for the primitive arithmetic objective.

This is proof-carrying optimization data.  It does not assert that primes are
the optimizer unless such a witness is supplied.
-/
structure FinitePrimitiveMaxEntWitness
    (threshold : ℕ)
    (candidate : Finset ℕ) where
  candidate_primitive : PrimitiveFinset candidate
  candidate_supported : SupportedAboveFinset threshold candidate
  maximizes_weight :
    ∀ A : Finset ℕ,
      PrimitiveFinset A →
      SupportedAboveFinset threshold A →
        primitiveWeightSum A ≤ primitiveWeightSum candidate

namespace FinitePrimitiveMaxEntWitness

variable {threshold : ℕ} {candidate : Finset ℕ}

/-- Re-export of the supplied primitive-weight maximality law. -/
theorem weight_le_candidate
    (W : FinitePrimitiveMaxEntWitness threshold candidate)
    (A : Finset ℕ)
    (hPrim : PrimitiveFinset A)
    (hSupp : SupportedAboveFinset threshold A) :
    primitiveWeightSum A ≤ primitiveWeightSum candidate :=
  W.maximizes_weight A hPrim hSupp

end FinitePrimitiveMaxEntWitness

/-! ## 3. Souriau calibration socket -/

/--
Souriau-style primitive zeta calibration.

`State` is an arbitrary thermodynamic/geometric carrier.  The calibration
states that its finite partition, entropy, and free-energy readouts agree with
the primitive arithmetic readouts on encoded primitive supports.
-/
structure PrimitiveSouriauZetaCalibration (State : Type*) where
  /-- Encode a finite arithmetic support as a model state. -/
  stateOfFinset : Finset ℕ → State

  /-- Model-specific finite partition readout. -/
  partitionReadout : State → ℝ → ℝ

  /-- Model-specific entropy readout. -/
  entropyReadout : State → ℝ

  /-- Model-specific free-energy/action readout. -/
  freeEnergyReadout : State → ℝ

  /-- Partition calibration against the restricted finite zeta partition. -/
  partition_eq_finiteZetaPartition :
    ∀ A : Finset ℕ, ∀ β : ℝ,
      partitionReadout (stateOfFinset A) β =
        primitiveFiniteZetaPartition A β

  /-- Entropy calibration against the primitive-weight objective. -/
  entropy_eq_primitiveWeightSum :
    ∀ A : Finset ℕ,
      entropyReadout (stateOfFinset A) = primitiveWeightSum A

  /-- Free-energy/action calibration against the primitive-weight objective. -/
  freeEnergy_eq_primitiveWeightSum :
    ∀ A : Finset ℕ,
      freeEnergyReadout (stateOfFinset A) = primitiveWeightSum A

namespace PrimitiveSouriauZetaCalibration

variable {State : Type*}
variable (C : PrimitiveSouriauZetaCalibration State)

/-- The calibrated model partition is nonnegative on encoded finite supports. -/
theorem partitionReadout_nonneg
    (A : Finset ℕ) (β : ℝ) :
    0 ≤ C.partitionReadout (C.stateOfFinset A) β := by
  rw [C.partition_eq_finiteZetaPartition A β]
  exact primitiveFiniteZetaPartition_nonneg A β

/--
After calibration, the model entropy readout is exactly the integrated
restricted zeta partition.
-/
theorem entropy_eq_integral_partitionReadout
    (A : Finset ℕ) :
    C.entropyReadout (C.stateOfFinset A) =
      ∫ β : ℝ in Set.Ioi 1, C.partitionReadout (C.stateOfFinset A) β := by
  calc
    C.entropyReadout (C.stateOfFinset A)
        = primitiveWeightSum A :=
          C.entropy_eq_primitiveWeightSum A
    _ = ∫ β : ℝ in Set.Ioi 1, primitiveFiniteZetaPartition A β :=
          primitiveWeightSum_eq_integral_finiteZetaPartition A
    _ = ∫ β : ℝ in Set.Ioi 1,
          C.partitionReadout (C.stateOfFinset A) β := by
          simp_rw [C.partition_eq_finiteZetaPartition A]

/--
After calibration, the model free-energy/action readout is exactly the
integrated restricted zeta partition.
-/
theorem freeEnergy_eq_integral_partitionReadout
    (A : Finset ℕ) :
    C.freeEnergyReadout (C.stateOfFinset A) =
      ∫ β : ℝ in Set.Ioi 1, C.partitionReadout (C.stateOfFinset A) β := by
  calc
    C.freeEnergyReadout (C.stateOfFinset A)
        = primitiveWeightSum A :=
          C.freeEnergy_eq_primitiveWeightSum A
    _ = ∫ β : ℝ in Set.Ioi 1, primitiveFiniteZetaPartition A β :=
          primitiveWeightSum_eq_integral_finiteZetaPartition A
    _ = ∫ β : ℝ in Set.Ioi 1,
          C.partitionReadout (C.stateOfFinset A) β := by
          simp_rw [C.partition_eq_finiteZetaPartition A]

/-- Calibrated entropy comparison is primitive-weight comparison. -/
theorem entropy_le_iff_weight_le
    (A B : Finset ℕ) :
    C.entropyReadout (C.stateOfFinset A) ≤
        C.entropyReadout (C.stateOfFinset B) ↔
      primitiveWeightSum A ≤ primitiveWeightSum B := by
  rw [C.entropy_eq_primitiveWeightSum A, C.entropy_eq_primitiveWeightSum B]

/-- Calibrated free-energy comparison is primitive-weight comparison. -/
theorem freeEnergy_le_iff_weight_le
    (A B : Finset ℕ) :
    C.freeEnergyReadout (C.stateOfFinset A) ≤
        C.freeEnergyReadout (C.stateOfFinset B) ↔
      primitiveWeightSum A ≤ primitiveWeightSum B := by
  rw [C.freeEnergy_eq_primitiveWeightSum A, C.freeEnergy_eq_primitiveWeightSum B]

/--
A primitive MaxEnt witness calibrates to entropy maximality in any Souriau
model satisfying `PrimitiveSouriauZetaCalibration`.
-/
theorem entropyReadout_le_candidate_of_maxEnt
    {threshold : ℕ} {candidate A : Finset ℕ}
    (W : FinitePrimitiveMaxEntWitness threshold candidate)
    (hPrim : PrimitiveFinset A)
    (hSupp : SupportedAboveFinset threshold A) :
    C.entropyReadout (C.stateOfFinset A) ≤
      C.entropyReadout (C.stateOfFinset candidate) := by
  rw [C.entropy_eq_primitiveWeightSum A,
      C.entropy_eq_primitiveWeightSum candidate]
  exact W.weight_le_candidate A hPrim hSupp

/--
A primitive MaxEnt witness calibrates to free-energy/action maximality in any
Souriau model satisfying `PrimitiveSouriauZetaCalibration`.
-/
theorem freeEnergyReadout_le_candidate_of_maxEnt
    {threshold : ℕ} {candidate A : Finset ℕ}
    (W : FinitePrimitiveMaxEntWitness threshold candidate)
    (hPrim : PrimitiveFinset A)
    (hSupp : SupportedAboveFinset threshold A) :
    C.freeEnergyReadout (C.stateOfFinset A) ≤
      C.freeEnergyReadout (C.stateOfFinset candidate) := by
  rw [C.freeEnergy_eq_primitiveWeightSum A,
      C.freeEnergy_eq_primitiveWeightSum candidate]
  exact W.weight_le_candidate A hPrim hSupp

/--
Admissible configurations can be compared directly against a witnessed
candidate at the same threshold.
-/
theorem entropyReadout_le_candidate_of_admissible_maxEnt
    (A : PrimitiveAdmissibleFinset)
    {candidate : Finset ℕ}
    (W : FinitePrimitiveMaxEntWitness A.threshold candidate) :
    C.entropyReadout (C.stateOfFinset A.support) ≤
      C.entropyReadout (C.stateOfFinset candidate) := by
  rw [C.entropy_eq_primitiveWeightSum A.support,
      C.entropy_eq_primitiveWeightSum candidate]
  exact W.weight_le_candidate A.support A.primitive A.supportedAbove

/-- The same admissible comparison for the calibrated free-energy/action readout. -/
theorem freeEnergyReadout_le_candidate_of_admissible_maxEnt
    (A : PrimitiveAdmissibleFinset)
    {candidate : Finset ℕ}
    (W : FinitePrimitiveMaxEntWitness A.threshold candidate) :
    C.freeEnergyReadout (C.stateOfFinset A.support) ≤
      C.freeEnergyReadout (C.stateOfFinset candidate) := by
  rw [C.freeEnergy_eq_primitiveWeightSum A.support,
      C.freeEnergy_eq_primitiveWeightSum candidate]
  exact W.weight_le_candidate A.support A.primitive A.supportedAbove

end PrimitiveSouriauZetaCalibration

end InfoGeometry.Arithmetic.PrimitiveSouriauZeta
