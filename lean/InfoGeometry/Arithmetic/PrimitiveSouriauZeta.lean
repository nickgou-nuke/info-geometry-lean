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
* model-specific Souriau entropy/objective readouts calibrated to the
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

/-- Finite restricted partition is zero on empty support. -/
@[simp] theorem primitiveFiniteZetaPartition_empty (β : ℝ) :
    primitiveFiniteZetaPartition (∅ : Finset ℕ) β = 0 := by
  simp [primitiveFiniteZetaPartition]

/-- Finite restricted partition on singleton support is the kernel term. -/
@[simp] theorem primitiveFiniteZetaPartition_singleton
    (n : ℕ) (β : ℝ) :
    primitiveFiniteZetaPartition ({n} : Finset ℕ) β = primitiveMellinKernel n β := by
  simp [primitiveFiniteZetaPartition]

/-- Finite restricted partition as an arithmetic partition with unit counts. -/
theorem primitiveFiniteZetaPartition_eq_arithmeticPartition_unit
    (A : Finset ℕ) (β : ℝ) :
    primitiveFiniteZetaPartition A β =
      arithmeticPartition A (fun _ => (1 : ℝ)) β := by
  simp [primitiveFiniteZetaPartition, arithmeticPartition, arithmeticCountWeight]

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

/-- The support of an admissible configuration is primitive. -/
theorem support_primitive
    (A : PrimitiveAdmissibleFinset) :
    PrimitiveFinset A.support := A.primitive

/-- The support of an admissible configuration is supported above its threshold. -/
theorem support_supportedAbove
    (A : PrimitiveAdmissibleFinset) :
    SupportedAboveFinset A.threshold A.support := A.supportedAbove

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

/-- The objective of an admissible configuration is nonnegative. -/
theorem objective_nonneg
    (A : PrimitiveAdmissibleFinset) : 0 ≤ A.objective := by
  simpa [objective] using primitiveWeightSum_nonneg A.support

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

/-- The candidate of a finite MaxEnt witness is itself admissible finite data. -/
def candidateAdmissible
    (W : FinitePrimitiveMaxEntWitness threshold candidate) :
    PrimitiveAdmissibleFinset where
  support := candidate
  threshold := threshold
  primitive := W.candidate_primitive
  supportedAbove := W.candidate_supported

@[simp] theorem candidateAdmissible_objective
    (W : FinitePrimitiveMaxEntWitness threshold candidate) :
    W.candidateAdmissible.objective = primitiveWeightSum candidate := by
  rfl

end FinitePrimitiveMaxEntWitness

/-! ## 3. Souriau calibration socket -/

/--
Souriau-style primitive zeta calibration.

`State` is an arbitrary thermodynamic/geometric carrier.

The only direct arithmetic calibration is the objective/action readout:
`objectiveReadout = primitiveWeightSum`.

Entropy and the legacy free-energy/action readout are calibrated to that
objective. Their equalities with `primitiveWeightSum` are therefore derived
theorems, not independent fields.
-/
structure PrimitiveSouriauZetaCalibration (State : Type*) where
  /-- Encode a finite arithmetic support as a model state. -/
  stateOfFinset : Finset ℕ → State

  /-- Model-specific finite partition readout. -/
  partitionReadout : State → ℝ → ℝ

  /-- Model-specific entropy readout. -/
  entropyReadout : State → ℝ

  /-- Calibrated model-specific objective (action/readout) over `State`. -/
  objectiveReadout : State → ℝ

  /--
  Legacy compatibility name for legacy free-energy/action wording.

  This field is intentionally aligned with `objectiveReadout`; the bridge does
  not claim physical Helmholtz free energy unless the model supplies that
  interpretation separately.
  -/
  freeEnergyReadout : State → ℝ

  /-- Partition calibration against the restricted finite zeta partition. -/
  partition_eq_finiteZetaPartition :
    ∀ A : Finset ℕ, ∀ β : ℝ,
      partitionReadout (stateOfFinset A) β =
        primitiveFiniteZetaPartition A β

  /-- Primary arithmetic calibration. -/
  objective_eq_primitiveWeightSum :
    ∀ A : Finset ℕ,
      objectiveReadout (stateOfFinset A) = primitiveWeightSum A

  /-- Entropy is calibrated to the primary objective. -/
  entropy_eq_objective :
    ∀ A : Finset ℕ,
      entropyReadout (stateOfFinset A) = objectiveReadout (stateOfFinset A)

  /-- Legacy free-energy/action readout is calibrated to the primary objective. -/
  freeEnergy_eq_objective :
    ∀ A : Finset ℕ,
      freeEnergyReadout (stateOfFinset A) = objectiveReadout (stateOfFinset A)

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
Derived entropy calibration against the primitive-weight objective.

This is no longer a field; it follows from entropy/objective compatibility and
the primary objective calibration.
-/
theorem entropy_eq_primitiveWeightSum
    (A : Finset ℕ) :
    C.entropyReadout (C.stateOfFinset A) = primitiveWeightSum A := by
  rw [C.entropy_eq_objective A]
  exact C.objective_eq_primitiveWeightSum A

/--
Derived legacy free-energy/action calibration against the primitive-weight
objective.

This is no longer a field; it follows from free-energy/objective compatibility
and the primary objective calibration.
-/
theorem freeEnergy_eq_primitiveWeightSum
    (A : Finset ℕ) :
    C.freeEnergyReadout (C.stateOfFinset A) = primitiveWeightSum A := by
  rw [C.freeEnergy_eq_objective A]
  exact C.objective_eq_primitiveWeightSum A

/-- The legacy free-energy/action readout agrees with the objective readout. -/
theorem freeEnergyReadout_eq_objectiveReadout
    (A : Finset ℕ) :
    C.freeEnergyReadout (C.stateOfFinset A) =
      C.objectiveReadout (C.stateOfFinset A) :=
  C.freeEnergy_eq_objective A

/-- The entropy readout agrees with the objective readout. -/
theorem entropyReadout_eq_objectiveReadout
    (A : Finset ℕ) :
    C.entropyReadout (C.stateOfFinset A) =
      C.objectiveReadout (C.stateOfFinset A) :=
  C.entropy_eq_objective A

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
          apply MeasureTheory.integral_congr_ae
          filter_upwards with β
          simp [C.partition_eq_finiteZetaPartition A β]

/--
After calibration, the objective readout is exactly the integrated restricted
zeta partition.
-/
theorem objective_eq_integral_partitionReadout
    (A : Finset ℕ) :
    C.objectiveReadout (C.stateOfFinset A) =
      ∫ β : ℝ in Set.Ioi 1, C.partitionReadout (C.stateOfFinset A) β := by
  calc
    C.objectiveReadout (C.stateOfFinset A)
        = primitiveWeightSum A :=
          C.objective_eq_primitiveWeightSum A
    _ = ∫ β : ℝ in Set.Ioi 1, primitiveFiniteZetaPartition A β :=
          primitiveWeightSum_eq_integral_finiteZetaPartition A
    _ = ∫ β : ℝ in Set.Ioi 1,
          C.partitionReadout (C.stateOfFinset A) β := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with β
          simp [C.partition_eq_finiteZetaPartition A β]

/--
After calibration, the legacy free-energy field agrees with the partition integral
via the compatibility bridge.
-/
theorem freeEnergy_eq_integral_partitionReadout
    (A : Finset ℕ) :
    C.freeEnergyReadout (C.stateOfFinset A) =
      ∫ β : ℝ in Set.Ioi 1, C.partitionReadout (C.stateOfFinset A) β := by
  rw [C.freeEnergy_eq_objective A]
  exact C.objective_eq_integral_partitionReadout A

/-- Calibrated entropy comparison is primitive-weight comparison. -/
theorem entropy_le_iff_weight_le
    (A B : Finset ℕ) :
    C.entropyReadout (C.stateOfFinset A) ≤
        C.entropyReadout (C.stateOfFinset B) ↔
      primitiveWeightSum A ≤ primitiveWeightSum B := by
  rw [C.entropy_eq_primitiveWeightSum A, C.entropy_eq_primitiveWeightSum B]

/-- Calibrated objective comparison is primitive-weight comparison. -/
theorem objective_le_iff_weight_le
    (A B : Finset ℕ) :
    C.objectiveReadout (C.stateOfFinset A) ≤
        C.objectiveReadout (C.stateOfFinset B) ↔
      primitiveWeightSum A ≤ primitiveWeightSum B := by
  rw [C.objective_eq_primitiveWeightSum A, C.objective_eq_primitiveWeightSum B]

/-- Legacy free-energy comparison is primitive-weight comparison. -/
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
A primitive MaxEnt witness calibrates to objective maximality in any
Souriau model satisfying `PrimitiveSouriauZetaCalibration`.
-/
theorem objectiveReadout_le_candidate_of_maxEnt
    {threshold : ℕ} {candidate A : Finset ℕ}
    (W : FinitePrimitiveMaxEntWitness threshold candidate)
    (hPrim : PrimitiveFinset A)
    (hSupp : SupportedAboveFinset threshold A) :
    C.objectiveReadout (C.stateOfFinset A) ≤
      C.objectiveReadout (C.stateOfFinset candidate) := by
  rw [C.objective_eq_primitiveWeightSum A,
      C.objective_eq_primitiveWeightSum candidate]
  exact W.weight_le_candidate A hPrim hSupp

/-- Primary naming for primitive MaxEnt entropy comparison in calibrated models. -/
theorem entropy_le_candidate_of_maxEnt
    {threshold : ℕ} {candidate A : Finset ℕ}
    (C : PrimitiveSouriauZetaCalibration State)
    (W : FinitePrimitiveMaxEntWitness threshold candidate)
    (hPrim : PrimitiveFinset A)
    (hSupp : SupportedAboveFinset threshold A) :
    C.entropyReadout (C.stateOfFinset A) ≤
      C.entropyReadout (C.stateOfFinset candidate) :=
  by
    rw [C.entropy_eq_primitiveWeightSum A,
        C.entropy_eq_primitiveWeightSum candidate]
    exact W.weight_le_candidate A hPrim hSupp

/-- Primary naming for primitive MaxEnt objective comparison in calibrated models. -/
theorem objective_le_candidate_of_maxEnt
    {threshold : ℕ} {candidate A : Finset ℕ}
    (C : PrimitiveSouriauZetaCalibration State)
    (W : FinitePrimitiveMaxEntWitness threshold candidate)
    (hPrim : PrimitiveFinset A)
    (hSupp : SupportedAboveFinset threshold A) :
    C.objectiveReadout (C.stateOfFinset A) ≤
      C.objectiveReadout (C.stateOfFinset candidate) :=
  by
    rw [C.objective_eq_primitiveWeightSum A,
        C.objective_eq_primitiveWeightSum candidate]
    exact W.weight_le_candidate A hPrim hSupp

/--
Legacy compatibility: free-energy maximality follows from objective naming.
-/
theorem freeEnergyReadout_le_candidate_of_maxEnt
    {threshold : ℕ} {candidate A : Finset ℕ}
    (W : FinitePrimitiveMaxEntWitness threshold candidate)
    (hPrim : PrimitiveFinset A)
    (hSupp : SupportedAboveFinset threshold A) :
    C.freeEnergyReadout (C.stateOfFinset A) ≤
      C.freeEnergyReadout (C.stateOfFinset candidate) := by
  rw [C.freeEnergy_eq_objective A, C.freeEnergy_eq_objective candidate]
  exact C.objectiveReadout_le_candidate_of_maxEnt (threshold := threshold) (candidate := candidate)
    W hPrim hSupp

/-! admissible calibrated comparisons -/
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
theorem objectiveReadout_le_candidate_of_admissible_maxEnt
    (A : PrimitiveAdmissibleFinset)
    {candidate : Finset ℕ}
    (W : FinitePrimitiveMaxEntWitness A.threshold candidate) :
    C.objectiveReadout (C.stateOfFinset A.support) ≤
      C.objectiveReadout (C.stateOfFinset candidate) := by
  rw [C.objective_eq_primitiveWeightSum A.support,
      C.objective_eq_primitiveWeightSum candidate]
  exact W.weight_le_candidate A.support A.primitive A.supportedAbove

/-- Primary naming for admissible primitive MaxEnt entropy calibration. -/
theorem entropy_le_candidate_of_admissible_maxEnt
    (A : PrimitiveAdmissibleFinset)
    {candidate : Finset ℕ}
    (C : PrimitiveSouriauZetaCalibration State)
    (W : FinitePrimitiveMaxEntWitness A.threshold candidate) :
    C.entropyReadout (C.stateOfFinset A.support) ≤
      C.entropyReadout (C.stateOfFinset candidate) :=
  by
    rw [C.entropy_eq_primitiveWeightSum A.support,
        C.entropy_eq_primitiveWeightSum candidate]
    exact W.weight_le_candidate A.support A.primitive A.supportedAbove

/-- Primary naming for admissible primitive MaxEnt objective calibration. -/
theorem objective_le_candidate_of_admissible_maxEnt
    (A : PrimitiveAdmissibleFinset)
    {candidate : Finset ℕ}
    (C : PrimitiveSouriauZetaCalibration State)
    (W : FinitePrimitiveMaxEntWitness A.threshold candidate) :
    C.objectiveReadout (C.stateOfFinset A.support) ≤
      C.objectiveReadout (C.stateOfFinset candidate) :=
  by
    rw [C.objective_eq_primitiveWeightSum A.support,
        C.objective_eq_primitiveWeightSum candidate]
    exact W.weight_le_candidate A.support A.primitive A.supportedAbove

theorem freeEnergyReadout_le_candidate_of_admissible_maxEnt
    (A : PrimitiveAdmissibleFinset)
    {candidate : Finset ℕ}
    (W : FinitePrimitiveMaxEntWitness A.threshold candidate) :
    C.freeEnergyReadout (C.stateOfFinset A.support) ≤
      C.freeEnergyReadout (C.stateOfFinset candidate) := by
  rw [C.freeEnergy_eq_objective A.support,
      C.freeEnergy_eq_objective candidate]
  exact C.objectiveReadout_le_candidate_of_admissible_maxEnt (A := A) (candidate := candidate) W

/-- Admissible readout calibration in partition-integral form. -/
theorem objective_eq_integral_partitionReadout_of_admissible
    (A : PrimitiveAdmissibleFinset) :
    C.objectiveReadout (C.stateOfFinset A.support) =
      ∫ β : ℝ in Set.Ioi 1, C.partitionReadout (C.stateOfFinset A.support) β := by
  exact C.objective_eq_integral_partitionReadout A.support

/-- Legacy free-energy name for admissible partition calibration. -/
theorem freeEnergy_eq_integral_partitionReadout_of_admissible
    (A : PrimitiveAdmissibleFinset) :
    C.freeEnergyReadout (C.stateOfFinset A.support) =
      ∫ β : ℝ in Set.Ioi 1, C.partitionReadout (C.stateOfFinset A.support) β := by
  exact C.freeEnergy_eq_integral_partitionReadout A.support

/-- Legacy alias: compatibility of entropy and admissible partition calibration. -/
theorem entropy_eq_integral_partitionReadout_of_admissible
    (A : PrimitiveAdmissibleFinset) :
    C.entropyReadout (C.stateOfFinset A.support) =
      ∫ β : ℝ in Set.Ioi 1, C.partitionReadout (C.stateOfFinset A.support) β := by
  exact C.entropy_eq_integral_partitionReadout A.support

end PrimitiveSouriauZetaCalibration

/-! ## 4. Constructive identity calibration -/

/--
The identity arithmetic state model.

Here the model state is literally a finite support, so partition, entropy, and
objective readouts are definitionally the primitive arithmetic readouts.
-/
def identityPrimitiveSouriauZetaCalibration :
    PrimitiveSouriauZetaCalibration (Finset ℕ) where
  stateOfFinset := id
  partitionReadout := primitiveFiniteZetaPartition
  entropyReadout := primitiveWeightSum
  objectiveReadout := primitiveWeightSum
  freeEnergyReadout := primitiveWeightSum
  partition_eq_finiteZetaPartition := by
    intro A β
    rfl
  objective_eq_primitiveWeightSum := by
    intro A
    rfl
  entropy_eq_objective := by
    intro A
    rfl
  freeEnergy_eq_objective := by
    intro A
    rfl

namespace identityPrimitiveSouriauZetaCalibration

/--
In the identity arithmetic model, the entropy readout is constructively the
primitive weight sum.
-/
theorem entropy_eq_weight
    (A : Finset ℕ) :
    identityPrimitiveSouriauZetaCalibration.entropyReadout
        (identityPrimitiveSouriauZetaCalibration.stateOfFinset A)
      =
    primitiveWeightSum A :=
  identityPrimitiveSouriauZetaCalibration.entropy_eq_primitiveWeightSum A

/--
In the identity arithmetic model, the objective readout is constructively the
primitive weight sum.
-/
theorem objective_eq_weight
    (A : Finset ℕ) :
    identityPrimitiveSouriauZetaCalibration.objectiveReadout
        (identityPrimitiveSouriauZetaCalibration.stateOfFinset A)
      =
    primitiveWeightSum A :=
  identityPrimitiveSouriauZetaCalibration.objective_eq_primitiveWeightSum A

/--
In the identity arithmetic model, the finite partition readout is
constructively the restricted finite zeta partition.
-/
theorem partition_eq_finite_zeta
    (A : Finset ℕ) (β : ℝ) :
    identityPrimitiveSouriauZetaCalibration.partitionReadout
        (identityPrimitiveSouriauZetaCalibration.stateOfFinset A)
        β
      =
    primitiveFiniteZetaPartition A β :=
  identityPrimitiveSouriauZetaCalibration.partition_eq_finiteZetaPartition A β

end identityPrimitiveSouriauZetaCalibration

end InfoGeometry.Arithmetic.PrimitiveSouriauZeta
