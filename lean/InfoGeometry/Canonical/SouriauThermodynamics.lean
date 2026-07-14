import InfoGeometry.GrandCanonical.ResponseMatrix
import InfoGeometry.Meta.Architecture
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# InfoGeometry.Canonical.SouriauThermodynamics

Source-faithful finite-state Souriau thermodynamics bridge.

This file records the part of the Souriau vocabulary that is already owned by
`InfoGeometry.GrandCanonical.Core`:

- a moment-map-shaped pair of observables `(energy, number)`,
- a geometric-temperature-shaped pair `(β, μ)`,
- the grand-canonical Gibbs weight and Massieu potential,
- the source-proved conjugacy laws
  `∂β log Z = -E[E - μN]` and `∂μ log Z = β E[N]`,
- the canonical one-observable Fisher/Hessian shadow
  `∂²β log Z = variance`.
- the finite two-parameter Souriau-Fisher response matrix, lifted directly from
  the verified grand-canonical Hessian surface.

It deliberately does not claim coadjoint-orbit equivariance, a full Souriau
metric tensor, or D1 commutator closure.  Those require separate owner
theorems.

Repository policy boundary:
this file is finite-dimensional response ownership, not a concrete global
Souriau coadjoint-orbit realization for groups such as `G₂(2)`, `G₂*`, or
`Spin(5,5)`.
-/

namespace SouriauThermodynamics

open InfoGeometry.GrandCanonical

/--
Cartan projection surface for Souriau/Weyl character readouts.

This is a functorial projection lane: it identifies the carrier and selected
Cartan element used by finite character shadows.  Operator ownership remains in
the representation and thermodynamic generator corridors.
-/
@[rep_depth thermo]
structure CartanSubalgebra (LieAlgebra : Type*) where
  cartanCarrier : Type*
  thermalElement : LieAlgebra → cartanCarrier

/--
Finite Souriau temperature projection for character readouts.

The full projective/operator temperature geometry lives in the thermodynamics
operator sidecars; this structure is the scalar projection used by the finite
Weyl/Souriau partition lane.
-/
@[rep_depth thermo]
structure SouriauTemperature (Cartan : Type*) where
  thermalElement : Cartan

/--
Finite thermal representation readout.

The partition/character equality is supplied as witness data, so this surface
does not assert a general Weyl character formula.
-/
@[rep_depth thermo]
structure ThermalRepresentation (Cartan : Type*) where
  character : Cartan → ℝ
  partitionFunction : SouriauTemperature Cartan → ℝ
  thermalElement : SouriauTemperature Cartan → Cartan
  partitionFunction_eq_character :
    ∀ T, partitionFunction T = character (thermalElement T)

namespace ThermalRepresentation

variable {Cartan : Type*} (R : ThermalRepresentation Cartan)

@[rep_depth thermo]
theorem partitionFunction_eq_character_at
    (T : SouriauTemperature Cartan) :
    R.partitionFunction T = R.character (R.thermalElement T) :=
  R.partitionFunction_eq_character T

end ThermalRepresentation

@[rep_depth thermo]
noncomputable def partitionFunction
    {Cartan : Type*}
    (R : ThermalRepresentation Cartan)
    (T : SouriauTemperature Cartan) : ℝ :=
  R.partitionFunction T

@[rep_depth thermo]
theorem partitionFunction_eq_character
    {Cartan : Type*}
    (R : ThermalRepresentation Cartan)
    (T : SouriauTemperature Cartan) :
    partitionFunction R T = R.character (R.thermalElement T) :=
  R.partitionFunction_eq_character T

/-- Generalized Souriau temperature surface for representation-theoretic callers. -/
@[rep_depth thermo]
structure GeneralizedSouriauTemperature (LieAlgebra : Type*) where
  beta : ℝ
  generator : LieAlgebra

/-- Classical moment-map surface used by the Weyl/Souriau compatibility lane. -/
@[rep_depth thermo]
structure ClassicalMomentMap (Phase : Type*) (LieAlgebra : Type*) where
  moment : Phase → LieAlgebra → ℝ

@[rep_depth thermo]
def classicalThermalHamiltonian
    {Phase LieAlgebra : Type*}
    (M : ClassicalMomentMap Phase LieAlgebra)
    (T : GeneralizedSouriauTemperature LieAlgebra)
    (x : Phase) : ℝ :=
  T.beta * M.moment x T.generator

@[rep_depth thermo]
noncomputable def classicalGibbsWeight
    {Phase LieAlgebra : Type*}
    (M : ClassicalMomentMap Phase LieAlgebra)
    (T : GeneralizedSouriauTemperature LieAlgebra)
    (x : Phase) : ℝ :=
  Real.exp (-(classicalThermalHamiltonian M T x))

/-- Quantum representation layer with trace existence kept as witness data. -/
@[rep_depth thermo]
structure QuantumRepresentationLayer (State LieAlgebra : Type*) where
  thermalGenerator : GeneralizedSouriauTemperature LieAlgebra → State → ℝ
  traceExists : Prop

@[rep_depth thermo]
noncomputable def quantumThermalGenerator
    {State LieAlgebra : Type*}
    (R : QuantumRepresentationLayer State LieAlgebra)
    (T : GeneralizedSouriauTemperature LieAlgebra)
    (x : State) : ℝ :=
  R.thermalGenerator T x

@[rep_depth thermo]
noncomputable def quantumPartitionFunction
    {State LieAlgebra : Type*}
    [Fintype State]
    (R : QuantumRepresentationLayer State LieAlgebra)
    (T : GeneralizedSouriauTemperature LieAlgebra) : ℝ :=
  ∑ x, Real.exp (-(quantumThermalGenerator R T x))

/-- Witness that a quantum trace decomposes into weight spaces before being read as a character. -/
@[rep_depth thermo]
structure WeightDecompositionWitness (State LieAlgebra : Type*) where
  representation : QuantumRepresentationLayer State LieAlgebra
  weightSpace : State → Prop
  traceExists : representation.traceExists

@[rep_depth thermo]
noncomputable def quantumCharacterIfWeighted
    {State LieAlgebra : Type*}
    [Fintype State]
    (W : WeightDecompositionWitness State LieAlgebra)
    (T : GeneralizedSouriauTemperature LieAlgebra) : ℝ :=
  quantumPartitionFunction W.representation T

/--
Finite moment-map shadow: the two owner observables used by the
grand-canonical kernel.
-/
structure SouriauMomentMap (α : Type _) where
  energy : α → ℝ
  number : α → ℝ

/--
Finite geometric-temperature shadow: inverse temperature and chemical
potential as the two thermodynamic parameters already present in
`GrandCanonical.Core`.
-/
structure GeometricTemperature where
  beta : ℝ
  mu : ℝ

variable {α : Type _}

/--
Finite representation-weight shadow. In the owner grand-canonical lane, a
weight is exactly the pair of conserved readouts carried by one state:
energy and number.
-/
structure SouriauWeight where
  energyWeight : ℝ
  numberWeight : ℝ

/-- The weight attached to a finite state by the Souriau moment-map shadow. -/
@[rep_depth transport]
def souriauWeightAt (M : SouriauMomentMap α) (x : α) : SouriauWeight where
  energyWeight := M.energy x
  numberWeight := M.number x

/--
Finite pairing between geometric temperature and a representation weight.
The sign convention matches the grand-canonical kernel:
`β * (E - μN)`.
-/
@[rep_depth transport]
def geometricTemperatureWeightPairing
    (T : GeometricTemperature) (w : SouriauWeight) : ℝ :=
  T.beta * (w.energyWeight - T.mu * w.numberWeight)

/-- Convert the finite Souriau moment-map shadow to the owner two-parameter data. -/
@[rep_depth transport]
def toGrandCanonicalTwoParam (M : SouriauMomentMap α) :
    GrandCanonicalTwoParam α where
  energy := M.energy
  number := M.number

/-- Shifted observable `E - μN` in Souriau notation. -/
@[rep_depth transport]
noncomputable def shiftedMomentReadout
    (M : SouriauMomentMap α) (T : GeometricTemperature) (x : α) : ℝ :=
  shiftedEnergy (toGrandCanonicalTwoParam M) T.mu x

/--
The finite Souriau weight pairing is exactly the exponent observable used by
the grand-canonical Gibbs kernel.
-/
@[rep_depth transport]
theorem geometricTemperatureWeightPairing_eq_beta_mul_shiftedMomentReadout
    (M : SouriauMomentMap α) (T : GeometricTemperature) (x : α) :
    geometricTemperatureWeightPairing T (souriauWeightAt M x) =
      T.beta * shiftedMomentReadout M T x := by
  rfl

/--
Unnormalized Gibbs-Souriau density written as the exponential of the negative
temperature-weight pairing.
-/
@[rep_depth transport]
noncomputable def souriauUnnormalizedDensity
    (M : SouriauMomentMap α) (T : GeometricTemperature) (x : α) : ℝ :=
  Real.exp (-geometricTemperatureWeightPairing T (souriauWeightAt M x))

/-- The weight-pairing density is exactly the owner grand-canonical exponential. -/
@[rep_depth transport]
theorem souriauUnnormalizedDensity_eq_gc_exponential
    (M : SouriauMomentMap α) (T : GeometricTemperature) (x : α) :
    souriauUnnormalizedDensity M T x =
      Real.exp (-T.beta * shiftedMomentReadout M T x) := by
  unfold souriauUnnormalizedDensity geometricTemperatureWeightPairing souriauWeightAt
    shiftedMomentReadout shiftedEnergy toGrandCanonicalTwoParam
  ring_nf

/-- Partition function written as a finite Gibbs-Souriau weight sum. -/
@[rep_depth transport]
noncomputable def souriauPartition
    [Fintype α] (M : SouriauMomentMap α) (T : GeometricTemperature) : ℝ :=
  ∑ x, souriauUnnormalizedDensity M T x

/-- The finite Gibbs-Souriau partition is the owner grand-canonical partition. -/
@[rep_depth transport]
theorem souriauPartition_eq_partitionGC
    [Fintype α] (M : SouriauMomentMap α) (T : GeometricTemperature) :
    souriauPartition M T =
      partitionGC (toGrandCanonicalTwoParam M) T.beta T.mu := by
  classical
  unfold souriauPartition partitionGC
  apply Finset.sum_congr rfl
  intro x hx
  rw [souriauUnnormalizedDensity_eq_gc_exponential]
  simp [shiftedMomentReadout]

/-- The finite Gibbs-Souriau partition is strictly positive. -/
@[rep_depth transport]
theorem souriauPartition_pos
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    0 < souriauPartition M T := by
  rw [souriauPartition_eq_partitionGC]
  exact partitionGC_pos (toGrandCanonicalTwoParam M) T.beta T.mu

/-- Souriau/Gibbs finite-state weight, definitionally the owner GC Gibbs weight. -/
@[rep_depth transport]
noncomputable def souriauGibbsWeight
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) (x : α) : ℝ :=
  gibbsWeightGC (toGrandCanonicalTwoParam M) T.beta T.mu x

/--
The normalized Gibbs-Souriau density is exactly the existing grand-canonical
Gibbs weight.
-/
@[rep_depth transport]
theorem souriauGibbsWeight_eq_density_div_partition
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) (x : α) :
    souriauGibbsWeight M T x =
      souriauUnnormalizedDensity M T x / souriauPartition M T := by
  unfold souriauGibbsWeight gibbsWeightGC
  rw [souriauUnnormalizedDensity_eq_gc_exponential,
    souriauPartition_eq_partitionGC]
  simp [shiftedMomentReadout]

/-- The finite Gibbs-Souriau normalized weight is nonnegative. -/
@[rep_depth transport]
theorem souriauGibbsWeight_nonneg
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) (x : α) :
    0 ≤ souriauGibbsWeight M T x := by
  exact gibbsWeightGC_nonneg (toGrandCanonicalTwoParam M) T.beta T.mu x

/-- The finite Gibbs-Souriau normalized weight is strictly positive. -/
@[rep_depth transport]
theorem souriauGibbsWeight_pos
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) (x : α) :
    0 < souriauGibbsWeight M T x := by
  exact gibbsWeightGC_pos (toGrandCanonicalTwoParam M) T.beta T.mu x

/-- The finite Gibbs-Souriau normalized weights sum to one. -/
@[rep_depth transport]
theorem souriauGibbsWeight_sum_one
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    ∑ x, souriauGibbsWeight M T x = 1 := by
  exact gibbsWeightGC_sum_one (toGrandCanonicalTwoParam M) T.beta T.mu

/-- Souriau/Massieu finite-state potential, definitionally the owner `potentialGC`. -/
@[rep_depth transport]
noncomputable def souriauMassieuPotential
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) : ℝ :=
  potentialGC (toGrandCanonicalTwoParam M) T.beta T.mu

/-- The finite Souriau/Massieu potential is the logarithm of the Souriau partition. -/
@[rep_depth transport]
theorem souriauMassieuPotential_eq_log_partition
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    souriauMassieuPotential M T = Real.log (souriauPartition M T) := by
  rw [souriauMassieuPotential, potentialGC, souriauPartition_eq_partitionGC]

/-- Mean shifted readout `E - μN` under the finite Souriau/Gibbs state. -/
@[rep_depth transport]
noncomputable def souriauMeanShift
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) : ℝ :=
  meanShift (toGrandCanonicalTwoParam M) T.beta T.mu

/-- Mean count/number readout under the finite Souriau/Gibbs state. -/
@[rep_depth transport]
noncomputable def souriauMeanNumber
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) : ℝ :=
  meanNumber (toGrandCanonicalTwoParam M) T.beta T.mu

/--
Expected finite temperature-weight pairing under the Gibbs-Souriau state.
-/
@[rep_depth transport]
noncomputable def souriauExpectedWeightPairing
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) : ℝ :=
  ∑ x, souriauGibbsWeight M T x *
    geometricTemperatureWeightPairing T (souriauWeightAt M x)

/-- Expected temperature-weight pairing equals `β` times the shifted mean. -/
@[rep_depth transport]
theorem souriauExpectedWeightPairing_eq_beta_mul_meanShift
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    souriauExpectedWeightPairing M T = T.beta * souriauMeanShift M T := by
  classical
  unfold souriauExpectedWeightPairing souriauMeanShift meanShift souriauGibbsWeight
    geometricTemperatureWeightPairing souriauWeightAt shiftedEnergy toGrandCanonicalTwoParam
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/--
Finite Souriau thermodynamic entropy potential:
`S = Φ + E[⟨β,J⟩]` in the current sign convention.
-/
@[rep_depth transport]
noncomputable def souriauThermodynamicEntropy
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) : ℝ :=
  souriauMassieuPotential M T + souriauExpectedWeightPairing M T

/-- Souriau entropy in finite grand-canonical coordinates. -/
@[rep_depth transport]
theorem souriauThermodynamicEntropy_eq_massieu_add_beta_mul_meanShift
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    souriauThermodynamicEntropy M T =
      souriauMassieuPotential M T + T.beta * souriauMeanShift M T := by
  rw [souriauThermodynamicEntropy, souriauExpectedWeightPairing_eq_beta_mul_meanShift]

/--
Finite Souriau-Fisher response packet. This is the verified `2×2`
grand-canonical Hessian transported into Souriau notation.
-/
@[rep_depth transport]
noncomputable def souriauFisherResponseMatrix
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) : ResponseMatrix2 :=
  responseMatrix (toGrandCanonicalTwoParam M) T.beta T.mu

/-- The same finite Souriau-Fisher response packet as a concrete `2×2` matrix. -/
@[rep_depth transport]
noncomputable def souriauFisherMetricMatrix
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  let R := souriauFisherResponseMatrix M T
  !![R.betaBeta, R.betaMu; R.muBeta, R.muMu]

/--
Finite Souriau-Koszul-Fisher tensor.

This is the Hessian readout surface used by the Souriau Fisher/Koszul
language.  It is definitionally the finite Souriau-Fisher response packet.
-/
@[rep_depth transport]
noncomputable def souriauKoszulFisherTensor
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) : ResponseMatrix2 :=
  souriauFisherResponseMatrix M T

@[simp] theorem souriauKoszulFisherTensor_eq_responseMatrix
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    souriauKoszulFisherTensor M T = souriauFisherResponseMatrix M T := rfl

/-- The `ββ` Souriau-Fisher response is the shifted-energy variance. -/
@[rep_depth transport]
theorem souriauFisher_betaBeta_eq_varianceShift
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    (souriauFisherResponseMatrix M T).betaBeta =
      varianceShift (toGrandCanonicalTwoParam M) T.beta T.mu := by
  simpa [souriauFisherResponseMatrix, responseMatrix] using
    betaHessian_eq_varianceShift (toGrandCanonicalTwoParam M) T.beta T.mu

/-- The `ββ` Souriau-Fisher response is nonnegative constructively. -/
@[rep_depth transport]
theorem souriauFisher_betaBeta_nonneg
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    0 ≤ (souriauFisherResponseMatrix M T).betaBeta := by
  rw [souriauFisher_betaBeta_eq_varianceShift]
  exact varianceShift_nonneg (toGrandCanonicalTwoParam M) T.beta T.mu

/-- The `μμ` Souriau-Fisher response is `β²` times number variance. -/
@[rep_depth transport]
theorem souriauFisher_muMu_eq_beta_sq_varianceNumber
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    (souriauFisherResponseMatrix M T).muMu =
      T.beta ^ (2 : ℕ) *
        varianceNumber (toGrandCanonicalTwoParam M) T.beta T.mu := by
  simpa [souriauFisherResponseMatrix, responseMatrix] using
    muHessian_eq_beta_sq_varianceNumber
      (toGrandCanonicalTwoParam M) T.beta T.mu

/-- The `μμ` Souriau-Fisher response is nonnegative constructively. -/
@[rep_depth transport]
theorem souriauFisher_muMu_nonneg
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    0 ≤ (souriauFisherResponseMatrix M T).muMu := by
  rw [souriauFisher_muMu_eq_beta_sq_varianceNumber]
  exact mul_nonneg (sq_nonneg T.beta)
    (varianceNumber_nonneg (toGrandCanonicalTwoParam M) T.beta T.mu)

/-- The `∂_μ ∂_β` Souriau-Fisher response is the number/covariance readout. -/
@[rep_depth transport]
theorem souriauFisher_betaMu_eq_meanNumber_sub_beta_mul_covariance
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    (souriauFisherResponseMatrix M T).betaMu =
      meanNumber (toGrandCanonicalTwoParam M) T.beta T.mu -
        T.beta * covarianceShiftNumber (toGrandCanonicalTwoParam M) T.beta T.mu := by
  simpa [souriauFisherResponseMatrix, responseMatrix] using
    betaMuHessian_eq_meanNumber_sub_beta_mul_covariance
      (toGrandCanonicalTwoParam M) T.beta T.mu

/-- The `∂_β ∂_μ` Souriau-Fisher response is the same number/covariance readout. -/
@[rep_depth transport]
theorem souriauFisher_muBeta_eq_meanNumber_sub_beta_mul_covariance
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    (souriauFisherResponseMatrix M T).muBeta =
      meanNumber (toGrandCanonicalTwoParam M) T.beta T.mu -
        T.beta * covarianceShiftNumber (toGrandCanonicalTwoParam M) T.beta T.mu := by
  simpa [souriauFisherResponseMatrix, responseMatrix] using
    muBetaHessian_eq_meanNumber_sub_beta_mul_covariance
      (toGrandCanonicalTwoParam M) T.beta T.mu

/-- Souriau-Fisher response symmetry: the finite Onsager shadow. -/
@[rep_depth transport]
theorem souriauFisherResponseMatrix_symmetric
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    (souriauFisherResponseMatrix M T).Symmetric := by
  simpa [souriauFisherResponseMatrix] using
    responseMatrix_symmetric_of_hessian (toGrandCanonicalTwoParam M) T.beta T.mu

/--
Finite Souriau-Koszul-Fisher Hessian packet.

The tensor readout is explicitly the second-derivative packet of the finite
Massieu potential in the owner grand-canonical coordinates, rewritten in
Souriau notation.
-/
@[rep_depth transport]
theorem souriauKoszulFisherTensor_hessian_packet
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    (souriauKoszulFisherTensor M T).betaBeta =
        varianceShift (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauKoszulFisherTensor M T).muMu =
        T.beta ^ (2 : ℕ) *
          varianceNumber (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauKoszulFisherTensor M T).betaMu =
        meanNumber (toGrandCanonicalTwoParam M) T.beta T.mu -
          T.beta * covarianceShiftNumber (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauKoszulFisherTensor M T).muBeta =
        meanNumber (toGrandCanonicalTwoParam M) T.beta T.mu -
          T.beta * covarianceShiftNumber (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauKoszulFisherTensor M T).Symmetric := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [souriauKoszulFisherTensor] using
      souriauFisher_betaBeta_eq_varianceShift M T
  · simpa [souriauKoszulFisherTensor] using
      souriauFisher_muMu_eq_beta_sq_varianceNumber M T
  · simpa [souriauKoszulFisherTensor] using
      souriauFisher_betaMu_eq_meanNumber_sub_beta_mul_covariance M T
  · simpa [souriauKoszulFisherTensor] using
      souriauFisher_muBeta_eq_meanNumber_sub_beta_mul_covariance M T
  · simpa [souriauKoszulFisherTensor] using
      souriauFisherResponseMatrix_symmetric M T

/-- Matrix-level Souriau-Fisher symmetry, i.e. finite Onsager reciprocity. -/
@[rep_depth transport]
theorem souriauFisherMetricMatrix_isSymm
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    (souriauFisherMetricMatrix M T).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simp [souriauFisherMetricMatrix]
  · simpa [souriauFisherMetricMatrix, souriauFisherResponseMatrix,
      responseMatrix, ResponseMatrix2.Symmetric] using
      (souriauFisherResponseMatrix_symmetric M T).symm
  · simpa [souriauFisherMetricMatrix, souriauFisherResponseMatrix,
      responseMatrix, ResponseMatrix2.Symmetric] using
      souriauFisherResponseMatrix_symmetric M T
  · simp [souriauFisherMetricMatrix]

/--
Finite Souriau-Fisher PSD from the concrete variance diagonals and a remaining
determinant/non-spinodal gate.
-/
@[rep_depth transport]
theorem souriauFisherResponseMatrix_positiveSemidefinite_of_det_nonneg
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hdet : 0 ≤ (souriauFisherResponseMatrix M T).det) :
    (souriauFisherResponseMatrix M T).PositiveSemidefinite :=
  ⟨souriauFisher_betaBeta_nonneg M T,
    souriauFisher_muMu_nonneg M T,
    hdet⟩

/--
Finite inverse Souriau-Fisher response packet.

This is the algebraic inverse of the finite `2×2` Fisher/Onsager response
matrix.  It is defined everywhere as a formula, but it is certified as an
inverse only on the non-spinodal locus `det ≠ 0`.
-/
@[rep_depth transport]
noncomputable def souriauFisherInverseMetricResponse
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) : ResponseMatrix2 :=
  (souriauFisherResponseMatrix M T).inverseMetric

/-- The finite inverse Souriau-Fisher response packet as a concrete `2×2` matrix. -/
@[rep_depth transport]
noncomputable def souriauFisherInverseMetricMatrix
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  let R := souriauFisherInverseMetricResponse M T
  !![R.betaBeta, R.betaMu; R.muBeta, R.muMu]

/-- The inverse finite Souriau-Fisher metric is symmetric. -/
@[rep_depth transport]
theorem souriauFisherInverseMetricResponse_symmetric
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    (souriauFisherInverseMetricResponse M T).Symmetric :=
  ResponseMatrix2.inverseMetric_symmetric
    (souriauFisherResponseMatrix_symmetric M T)

/-- Right inverse law for the finite Souriau-Fisher metric on `det ≠ 0`. -/
@[rep_depth transport]
theorem souriauFisher_comp_inverseMetric_of_det_ne_zero
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hdet : (souriauFisherResponseMatrix M T).det ≠ 0) :
    (souriauFisherResponseMatrix M T).compose
        (souriauFisherInverseMetricResponse M T) =
      ResponseMatrix2.identityMetric :=
  ResponseMatrix2.compose_inverseMetric_of_det_ne_zero hdet

/-- Left inverse law for the finite Souriau-Fisher metric on `det ≠ 0`. -/
@[rep_depth transport]
theorem souriauFisher_inverseMetric_comp_of_det_ne_zero
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hdet : (souriauFisherResponseMatrix M T).det ≠ 0) :
    (souriauFisherInverseMetricResponse M T).compose
        (souriauFisherResponseMatrix M T) =
      ResponseMatrix2.identityMetric :=
  ResponseMatrix2.inverseMetric_compose_of_det_ne_zero hdet

/--
Finite Souriau-Onsager entropy production for thermodynamic force vector
`(xβ, xμ)`.
-/
@[rep_depth transport]
noncomputable def souriauEntropyProduction
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) (xβ xμ : ℝ) : ℝ :=
  (souriauFisherResponseMatrix M T).entropyProduction xβ xμ

/--
Finite second-law shadow: if the Souriau-Fisher response packet is positive
semidefinite, its Onsager entropy production is nonnegative.
-/
@[rep_depth transport]
theorem souriauEntropyProduction_nonneg_of_positiveSemidefinite
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hPSD : (souriauFisherResponseMatrix M T).PositiveSemidefinite)
    (xβ xμ : ℝ) :
    0 ≤ souriauEntropyProduction M T xβ xμ := by
  simpa [souriauEntropyProduction] using
    ResponseMatrix2.entropyProduction_nonneg_of_symmetric_positiveSemidefinite
      (souriauFisherResponseMatrix_symmetric M T) hPSD xβ xμ

/--
Finite Souriau-Onsager second law with only the determinant gate left explicit.

The diagonal Fisher positivity is constructed from the variance identities, so
callers no longer need to package it as a hypothesis.
-/
@[rep_depth transport]
theorem souriauEntropyProduction_nonneg_of_det_nonneg
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hdet : 0 ≤ (souriauFisherResponseMatrix M T).det)
    (xβ xμ : ℝ) :
    0 ≤ souriauEntropyProduction M T xβ xμ :=
  souriauEntropyProduction_nonneg_of_positiveSemidefinite M T
    (souriauFisherResponseMatrix_positiveSemidefinite_of_det_nonneg M T hdet)
    xβ xμ

/--
Finite strict second-law equality case.

This is the repo-native finite form of the prose statement
`σ = 0` iff the thermodynamic force vanishes.  It requires the explicit
positive-definite response gate; PSD alone only proves nonnegativity.
-/
@[rep_depth transport]
theorem souriauEntropyProduction_eq_zero_iff_force_zero_of_positiveDefinite
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hPD : (souriauFisherResponseMatrix M T).PositiveDefinite)
    (xβ xμ : ℝ) :
    souriauEntropyProduction M T xβ xμ = 0 ↔ xβ = 0 ∧ xμ = 0 := by
  simpa [souriauEntropyProduction] using
    ResponseMatrix2.entropyProduction_eq_zero_iff_force_zero_of_positiveDefinite
      hPD xβ xμ

/--
Finite Souriau-Fisher/Onsager proof packet.

This is the source-supported finite theorem corresponding to the usual proof
outline:

1. the Hessian of the finite Massieu/log-partition potential gives the
   Souriau-Fisher response entries;
2. the mixed entries agree, giving finite Onsager reciprocity;
3. a positive-semidefinite response packet gives nonnegative entropy
   production.

The positive-semidefinite hypothesis is explicit: no global positivity is
claimed for indefinite/operatorial/Krein lanes without a separate PSD gate.
-/
@[rep_depth transport]
theorem souriauFisherOnsager_proof_packet
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hPSD : (souriauFisherResponseMatrix M T).PositiveSemidefinite)
    (xβ xμ : ℝ) :
    (souriauFisherResponseMatrix M T).betaBeta =
        varianceShift (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauFisherResponseMatrix M T).muMu =
        T.beta ^ (2 : ℕ) *
          varianceNumber (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauFisherResponseMatrix M T).betaMu =
        meanNumber (toGrandCanonicalTwoParam M) T.beta T.mu -
          T.beta * covarianceShiftNumber (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauFisherResponseMatrix M T).muBeta =
        meanNumber (toGrandCanonicalTwoParam M) T.beta T.mu -
          T.beta * covarianceShiftNumber (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauFisherResponseMatrix M T).Symmetric
      ∧ 0 ≤ souriauEntropyProduction M T xβ xμ :=
  ⟨souriauFisher_betaBeta_eq_varianceShift M T,
    souriauFisher_muMu_eq_beta_sq_varianceNumber M T,
    souriauFisher_betaMu_eq_meanNumber_sub_beta_mul_covariance M T,
    souriauFisher_muBeta_eq_meanNumber_sub_beta_mul_covariance M T,
    souriauFisherResponseMatrix_symmetric M T,
    souriauEntropyProduction_nonneg_of_positiveSemidefinite M T hPSD xβ xμ⟩

/-- Souriau-Koszul-Fisher symmetry: the finite Onsager shadow. -/
@[rep_depth transport]
theorem souriauKoszulFisherTensor_symmetric
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    (souriauKoszulFisherTensor M T).Symmetric := by
  simpa [souriauKoszulFisherTensor] using
    souriauFisherResponseMatrix_symmetric M T

/-- The Souriau-Koszul-Fisher tensor is positive semidefinite on `det ≥ 0`. -/
@[rep_depth transport]
theorem souriauKoszulFisherTensor_positiveSemidefinite_of_det_nonneg
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hdet : 0 ≤ (souriauKoszulFisherTensor M T).det) :
    (souriauKoszulFisherTensor M T).PositiveSemidefinite := by
  simpa [souriauKoszulFisherTensor] using
    souriauFisherResponseMatrix_positiveSemidefinite_of_det_nonneg M T hdet

/-- The inverse Souriau-Koszul-Fisher response packet is symmetric. -/
@[rep_depth transport]
theorem souriauKoszulFisherTensor_inverseMetric_symmetric
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    (souriauFisherInverseMetricResponse M T).Symmetric := by
  simpa using souriauFisherInverseMetricResponse_symmetric M T

/-- Right inverse law for the finite Souriau-Koszul-Fisher tensor on `det ≠ 0`. -/
@[rep_depth transport]
theorem souriauKoszulFisherTensor_comp_inverseMetric_of_det_ne_zero
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hdet : (souriauKoszulFisherTensor M T).det ≠ 0) :
    (souriauKoszulFisherTensor M T).compose
        (souriauFisherInverseMetricResponse M T) =
      ResponseMatrix2.identityMetric := by
  simpa [souriauKoszulFisherTensor] using
    souriauFisher_comp_inverseMetric_of_det_ne_zero M T hdet

/-- Left inverse law for the finite Souriau-Koszul-Fisher tensor on `det ≠ 0`. -/
@[rep_depth transport]
theorem souriauKoszulFisherTensor_inverseMetric_comp_of_det_ne_zero
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hdet : (souriauKoszulFisherTensor M T).det ≠ 0) :
    (souriauFisherInverseMetricResponse M T).compose
        (souriauKoszulFisherTensor M T) =
      ResponseMatrix2.identityMetric := by
  simpa [souriauKoszulFisherTensor] using
    souriauFisher_inverseMetric_comp_of_det_ne_zero M T hdet

/-- Souriau-Koszul-Fisher entropy production is nonnegative on `det ≥ 0`. -/
@[rep_depth transport]
theorem souriauKoszulFisherTensor_entropyProduction_nonneg_of_det_nonneg
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hdet : 0 ≤ (souriauKoszulFisherTensor M T).det)
    (xβ xμ : ℝ) :
    0 ≤ (souriauKoszulFisherTensor M T).entropyProduction xβ xμ := by
  simpa [souriauKoszulFisherTensor, souriauEntropyProduction] using
    souriauEntropyProduction_nonneg_of_det_nonneg M T hdet xβ xμ

/--
Finite Souriau-Koszul-Fisher proof packet.

This is the direct package form of the owned response-matrix content:

* variance/covariance Hessian readout;
* Onsager reciprocity;
* positive-semidefinite gate from `det ≥ 0`;
* entropy production nonnegativity on the same gate;
* explicit inverse laws on the non-spinodal locus `det ≠ 0`.
-/
@[rep_depth transport]
theorem souriauKoszulFisherTensor_proof_packet
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hdet : 0 ≤ (souriauKoszulFisherTensor M T).det)
    (xβ xμ : ℝ) :
    (souriauKoszulFisherTensor M T).betaBeta =
        varianceShift (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauKoszulFisherTensor M T).muMu =
        T.beta ^ (2 : ℕ) *
          varianceNumber (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauKoszulFisherTensor M T).betaMu =
        meanNumber (toGrandCanonicalTwoParam M) T.beta T.mu -
          T.beta * covarianceShiftNumber (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauKoszulFisherTensor M T).muBeta =
        meanNumber (toGrandCanonicalTwoParam M) T.beta T.mu -
          T.beta * covarianceShiftNumber (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauKoszulFisherTensor M T).Symmetric
      ∧ (souriauKoszulFisherTensor M T).PositiveSemidefinite
      ∧ 0 ≤ (souriauKoszulFisherTensor M T).entropyProduction xβ xμ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [souriauKoszulFisherTensor] using
      souriauFisher_betaBeta_eq_varianceShift M T
  · simpa [souriauKoszulFisherTensor] using
      souriauFisher_muMu_eq_beta_sq_varianceNumber M T
  · simpa [souriauKoszulFisherTensor] using
      souriauFisher_betaMu_eq_meanNumber_sub_beta_mul_covariance M T
  · simpa [souriauKoszulFisherTensor] using
      souriauFisher_muBeta_eq_meanNumber_sub_beta_mul_covariance M T
  · exact souriauKoszulFisherTensor_symmetric M T
  · exact souriauKoszulFisherTensor_positiveSemidefinite_of_det_nonneg M T hdet
  · exact souriauKoszulFisherTensor_entropyProduction_nonneg_of_det_nonneg M T hdet xβ xμ

/-- The `β` direction is conjugate to the shifted observable `E - μN`. -/
@[rep_depth transport]
theorem souriau_beta_conjugate_shifted_readout
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    deriv (fun β => souriauMassieuPotential M { T with beta := β }) T.beta =
      -souriauMeanShift M T := by
  simpa [souriauMassieuPotential, souriauMeanShift, toGrandCanonicalTwoParam] using
    potentialGC_deriv_beta_eq_neg_meanShift
      (toGrandCanonicalTwoParam M) T.beta T.mu

/-- The `μ` direction is conjugate to the count observable `N`. -/
@[rep_depth transport]
theorem souriau_mu_conjugate_number_readout
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    deriv (fun μ => souriauMassieuPotential M { T with mu := μ }) T.mu =
      T.beta * souriauMeanNumber M T := by
  simpa [souriauMassieuPotential, souriauMeanNumber, toGrandCanonicalTwoParam] using
    potentialGC_deriv_mu_eq_beta_meanNumber
      (toGrandCanonicalTwoParam M) T.beta T.mu

/--
Search-facing Gibbs-Souriau/Fisher/Onsager second-law packet.

This is the finite theorem corresponding to the standard derivation:

* first Massieu derivatives give the conjugate mean readouts;
* second Massieu derivatives give the finite Souriau-Fisher Hessian entries;
* mixed Hessian equality gives finite Onsager reciprocity;
* an explicit positive-semidefinite response gate gives `σ = Xᵀ L X ≥ 0`.

The PSD hypothesis is a real hypothesis, not inferred from prose.  Strict
positive definiteness and the infinite coadjoint-orbit theorem live behind
separate hypotheses in the operatorial/metriplectic owner layers.
-/
@[rep_depth transport]
theorem gibbsSouriau_massieu_fisher_onsager_secondLaw_packet
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature)
    (hPSD : (souriauFisherResponseMatrix M T).PositiveSemidefinite)
    (xβ xμ : ℝ) :
    deriv (fun β => souriauMassieuPotential M { T with beta := β }) T.beta =
        -souriauMeanShift M T
      ∧ deriv (fun μ => souriauMassieuPotential M { T with mu := μ }) T.mu =
        T.beta * souriauMeanNumber M T
      ∧ (souriauFisherResponseMatrix M T).betaBeta =
        varianceShift (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauFisherResponseMatrix M T).muMu =
        T.beta ^ (2 : ℕ) *
          varianceNumber (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauFisherResponseMatrix M T).betaMu =
        meanNumber (toGrandCanonicalTwoParam M) T.beta T.mu -
          T.beta * covarianceShiftNumber (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauFisherResponseMatrix M T).muBeta =
        meanNumber (toGrandCanonicalTwoParam M) T.beta T.mu -
          T.beta * covarianceShiftNumber (toGrandCanonicalTwoParam M) T.beta T.mu
      ∧ (souriauFisherResponseMatrix M T).Symmetric
      ∧ 0 ≤ souriauEntropyProduction M T xβ xμ := by
  exact ⟨souriau_beta_conjugate_shifted_readout M T,
    souriau_mu_conjugate_number_readout M T,
    souriauFisher_betaBeta_eq_varianceShift M T,
    souriauFisher_muMu_eq_beta_sq_varianceNumber M T,
    souriauFisher_betaMu_eq_meanNumber_sub_beta_mul_covariance M T,
    souriauFisher_muBeta_eq_meanNumber_sub_beta_mul_covariance M T,
    souriauFisherResponseMatrix_symmetric M T,
    souriauEntropyProduction_nonneg_of_positiveSemidefinite M T hPSD xβ xμ⟩

/--
Canonical one-observable Fisher/Hessian shadow: the finite Souriau bridge
reduces to the existing owner theorem `hessian = variance` on the `μ = 0`
single-observable slice.
-/
@[rep_depth transport]
theorem souriau_canonical_hessian_eq_variance
    [Fintype α] [Nonempty α]
    (energy : α → ℝ) (β : ℝ) :
    hessian ({ energy := energy } : GrandCanonicalParams α) β =
      variance ({ energy := energy } : GrandCanonicalParams α) β := by
  exact potential_second_derivative_eq_variance
    ({ energy := energy } : GrandCanonicalParams α) β

/--
Souriau-Cartan temperature shadow.
-/
structure SouriauCartanTemperature where
  beta : ℝ
  mu : ℝ

/--
The finite Gibbs-Souriau partition viewed as a thermal character evaluation.
-/
@[rep_depth transport]
noncomputable def souriauPartitionAsCharacter
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) : ℝ :=
  souriauPartition M T

/--
Agreement between character evaluation and the finite partition function.
-/
@[rep_depth transport]
theorem souriauPartitionAsCharacter_eq_souriauPartition
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    souriauPartitionAsCharacter M T = souriauPartition M T := by
  rfl

end SouriauThermodynamics
