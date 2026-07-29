import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative
import InfoGeometry.OperatorAlgebra.ModularWeightTrace
import InfoGeometry.Canonical.TomitaTakesakiKMSEntropyBracket

/-!
# InfoGeometry.ModularVolumePotential

Theorem-safe data surface for the modular thermodynamic layer:

* classical log-Radon–Nikodym potentials,
* relative surprisal and KL-style divergence readouts,
* Gibbs/free-energy regularization,
* Tomita–Takesaki-style modular flow data,
* and a supertrace-oriented extension.

No analytic theorems are asserted here.  All declarations are structural
packets and constructors exposing the data required by later owner pipelines.
-/

noncomputable section

namespace InfoGeometry

namespace ModularVolumePotential

/--
Classical Radon–Nikodym potential packet.

The field `logPotential` is the signed logarithmic density (surprisal) and
`relativeDensity` is the raw density with respect to a reference volume.
-/
abbrev LogRadonNikodymPacket (SampleSpace : Type*) [MeasurableSpace SampleSpace] : Type _ :=
  Σ' referenceMeasure : MeasureTheory.Measure SampleSpace,
    Σ' stateMeasure : MeasureTheory.Measure SampleSpace,
      Σ' relativeDensity : SampleSpace → ℝ,
        Σ' logPotential : SampleSpace → ℝ,
          ∀ x, logPotential x = -Real.log (relativeDensity x)

/--
Relative surprisal / KL packet.

`relativeLogPotential` plays the role of
`log(dμ/dη)`, and `klReadout` is the corresponding scalar divergence-like
expectation value.
-/
abbrev RelativeSurprisalPacket
    (SampleSpace : Type*) [MeasurableSpace SampleSpace] : Type _ :=
  Σ' sourceMeasure : MeasureTheory.Measure SampleSpace,
    Σ' referenceMeasure : MeasureTheory.Measure SampleSpace,
      Σ' relativeDensity : SampleSpace → ENNReal,
        Σ' sourceMeasure_eq_withDensity :
          sourceMeasure = referenceMeasure.withDensity relativeDensity,
          Σ' relativeLogPotential : SampleSpace → ℝ,
            Σ' relativeLogPotential_eq :
              (∀ x, relativeLogPotential x =
                -Real.log ((relativeDensity x).toReal)),
              ℝ

namespace RelativeSurprisalPacket

abbrev sourceMeasure {SampleSpace : Type*} [MeasurableSpace SampleSpace]
    (P : RelativeSurprisalPacket SampleSpace) : MeasureTheory.Measure SampleSpace := P.1
abbrev referenceMeasure {SampleSpace : Type*} [MeasurableSpace SampleSpace]
    (P : RelativeSurprisalPacket SampleSpace) : MeasureTheory.Measure SampleSpace := P.2.1
abbrev relativeDensity {SampleSpace : Type*} [MeasurableSpace SampleSpace]
    (P : RelativeSurprisalPacket SampleSpace) : SampleSpace → ENNReal := P.2.2.1
abbrev sourceMeasure_eq_withDensity {SampleSpace : Type*} [MeasurableSpace SampleSpace]
    (P : RelativeSurprisalPacket SampleSpace) :
    P.1 = P.2.1.withDensity P.2.2.1 := P.2.2.2.1
abbrev relativeLogPotential {SampleSpace : Type*} [MeasurableSpace SampleSpace]
    (P : RelativeSurprisalPacket SampleSpace) : SampleSpace → ℝ := P.2.2.2.2.1
abbrev relativeLogPotential_eq {SampleSpace : Type*} [MeasurableSpace SampleSpace]
    (P : RelativeSurprisalPacket SampleSpace) :
    ∀ x, P.2.2.2.2.1 x =
      -Real.log ((P.2.2.1 x).toReal) := P.2.2.2.2.2.1
abbrev klReadout {SampleSpace : Type*} [MeasurableSpace SampleSpace]
    (P : RelativeSurprisalPacket SampleSpace) : ℝ := P.2.2.2.2.2.2

end RelativeSurprisalPacket

/--
Finite/free-energy packet.

This captures the Gibbs regularization pattern
`σβ ∝ e^{-βH}/Zβ` at a constructive level.
-/
structure GibbsFreeEnergyPacket where
  /-- Energy observable or Hamiltonian on a state carrier. -/
  StateSpace : Type*
  /-- Inverse temperature β. -/
  inverseTemperature : ℝ
  /-- Energy readout. -/
  energy : StateSpace → ℝ
  /-- Gibbs partition log-normalizer (the additive constant `log Z_β`). -/
  logPartitionConstant : ℝ
  /-- A Gibbs-style density map on state space. -/
  gibbsWeight : StateSpace → ℝ
  /-- Gibbs reference state witness. -/
  gibbsState : StateSpace
  /-- Free-energy functional (as an explicit scalar readout). -/
  freeEnergy : StateSpace → ℝ

  /-- Relative divergence to Gibbs readout (`KL_to_Gibbs`). -/
  klToGibbs : StateSpace → ℝ

  /-- Gibbs law (`gibbsWeight = exp(-(βE+logZ))`). -/
  gibbsWeight_eq :
    ∀ s, gibbsWeight s = Real.exp (-(inverseTemperature * energy s) - logPartitionConstant)
  /-- Free-energy splitting witness (`F = E + β⁻¹ KL_to_Gibbs`). -/
  freeEnergy_eq :
    ∀ s, freeEnergy s = energy s + inverseTemperature⁻¹ * klToGibbs s

/-- Normalization source for modular thermodynamics. -/
inductive ModularNormalizationReference where
  /-- A trace/weight normalization is available. -/
  | trace (partition : ℝ)
  /-- Type-III-style normalization is supplied by modular/KMS data. -/
  | kms (partition : ℝ)

/--
Noncommutative modular-flow packet (Tomita–Takesaki style skeleton).

No full modular theory is assumed; the fields record only explicit
compatible data supplied by witnesses.
-/
structure ModularFlowPacket (Algebra : Type*) [Ring Algebra] where
  /-- The operator-valued modular flow owner. -/
  modularOwner :
    InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative.ModularFlow Algebra
  /-- Modular Hamiltonian (log density/potential) on states. -/
  modularHamiltonian : Algebra → ℝ
  /-- Connes cocycle trace shadow (`[Dφ:Dψ]_t` in abstract notation). -/
  connesCocycle : ℝ → Algebra → ℝ
  /-- Relative modular potential witness. -/
  relativeModularPotential : Algebra → Algebra → ℝ
  /-- Explicit choice between trace and modular/KMS normalization. -/
  normalizationReference : ModularNormalizationReference

  /-- Distinguished state/witness carrying the modular data. -/
  modularState : Algebra

/--
Supervolume layer (graded/signed trace skeleton).
-/
abbrev SupervolumePacket (Algebra : Type*) [Ring Algebra] : Type _ :=
  Σ' supertraceOwner : InfoGeometry.OperatorAlgebra.SuperTraceDatum Algebra,
    Σ' evenTrace : Algebra → ℝ,
      Σ' oddTrace : Algebra → ℝ,
        ∀ x : Algebra,
          supertraceOwner.supertrace x = evenTrace x - oddTrace x

/--
Dissipative KMS-compatible flow skeleton (GKSL-style container).

This remains a witness-level wrapper of a generator and entropy/energy
functional decay shadow.
-/
structure GKSLPacket (n : ℕ) where
  /-- Hamiltonian matrix in the noncommutative state algebra. -/
  hamiltonian : Matrix (Fin n) (Fin n) ℝ
  /-- Lindblad jump operator matrix. -/
  jumpOperator : Matrix (Fin n) (Fin n) ℝ
  /-- One-parameter generator on matrix states. -/
  generator : ℝ → Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ
  /-- Generator is the canonical Hamiltonian plus Lindblad dissipator. -/
  generator_eq : ∀ t ρ,
    generator t ρ =
      TomitaTakesakiKMSEntropy.hamiltonianCommutator hamiltonian ρ +
        TomitaTakesakiKMSEntropy.lindbladDissipator jumpOperator ρ
  /-- Energy/potential Lyapunov readout carried by the flow. -/
  freeEnergyShadow : Matrix (Fin n) (Fin n) ℝ → ℝ
  /-- Dissipative monotonicity for nonnegative time (shadow law). -/
  freeEnergy_monotone :
    ∀ ρ t, 0 ≤ t → freeEnergyShadow (generator t ρ) ≤ freeEnergyShadow ρ

  /-- Equilibrium/reference state used by the flow data. -/
  equilibriumState : Matrix (Fin n) (Fin n) ℝ

/-!
Finite spectral-thermal normalization schema.

These structures model the modular spectral partition function at the witness level:
`Z = Σ e^{-βE} dν_H(E)` on a finite spectrum index.
-/
/-- Spectral data with explicit modular tilt. -/
abbrev SpectralBoltzmannPacket (S : Type*) : Type _ :=
  Σ' inverseTemperature : ℝ,
    Σ' spectralEnergy : S → ℝ,
      Σ' spectralVolume : S → ℝ,
        Σ' modularPotential : S → ℝ,
          Σ' boltzmannFactor : S → ℝ,
            (∀ s : S, modularPotential s = inverseTemperature * spectralEnergy s) ∧
              ∀ s : S, boltzmannFactor s = Real.exp (- modularPotential s)

namespace SpectralBoltzmannPacket

abbrev inverseTemperature {S : Type*} (Z : SpectralBoltzmannPacket S) : ℝ := Z.1
abbrev spectralEnergy {S : Type*} (Z : SpectralBoltzmannPacket S) : S → ℝ := Z.2.1
abbrev spectralVolume {S : Type*} (Z : SpectralBoltzmannPacket S) : S → ℝ := Z.2.2.1
abbrev modularPotential {S : Type*} (Z : SpectralBoltzmannPacket S) : S → ℝ := Z.2.2.2.1
abbrev boltzmannFactor {S : Type*} (Z : SpectralBoltzmannPacket S) : S → ℝ := Z.2.2.2.2.1
abbrev modularPotential_eq {S : Type*} (Z : SpectralBoltzmannPacket S) :
    ∀ s : S, Z.2.2.2.1 s = Z.1 * Z.2.1 s := Z.2.2.2.2.2.1
abbrev boltzmannFactor_eq {S : Type*} (Z : SpectralBoltzmannPacket S) :
    ∀ s : S, Z.2.2.2.2.1 s = Real.exp (- Z.2.2.2.1 s) := Z.2.2.2.2.2.2

end SpectralBoltzmannPacket

structure FiniteSpectralBoltzmannPartition (S : Type*) [Fintype S] where
  /-- Spectral tilt data for the model. -/
  spectrum : SpectralBoltzmannPacket S
  /-- Partition value (`Z_β`) for the supplied finite spectrum. -/
  partition : ℝ
  /-- Core partition identity, expressed as finite spectral sum. -/
  partition_eq :
    partition = ∑ s : S, spectrum.boltzmannFactor s * spectrum.spectralVolume s

/--
Partition normalization identity in the explicit tilt form.

This is the structural theorem-schema version of
`Z_β = \sum_s e^{-βE(s)} \\, dν_H(s)`.
-/
theorem finiteSpectralPartitionNormalization
    (S : Type*) [Fintype S]
    (Z : FiniteSpectralBoltzmannPartition S) :
    Z.partition =
      ∑ s : S,
        Real.exp (- (Z.spectrum.inverseTemperature * Z.spectrum.spectralEnergy s)) *
          Z.spectrum.spectralVolume s := by
  calc
    Z.partition = ∑ s : S, Z.spectrum.boltzmannFactor s * Z.spectrum.spectralVolume s :=
      Z.partition_eq
    _ = ∑ s : S, Real.exp (- Z.spectrum.modularPotential s) *
          Z.spectrum.spectralVolume s := by
      refine Finset.sum_congr rfl ?_
      intro s hs
      change Z.spectrum.2.2.2.2.1 s * Z.spectrum.2.2.1 s =
        Real.exp (-Z.spectrum.2.2.2.1 s) * Z.spectrum.2.2.1 s
      rw [SpectralBoltzmannPacket.boltzmannFactor_eq Z.spectrum s]
    _ = ∑ s : S, Real.exp (-(Z.spectrum.inverseTemperature * Z.spectrum.spectralEnergy s)) *
          Z.spectrum.spectralVolume s := by
      refine Finset.sum_congr rfl ?_
      intro s hs
      change Real.exp (-Z.spectrum.2.2.2.1 s) * Z.spectrum.2.2.1 s =
        Real.exp (-(Z.spectrum.1 * Z.spectrum.2.1 s)) * Z.spectrum.2.2.1 s
      rw [SpectralBoltzmannPacket.modularPotential_eq Z.spectrum s]

/-- The capstone normalization schema for finite spectral thermodynamics. -/
def FiniteSpectralThermodynamicNormalizationSchema (S : Type*) [Fintype S] : Prop :=
  ∀ (Z : FiniteSpectralBoltzmannPartition S),
    Z.partition =
      ∑ s : S,
        Real.exp (- (Z.spectrum.inverseTemperature * Z.spectrum.spectralEnergy s)) *
          Z.spectrum.spectralVolume s

/-- Constructor witnessing the finite spectral thermodynamic normalization schema. -/
theorem constructFiniteSpectralThermodynamicNormalizationSchema
    (S : Type*) [Fintype S] :
    FiniteSpectralThermodynamicNormalizationSchema S := by
  intro Z
  exact finiteSpectralPartitionNormalization S Z

/-!
Modular thermodynamic subpacket for Boltzmann-normalized spectral volume.

This packet is theorem-safe: it records explicit finite-stage data for the
Boltzmann tilt and normalization of spectral volume.  It does not assert
analytic assumptions.
-/
structure SpectralThermalNormalizationPacket where
  /-- Energy/spectral parameter space. -/
  EnergySpace : Type*
  /-- Spectral geometry/topology shadow carrying the energy label space. -/
  SpectralGeometry : Type*
  /-- Spectral volume/density-of-states datum (`dν_H`). -/
  spectralVolume : EnergySpace → ℝ
  /-- Energy readout (`E`). -/
  energy : EnergySpace → ℝ
  /-- Inverse temperature (`β`). -/
  inverseTemperature : ℝ
  /-- Witness that the inverse temperature is strictly positive. -/
  inverseTemperature_pos : 0 < inverseTemperature
  /-- Boltzmann/modular potential (`β * E` in the standard model). -/
  boltzmannPotential : EnergySpace → ℝ
  /-- Explicit Boltzmann potential law (`β * E`). -/
  boltzmannPotential_eq :
    ∀ e : EnergySpace, boltzmannPotential e = inverseTemperature * energy e
  /-- Spectral normalization constant (`Z_β`). -/
  partitionFunction : ℝ
  /-- Positivity of the normalization constant (`Z_β > 0`). -/
  partitionFunction_pos : 0 < partitionFunction
  /-- Normalized spectral Gibbs/KMS-type state carrier. -/
  normalizedSpectralState : Type*

/--
Modular transport bridge packet.

This keeps the Connes-cocycle transport interpretation explicit at the
structural level: it records two-state modular frames and abstract transport
carriers between them.  Finite Connes-cocycle transport theorems are owned by
`InfoGeometry.GrandUnification.ModularTransport`.
-/
structure ModularTransportBridgePacket where
  /-- Von Neumann / operator-algebraic system carrier. -/
  VonNeumannSystem : Type*
  /-- Parameterized space of faithful states/weights. -/
  StateWeightSpace : Type*
  /-- Source/reference state or weight. -/
  referenceWeight : StateWeightSpace
  /-- Target/endpoint state or weight. -/
  targetWeight : StateWeightSpace
  /-- Modular flow attached to a state/weight. -/
  modularFlow : StateWeightSpace → Type*
  /-- Connes cocycle / transport carrier between two weights. -/
  connesCocycle : StateWeightSpace → StateWeightSpace → Type*
  /-- Log-potential / modular Hamiltonian on the transport path. -/
  modularPotential : Type*
  /-- Relative-entropy or free-energy transport cost carrier. -/
  transportFreeEnergy : Type*
  /-- Optional Berry/holonomy comparison carrier. -/
  holonomyComparison : Type*
  /-- Optional Ricci/Perelman transport comparison carrier. -/
  perelmanComparison : Type*

/-!
Normalize by the supplied modular reference data, with an explicit branch for
type III/trace-free situations.
-/
def modularPartitionNormalization
    {Algebra : Type*} [Ring Algebra]
    (mf : ModularFlowPacket Algebra) : ℝ := by
  exact match mf.normalizationReference with
    | .trace partition => partition
    | .kms partition => partition

/-- Modular normalization is by trace when a trace reference is supplied. -/
theorem modularPartitionNormalization_trace
    {Algebra : Type*} [Ring Algebra]
    (mf : ModularFlowPacket Algebra) (partition : ℝ)
    (h : mf.normalizationReference = .trace partition) :
    modularPartitionNormalization mf = partition := by
  rw [modularPartitionNormalization, h]

/-- Modular normalization is by KMS/modular data when no trace reference is supplied. -/
theorem modularPartitionNormalization_kms
    {Algebra : Type*} [Ring Algebra]
    (mf : ModularFlowPacket Algebra) (partition : ℝ)
    (h : mf.normalizationReference = .kms partition) :
    modularPartitionNormalization mf = partition := by
  rw [modularPartitionNormalization, h]

/--
Integrated modular-volume thermodynamic packet.
-/
structure ModularVolumePotentialPacket
    (SampleSpace Algebra : Type*) (n : ℕ)
    [MeasurableSpace SampleSpace] [Ring Algebra] where
  /-- Classical measure/potential layer. -/
  logRN : LogRadonNikodymPacket SampleSpace
  /-- Relative surprisal and KL readout layer. -/
  relativeKL : RelativeSurprisalPacket SampleSpace
  /-- Gibbs/free-energy layer. -/
  freeEnergy : GibbsFreeEnergyPacket
  /-- Modular flow and modular Hamiltonian layer. -/
  modularFlow : ModularFlowPacket Algebra
  /-- Graded/supertrace layer. -/
  supervolume : SupervolumePacket Algebra
  /-- Dissipative/KMS-compatible flow layer. -/
  dissipativeFlow : GKSLPacket n

/-!
Grand unification bridge packet.

This packet is intentionally structural: it records the carriers and explicit
comparison propositions for the classical, noncommutative modular, and
spectral-volume layers without promoting those propositions to local theorems.
-/
structure ModularVolumeBridgePacket where
  ClassicalMeasureSpace : Type*
  VonNeumannSystem : Type*
  SpectralGeometry : Type*
  /-- Classical state/density carrier. -/
  classicalState : Type*
  /-- Classical reference volume/measure readout. -/
  classicalVolume : ClassicalMeasureSpace → ℝ
  /-- Logarithmic Radon–Nikodym potential. -/
  classicalLogPotential : classicalState → ClassicalMeasureSpace → ℝ
  /-- Modular reference weight/state carrier. -/
  modularWeight : Type*
  /-- Relative modular data carrier (`[Dφ:Dψ]`, modular operators, etc.). -/
  modularData : modularWeight → modularWeight → Type*
  /-- Carrier of modular Hamiltonians / modular log-potentials. -/
  ModularHamiltonianCarrier : Type*
  /-- Modular Hamiltonian attached to a reference weight. -/
  modularHamiltonian : modularWeight → ModularHamiltonianCarrier
  /-- Map comparing a classical state with its modular-weight realization. -/
  stateToModularWeight : classicalState → modularWeight
  /-- Classical KL-divergence functional. -/
  klDivergence : classicalState → classicalState → ℝ
  /-- Araki relative-entropy functional. -/
  arakiRelativeEntropy : modularWeight → modularWeight → ℝ
  /-- Energy and free-energy functionals on classical states. -/
  energy : classicalState → ℝ
  freeEnergy : classicalState → ℝ
  /-- Gibbs comparison data used by the free-energy split. -/
  inverseTemperature : ℝ
  gibbsReference : classicalState
  /-- Spectral volume and its Weyl-gauge comparison readout. -/
  spectralVolume : SpectralGeometry → ℝ
  weylVolumeGauge : SpectralGeometry → ℝ
  /-- Spectral thermal normalization data (`Z_β`). -/
  spectralThermalNormalization : SpectralThermalNormalizationPacket
  /-- Connes-cocycle transport data. -/
  modularTransport : ModularTransportBridgePacket

namespace ModularVolumeBridgePacket

/-- KL and Araki entropy agree after the selected state-to-weight realization. -/
def entropyComparison (B : ModularVolumeBridgePacket) : Prop :=
  ∀ μ η : B.classicalState,
    B.klDivergence μ η =
      B.arakiRelativeEntropy
        (B.stateToModularWeight μ) (B.stateToModularWeight η)

/-- Free energy is energy plus the inverse-temperature-scaled Gibbs divergence. -/
def freeEnergyComparison (B : ModularVolumeBridgePacket) : Prop :=
  ∀ μ : B.classicalState,
    B.freeEnergy μ =
      B.energy μ +
        B.inverseTemperature⁻¹ * B.klDivergence μ B.gibbsReference

/-- Spectral volume agrees pointwise with the selected Weyl-volume gauge. -/
def spectralVolumeComparison (B : ModularVolumeBridgePacket) : Prop :=
  ∀ x : B.SpectralGeometry,
    B.spectralVolume x = B.weylVolumeGauge x

end ModularVolumeBridgePacket

namespace LogRadonNikodymPacket

abbrev referenceMeasure {SampleSpace : Type*} [MeasurableSpace SampleSpace]
    (P : LogRadonNikodymPacket SampleSpace) : MeasureTheory.Measure SampleSpace := P.1

abbrev stateMeasure {SampleSpace : Type*} [MeasurableSpace SampleSpace]
    (P : LogRadonNikodymPacket SampleSpace) : MeasureTheory.Measure SampleSpace := P.2.1

abbrev relativeDensity {SampleSpace : Type*} [MeasurableSpace SampleSpace]
    (P : LogRadonNikodymPacket SampleSpace) : SampleSpace → ℝ := P.2.2.1

abbrev logPotential {SampleSpace : Type*} [MeasurableSpace SampleSpace]
    (P : LogRadonNikodymPacket SampleSpace) : SampleSpace → ℝ := P.2.2.2.1

abbrev logPotential_eq {SampleSpace : Type*} [MeasurableSpace SampleSpace]
    (P : LogRadonNikodymPacket SampleSpace) :
    ∀ x, P.2.2.2.1 x = -Real.log (P.2.2.1 x) := P.2.2.2.2

/-- Rewrite `logPotential` as a negative log-density. -/
@[simp] theorem logPotential_eq_neg_log_density
    {SampleSpace : Type*} [MeasurableSpace SampleSpace]
    (P : LogRadonNikodymPacket SampleSpace) (x : SampleSpace) :
    P.logPotential x = -Real.log (P.relativeDensity x) := by
  exact P.logPotential_eq x

end LogRadonNikodymPacket

namespace GibbsFreeEnergyPacket

/-- Exponential Gibbs-weight law projection. -/
@[simp] theorem gibbsWeight_eq_exp
    (P : GibbsFreeEnergyPacket) (s : P.StateSpace) :
    P.gibbsWeight s = Real.exp (-(P.inverseTemperature * P.energy s) - P.logPartitionConstant) := by
  exact P.gibbsWeight_eq s

/-- Free-energy split projection. -/
theorem freeEnergy_eq_energy_add_betaInv_mul_KL
    (P : GibbsFreeEnergyPacket) (s : P.StateSpace) :
    P.freeEnergy s = P.energy s + P.inverseTemperature⁻¹ * P.klToGibbs s := by
  exact P.freeEnergy_eq s

end GibbsFreeEnergyPacket

namespace SpectralBoltzmannPacket

/-- Boltzmann factor in the standard form `exp(-(β*E))`. -/
theorem boltzmannFactor_eq_exp_neg_beta_energy
    (S : Type*) (Z : SpectralBoltzmannPacket S) (s : S) :
    Z.boltzmannFactor s = Real.exp (-(Z.inverseTemperature * Z.spectralEnergy s)) := by
  change Z.2.2.2.2.1 s = Real.exp (-(Z.1 * Z.2.1 s))
  rw [SpectralBoltzmannPacket.boltzmannFactor_eq Z s,
    SpectralBoltzmannPacket.modularPotential_eq Z s]

end SpectralBoltzmannPacket

namespace SupervolumePacket

abbrev supertraceOwner {Algebra : Type*} [Ring Algebra]
    (P : SupervolumePacket Algebra) :
    InfoGeometry.OperatorAlgebra.SuperTraceDatum Algebra := P.1

abbrev evenTrace {Algebra : Type*} [Ring Algebra]
    (P : SupervolumePacket Algebra) : Algebra → ℝ := P.2.1

abbrev oddTrace {Algebra : Type*} [Ring Algebra]
    (P : SupervolumePacket Algebra) : Algebra → ℝ := P.2.2.1

abbrev supertrace_eq {Algebra : Type*} [Ring Algebra]
    (P : SupervolumePacket Algebra) :
    ∀ x : Algebra,
      P.1.supertrace x = P.2.1 x - P.2.2.1 x := P.2.2.2

def supertrace {Algebra : Type*} [Ring Algebra]
    (P : SupervolumePacket Algebra) : Algebra → ℝ :=
  P.supertraceOwner.supertrace

@[simp] theorem supertrace_eq_even_sub_odd
    {Algebra : Type*} [Ring Algebra]
    (P : SupervolumePacket Algebra) (x : Algebra) :
    P.supertrace x = P.evenTrace x - P.oddTrace x := by
  exact P.supertrace_eq x

end SupervolumePacket

namespace GKSLPacket

/-- Free-energy decay is the native Lyapunov inequality at nonnegative time. -/
def freeEnergyDecay
    {n : ℕ} (P : GKSLPacket n)
    (ρ : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : Prop :=
  0 ≤ t →
    P.freeEnergyShadow (P.generator t ρ) ≤ P.freeEnergyShadow ρ

/-- The installed GKSL monotonicity law proves the derived decay predicate. -/
theorem freeEnergyDecay_holds_apply
    {n : ℕ} (P : GKSLPacket n)
    (ρ : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    P.freeEnergyDecay ρ t :=
  P.freeEnergy_monotone ρ t

/-- Dissipative shadow generator contract (nonnegative times only). -/
theorem freeEnergyShadow_generator_le
    {n : ℕ} (P : GKSLPacket n)
    (ρ : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (ht : 0 ≤ t) :
    P.freeEnergyShadow (P.generator t ρ) ≤ P.freeEnergyShadow ρ := by
  exact P.freeEnergy_monotone ρ t ht

end GKSLPacket

end ModularVolumePotential

end InfoGeometry
