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
abbrev GibbsFreeEnergyPacket : Type _ :=
  Σ' StateSpace : Type*,
    Σ' inverseTemperature : ℝ,
      Σ' energy : StateSpace → ℝ,
        Σ' logPartitionConstant : ℝ,
          Σ' gibbsWeight : StateSpace → ℝ,
            Σ' gibbsState : StateSpace,
              Σ' freeEnergy : StateSpace → ℝ,
                Σ' klToGibbs : StateSpace → ℝ,
                  Σ' gibbsWeight_eq :
                    ∀ s : StateSpace,
                      gibbsWeight s =
                        Real.exp (-(inverseTemperature * energy s) - logPartitionConstant),
                    Σ' freeEnergy_eq :
                      ∀ s : StateSpace,
                        freeEnergy s = energy s + inverseTemperature⁻¹ * klToGibbs s,
                      Type*

namespace GibbsFreeEnergyPacket

abbrev StateSpace (P : GibbsFreeEnergyPacket) : Type _ := P.1
abbrev inverseTemperature (P : GibbsFreeEnergyPacket) : ℝ := P.2.1
abbrev energy (P : GibbsFreeEnergyPacket) : StateSpace P → ℝ := P.2.2.1
abbrev logPartitionConstant (P : GibbsFreeEnergyPacket) : ℝ := P.2.2.2.1
abbrev gibbsWeight (P : GibbsFreeEnergyPacket) : StateSpace P → ℝ := P.2.2.2.2.1
abbrev gibbsState (P : GibbsFreeEnergyPacket) : StateSpace P := P.2.2.2.2.2.1
abbrev freeEnergy (P : GibbsFreeEnergyPacket) : StateSpace P → ℝ := P.2.2.2.2.2.2.1
abbrev klToGibbs (P : GibbsFreeEnergyPacket) : StateSpace P → ℝ := P.2.2.2.2.2.2.2.1
abbrev gibbsWeight_eq (P : GibbsFreeEnergyPacket) := P.2.2.2.2.2.2.2.2.1
abbrev freeEnergy_eq (P : GibbsFreeEnergyPacket) := P.2.2.2.2.2.2.2.2.2.1

end GibbsFreeEnergyPacket

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
abbrev ModularFlowPacket (Algebra : Type*) [Ring Algebra] : Type _ :=
  InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative.ModularFlow Algebra ×
    ((Algebra → ℝ) ×
      ((ℝ → Algebra → ℝ) ×
        ((Algebra → Algebra → ℝ) ×
          (ModularNormalizationReference × Algebra))))

namespace ModularFlowPacket

abbrev modularOwner {Algebra : Type*} [Ring Algebra]
    (P : ModularFlowPacket Algebra) :
    InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative.ModularFlow Algebra := P.1
abbrev modularHamiltonian {Algebra : Type*} [Ring Algebra]
    (P : ModularFlowPacket Algebra) : Algebra → ℝ := P.2.1
abbrev connesCocycle {Algebra : Type*} [Ring Algebra]
    (P : ModularFlowPacket Algebra) : ℝ → Algebra → ℝ := P.2.2.1
abbrev relativeModularPotential {Algebra : Type*} [Ring Algebra]
    (P : ModularFlowPacket Algebra) : Algebra → Algebra → ℝ := P.2.2.2.1
abbrev normalizationReference {Algebra : Type*} [Ring Algebra]
    (P : ModularFlowPacket Algebra) : ModularNormalizationReference := P.2.2.2.2.1
abbrev modularState {Algebra : Type*} [Ring Algebra]
    (P : ModularFlowPacket Algebra) : Algebra := P.2.2.2.2.2

end ModularFlowPacket

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

This remains a property-level wrapper of a generator and entropy/energy
functional decay shadow.
-/
abbrev GKSLPacket (n : ℕ) : Type _ :=
  Σ' hamiltonian : Matrix (Fin n) (Fin n) ℝ,
    Σ' jumpOperator : Matrix (Fin n) (Fin n) ℝ,
      Σ' generator : ℝ → Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ,
        Σ' generator_eq :
          ∀ t ρ,
            generator t ρ =
              TomitaTakesakiKMSEntropy.hamiltonianCommutator hamiltonian ρ +
                TomitaTakesakiKMSEntropy.lindbladDissipator jumpOperator ρ,
          Σ' freeEnergyShadow : Matrix (Fin n) (Fin n) ℝ → ℝ,
            Σ' freeEnergy_monotone :
              ∀ ρ t, 0 ≤ t → freeEnergyShadow (generator t ρ) ≤ freeEnergyShadow ρ,
              Matrix (Fin n) (Fin n) ℝ

namespace GKSLPacket

abbrev hamiltonian {n : ℕ} (P : GKSLPacket n) : Matrix (Fin n) (Fin n) ℝ := P.1
abbrev jumpOperator {n : ℕ} (P : GKSLPacket n) : Matrix (Fin n) (Fin n) ℝ := P.2.1
abbrev generator {n : ℕ} (P : GKSLPacket n) :
    ℝ → Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ := P.2.2.1
abbrev generator_eq {n : ℕ} (P : GKSLPacket n) :
    ∀ t ρ, P.2.2.1 t ρ =
      TomitaTakesakiKMSEntropy.hamiltonianCommutator P.1 ρ +
        TomitaTakesakiKMSEntropy.lindbladDissipator P.2.1 ρ := P.2.2.2.1
abbrev freeEnergyShadow {n : ℕ} (P : GKSLPacket n) :
    Matrix (Fin n) (Fin n) ℝ → ℝ := P.2.2.2.2.1
abbrev freeEnergy_monotone {n : ℕ} (P : GKSLPacket n) :
    ∀ ρ t, 0 ≤ t →
      P.2.2.2.2.1 (P.2.2.1 t ρ) ≤ P.2.2.2.2.1 ρ := P.2.2.2.2.2.1
abbrev equilibriumState {n : ℕ} (P : GKSLPacket n) :
    Matrix (Fin n) (Fin n) ℝ := P.2.2.2.2.2.2

end GKSLPacket

/-!
Finite spectral-thermal normalization schema.

These structures model the modular spectral partition function at the property level:
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

abbrev FiniteSpectralBoltzmannPartition (S : Type*) [Fintype S] :=
  SpectralBoltzmannPacket S

namespace FiniteSpectralBoltzmannPartition

/-- Compatibility accessor for the native dependent-sum carrier. -/
abbrev spectrum {S : Type*} [Fintype S]
    (Z : FiniteSpectralBoltzmannPartition S) : SpectralBoltzmannPacket S := Z

/-- The finite partition value determined by the supplied spectral data. -/
noncomputable abbrev partition
    {S : Type*} [Fintype S]
    (Z : FiniteSpectralBoltzmannPartition S) : ℝ :=
  ∑ s : S, Z.spectrum.boltzmannFactor s * Z.spectrum.spectralVolume s

/-- The partition value is exactly its defining finite spectral sum. -/
theorem partition_eq
    {S : Type*} [Fintype S]
    (Z : FiniteSpectralBoltzmannPartition S) :
    Z.partition =
      ∑ s : S, Z.spectrum.boltzmannFactor s * Z.spectrum.spectralVolume s := by
  rfl

end FiniteSpectralBoltzmannPartition

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
abbrev SpectralThermalNormalizationPacket : Type _ :=
  Σ' EnergySpace : Type*,
    Σ' SpectralGeometry : Type*,
      Σ' spectralVolume : EnergySpace → ℝ,
        Σ' energy : EnergySpace → ℝ,
          Σ' inverseTemperature : ℝ,
            Σ' inverseTemperature_pos : 0 < inverseTemperature,
              Σ' boltzmannPotential : EnergySpace → ℝ,
                Σ' boltzmannPotential_eq :
                  ∀ e : EnergySpace,
                    boltzmannPotential e = inverseTemperature * energy e,
                  Σ' partitionFunction : ℝ,
                    Σ' partitionFunction_pos : 0 < partitionFunction,
                      Type*

namespace SpectralThermalNormalizationPacket

abbrev EnergySpace (P : SpectralThermalNormalizationPacket) : Type _ := P.1
abbrev SpectralGeometry (P : SpectralThermalNormalizationPacket) : Type _ := P.2.1
abbrev spectralVolume (P : SpectralThermalNormalizationPacket) : EnergySpace P → ℝ := P.2.2.1
abbrev energy (P : SpectralThermalNormalizationPacket) : EnergySpace P → ℝ := P.2.2.2.1
abbrev inverseTemperature (P : SpectralThermalNormalizationPacket) : ℝ := P.2.2.2.2.1
abbrev inverseTemperature_pos (P : SpectralThermalNormalizationPacket) :
    0 < P.2.2.2.2.1 := P.2.2.2.2.2.1
abbrev boltzmannPotential (P : SpectralThermalNormalizationPacket) :
    EnergySpace P → ℝ := P.2.2.2.2.2.2.1
abbrev boltzmannPotential_eq (P : SpectralThermalNormalizationPacket) :=
  P.2.2.2.2.2.2.2.1
abbrev partitionFunction (P : SpectralThermalNormalizationPacket) : ℝ :=
  P.2.2.2.2.2.2.2.2.1
abbrev partitionFunction_pos (P : SpectralThermalNormalizationPacket) :
    0 < P.2.2.2.2.2.2.2.2.1 := P.2.2.2.2.2.2.2.2.2.1
abbrev normalizedSpectralState (P : SpectralThermalNormalizationPacket) : Type* :=
  P.2.2.2.2.2.2.2.2.2.2

end SpectralThermalNormalizationPacket

/--
Modular transport bridge packet.

This keeps the Connes-cocycle transport interpretation explicit at the
structural level: it records two-state modular frames and abstract transport
carriers between them.  Finite Connes-cocycle transport theorems are owned by
`InfoGeometry.GrandUnification.ModularTransport`.
-/
abbrev ModularTransportBridgePacket : Type _ :=
  Σ' VonNeumannSystem : Type*,
    Σ' StateWeightSpace : Type*,
      Σ' referenceWeight : StateWeightSpace,
        Σ' targetWeight : StateWeightSpace,
          Σ' modularFlow : StateWeightSpace → Type*,
            Σ' connesCocycle : StateWeightSpace → StateWeightSpace → Type*,
              Σ' modularPotential : Type*,
                Σ' transportFreeEnergy : Type*,
                  Type* × Type*

namespace ModularTransportBridgePacket

abbrev VonNeumannSystem (P : ModularTransportBridgePacket) : Type _ := P.1
abbrev StateWeightSpace (P : ModularTransportBridgePacket) : Type _ := P.2.1
abbrev referenceWeight (P : ModularTransportBridgePacket) : StateWeightSpace P := P.2.2.1
abbrev targetWeight (P : ModularTransportBridgePacket) : StateWeightSpace P := P.2.2.2.1
abbrev modularFlow (P : ModularTransportBridgePacket) : StateWeightSpace P → Type* := P.2.2.2.2.1
abbrev connesCocycle (P : ModularTransportBridgePacket) :
    StateWeightSpace P → StateWeightSpace P → Type* := P.2.2.2.2.2.1
abbrev modularPotential (P : ModularTransportBridgePacket) : Type* := P.2.2.2.2.2.2.1
abbrev transportFreeEnergy (P : ModularTransportBridgePacket) : Type* := P.2.2.2.2.2.2.2.1
abbrev holonomyComparison (P : ModularTransportBridgePacket) : Type* := P.2.2.2.2.2.2.2.2.1
abbrev perelmanComparison (P : ModularTransportBridgePacket) : Type* := P.2.2.2.2.2.2.2.2.2

end ModularTransportBridgePacket

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
abbrev ModularVolumePotentialPacket
    (SampleSpace Algebra : Type*) (n : ℕ)
    [MeasurableSpace SampleSpace] [Ring Algebra] : Type _ :=
  LogRadonNikodymPacket SampleSpace ×
    (RelativeSurprisalPacket SampleSpace ×
      (GibbsFreeEnergyPacket ×
        (ModularFlowPacket Algebra ×
          (SupervolumePacket Algebra × GKSLPacket n))))

namespace ModularVolumePotentialPacket

abbrev logRN {SampleSpace Algebra : Type*} {n : ℕ}
    [MeasurableSpace SampleSpace] [Ring Algebra]
    (P : ModularVolumePotentialPacket SampleSpace Algebra n) :
    LogRadonNikodymPacket SampleSpace := P.1
abbrev relativeKL {SampleSpace Algebra : Type*} {n : ℕ}
    [MeasurableSpace SampleSpace] [Ring Algebra]
    (P : ModularVolumePotentialPacket SampleSpace Algebra n) :
    RelativeSurprisalPacket SampleSpace := P.2.1
abbrev freeEnergy {SampleSpace Algebra : Type*} {n : ℕ}
    [MeasurableSpace SampleSpace] [Ring Algebra]
    (P : ModularVolumePotentialPacket SampleSpace Algebra n) : GibbsFreeEnergyPacket := P.2.2.1
abbrev modularFlow {SampleSpace Algebra : Type*} {n : ℕ}
    [MeasurableSpace SampleSpace] [Ring Algebra]
    (P : ModularVolumePotentialPacket SampleSpace Algebra n) : ModularFlowPacket Algebra := P.2.2.2.1
abbrev supervolume {SampleSpace Algebra : Type*} {n : ℕ}
    [MeasurableSpace SampleSpace] [Ring Algebra]
    (P : ModularVolumePotentialPacket SampleSpace Algebra n) : SupervolumePacket Algebra := P.2.2.2.2.1
abbrev dissipativeFlow {SampleSpace Algebra : Type*} {n : ℕ}
    [MeasurableSpace SampleSpace] [Ring Algebra]
    (P : ModularVolumePotentialPacket SampleSpace Algebra n) : GKSLPacket n := P.2.2.2.2.2

end ModularVolumePotentialPacket

/-!
Grand unification bridge packet.

This packet is intentionally structural: it records the carriers and explicit
comparison propositions for the classical, noncommutative modular, and
spectral-volume layers without promoting those propositions to local theorems.
-/
abbrev ModularVolumeBridgePacket : Type _ :=
  Σ' ClassicalMeasureSpace : Type*,
    Σ' VonNeumannSystem : Type*,
      Σ' SpectralGeometry : Type*,
        Σ' classicalState : Type*,
          Σ' classicalVolume : ClassicalMeasureSpace → ℝ,
            Σ' classicalLogPotential : classicalState → ClassicalMeasureSpace → ℝ,
              Σ' modularWeight : Type*,
                Σ' modularData : modularWeight → modularWeight → Type*,
                  Σ' ModularHamiltonianCarrier : Type*,
                    Σ' modularHamiltonian : modularWeight → ModularHamiltonianCarrier,
                      Σ' stateToModularWeight : classicalState → modularWeight,
                        Σ' klDivergence : classicalState → classicalState → ℝ,
                          Σ' arakiRelativeEntropy : modularWeight → modularWeight → ℝ,
                            Σ' energy : classicalState → ℝ,
                              Σ' freeEnergy : classicalState → ℝ,
                                Σ' inverseTemperature : ℝ,
                                  Σ' gibbsReference : classicalState,
                                    Σ' spectralVolume : SpectralGeometry → ℝ,
                                      Σ' weylVolumeGauge : SpectralGeometry → ℝ,
                                        Σ' spectralThermalNormalization :
                                          SpectralThermalNormalizationPacket,
                                          ModularTransportBridgePacket

namespace ModularVolumeBridgePacket

abbrev tail₁ (B : ModularVolumeBridgePacket) := B.2
abbrev tail₂ (B : ModularVolumeBridgePacket) := (tail₁ B).2
abbrev tail₃ (B : ModularVolumeBridgePacket) := (tail₂ B).2
abbrev tail₄ (B : ModularVolumeBridgePacket) := (tail₃ B).2
abbrev tail₅ (B : ModularVolumeBridgePacket) := (tail₄ B).2
abbrev tail₆ (B : ModularVolumeBridgePacket) := (tail₅ B).2
abbrev tail₇ (B : ModularVolumeBridgePacket) := (tail₆ B).2
abbrev tail₈ (B : ModularVolumeBridgePacket) := (tail₇ B).2
abbrev tail₉ (B : ModularVolumeBridgePacket) := (tail₈ B).2
abbrev tail₁₀ (B : ModularVolumeBridgePacket) := (tail₉ B).2
abbrev tail₁₁ (B : ModularVolumeBridgePacket) := (tail₁₀ B).2
abbrev tail₁₂ (B : ModularVolumeBridgePacket) := (tail₁₁ B).2
abbrev tail₁₃ (B : ModularVolumeBridgePacket) := (tail₁₂ B).2
abbrev tail₁₄ (B : ModularVolumeBridgePacket) := (tail₁₃ B).2
abbrev tail₁₅ (B : ModularVolumeBridgePacket) := (tail₁₄ B).2
abbrev tail₁₆ (B : ModularVolumeBridgePacket) := (tail₁₅ B).2
abbrev tail₁₇ (B : ModularVolumeBridgePacket) := (tail₁₆ B).2
abbrev tail₁₈ (B : ModularVolumeBridgePacket) := (tail₁₇ B).2
abbrev tail₁₉ (B : ModularVolumeBridgePacket) := (tail₁₈ B).2
abbrev tail₂₀ (B : ModularVolumeBridgePacket) := (tail₁₉ B).2

abbrev ClassicalMeasureSpace (B : ModularVolumeBridgePacket) : Type _ := B.1
abbrev VonNeumannSystem (B : ModularVolumeBridgePacket) : Type _ := (tail₁ B).1
abbrev SpectralGeometry (B : ModularVolumeBridgePacket) : Type _ := (tail₂ B).1
abbrev classicalState (B : ModularVolumeBridgePacket) : Type _ := (tail₃ B).1
abbrev classicalVolume (B : ModularVolumeBridgePacket) : ClassicalMeasureSpace B → ℝ := (tail₄ B).1
abbrev classicalLogPotential (B : ModularVolumeBridgePacket) :
    classicalState B → ClassicalMeasureSpace B → ℝ := (tail₅ B).1
abbrev modularWeight (B : ModularVolumeBridgePacket) : Type _ := (tail₆ B).1
abbrev modularData (B : ModularVolumeBridgePacket) :
    modularWeight B → modularWeight B → Type _ := (tail₇ B).1
abbrev ModularHamiltonianCarrier (B : ModularVolumeBridgePacket) : Type _ := (tail₈ B).1
abbrev modularHamiltonian (B : ModularVolumeBridgePacket) :
    modularWeight B → ModularHamiltonianCarrier B := (tail₉ B).1
abbrev stateToModularWeight (B : ModularVolumeBridgePacket) :
    classicalState B → modularWeight B := (tail₁₀ B).1
abbrev klDivergence (B : ModularVolumeBridgePacket) :
    classicalState B → classicalState B → ℝ := (tail₁₁ B).1
abbrev arakiRelativeEntropy (B : ModularVolumeBridgePacket) :
    modularWeight B → modularWeight B → ℝ := (tail₁₂ B).1
abbrev energy (B : ModularVolumeBridgePacket) : classicalState B → ℝ := (tail₁₃ B).1
abbrev freeEnergy (B : ModularVolumeBridgePacket) : classicalState B → ℝ := (tail₁₄ B).1
abbrev inverseTemperature (B : ModularVolumeBridgePacket) : ℝ := (tail₁₅ B).1
abbrev gibbsReference (B : ModularVolumeBridgePacket) : classicalState B := (tail₁₆ B).1
abbrev spectralVolume (B : ModularVolumeBridgePacket) : SpectralGeometry B → ℝ := (tail₁₇ B).1
abbrev weylVolumeGauge (B : ModularVolumeBridgePacket) : SpectralGeometry B → ℝ := (tail₁₈ B).1
abbrev spectralThermalNormalization (B : ModularVolumeBridgePacket) :
    SpectralThermalNormalizationPacket := (tail₁₉ B).1
abbrev modularTransport (B : ModularVolumeBridgePacket) : ModularTransportBridgePacket := tail₂₀ B

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
