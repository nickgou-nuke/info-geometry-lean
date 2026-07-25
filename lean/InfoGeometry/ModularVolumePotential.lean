import Mathlib.Tactic

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
structure LogRadonNikodymPacket where
  /-- Underlying event/sample type. -/
  SampleSpace : Type*
  /-- Reference volume state carrier (e.g. ν). -/
  ReferenceCarrier : Type*
  /-- State carrier (e.g. μ). -/
  StateCarrier : Type*
  /-- Density of states against reference (`dμ/dν`). -/
  relativeDensity : StateCarrier → SampleSpace → ℝ
  /-- Log-potential (`−log(dμ/dν)`). -/
  logPotential : StateCarrier → SampleSpace → ℝ

  /-- Signed log law: `logPotential = -log(relativeDensity)`. -/
  logPotential_eq :
    ∀ μ x, logPotential μ x = -Real.log (relativeDensity μ x)

  /-- Reference volume witness carried by the packet. -/
  referenceVolume : ReferenceCarrier

  /-- Chosen reference carrier for the state. -/
  stateVolume : StateCarrier

/--
Relative surprisal / KL packet.

`relativeLogPotential` plays the role of
`log(dμ/dη)`, and `klReadout` is the corresponding scalar divergence-like
expectation value.
-/
structure RelativeSurprisalPacket where
  /-- Source state of the KL comparison. -/
  SourceState : Type*
  /-- Reference state of the KL comparison. -/
  ReferenceState : Type*

  /-- Relative log-density on sample points (`log(dμ/dη)`). -/
  relativeLogPotential : SourceState → ReferenceState → ℝ → ℝ

  /-- Scalar divergence-like readout for each pair of states. -/
  klReadout : SourceState → ReferenceState → ℝ

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

/--
Noncommutative modular-flow packet (Tomita–Takesaki style skeleton).

No full modular theory is assumed; the fields record only explicit
compatible data supplied by witnesses.
-/
structure ModularFlowPacket where
  /-- Algebra/observable carrier. -/
  AlgebraCarrier : Type*
  /-- State/cyclic-vector carrier used by the modular packet. -/
  StateCarrier : Type*
  /-- Modular time action. -/
  modularFlow : ℝ → StateCarrier → StateCarrier
  /-- Modular Hamiltonian (log density/potential) on states. -/
  modularHamiltonian : StateCarrier → ℝ
  /-- Connes cocycle trace shadow (`[Dφ:Dψ]_t` in abstract notation). -/
  connesCocycle : ℝ → StateCarrier → ℝ
  /-- Relative modular potential witness. -/
  relativeModularPotential : StateCarrier → StateCarrier → ℝ
  /-- Whether a trace/volume reference has been explicitly chosen.

      In Type III regimes this is typically false and modular/KMS data is
      primary.
  -/
  hasTraceReference : Prop
  /-- Trace-based normalization, when a trace/weight reference is supplied. -/
  tracePartition : hasTraceReference → ℝ
  /-- KMS/modular normalization, when no trace/weight reference is supplied. -/
  kmsPartition : ¬ hasTraceReference → ℝ

  /-- Distinguished state/witness carrying the modular data. -/
  modularState : StateCarrier

/--
Supervolume layer (graded/signed trace skeleton).
-/
structure SupervolumePacket where
  /-- Graded object carrier. -/
  GradedCarrier : Type*
  /-- Even sector. -/
  EvenSector : Type*
  /-- Odd sector. -/
  OddSector : Type*
  /-- Even-trace contribution. -/
  evenTrace : GradedCarrier → ℝ
  /-- Odd-trace contribution. -/
  oddTrace : GradedCarrier → ℝ
  /-- Supertrace/effective signed volume assignment. -/
  supertrace : GradedCarrier → ℝ
  /-- Supertrace as graded difference: `Str = Tr_even - Tr_odd`. -/
  supertrace_eq : ∀ x : GradedCarrier, supertrace x = evenTrace x - oddTrace x

/--
Dissipative KMS-compatible flow skeleton (GKSL-style container).

This remains a witness-level wrapper of a generator and entropy/energy
functional decay shadow.
-/
structure GKSLPacket where
  /-- Open-system state carrier. -/
  StateCarrier : Type*
  /-- One-parameter semigroup generator placeholder. -/
  generator : ℝ → StateCarrier → StateCarrier
  /-- Abstract dissipation/jump carrier witness. -/
  jumpIndex : Type*
  /-- Abstract anticommutator term, witnessing GKSL structure at sector level. -/
  anticommutator : jumpIndex → StateCarrier → StateCarrier → StateCarrier
  /-- Abstract involution/join map for jump terms. -/
  involution : StateCarrier → StateCarrier
  /-- Energy/potential Lyapunov readout carried by the flow. -/
  freeEnergyShadow : StateCarrier → ℝ
  /-- Monotonicity witness requested by flow narratives. -/
  freeEnergyDecay : StateCarrier → ℝ → Prop
  /-- Concrete monotonicity instance for the shadow flow. -/
  freeEnergyDecay_holds : ∀ ρ t, freeEnergyDecay ρ t
  /-- Dissipative monotonicity for nonnegative time (shadow law). -/
  freeEnergy_monotone :
    ∀ ρ t, 0 ≤ t → freeEnergyShadow (generator t ρ) ≤ freeEnergyShadow ρ

  /-- Equilibrium/reference state used by the flow data. -/
  equilibriumState : StateCarrier

/-!
Finite spectral-thermal normalization schema.

These structures model the modular spectral partition function at the witness level:
`Z = Σ e^{-βE} dν_H(E)` on a finite spectrum index.
-/
/-- Spectral data with explicit modular tilt. -/
structure SpectralBoltzmannPacket (S : Type*) where
  /-- Inverse temperature β. -/
  inverseTemperature : ℝ
  /-- Energy/spectral parameter (`E`). -/
  spectralEnergy : S → ℝ
  /-- Geometric/spectral volume (`dν_H` density on the chosen model index). -/
  spectralVolume : S → ℝ
  /-- Modular potential used in the tilt (`Φ_β`). -/
  modularPotential : S → ℝ
  /-- Boltzmann factor (`e^{-Φ_β}`). -/
  boltzmannFactor : S → ℝ
  /-- Modulation law (`Φ_β(s)=β*E(s)`). -/
  modularPotential_eq :
    ∀ s : S, modularPotential s = inverseTemperature * spectralEnergy s
  /-- Explicit factor law field. -/
  boltzmannFactor_eq :
    ∀ s : S, boltzmannFactor s = Real.exp (- modularPotential s)

/-- Finite spectral partition schema. -/
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
      rw [Z.spectrum.boltzmannFactor_eq s]
    _ = ∑ s : S, Real.exp (-(Z.spectrum.inverseTemperature * Z.spectrum.spectralEnergy s)) *
          Z.spectrum.spectralVolume s := by
      refine Finset.sum_congr rfl ?_
      intro s hs
      rw [Z.spectrum.modularPotential_eq s]

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
def modularPartitionNormalization (mf : ModularFlowPacket) : ℝ := by
  classical
  exact if h : mf.hasTraceReference then mf.tracePartition h else mf.kmsPartition h

/-- Modular normalization is by trace when a trace reference is supplied. -/
theorem modularPartitionNormalization_trace
    (mf : ModularFlowPacket) (h : mf.hasTraceReference) :
    modularPartitionNormalization mf = mf.tracePartition h := by
  classical
  simp [modularPartitionNormalization, h]

/-- Modular normalization is by KMS/modular data when no trace reference is supplied. -/
theorem modularPartitionNormalization_kms
    (mf : ModularFlowPacket) (h : ¬ mf.hasTraceReference) :
    modularPartitionNormalization mf = mf.kmsPartition h := by
  classical
  simp [modularPartitionNormalization, h]

/--
Integrated modular-volume thermodynamic packet.
-/
structure ModularVolumePotentialPacket where
  /-- Classical measure/potential layer. -/
  logRN : LogRadonNikodymPacket
  /-- Relative surprisal and KL readout layer. -/
  relativeKL : RelativeSurprisalPacket
  /-- Gibbs/free-energy layer. -/
  freeEnergy : GibbsFreeEnergyPacket
  /-- Modular flow and modular Hamiltonian layer. -/
  modularFlow : ModularFlowPacket
  /-- Graded/supertrace layer. -/
  supervolume : SupervolumePacket
  /-- Dissipative/KMS-compatible flow layer. -/
  dissipativeFlow : GKSLPacket

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
  /-- Classical reference volume/measure carrier. -/
  classicalVolume : Type*
  /-- Classical state/density carrier. -/
  classicalState : Type*
  /-- Logarithmic Radon–Nikodym potential carrier. -/
  classicalLogPotential : Type*
  /-- Modular reference weight/state carrier. -/
  modularWeight : Type*
  /-- Relative modular data carrier (`[Dφ:Dψ]`, modular operators, etc.). -/
  modularData : Type*
  /-- Modular Hamiltonian / modular log-potential carrier. -/
  modularHamiltonian : Type*
  /-- KL-divergence proposition (written as `D_{KL}(μ|η)` in this layer). -/
  klDivergence : Prop
  /-- Araki entropy carrier. -/
  arakiRelativeEntropy : Type*
  /-- Free-energy proposition. -/
  freeEnergy : Prop
  /-- Spectral volume / density-of-states proposition. -/
  spectralVolume : Prop
  /-- Weyl/volume asymptotic proposition. -/
  weylVolumeGauge : Prop
  /-- Spectral thermal normalization data (`Z_β`). -/
  spectralThermalNormalization : SpectralThermalNormalizationPacket
  /-- Connes-cocycle transport data. -/
  modularTransport : ModularTransportBridgePacket
  /-- Comparison proposition linking KL and Araki entropy reductions. -/
  entropyComparison : Prop
  /-- Comparison proposition linking free energy to relative entropy. -/
  freeEnergyComparison : Prop
  /-- Comparison proposition linking spectral volume and geometric volume asymptotics. -/
  spectralVolumeComparison : Prop

namespace LogRadonNikodymPacket

/-- Rewrite `logPotential` as a negative log-density. -/
@[simp] theorem logPotential_eq_neg_log_density
    (P : LogRadonNikodymPacket) (μ : P.StateCarrier) (x : P.SampleSpace) :
    P.logPotential μ x = -Real.log (P.relativeDensity μ x) := by
  exact P.logPotential_eq μ x

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
  rw [Z.boltzmannFactor_eq, Z.modularPotential_eq]

end SpectralBoltzmannPacket

namespace SupervolumePacket

@[simp] theorem supertrace_eq_even_sub_odd
    (P : SupervolumePacket) (x : P.GradedCarrier) :
    P.supertrace x = P.evenTrace x - P.oddTrace x := by
  exact P.supertrace_eq x

end SupervolumePacket

namespace GKSLPacket

/-- Shadow of the decay witness evaluated on a time step. -/
theorem freeEnergyDecay_holds_apply
    (P : GKSLPacket) (ρ : P.StateCarrier) (t : ℝ) :
    P.freeEnergyDecay ρ t := by
  exact P.freeEnergyDecay_holds ρ t

/-- Dissipative shadow generator contract (nonnegative times only). -/
theorem freeEnergyShadow_generator_le
    (P : GKSLPacket) (ρ : P.StateCarrier) (t : ℝ) (ht : 0 ≤ t) :
    P.freeEnergyShadow (P.generator t ρ) ≤ P.freeEnergyShadow ρ := by
  exact P.freeEnergy_monotone ρ t ht

end GKSLPacket

end ModularVolumePotential

end InfoGeometry
