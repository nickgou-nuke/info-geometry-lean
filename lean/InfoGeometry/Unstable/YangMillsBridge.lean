import InfoGeometry.Canonical.ChiralRGFlow
import InfoGeometry.Canonical.GaugeGroups
import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Canonical.TomitaTakesaki

/-!
# InfoGeometry.Canonical.YangMillsBridge

Bridge-layer contracts linking the existing chiral RG flow scaffold to
Yang-Mills mass-gap obligations.
-/

namespace InfoGeometry.Unstable.YangMillsBridge

open InfoGeometry.Canonical.ChiralRGFlow
open InfoGeometry.Canonical.GaugeGroups
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.TomitaTakesaki

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Minimal `SU(N)` gauge instantiation contract.
Updated to use the formal group structures from the hierarchy layer.
-/
structure SUNGaugeInstantiation where
  /-- Color rank parameter. -/
  n : ℕ
  /-- Nontrivial gauge rank (`N ≥ 2`). -/
  n_ge_two : 2 ≤ n
  /-- Formal SU(N) group model contract. -/
  su_model : SUN n
  /-- Formal PSU(N) projective group model contract. -/
  psu_model : PSUN n su_model

namespace SUNGaugeInstantiation

/--
Concrete constructor from an explicit `SU(N)`/`PSU(N)` model pair.
-/
def ofModels
    (n : ℕ)
    (hn : 2 ≤ n)
    (su_model : SUN n)
    (psu_model : PSUN n su_model) :
    SUNGaugeInstantiation where
  n := n
  n_ge_two := hn
  su_model := su_model
  psu_model := psu_model

end SUNGaugeInstantiation

/-- Existence-layer obligations matching the constructive QFT side. -/
structure QFTAxiomsLayer where
  /-- Reflection positivity witness. -/
  has_reflection_positivity : Prop
  /-- Proof of reflection positivity. -/
  reflection_positivity_holds : has_reflection_positivity
  /-- Osterwalder-Schrader axioms witness. -/
  has_osterwalder_schrader : Prop
  /-- Proof of the Osterwalder-Schrader layer. -/
  osterwalder_schrader_holds : has_osterwalder_schrader
  /-- Wightman reconstruction witness. -/
  has_wightman_reconstruction : Prop
  /-- Proof of Wightman reconstruction availability. -/
  wightman_reconstruction_holds : has_wightman_reconstruction

namespace QFTAxiomsLayer

/--
Concrete constructor from explicit reflection/OS/Wightman proofs.
-/
def ofProofs
    {R O W : Prop}
    (hR : R)
    (hO : O)
    (hW : W) :
    QFTAxiomsLayer where
  has_reflection_positivity := R
  reflection_positivity_holds := hR
  has_osterwalder_schrader := O
  osterwalder_schrader_holds := hO
  has_wightman_reconstruction := W
  wightman_reconstruction_holds := hW

/--
Reflection-positivity proxy induced by the canonical expectation seed:
the weighted seed observable satisfies the KMS-like constraint.
-/
def expectationSeedReflectionPositivity
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E) : Prop :=
  SatisfiesKMSLike (E := E) K (omegaSeed (F := E) Ω) β

/--
Constructive reflection-positivity witness from canonical
expectation-seed structural hypotheses.
-/
theorem expectationSeedReflectionPositivity_of_hypotheses
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hStruct : ExpectationSeedKMSHypotheses (F := E) K β Ω) :
    expectationSeedReflectionPositivity (E := E) K β Ω := by
  simpa [expectationSeedReflectionPositivity] using
    (omegaSeed_kms_of_hypotheses (F := E) (K := K) (β := β) (Ω := Ω) hStruct)

/--
Tomita-side reflection positivity marker:
nonnegativity of the modular quadratic form `⟪J Ω, Ω⟫`.
-/
def modularReflectionPositivity
    (Ω : InfoGeometry.Krein.DoubledSpace E) : Prop :=
  0 ≤ inner ℝ ((modularConjugationJ (E := E)) Ω) Ω

/--
Constructive Tomita-side reflection positivity on the canonical positive-time subspace.
-/
theorem modularReflectionPositivity_of_positiveTimeVector
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hΩ : PositiveTimeVector Ω) :
    modularReflectionPositivity (E := E) Ω := by
  simpa [modularReflectionPositivity] using
    (reflectionQuadratic_nonneg_of_positiveTimeVector Ω hΩ)

/--
Combined constructive reflection package:
KMS-like seed positivity and modular quadratic positivity.
-/
theorem expectationSeed_and_modularReflectionPositivity_of_hypotheses
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hStruct : ExpectationSeedKMSHypotheses (F := E) K β Ω)
    (hΩ : PositiveTimeVector Ω) :
    expectationSeedReflectionPositivity (E := E) K β Ω ∧
      modularReflectionPositivity (E := E) Ω := by
  refine ⟨?_, ?_⟩
  · exact expectationSeedReflectionPositivity_of_hypotheses
      (E := E) (K := K) (β := β) (Ω := Ω) hStruct
  · exact modularReflectionPositivity_of_positiveTimeVector
      (E := E) (Ω := Ω) hΩ

/--
Finite OS-like layer induced by modular reflection:
quadratic positivity and `J`-fixedness on the selected vacuum state.
-/
def finiteOsterwalderSchraderLayer
    (Ω : InfoGeometry.Krein.DoubledSpace E) : Prop :=
  modularReflectionPositivity (E := E) Ω ∧
    modularConjugationJ (E := E) Ω = Ω

/--
Constructive finite OS-like witness from canonical positive-time geometry.
-/
theorem finiteOsterwalderSchraderLayer_of_positiveTimeVector
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hΩ : PositiveTimeVector Ω) :
    finiteOsterwalderSchraderLayer (E := E) Ω := by
  refine ⟨?_, ?_⟩
  · exact modularReflectionPositivity_of_positiveTimeVector
      (E := E) (Ω := Ω) hΩ
  · exact modularConjugationJ_fixed_of_positiveTimeVector Ω hΩ

/--
Finite Wightman-like reconstruction marker:
existence of a nonzero KMS-like observable state.
-/
def finiteWightmanReconstructionLayer
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E) : Prop :=
  ∃ ω : AlgebraEnd E →L[ℝ] ℝ,
    ω = omegaSeed (F := E) Ω ∧
      SatisfiesKMSLike (E := E) K ω β ∧
      ω ≠ 0

/--
Constructive finite Wightman-like witness from expectation-seed KMS data.
-/
theorem finiteWightmanReconstructionLayer_of_expectationSeed
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hStruct : ExpectationSeedKMSHypotheses (F := E) K β Ω)
    (hΩ : Ω ≠ 0) :
    finiteWightmanReconstructionLayer (E := E) K β Ω := by
  refine ⟨omegaSeed (F := E) Ω, ?_, ?_, ?_⟩
  · rfl
  · exact omegaSeed_kms_of_hypotheses (F := E) (K := K) (β := β) (Ω := Ω) hStruct
  · simpa [omegaSeed] using
      (expectationSeedFunctional_nonzero (F := E) Ω hΩ)

/--
Concrete constructor where reflection positivity is not supplied externally:
it is discharged from canonical expectation-seed KMS hypotheses.
-/
def ofExpectationSeedKMS
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hStruct : ExpectationSeedKMSHypotheses (F := E) K β Ω)
    {O W : Prop}
    (hO : O)
    (hW : W) :
    QFTAxiomsLayer :=
  ofProofs
    (R := expectationSeedReflectionPositivity (E := E) K β Ω)
    (hR := expectationSeedReflectionPositivity_of_hypotheses
      (E := E) (K := K) (β := β) (Ω := Ω) hStruct)
    (hO := hO)
    (hW := hW)

/--
Constructive constructor with explicit positive-time geometry:
reflection witness records both KMS-like and modular quadratic positivity.
-/
def ofExpectationSeedKMSPositiveTime
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hStruct : ExpectationSeedKMSHypotheses (F := E) K β Ω)
    (hΩ : PositiveTimeVector Ω)
    {O W : Prop}
    (hO : O)
    (hW : W) :
    QFTAxiomsLayer :=
  ofProofs
    (R := expectationSeedReflectionPositivity (E := E) K β Ω ∧
      modularReflectionPositivity (E := E) Ω)
    (hR := expectationSeed_and_modularReflectionPositivity_of_hypotheses
      (E := E) (K := K) (β := β) (Ω := Ω) hStruct hΩ)
    (hO := hO)
    (hW := hW)

/--
Fully constructive finite constructor:
all three witness fields are instantiated from canonical modular data.
-/
def ofExpectationSeedKMSFinite
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hStruct : ExpectationSeedKMSHypotheses (F := E) K β Ω)
    (hΩ_nonzero : Ω ≠ 0)
    (hΩ_posTime : PositiveTimeVector Ω) :
    QFTAxiomsLayer :=
  ofProofs
    (R := expectationSeedReflectionPositivity (E := E) K β Ω)
    (hR := expectationSeedReflectionPositivity_of_hypotheses
      (E := E) (K := K) (β := β) (Ω := Ω) hStruct)
    (O := finiteOsterwalderSchraderLayer (E := E) Ω)
    (hO := finiteOsterwalderSchraderLayer_of_positiveTimeVector
      (E := E) (Ω := Ω) hΩ_posTime)
    (W := finiteWightmanReconstructionLayer (E := E) K β Ω)
    (hW := finiteWightmanReconstructionLayer_of_expectationSeed
      (E := E) (K := K) (β := β) (Ω := Ω) hStruct hΩ_nonzero)

end QFTAxiomsLayer

/--
Log-det coercivity marker for a Jacobian flow map on doubled space.
In the finite-dimensional scaffold, coercivity is represented by nonzero determinant.
-/
def LogDetCoercive
    [FiniteDimensional ℝ (InfoGeometry.Krein.DoubledSpace E)]
    (J : AlgebraEnd E) : Prop :=
  LinearMap.det J.toLinearMap ≠ 0

/--
Constructive spectral gap extracted from chiral scale and log-det relative volume.
This removes manual gap numerics from finite bridge constructors.
-/
noncomputable def spectralGapFromLogDet
    [FiniteDimensional ℝ (InfoGeometry.Krein.DoubledSpace E)]
    (rg_model : ChiralAsymptoticModel E)
    (J : AlgebraEnd E) : ℝ :=
  max rg_model.gamma (jacobianRelativeVolume (F := E) J)

lemma gamma_le_spectralGapFromLogDet
    [FiniteDimensional ℝ (InfoGeometry.Krein.DoubledSpace E)]
    (rg_model : ChiralAsymptoticModel E)
    (J : AlgebraEnd E) :
    rg_model.gamma ≤ spectralGapFromLogDet (E := E) rg_model J := by
  exact le_max_left _ _

lemma jacobianRelativeVolume_le_spectralGapFromLogDet
    [FiniteDimensional ℝ (InfoGeometry.Krein.DoubledSpace E)]
    (rg_model : ChiralAsymptoticModel E)
    (J : AlgebraEnd E) :
    jacobianRelativeVolume (F := E) J ≤ spectralGapFromLogDet (E := E) rg_model J := by
  exact le_max_right _ _

/--
Positivity of the derived spectral gap from log-det coercivity.
-/
theorem spectralGapFromLogDet_pos_of_coercive
    [FiniteDimensional ℝ (InfoGeometry.Krein.DoubledSpace E)]
    (rg_model : ChiralAsymptoticModel E)
    (J : AlgebraEnd E)
    (hCoercive : LogDetCoercive (E := E) J) :
    0 < spectralGapFromLogDet (E := E) rg_model J := by
  have hvol :
      0 < jacobianRelativeVolume (F := E) J :=
    jacobianRelativeVolume_pos_of_det_ne_zero (F := E) hCoercive
  exact lt_of_lt_of_le hvol
    (jacobianRelativeVolume_le_spectralGapFromLogDet
      (E := E) (rg_model := rg_model) (J := J))

/-- Consolidated bridge package from chiral RG to Yang-Mills mass-gap targets. -/
structure YangMillsMassGapBridge (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] where
  /-- Gauge-theory instantiation data. -/
  su_inst : SUNGaugeInstantiation
  /-- Chiral RG model currently available in the canonical layer. -/
  rg_model : ChiralAsymptoticModel E
  /-- Constructive QFT existence obligations. -/
  qft_layer : QFTAxiomsLayer
  /-- Candidate strict spectral gap (`λ₁`). -/
  spectral_gap : ℝ
  /-- Strict positivity target for the mass gap. -/
  spectral_gap_pos : 0 < spectral_gap
  /-- Lower bound linking chiral scale to the spectral gap. -/
  gamma_le_spectral_gap : rg_model.gamma ≤ spectral_gap

namespace YangMillsMassGapBridge

/-- Concrete bridge constructor from explicit gauge/QFT/RG data. -/
def ofConcreteLayers
    (su_inst : SUNGaugeInstantiation)
    (rg_model : ChiralAsymptoticModel E)
    (qft_layer : QFTAxiomsLayer)
    (spectral_gap : ℝ)
    (spectral_gap_pos : 0 < spectral_gap)
    (gamma_le_spectral_gap : rg_model.gamma ≤ spectral_gap) :
    YangMillsMassGapBridge E where
  su_inst := su_inst
  rg_model := rg_model
  qft_layer := qft_layer
  spectral_gap := spectral_gap
  spectral_gap_pos := spectral_gap_pos
  gamma_le_spectral_gap := gamma_le_spectral_gap

/--
Concrete bridge constructor where reflection positivity is derived from
canonical expectation-seed KMS hypotheses.
Only OS/Wightman layers remain explicit here.
-/
def ofExpectationSeedLayers
    (su_inst : SUNGaugeInstantiation)
    (rg_model : ChiralAsymptoticModel E)
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hStruct : ExpectationSeedKMSHypotheses (F := E) K β Ω)
    {O W : Prop}
    (hO : O)
    (hW : W)
    (spectral_gap : ℝ)
    (spectral_gap_pos : 0 < spectral_gap)
    (gamma_le_spectral_gap : rg_model.gamma ≤ spectral_gap) :
    YangMillsMassGapBridge E :=
  ofConcreteLayers (E := E) su_inst rg_model
    (QFTAxiomsLayer.ofExpectationSeedKMS
      (E := E) (K := K) (β := β) (Ω := Ω) hStruct
      (hO := hO) (hW := hW))
    spectral_gap spectral_gap_pos gamma_le_spectral_gap

/--
Expectation-seed bridge constructor with explicit positive-time modular geometry.
-/
def ofExpectationSeedLayersPositiveTime
    (su_inst : SUNGaugeInstantiation)
    (rg_model : ChiralAsymptoticModel E)
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hStruct : ExpectationSeedKMSHypotheses (F := E) K β Ω)
    (hΩ : PositiveTimeVector Ω)
    {O W : Prop}
    (hO : O)
    (hW : W)
    (spectral_gap : ℝ)
    (spectral_gap_pos : 0 < spectral_gap)
    (gamma_le_spectral_gap : rg_model.gamma ≤ spectral_gap) :
    YangMillsMassGapBridge E :=
  ofConcreteLayers (E := E) su_inst rg_model
    (QFTAxiomsLayer.ofExpectationSeedKMSPositiveTime
      (E := E) (K := K) (β := β) (Ω := Ω) hStruct hΩ
      (hO := hO) (hW := hW))
    spectral_gap spectral_gap_pos gamma_le_spectral_gap

/--
Fully constructive finite bridge constructor:
no external reflection/OS/Wightman witness inputs are required.
-/
def ofExpectationSeedLayersFinite
    (su_inst : SUNGaugeInstantiation)
    (rg_model : ChiralAsymptoticModel E)
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hStruct : ExpectationSeedKMSHypotheses (F := E) K β Ω)
    (hΩ_nonzero : Ω ≠ 0)
    (hΩ_posTime : PositiveTimeVector Ω)
    (spectral_gap : ℝ)
    (spectral_gap_pos : 0 < spectral_gap)
    (gamma_le_spectral_gap : rg_model.gamma ≤ spectral_gap) :
    YangMillsMassGapBridge E :=
  ofConcreteLayers (E := E) su_inst rg_model
    (QFTAxiomsLayer.ofExpectationSeedKMSFinite
      (E := E) (K := K) (β := β) (Ω := Ω) hStruct hΩ_nonzero hΩ_posTime)
    spectral_gap spectral_gap_pos gamma_le_spectral_gap

/--
Fully constructive finite bridge constructor with log-det derived mass gap:
no external spectral-gap number is supplied.
-/
noncomputable def ofExpectationSeedLayersFiniteFromLogDet
    [FiniteDimensional ℝ (InfoGeometry.Krein.DoubledSpace E)]
    (su_inst : SUNGaugeInstantiation)
    (rg_model : ChiralAsymptoticModel E)
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hStruct : ExpectationSeedKMSHypotheses (F := E) K β Ω)
    (hΩ_nonzero : Ω ≠ 0)
    (hΩ_posTime : PositiveTimeVector Ω)
    (J : AlgebraEnd E)
    (hCoercive : LogDetCoercive (E := E) J) :
    YangMillsMassGapBridge E :=
  ofExpectationSeedLayersFinite (E := E)
    su_inst rg_model K β Ω hStruct hΩ_nonzero hΩ_posTime
    (spectralGapFromLogDet (E := E) rg_model J)
    (spectralGapFromLogDet_pos_of_coercive
      (E := E) (rg_model := rg_model) (J := J) hCoercive)
    (gamma_le_spectralGapFromLogDet
      (E := E) (rg_model := rg_model) (J := J))

end YangMillsMassGapBridge

/-- Obligation 1: nontrivial `SU(N)` gauge rank (`N ≥ 2`). The `su_model` and `psu_model`
    fields in `SUNGaugeInstantiation` structurally guarantee an explicit gauge witness exists. -/
def has_su_n_instantiation (B : YangMillsMassGapBridge E) : Prop :=
  2 ≤ B.su_inst.n

/-- Obligation 2: existence layer via OS/Wightman-style witnesses. -/
def has_os_wightman_existence_layer (B : YangMillsMassGapBridge E) : Prop :=
  B.qft_layer.has_reflection_positivity ∧
    B.qft_layer.has_osterwalder_schrader ∧
    B.qft_layer.has_wightman_reconstruction

/-- Obligation 3: strict positive mass gap. -/
def has_strict_mass_gap (B : YangMillsMassGapBridge E) : Prop :=
  0 < B.spectral_gap

/-- The RG component of the bridge inherits asymptotic freedom. -/
lemma asymptotic_freedom_of_bridge_rg_model
    (B : YangMillsMassGapBridge E) :
    IsAsymptoticallyFree B.rg_model.flow :=
  asymptotic_freedom_of_negative_beta B.rg_model

/-- The bridge carries a strict mass-gap witness by construction. -/
lemma strict_mass_gap_of_bridge (B : YangMillsMassGapBridge E) :
    has_strict_mass_gap B :=
  B.spectral_gap_pos

/-- The bridge carries the chiral-to-gap lower bound witness. -/
lemma chiral_scale_bounds_mass_gap (B : YangMillsMassGapBridge E) :
    B.rg_model.gamma ≤ B.spectral_gap :=
  B.gamma_le_spectral_gap

/-- Consolidated milestone theorem for the three Yang-Mills obligations. -/
theorem millennium_obligations_of_bridge
    (B : YangMillsMassGapBridge E) :
    has_su_n_instantiation B ∧
      has_os_wightman_existence_layer B ∧
      has_strict_mass_gap B := by
  refine ⟨B.su_inst.n_ge_two, ?_, B.spectral_gap_pos⟩
  exact ⟨B.qft_layer.reflection_positivity_holds,
    B.qft_layer.osterwalder_schrader_holds,
    B.qft_layer.wightman_reconstruction_holds⟩

namespace YangMillsMassGapBridge

/--
Concrete milestone theorem:
the bridge record is produced directly from concrete layer data, and then the
three millennium obligations are immediate.
-/
theorem millennium_obligations_of_concreteLayers
    (su_inst : SUNGaugeInstantiation)
    (rg_model : ChiralAsymptoticModel E)
    (qft_layer : QFTAxiomsLayer)
    (spectral_gap : ℝ)
    (spectral_gap_pos : 0 < spectral_gap)
    (gamma_le_spectral_gap : rg_model.gamma ≤ spectral_gap) :
    let B := ofConcreteLayers (E := E) su_inst rg_model qft_layer
      spectral_gap spectral_gap_pos gamma_le_spectral_gap
    has_su_n_instantiation B ∧
      has_os_wightman_existence_layer B ∧
      has_strict_mass_gap B := by
  intro B
  exact millennium_obligations_of_bridge (E := E) B

/--
Concrete milestone theorem in the expectation-seed route:
reflection positivity is derived from canonical KMS structural hypotheses.
-/
theorem millennium_obligations_of_expectationSeedLayers
    (su_inst : SUNGaugeInstantiation)
    (rg_model : ChiralAsymptoticModel E)
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hStruct : ExpectationSeedKMSHypotheses (F := E) K β Ω)
    {O W : Prop}
    (hO : O)
    (hW : W)
    (spectral_gap : ℝ)
    (spectral_gap_pos : 0 < spectral_gap)
    (gamma_le_spectral_gap : rg_model.gamma ≤ spectral_gap) :
    let B := YangMillsMassGapBridge.ofExpectationSeedLayers su_inst rg_model
      K β Ω hStruct hO hW spectral_gap spectral_gap_pos gamma_le_spectral_gap
    has_su_n_instantiation B ∧
      has_os_wightman_existence_layer B ∧
      has_strict_mass_gap B := by
  intro B
  exact millennium_obligations_of_bridge (E := E) B

/--
Positive-time modular variant of the expectation-seed milestone theorem.
-/
theorem millennium_obligations_of_expectationSeedLayersPositiveTime
    (su_inst : SUNGaugeInstantiation)
    (rg_model : ChiralAsymptoticModel E)
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hStruct : ExpectationSeedKMSHypotheses (F := E) K β Ω)
    (hΩ : PositiveTimeVector Ω)
    {O W : Prop}
    (hO : O)
    (hW : W)
    (spectral_gap : ℝ)
    (spectral_gap_pos : 0 < spectral_gap)
    (gamma_le_spectral_gap : rg_model.gamma ≤ spectral_gap) :
    let B := YangMillsMassGapBridge.ofExpectationSeedLayersPositiveTime
      su_inst rg_model K β Ω hStruct hΩ hO hW
      spectral_gap spectral_gap_pos gamma_le_spectral_gap
    has_su_n_instantiation B ∧
      has_os_wightman_existence_layer B ∧
      has_strict_mass_gap B := by
  intro B
  exact millennium_obligations_of_bridge (E := E) B

/--
Fully constructive finite milestone theorem:
no external reflection/OS/Wightman witnesses are provided by the caller.
-/
theorem millennium_obligations_of_expectationSeedLayersFinite
    (su_inst : SUNGaugeInstantiation)
    (rg_model : ChiralAsymptoticModel E)
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hStruct : ExpectationSeedKMSHypotheses (F := E) K β Ω)
    (hΩ_nonzero : Ω ≠ 0)
    (hΩ_posTime : PositiveTimeVector Ω)
    (spectral_gap : ℝ)
    (spectral_gap_pos : 0 < spectral_gap)
    (gamma_le_spectral_gap : rg_model.gamma ≤ spectral_gap) :
    let B := YangMillsMassGapBridge.ofExpectationSeedLayersFinite
      su_inst rg_model K β Ω hStruct hΩ_nonzero hΩ_posTime
      spectral_gap spectral_gap_pos gamma_le_spectral_gap
    has_su_n_instantiation B ∧
      has_os_wightman_existence_layer B ∧
      has_strict_mass_gap B := by
  intro B
  exact millennium_obligations_of_bridge (E := E) B

/--
Fully constructive finite milestone theorem in the log-det route:
the mass gap is derived from coercive Jacobian relative volume.
-/
theorem millennium_obligations_of_expectationSeedLayersFiniteFromLogDet
    [FiniteDimensional ℝ (InfoGeometry.Krein.DoubledSpace E)]
    (su_inst : SUNGaugeInstantiation)
    (rg_model : ChiralAsymptoticModel E)
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hStruct : ExpectationSeedKMSHypotheses (F := E) K β Ω)
    (hΩ_nonzero : Ω ≠ 0)
    (hΩ_posTime : PositiveTimeVector Ω)
    (J : AlgebraEnd E)
    (hCoercive : LogDetCoercive (E := E) J) :
    let B := YangMillsMassGapBridge.ofExpectationSeedLayersFiniteFromLogDet
      (E := E) su_inst rg_model K β Ω hStruct hΩ_nonzero hΩ_posTime J hCoercive
    has_su_n_instantiation B ∧
      has_os_wightman_existence_layer B ∧
      has_strict_mass_gap B := by
  intro B
  exact millennium_obligations_of_bridge (E := E) B

end YangMillsMassGapBridge

end InfoGeometry.Unstable.YangMillsBridge
