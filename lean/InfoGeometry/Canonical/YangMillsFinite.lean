import InfoGeometry.Canonical.ChiralRGFlow
import InfoGeometry.Canonical.GaugeGroups
import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Canonical.TomitaTakesaki

/-!
# InfoGeometry.Canonical.YangMillsFinite

Finite constructive Yang-Mills scaffold promoted to the canonical layer.

This module provides a stable finite route where:
- reflection positivity is derived from expectation-seed/Tomita data,
- OS/Wightman finite markers are derived constructively,
- the spectral-gap parameter is derived from log-det coercivity.
-/

namespace InfoGeometry.Canonical.YangMillsFinite

open InfoGeometry.Canonical.ChiralRGFlow
open InfoGeometry.Canonical.GaugeGroups
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.TomitaTakesaki

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace FiniteQFTLayer

/-- Reflection-positivity marker from the expectation seed. -/
def expectationSeedReflectionPositivity
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E) : Prop :=
  SatisfiesKMSLike (E := E) K (omegaSeed (F := E) Ω) β

/-- Constructive reflection positivity from explicit seed-KMS derivation hypotheses. -/
theorem expectationSeedReflectionPositivity_of_hypotheses
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hJointKernel : JointKernelOnOmega (F := E) K β Ω)
    (hCommOrthogonal : CommutatorOrthogonalOnOmega (F := E) Ω) :
    expectationSeedReflectionPositivity (E := E) K β Ω := by
  simpa [expectationSeedReflectionPositivity] using
    (omegaSeed_kms_of_jointKernel_commutator
      (F := E) (K := K) (β := β) (Ω := Ω) hJointKernel hCommOrthogonal)

/-- Finite OS-like marker induced by modular reflection geometry. -/
def finiteOsterwalderSchraderLayer
    (Ω : InfoGeometry.Krein.DoubledSpace E) : Prop :=
  0 ≤ inner ℝ ((modularConjugationJ (E := E)) Ω) Ω ∧
    modularConjugationJ (E := E) Ω = Ω

/-- Constructive finite OS-like witness from positive-time geometry. -/
theorem finiteOsterwalderSchraderLayer_of_positiveTimeVector
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hΩ : PositiveTimeVector Ω) :
    finiteOsterwalderSchraderLayer (E := E) Ω := by
  refine ⟨?_, ?_⟩
  · simpa using reflectionQuadratic_nonneg_of_positiveTimeVector (E := E) Ω hΩ
  · exact modularConjugationJ_fixed_of_positiveTimeVector (E := E) Ω hΩ

/-- Finite Wightman-like marker from nonzero KMS-like expectation seed. -/
def finiteWightmanReconstructionLayer
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E) : Prop :=
  ∃ ω : AlgebraEnd E →L[ℝ] ℝ,
    ω = omegaSeed (F := E) Ω ∧
      SatisfiesKMSLike (E := E) K ω β ∧
      ω ≠ 0

/-- Constructive finite Wightman-like witness from expectation-seed data. -/
theorem finiteWightmanReconstructionLayer_of_expectationSeed
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hJointKernel : JointKernelOnOmega (F := E) K β Ω)
    (hCommOrthogonal : CommutatorOrthogonalOnOmega (F := E) Ω)
    (hΩ : Ω ≠ 0) :
    finiteWightmanReconstructionLayer (E := E) K β Ω := by
  refine ⟨omegaSeed (F := E) Ω, rfl, ?_, ?_⟩
  · exact omegaSeed_kms_of_jointKernel_commutator
      (F := E) (K := K) (β := β) (Ω := Ω) hJointKernel hCommOrthogonal
  · simpa [omegaSeed] using
      (expectationSeedFunctional_nonzero (F := E) Ω hΩ)

end FiniteQFTLayer

/--
Log-det coercivity marker for Jacobian flow maps on doubled space.
In the finite-dimensional scaffold this is determinant nondegeneracy.
-/
def logDetCoercive
    [FiniteDimensional ℝ (InfoGeometry.Krein.DoubledSpace E)]
    (J : AlgebraEnd E) : Prop :=
  LinearMap.det J.toLinearMap ≠ 0

/-- Derived finite spectral gap from chiral scale and log-det relative volume. -/
noncomputable def spectralGapFromLogDet
    [FiniteDimensional ℝ (InfoGeometry.Krein.DoubledSpace E)]
    (rg_model : ChiralAsymptoticModel E)
    (J : AlgebraEnd E) : ℝ :=
  max rg_model.gamma (jacobianRelativeVolume (F := E) J)

lemma gamma_le_spectralGapFromLogDet
    [FiniteDimensional ℝ (InfoGeometry.Krein.DoubledSpace E)]
    (rg_model : ChiralAsymptoticModel E)
    (J : AlgebraEnd E) :
    rg_model.gamma ≤ spectralGapFromLogDet (E := E) rg_model J :=
  le_max_left _ _

/-- Positivity of the derived gap from log-det coercivity. -/
theorem spectralGapFromLogDet_pos_of_coercive
    [FiniteDimensional ℝ (InfoGeometry.Krein.DoubledSpace E)]
    (rg_model : ChiralAsymptoticModel E)
    (J : AlgebraEnd E)
    (hCoercive : logDetCoercive (E := E) J) :
    0 < spectralGapFromLogDet (E := E) rg_model J := by
  have hvol :
      0 < jacobianRelativeVolume (F := E) J :=
    jacobianRelativeVolume_pos_of_det_ne_zero (F := E) hCoercive
  exact lt_of_lt_of_le hvol (le_max_right _ _)

/-- Finite constructive Yang-Mills bridge package. -/
structure FiniteYangMillsBridge (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] where
  n : ℕ
  n_ge_two : 2 ≤ n
  su_model : SUN n
  psu_model : PSUN n su_model
  rg_model : ChiralAsymptoticModel E
  K : AlgebraEnd E
  β : ℝ
  Ω : InfoGeometry.Krein.DoubledSpace E
  hJointKernel : JointKernelOnOmega (F := E) K β Ω
  hCommOrthogonal : CommutatorOrthogonalOnOmega (F := E) Ω
  hΩ_nonzero : Ω ≠ 0
  hΩ_posTime : PositiveTimeVector Ω
  spectral_gap : ℝ
  spectral_gap_pos : 0 < spectral_gap
  gamma_le_spectral_gap : rg_model.gamma ≤ spectral_gap

namespace FiniteYangMillsBridge

/-- Constructor from explicit finite gauge/QFT/RG/gap data. -/
def ofConcrete
    (n : ℕ)
    (n_ge_two : 2 ≤ n)
    (su_model : SUN n)
    (psu_model : PSUN n su_model)
    (rg_model : ChiralAsymptoticModel E)
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hJointKernel : JointKernelOnOmega (F := E) K β Ω)
    (hCommOrthogonal : CommutatorOrthogonalOnOmega (F := E) Ω)
    (hΩ_nonzero : Ω ≠ 0)
    (hΩ_posTime : PositiveTimeVector Ω)
    (spectral_gap : ℝ)
    (spectral_gap_pos : 0 < spectral_gap)
    (gamma_le_spectral_gap : rg_model.gamma ≤ spectral_gap) :
    FiniteYangMillsBridge E where
  n := n
  n_ge_two := n_ge_two
  su_model := su_model
  psu_model := psu_model
  rg_model := rg_model
  K := K
  β := β
  Ω := Ω
  hJointKernel := hJointKernel
  hCommOrthogonal := hCommOrthogonal
  hΩ_nonzero := hΩ_nonzero
  hΩ_posTime := hΩ_posTime
  spectral_gap := spectral_gap
  spectral_gap_pos := spectral_gap_pos
  gamma_le_spectral_gap := gamma_le_spectral_gap

/--
Fully constructive finite bridge:
QFT witnesses come from expectation-seed data and gap comes from log-det coercivity.
-/
noncomputable def ofExpectationSeedFromLogDet
    [FiniteDimensional ℝ (InfoGeometry.Krein.DoubledSpace E)]
    (n : ℕ)
    (n_ge_two : 2 ≤ n)
    (su_model : SUN n)
    (psu_model : PSUN n su_model)
    (rg_model : ChiralAsymptoticModel E)
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hJointKernel : JointKernelOnOmega (F := E) K β Ω)
    (hCommOrthogonal : CommutatorOrthogonalOnOmega (F := E) Ω)
    (hΩ_nonzero : Ω ≠ 0)
    (hΩ_posTime : PositiveTimeVector Ω)
    (J : AlgebraEnd E)
    (hCoercive : logDetCoercive (E := E) J) :
    FiniteYangMillsBridge E :=
  ofConcrete (E := E) n n_ge_two su_model psu_model rg_model K β Ω
    hJointKernel hCommOrthogonal hΩ_nonzero hΩ_posTime
    (spectralGapFromLogDet (E := E) rg_model J)
    (spectralGapFromLogDet_pos_of_coercive
      (E := E) (rg_model := rg_model) (J := J) hCoercive)
    (gamma_le_spectralGapFromLogDet
      (E := E) (rg_model := rg_model) (J := J))

/-- Obligation 1: nontrivial gauge rank (`N ≥ 2`). -/
def hasGaugeRank (B : FiniteYangMillsBridge E) : Prop :=
  2 ≤ B.n

/-- Obligation 2: finite existence layer. -/
def hasExistenceLayer (B : FiniteYangMillsBridge E) : Prop :=
  FiniteQFTLayer.expectationSeedReflectionPositivity (E := E) B.K B.β B.Ω ∧
    FiniteQFTLayer.finiteOsterwalderSchraderLayer (E := E) B.Ω ∧
    FiniteQFTLayer.finiteWightmanReconstructionLayer (E := E) B.K B.β B.Ω

/-- Obligation 3: strict finite mass gap. -/
def hasStrictMassGap (B : FiniteYangMillsBridge E) : Prop :=
  0 < B.spectral_gap

/--
Expanded finite existence claims derived from the bridge's closure state.
-/
theorem existenceClaims_of_bridge
    (B : FiniteYangMillsBridge E) :
    ∃ (K : AlgebraEnd E) (β : ℝ) (Ω : InfoGeometry.Krein.DoubledSpace E),
      FiniteQFTLayer.expectationSeedReflectionPositivity (E := E) K β Ω ∧
        FiniteQFTLayer.finiteOsterwalderSchraderLayer (E := E) Ω ∧
        FiniteQFTLayer.finiteWightmanReconstructionLayer (E := E) K β Ω :=
  ⟨B.K, B.β, B.Ω,
    FiniteQFTLayer.expectationSeedReflectionPositivity_of_hypotheses
      (E := E) (K := B.K) (β := B.β) (Ω := B.Ω) B.hJointKernel B.hCommOrthogonal,
    FiniteQFTLayer.finiteOsterwalderSchraderLayer_of_positiveTimeVector
      (E := E) (Ω := B.Ω) B.hΩ_posTime,
    FiniteQFTLayer.finiteWightmanReconstructionLayer_of_expectationSeed
      (E := E) (K := B.K) (β := B.β) (Ω := B.Ω)
      B.hJointKernel B.hCommOrthogonal B.hΩ_nonzero⟩

/-- Consolidated finite milestone theorem. -/
theorem obligations_of_bridge
    (B : FiniteYangMillsBridge E) :
    hasGaugeRank B ∧ hasExistenceLayer B ∧ hasStrictMassGap B := by
  refine ⟨B.n_ge_two, ?_, B.spectral_gap_pos⟩
  refine ⟨?_, ?_, ?_⟩
  · exact FiniteQFTLayer.expectationSeedReflectionPositivity_of_hypotheses
      (E := E) (K := B.K) (β := B.β) (Ω := B.Ω)
      B.hJointKernel B.hCommOrthogonal
  · exact FiniteQFTLayer.finiteOsterwalderSchraderLayer_of_positiveTimeVector
      (E := E) (Ω := B.Ω) B.hΩ_posTime
  · exact FiniteQFTLayer.finiteWightmanReconstructionLayer_of_expectationSeed
      (E := E) (K := B.K) (β := B.β) (Ω := B.Ω)
      B.hJointKernel B.hCommOrthogonal B.hΩ_nonzero

/-- Fully constructive finite milestone theorem in the log-det route. -/
theorem obligations_of_expectationSeedFromLogDet
    [FiniteDimensional ℝ (InfoGeometry.Krein.DoubledSpace E)]
    (n : ℕ)
    (n_ge_two : 2 ≤ n)
    (su_model : SUN n)
    (psu_model : PSUN n su_model)
    (rg_model : ChiralAsymptoticModel E)
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hJointKernel : JointKernelOnOmega (F := E) K β Ω)
    (hCommOrthogonal : CommutatorOrthogonalOnOmega (F := E) Ω)
    (hΩ_nonzero : Ω ≠ 0)
    (hΩ_posTime : PositiveTimeVector Ω)
    (J : AlgebraEnd E)
    (hCoercive : logDetCoercive (E := E) J) :
    let B := ofExpectationSeedFromLogDet
      (E := E) n n_ge_two su_model psu_model rg_model K β Ω hJointKernel hCommOrthogonal
      hΩ_nonzero hΩ_posTime J hCoercive
    hasGaugeRank B ∧ hasExistenceLayer B ∧ hasStrictMassGap B := by
  intro B
  exact obligations_of_bridge (E := E) B

end FiniteYangMillsBridge

end InfoGeometry.Canonical.YangMillsFinite
