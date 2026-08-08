import InfoGeometry.Canonical.KMSSinkhornSeedState
import InfoGeometry.Canonical.TomitaTakesaki

/-!
# InfoGeometry.Canonical.YangMillsFiniteQFT

Finite constructive QFT property layer for the canonical Yang-Mills scaffold.
-/

namespace InfoGeometry.Canonical.YangMillsFinite

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

/-- Constructive reflection positivity from the joint-kernel and commutator hypotheses. -/
theorem expectationSeedReflectionPositivity_of_jointKernel_commutator
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hJointKernel : JointKernelOnOmega (F := E) K β Ω)
    (hCommOrthogonal : CommutatorOrthogonalOnOmega (F := E) Ω) :
    expectationSeedReflectionPositivity (E := E) K β Ω := by
  simpa [expectationSeedReflectionPositivity] using
    (omegaSeed_kms_of_jointKernel_commutator
      (F := E) (K := K) (β := β) (Ω := Ω) hJointKernel hCommOrthogonal)

/-- Compatibility alias for the older theorem name. -/
private theorem expectationSeedReflectionPositivity_of_hypotheses
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hJointKernel : JointKernelOnOmega (F := E) K β Ω)
    (hCommOrthogonal : CommutatorOrthogonalOnOmega (F := E) Ω) :
    expectationSeedReflectionPositivity (E := E) K β Ω :=
  expectationSeedReflectionPositivity_of_jointKernel_commutator
    (E := E) (K := K) (β := β) (Ω := Ω) hJointKernel hCommOrthogonal

/-- Finite OS-like marker induced by modular reflection geometry. -/
def finiteOsterwalderSchraderLayer
    (Ω : InfoGeometry.Krein.DoubledSpace E) : Prop :=
  0 ≤ inner ℝ ((modularConjugationJ (E := E)) Ω) Ω ∧
    modularConjugationJ (E := E) Ω = Ω

/-- Owner-name form of the same finite OS-like reflection layer. -/
def finiteOsterwalderSchraderLayerRoot
    (Ω : InfoGeometry.Krein.DoubledSpace E) : Prop :=
  0 ≤ inner ℝ ((InfoGeometry.Krein.modular_j (E := E)) Ω) Ω ∧
    InfoGeometry.Krein.modular_j (E := E) Ω = Ω

omit [CompleteSpace E] in
@[simp] theorem finiteOsterwalderSchraderLayerRoot_iff
    (Ω : InfoGeometry.Krein.DoubledSpace E) :
    finiteOsterwalderSchraderLayerRoot (E := E) Ω ↔
      finiteOsterwalderSchraderLayer (E := E) Ω := by
  simp [finiteOsterwalderSchraderLayerRoot, finiteOsterwalderSchraderLayer]

/-- Constructive finite OS-like property from positive-time geometry. -/
theorem finiteOsterwalderSchraderLayer_of_positiveTimeVector
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hΩ : PositiveTimeVector Ω) :
    finiteOsterwalderSchraderLayer (E := E) Ω := by
  refine ⟨?_, ?_⟩
  · simpa using reflectionQuadratic_nonneg_of_positiveTimeVector (E := E) Ω hΩ
  · exact modularConjugationJ_fixed_of_positiveTimeVector (E := E) Ω hΩ

/-- Root-name property from positive-time geometry. -/
theorem finiteOsterwalderSchraderLayerRoot_of_positiveTimeVector
    (Ω : InfoGeometry.Krein.DoubledSpace E)
    (hΩ : PositiveTimeVector Ω) :
    finiteOsterwalderSchraderLayerRoot (E := E) Ω := by
  simpa using finiteOsterwalderSchraderLayer_of_positiveTimeVector (E := E) Ω hΩ

/-- Finite Wightman-like marker from nonzero KMS-like expectation seed. -/
def finiteWightmanReconstructionLayer
    (K : AlgebraEnd E)
    (β : ℝ)
    (Ω : InfoGeometry.Krein.DoubledSpace E) : Prop :=
  ∃ ω : AlgebraEnd E →L[ℝ] ℝ,
    ω = omegaSeed (F := E) Ω ∧
      SatisfiesKMSLike (E := E) K ω β ∧
      ω ≠ 0

/-- Constructive finite Wightman-like property from expectation-seed data. -/
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
      (omegaSeed_nonzero (F := E) Ω hΩ)

end FiniteQFTLayer

end InfoGeometry.Canonical.YangMillsFinite
