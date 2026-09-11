import InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.ProjectiveNullConfigurationWordAction

/-!
# Topological word action on unordered projective-null configurations

This owner consumes the algebraic word action and the already proved
generator homeomorphisms.  It proves continuity and homeomorphism of each
finite word under explicit continuity hypotheses on the native linear
generators and their inverses.  It does not construct loops, fundamental
groups, monodromy, or anyon statistics.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Twistor.ProjectiveNullConfigurationWordTopology

open InfoGeometry.Canonical.FiniteMajoranaBraiding
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullConfigurationWordAction
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mapUnorderedConfigurationWord_continuous
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (hcont : ∀ i, Continuous ((ρ i : V → V))) (w : BraidWord) :
    @Continuous (Unordered Q n) (Unordered Q n)
      (unorderedConfigurationTopology Q n) (unorderedConfigurationTopology Q n)
      (mapUnorderedConfigurationWord Q ρ hQ n w) := by
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  induction w with
  | nil => exact continuous_id
  | cons i w ih =>
      change Continuous
        (mapUnorderedConfiguration Q ρ hQ i n ∘
          mapUnorderedConfigurationWord Q ρ hQ n w)
      exact (mapUnorderedConfiguration_continuous Q ρ hQ i n (hcont i)).comp ih

theorem mapUnorderedConfigurationWord_isHomeomorph
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (n : ℕ)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V))) (w : BraidWord) :
    @IsHomeomorph (Unordered Q n) (Unordered Q n)
      (unorderedConfigurationTopology Q n) (unorderedConfigurationTopology Q n)
      (mapUnorderedConfigurationWord Q ρ hQ n w) := by
  letI : TopologicalSpace (ℙ K V) :=
    projectivizationQuotientTopology (K := K) (V := V)
  letI : TopologicalSpace (TwistorSpace Q) := nullBoundaryTopology Q
  letI : TopologicalSpace (Ordered Q n) := orderedConfigurationTopology Q n
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  induction w with
  | nil =>
      change @IsHomeomorph (Unordered Q n) (Unordered Q n)
        _ _ id
      exact (Homeomorph.refl (Unordered Q n)).isHomeomorph
  | cons i w ih =>
      change @IsHomeomorph (Unordered Q n) (Unordered Q n)
        _ _ (mapUnorderedConfiguration Q ρ hQ i n ∘
          mapUnorderedConfigurationWord Q ρ hQ n w)
      exact (mapUnorderedConfiguration_isHomeomorph Q ρ hQ i n
        (hcont i) (hcont_inv i)).comp ih

end InfoGeometry.Twistor.ProjectiveNullConfigurationWordTopology
