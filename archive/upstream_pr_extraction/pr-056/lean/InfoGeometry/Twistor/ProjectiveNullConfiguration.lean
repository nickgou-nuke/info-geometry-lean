import InfoGeometry.Twistor.ProjectiveNullArtinBraid
import InfoGeometry.Projective.ProjectiveNullBoundaryBraidFrameBridge

/-!
# Ordered configurations on a projective null boundary

This owner restricts the already proved null-preserving projective linear maps
to finite ordered configurations of distinct null points.  The induced map is
a diagonal configuration-preserving action.  It is not an elementary braid
exchange, a loop in an unordered configuration space, or monodromy.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullConfiguration

open InfoGeometry.Twistor.ProjectiveNullArtinBraid
open InfoGeometry.Projective.ProjectiveNullBoundaryBraidFrameBridge

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Ordered configurations of distinct points on the quadratic null boundary. -/
abbrev NullOrderedConfiguration (Q : QuadraticForm K V) (n : ℕ) :=
  OrderedConfiguration (TwistorSpace Q) n

/-- A projectivized linear equivalence is injective on the null-boundary
subtype. -/
theorem nullProjectiveGenerator_injective
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (i : ℕ) :
    Function.Injective (nullProjectiveGenerator Q ρ hQ i) := by
  intro p q hpq
  apply Subtype.ext
  apply Projectivization.map_injective (ρ i).toLinearMap (ρ i).injective
  exact congrArg Subtype.val hpq

/-- Apply one null-preserving projective generator diagonally to an ordered
configuration.  Injectivity preserves pairwise distinctness. -/
def mapOrderedConfiguration
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (generator : ℕ) (n : ℕ) :
    NullOrderedConfiguration Q n → NullOrderedConfiguration Q n := by
  intro p
  refine ⟨fun j => nullProjectiveGenerator Q ρ hQ generator (p.1 j), ?_⟩
  intro j k hjk heq
  exact p.2 j k hjk
    (nullProjectiveGenerator_injective Q ρ hQ generator heq)

@[simp] theorem mapOrderedConfiguration_apply
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (generator : ℕ) (n : ℕ)
    (p : NullOrderedConfiguration Q n) (j : Fin n) :
    (mapOrderedConfiguration Q ρ hQ generator n p).1 j =
      nullProjectiveGenerator Q ρ hQ generator (p.1 j) :=
  rfl

/-- The diagonal configuration map is injective because its action on every
null-boundary point is injective. -/
theorem mapOrderedConfiguration_injective
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (generator : ℕ) (n : ℕ) :
    Function.Injective (mapOrderedConfiguration Q ρ hQ generator n) := by
  intro p q hpq
  apply Subtype.ext
  funext j
  apply nullProjectiveGenerator_injective Q ρ hQ generator
  exact congrFun (congrArg Subtype.val hpq) j

end InfoGeometry.Twistor.ProjectiveNullConfiguration
