import InfoGeometry.Algebra.SplitMetricSpace
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic

/-!
# Split Metric Lie Algebra — Orthogonal Lie Algebra Layer

The Lie algebra `𝔬(β)` of the orthogonal group `O(β)` consists of
skew-symmetric endomorphisms with the commutator bracket.

Uses mathlib's native `LieAlgebra`, `skewAdjointLieSubalgebra`,
`Module.End`, `LinearMap`, `LinearEquiv`.
-/

namespace InfoGeometry.Algebra

/-- The orthogonal Lie algebra of a split metric space:
    skew-symmetric endomorphisms with commutator bracket. -/
structure SplitMetricLieAlgebra (R : Type*) [CommRing R] (S : SplitMetricSpace R) where
  L : Type*
  addCommGroup : AddCommGroup L
  module : Module R L
  lieRing : LieRing L
  lieAlgebra : LieAlgebra R L

  -- The faithful embedding into skew-symmetric endomorphisms of V
  toSkewEnd : L →ₗ[R] skewAdjointLieSubalgebra S.beta

  -- The bracket is the commutator
  bracket_eq_commutator : ∀ (x y : L), toSkewEnd ⁅x, y⁆ = ⁅toSkewEnd x, toSkewEnd y⁆

  -- Faithfulness of the embedding
  toSkewEnd_injective : Function.Injective toSkewEnd

namespace SplitMetricLieAlgebra

attribute [instance] SplitMetricLieAlgebra.addCommGroup SplitMetricLieAlgebra.module
  SplitMetricLieAlgebra.lieRing SplitMetricLieAlgebra.lieAlgebra

variable {R : Type*} [CommRing R]
variable {S : SplitMetricSpace R}
variable (L : SplitMetricLieAlgebra R S)

@[simp] def bracket (x y : L.L) : L.L := ⁅x, y⁆

-- The action on the metric space V
def action (x : L.L) (v : S.V) : S.V := (L.toSkewEnd x : Module.End R S.V) v

-- The action is by skew-symmetric endomorphisms
theorem action_skew (x : L.L) (u v : S.V) :
    S.beta (action L x u) v + S.beta u (action L x v) = 0 := by
  change S.beta ((L.toSkewEnd x : Module.End R S.V) u) v + S.beta u ((L.toSkewEnd x : Module.End R S.V) v) = 0
  rw [(L.toSkewEnd x).property u v]
  simp

-- The action preserves the Lie bracket (it's a Lie algebra homomorphism)
theorem action_lie_hom (x y : L.L) (v : S.V) :
    action L (bracket L x y) v = action L x (action L y v) - action L y (action L x v) := by
  change (L.toSkewEnd ⁅x, y⁆ : Module.End R S.V) v = _
  rw [L.bracket_eq_commutator]
  rfl

-- The native mathlib skew-adjoint Lie subalgebra of End(V) for the bilinear form beta
def nativeSkewAdjointLieSubalgebra : LieSubalgebra R (Module.End R S.V) :=
  skewAdjointLieSubalgebra S.beta

end SplitMetricLieAlgebra

/-- A homomorphism of split metric Lie algebras preserving bracket and action. -/
structure SplitMetricLieAlgebraHom {R : Type*} [CommRing R]
    {S₁ S₂ : SplitMetricSpace R}
    (L₁ : SplitMetricLieAlgebra R S₁) (L₂ : SplitMetricLieAlgebra R S₂) where
  toLinearMap : L₁.L →ₗ[R] L₂.L
  map_bracket : ∀ (x y : L₁.L), toLinearMap (⁅x, y⁆) = ⁅toLinearMap x, toLinearMap y⁆

/-- An equivalence of split metric Lie algebras. -/
structure SplitMetricLieAlgebraEquiv {R : Type*} [CommRing R]
    {S₁ S₂ : SplitMetricSpace R}
    (L₁ : SplitMetricLieAlgebra R S₁) (L₂ : SplitMetricLieAlgebra R S₂) where
  toLinearEquiv : L₁.L ≃ₗ[R] L₂.L
  map_bracket : ∀ (x y : L₁.L), toLinearEquiv (⁅x, y⁆) = ⁅toLinearEquiv x, toLinearEquiv y⁆

end InfoGeometry.Algebra
