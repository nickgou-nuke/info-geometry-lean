import Mathlib.Algebra.Module.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

/-!
# Split Metric Space — Native Mathlib Bilinear Form Layer

Uses mathlib's native `BilinForm`, `IsSymm`, `Nondegenerate`.
Concrete models provide the explicit decomposition.
-/

namespace InfoGeometry.Algebra

/-- A split metric space over a commutative ring `R`:
    a module `V` with a symmetric, nondegenerate bilinear form `β : V × V → R`. -/
structure SplitMetricSpace (R : Type*) [CommRing R] where
  V : Type*
  [addCommGroup : AddCommGroup V]
  [module : Module R V]

  -- The bilinear form (mathlib native)
  beta : LinearMap.BilinForm R V

  -- Symmetry: β(x, y) = β(y, x)
  beta_symm : beta.IsSymm

  -- Nondegeneracy: β(x, -) = 0 → x = 0
  beta_nondegenerate : beta.Nondegenerate

attribute [instance] SplitMetricSpace.addCommGroup SplitMetricSpace.module

namespace SplitMetricSpace

variable {R : Type*} [CommRing R]
variable (S : SplitMetricSpace R)

-- The orthogonal group O(β) = { g : V ≃ₗ[R] V | β(gx, gy) = β(x, y) }
def OrthogonalGroup : Type* :=
  { g : S.V ≃ₗ[R] S.V // ∀ x y, S.beta x y = S.beta (g x) (g y) }

-- The Lie algebra of the orthogonal group: skew-symmetric endomorphisms
def SkewEndomorphisms : Type* :=
  skewAdjointLieSubalgebra S.beta

end SplitMetricSpace

/-- A morphism of split metric spaces: a linear map preserving the bilinear form. -/
structure SplitMetricSpaceHom {R : Type*} [CommRing R] (S₁ S₂ : SplitMetricSpace R) where
  toLinearMap : S₁.V →ₗ[R] S₂.V
  map_beta : ∀ (x y : S₁.V), S₂.beta (toLinearMap x) (toLinearMap y) = S₁.beta x y

/-- An isomorphism of split metric spaces. -/
structure SplitMetricSpaceEquiv {R : Type*} [CommRing R] (S₁ S₂ : SplitMetricSpace R) where
  toLinearEquiv : S₁.V ≃ₗ[R] S₂.V
  map_beta : ∀ (x y : S₁.V), S₂.beta (toLinearEquiv x) (toLinearEquiv y) = S₁.beta x y

end InfoGeometry.Algebra
