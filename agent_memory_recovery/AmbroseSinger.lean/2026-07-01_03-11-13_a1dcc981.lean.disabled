import Mathlib.Topology.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Basic

namespace InfoGeometry.Kaehler

universe u v w

/-- Abstract base for a manifold. -/
class Manifold (M : Type u)

/-- Abstract base for a vector bundle over a manifold. -/
class VectorBundle (M : Type u) [Manifold M] (E : Type v)

/-- Connection with a curvature form taking values in a Lie algebra. -/
class Connection (M : Type u) [Manifold M] (E : Type v) [VectorBundle M E] (𝔤 : Type w) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] where
  curvature : M → 𝔤

/-- Holonomy Lie Algebra of a connection at a point p. -/
noncomputable def holonomyLieAlgebra {M : Type u} [Manifold M] {E : Type v} [VectorBundle M E] {𝔤 : Type w} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  (conn : Connection M E 𝔤) (p : M) : Submodule ℝ 𝔤 := sorry

/-- The Bergman Line Bundle is a specific vector bundle over a Kähler manifold. -/
class BergmanLineBundle (M : Type u) [Manifold M] (L : Type v) extends VectorBundle M L

/-- 
Ambrose-Singer reduction theorem for the Bergman line bundle.
For contractible loops, the holonomy Lie algebra is exactly the span of the curvature form.
-/
theorem ambrose_singer_bergman_reduction
  {M : Type u} [Manifold M] {L : Type v} [BergmanLineBundle M L]
  {𝔤 : Type w} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  (conn : Connection M L 𝔤) (p : M) :
  holonomyLieAlgebra conn p = Submodule.span ℝ {conn.curvature p} := by
  sorry

end InfoGeometry.Kaehler
