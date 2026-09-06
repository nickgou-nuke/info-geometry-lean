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

-- [STITCHER: MISSING OVERLAP] --
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Topology.Basic

namespace InfoGeometry.Kaehler

open Set

/-- 1. Define the Smooth Manifold -/
class SmoothManifold (M : Type _) [TopologicalSpace M]

/-- 2. Define the Principal Bundle -/
structure PrincipalBundle (M : Type _) (G : Type _) [TopologicalSpace M] [SmoothManifold M] [Group G] [TopologicalSpace G] where
  P : Type _
  [top : TopologicalSpace P]
  proj : P → M
  action : G → P → P

variable {R : Type _} [CommRing R]
variable {M : Type _} [TopologicalSpace M] [SmoothManifold M]
variable {G : Type _} [TopologicalSpace G] [Group G]
variable {g : Type _} [AddCommGroup g] [Module R g] [LieRing g] [LieAlgebra R g]

/-- 3. Define the Connection -/
class Connection (B : PrincipalBundle M G) where
  /-- Parallel transport along loops -/
  parallel_transport : M → M → B.P → B.P

/-- 4. Define the Curvature Form -/
class CurvatureForm (B : PrincipalBundle M G) [Connection B] (g : Type _) [AddCommGroup g] [Module R g] [LieRing g] [LieAlgebra R g] where
  /-- Curvature form evaluates to elements in the Lie algebra g -/
  Omega : B.P → g

/-- A mock type for loops in M based at x -/
opaque Loop (M : Type _) [TopologicalSpace M] (x : M) : Type _

/-- 5. Define Contractible loops (contracts to an internal point) -/
opaque IsContractible {x : M} (gamma : Loop M x) : Prop

/-- 6. Define the Holonomy Group -/
opaque HolonomyGroup (B : PrincipalBundle M G) [Connection B] (p : B.P) : Subgroup G

/-- The Lie algebra of the holonomy group -/
opaque HolonomyLieAlgebra (B : PrincipalBundle M G) [Connection B] (p : B.P) (g : Type _) [AddCommGroup g] [Module R g] [LieRing g] [LieAlgebra R g] : LieSubalgebra R g

/-- Submodule spanned by curvature evaluated on the horizontal subspaces of the bundle -/
def CurvatureSpan (B : PrincipalBundle M G) [Connection B] (g : Type _) [AddCommGroup g] [Module R g] [LieRing g] [LieAlgebra R g] [CurvatureForm B g] : Submodule R g :=
  Submodule.span R (Set.range (CurvatureForm.Omega (B := B) (g := g)))

/-- 7. The Ambrose-Singer Theorem:
For a principal bundle with a connection, the Lie algebra of the holonomy group
(restricted to loops contracting to an internal point) is spanned by the curvature.
-/
theorem ambrose_singer (B : PrincipalBundle M G) [Connection B] [CurvatureForm B g] (p : B.P) :
    (HolonomyLieAlgebra B p g : Submodule R g) = CurvatureSpan B g :=
  sorry

end InfoGeometry.Kaehler

-- [STITCHER: MISSING OVERLAP] --
import Mathlib.Topology.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Module.Submodule.Basic

namespace InfoGeometry.Kaehler

universe u v w

class SmoothManifold (M : Type u) [TopologicalSpace M]

class PrincipalBundle (M : Type u) (G : Type v) [TopologicalSpace M] [SmoothManifold M] [Group G] [TopologicalSpace G] where
  P : Type w
  [top : TopologicalSpace P]
  proj : P → M
  action : G → P → P

variable {M G R g : Type _}
variable [TopologicalSpace M] [SmoothManifold M]
variable [TopologicalSpace G] [Group G]
variable [CommRing R]
variable [AddCommGroup g] [Module R g] [LieRing g] [LieAlgebra R g]

class Connection (B : PrincipalBundle M G) where
  parallel_transport : M → M → B.P → B.P

class CurvatureForm (B : PrincipalBundle M G) [Connection B] where
  Omega : B.P → g

opaque HolonomyGroup (B : PrincipalBundle M G) [Connection B] (p : B.P) : Subgroup G

opaque HolonomyLieAlgebra (B : PrincipalBundle M G) [Connection B] (p : B.P) : LieSubalgebra R g

def CurvatureSpan (B : PrincipalBundle M G) [Connection B] [cf : CurvatureForm B] : Submodule R g :=
  Submodule.span R (Set.range cf.Omega)

theorem ambrose_singer (B : PrincipalBundle M G) [Connection B] [CurvatureForm B] (p : B.P) :
    ((HolonomyLieAlgebra B p : LieSubalgebra R g) : Submodule R g) = CurvatureSpan B :=
  sorry

class BergmanLineBundle (M : Type _) (G : Type _) [TopologicalSpace M] [SmoothManifold M] [Group G] [TopologicalSpace G] extends PrincipalBundle M G

theorem ambrose_singer_bergman_reduction
    (B : BergmanLineBundle M G) [Connection B.toPrincipalBundle] [CurvatureForm B.toPrincipalBundle] (p : B.toPrincipalBundle.P) :
    ((HolonomyLieAlgebra B.toPrincipalBundle p : LieSubalgebra R g) : Submodule R g) = CurvatureSpan B.toPrincipalBundle := by
  exact ambrose_singer B.toPrincipalBundle p

end InfoGeometry.Kaehler
