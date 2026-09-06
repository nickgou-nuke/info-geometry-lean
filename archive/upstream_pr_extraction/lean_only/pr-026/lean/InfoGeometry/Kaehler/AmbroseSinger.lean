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

/--
Explicit carrier for the Ambrose--Singer theorem surface.

The loop space, contractibility predicate, holonomy group, and holonomy Lie
algebra are supplied as data by a geometric owner.  This file does not create
opaque constants for them and does not assert the Ambrose--Singer equality.
-/
structure AmbroseSingerContext (B : PrincipalBundle M G) [Connection B] (p : B.P) where
  Loop : Type _
  IsContractible : Loop → Prop
  HolonomyGroup : Subgroup G
  HolonomyLieAlgebra : LieSubalgebra R g

/- Submodule spanned by curvature evaluated on the horizontal subspaces of the bundle. -/
def CurvatureSpan (B : PrincipalBundle M G) [Connection B] [CurvatureForm (R := R) B g] :
    Submodule R g :=
  Submodule.span R (Set.range (CurvatureForm.Omega (R := R) (B := B) (g := g)))

/-
7. The Ambrose-Singer Theorem:
For a principal bundle with a connection, the Lie algebra of the holonomy group
(restricted to loops contracting to an internal point) is spanned by the curvature.

Open geometric owner obligation: this file only records the finite interface and
`CurvatureSpan`.  A separate geometric/Hestenes--Krein owner must supply a
context and prove any Ambrose--Singer equality relating the supplied holonomy Lie
algebra to `CurvatureSpan`.
-/

end InfoGeometry.Kaehler