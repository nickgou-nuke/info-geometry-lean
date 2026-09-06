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
