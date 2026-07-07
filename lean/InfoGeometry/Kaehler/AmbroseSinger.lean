import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Topology.Basic

namespace InfoGeometry.Kaehler

open Set

class SmoothManifold (M : Type _) [TopologicalSpace M]

structure PrincipalBundle (M : Type _) (G : Type _) [TopologicalSpace M] [SmoothManifold M]
    [Group G] [TopologicalSpace G] where
  P : Type _
  top : TopologicalSpace P
  proj : P → M
  action : G → P → P

attribute [instance] PrincipalBundle.top

variable {R : Type _} [CommRing R]
variable {M : Type _} [TopologicalSpace M] [SmoothManifold M]
variable {G : Type _} [TopologicalSpace G] [Group G]
variable {g : Type _} [AddCommGroup g] [Module R g] [LieRing g] [LieAlgebra R g]

class Connection (B : PrincipalBundle M G) where
  parallel_transport : M → M → B.P → B.P

class CurvatureForm (R : Type _) [CommRing R] (B : PrincipalBundle M G) [Connection B]
    (g : Type _) [AddCommGroup g] [Module R g] [LieRing g] [LieAlgebra R g] where
  Omega : B.P → g

def CurvatureSpan (R : Type _) [CommRing R] (B : PrincipalBundle M G) [Connection B]
    (g : Type _) [AddCommGroup g] [Module R g] [LieRing g] [LieAlgebra R g]
    [CurvatureForm R B g] : Submodule R g :=
  Submodule.span R (Set.range (CurvatureForm.Omega (R := R) (B := B) (g := g)))

@[simp] theorem CurvatureSpan_def (R : Type _) [CommRing R] (B : PrincipalBundle M G)
    [Connection B] (g : Type _) [AddCommGroup g] [Module R g] [LieRing g] [LieAlgebra R g]
    [CurvatureForm R B g] :
    CurvatureSpan (R := R) B g =
      Submodule.span R (Set.range (CurvatureForm.Omega (R := R) (B := B) (g := g))) :=
  rfl

/-!
The Ambrose-Singer identification is still open in this repository surface.
This file now keeps the owner API small and reusable, instead of carrying an
unproven general theorem with placeholder proof terms.
-/

end InfoGeometry.Kaehler
