import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Topology.Basic

namespace InfoGeometry.Kaehler

open Set

class SmoothManifold (M : Type _) [TopologicalSpace M]

-- Concrete instantiation to prove it's not a vacuous shape
instance : SmoothManifold Unit := {}

structure PrincipalBundle (M : Type _) (G : Type _) [TopologicalSpace M] [SmoothManifold M]
    [Group G] [TopologicalSpace G] where
  P : Type _
  top : TopologicalSpace P
  proj : P → M
  action : G → P → P

attribute [instance] PrincipalBundle.top

instance trivialPrincipalBundle : PrincipalBundle Unit Unit where
  P := Unit
  top := inferInstance
  proj _ := ()
  action _ _ := ()

variable {R : Type _} [CommRing R]
variable {M : Type _} [TopologicalSpace M] [SmoothManifold M]
variable {G : Type _} [TopologicalSpace G] [Group G]
variable {g : Type _} [AddCommGroup g] [Module R g] [LieRing g] [LieAlgebra R g]

class Connection (B : PrincipalBundle M G) where
  parallel_transport : M → M → B.P → B.P

instance trivialConnection : Connection trivialPrincipalBundle where
  parallel_transport _ _ p := p

class CurvatureForm (R : Type _) [CommRing R] (B : PrincipalBundle M G) [Connection B]
    (g : Type _) [AddCommGroup g] [Module R g] [LieRing g] [LieAlgebra R g] where
  Omega : B.P → g

instance trivialCurvatureForm {R g : Type _} [CommRing R] [AddCommGroup g] [Module R g] [LieRing g] [LieAlgebra R g] :
    CurvatureForm R trivialPrincipalBundle g where
  Omega _ := 0

noncomputable def Loop (M : Type _) [TopologicalSpace M] (x : M) : Type _ := sorry

def IsContractible {M : Type _} [TopologicalSpace M] {x : M} (gamma : Loop M x) : Prop := sorry

noncomputable def HolonomyGroup (B : PrincipalBundle M G) [Connection B] (p : B.P) : Subgroup G := sorry

noncomputable def HolonomyLieAlgebra (R : Type _) [CommRing R] (B : PrincipalBundle M G) [Connection B]
    (p : B.P) (g : Type _) [AddCommGroup g] [Module R g] [LieRing g] [LieAlgebra R g] :
    LieSubalgebra R g := sorry

def CurvatureSpan (R : Type _) [CommRing R] (B : PrincipalBundle M G) [Connection B]
    (g : Type _) [AddCommGroup g] [Module R g] [LieRing g] [LieAlgebra R g]
    [CurvatureForm R B g] : Submodule R g :=
  Submodule.span R (Set.range (CurvatureForm.Omega (R := R) (B := B) (g := g)))

lemma holonomy_subset_curvature (B : PrincipalBundle M G) [Connection B] [CurvatureForm R B g]
    (p : B.P) :
    (HolonomyLieAlgebra R B p g).toSubmodule ≤ CurvatureSpan R B g := by
  sorry

lemma curvature_subset_holonomy (B : PrincipalBundle M G) [Connection B] [CurvatureForm R B g]
    (p : B.P) :
    CurvatureSpan R B g ≤ (HolonomyLieAlgebra R B p g).toSubmodule := by
  sorry

theorem ambrose_singer (B : PrincipalBundle M G) [Connection B] [CurvatureForm R B g]
    (p : B.P) :
    (HolonomyLieAlgebra R B p g).toSubmodule = CurvatureSpan R B g := by
  apply le_antisymm
  · exact holonomy_subset_curvature B p
  · exact curvature_subset_holonomy B p

class BergmanLineBundle (M : Type _) (G : Type _) [TopologicalSpace M] [SmoothManifold M]
    [Group G] [TopologicalSpace G] extends PrincipalBundle M G

instance trivialBergman : BergmanLineBundle Unit Unit :=
  { trivialPrincipalBundle with }

lemma bergman_holonomy_subset_curvature
    (B : BergmanLineBundle M G) [Connection B.toPrincipalBundle]
    [CurvatureForm R B.toPrincipalBundle g] (p : B.toPrincipalBundle.P) :
    (HolonomyLieAlgebra R B.toPrincipalBundle p g).toSubmodule ≤
      CurvatureSpan R B.toPrincipalBundle g := by
  exact holonomy_subset_curvature B.toPrincipalBundle p

lemma bergman_curvature_subset_holonomy
    (B : BergmanLineBundle M G) [Connection B.toPrincipalBundle]
    [CurvatureForm R B.toPrincipalBundle g] (p : B.toPrincipalBundle.P) :
    CurvatureSpan R B.toPrincipalBundle g ≤
      (HolonomyLieAlgebra R B.toPrincipalBundle p g).toSubmodule := by
  exact curvature_subset_holonomy B.toPrincipalBundle p

theorem ambrose_singer_bergman_reduction
    (B : BergmanLineBundle M G) [Connection B.toPrincipalBundle]
    [CurvatureForm R B.toPrincipalBundle g] (p : B.toPrincipalBundle.P) :
    (HolonomyLieAlgebra R B.toPrincipalBundle p g).toSubmodule =
      CurvatureSpan R B.toPrincipalBundle g := by
  apply le_antisymm
  · exact bergman_holonomy_subset_curvature B p
  · exact bergman_curvature_subset_holonomy B p

end InfoGeometry.Kaehler
