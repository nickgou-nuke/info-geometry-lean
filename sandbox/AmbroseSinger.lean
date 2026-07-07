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
variable {g : Type _} [LieRing g] [LieAlgebra R g]

class Connection (B : PrincipalBundle M G) where
  parallel_transport : M → M → B.P → B.P

class CurvatureForm (R : Type _) [CommRing R] (B : PrincipalBundle M G) [Connection B]
    (g : Type _) [LieRing g] [LieAlgebra R g] where
  Omega : B.P → g

noncomputable def Loop (M : Type _) [TopologicalSpace M] (x : M) : Type _ := sorry

def IsContractible {M : Type _} [TopologicalSpace M] {x : M} (gamma : Loop M x) : Prop := sorry

noncomputable def HolonomyGroup (B : PrincipalBundle M G) [Connection B] (p : B.P) : Subgroup G := sorry

noncomputable def HolonomyLieAlgebra (R : Type _) [CommRing R] (B : PrincipalBundle M G) [Connection B]
    (p : B.P) (g : Type _) [LieRing g] [LieAlgebra R g] :
    LieSubalgebra R g := sorry

def CurvatureSpan (R : Type _) [CommRing R] (B : PrincipalBundle M G) [Connection B]
    (g : Type _) [LieRing g] [LieAlgebra R g]
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
  exact le_antisymm (holonomy_subset_curvature B p) (curvature_subset_holonomy B p)

class BergmanLineBundle (M : Type _) (G : Type _) [TopologicalSpace M] [SmoothManifold M]
    [Group G] [TopologicalSpace G] extends PrincipalBundle M G

lemma bergman_holonomy_subset_curvature
    (B : BergmanLineBundle M G) [Connection B.toPrincipalBundle]
    [CurvatureForm R B.toPrincipalBundle g] (p : B.toPrincipalBundle.P) :
    (HolonomyLieAlgebra R B.toPrincipalBundle p g).toSubmodule ≤
      CurvatureSpan R B.toPrincipalBundle g := by
  exact holonomy_subset_curvature (R := R) (g := g) B.toPrincipalBundle p

lemma bergman_curvature_subset_holonomy
    (B : BergmanLineBundle M G) [Connection B.toPrincipalBundle]
    [CurvatureForm R B.toPrincipalBundle g] (p : B.toPrincipalBundle.P) :
    CurvatureSpan R B.toPrincipalBundle g ≤
      (HolonomyLieAlgebra R B.toPrincipalBundle p g).toSubmodule := by
  exact curvature_subset_holonomy (R := R) (g := g) B.toPrincipalBundle p

theorem ambrose_singer_bergman_reduction
    (B : BergmanLineBundle M G) [Connection B.toPrincipalBundle]
    [CurvatureForm R B.toPrincipalBundle g] (p : B.toPrincipalBundle.P) :
    (HolonomyLieAlgebra R B.toPrincipalBundle p g).toSubmodule =
      CurvatureSpan R B.toPrincipalBundle g := by
  exact le_antisymm (bergman_holonomy_subset_curvature B p) (bergman_curvature_subset_holonomy B p)

instance myTrivialTopologicalSpace : TopologicalSpace Unit where
  IsOpen _ := True
  isOpen_univ := trivial
  isOpen_inter _ _ _ _ := trivial
  isOpen_sUnion _ _ := trivial

instance : SmoothManifold Unit := {}

instance : Group Unit where
  mul _ _ := ()
  one := ()
  inv _ := ()
  div _ _ := ()
  div_eq_mul_inv _ _ := rfl
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel _ := rfl

instance trivialPrincipalBundle : PrincipalBundle Unit Unit where
  P := Unit
  top := myTrivialTopologicalSpace
  proj _ := ()
  action _ _ := ()

instance trivialConnection : Connection trivialPrincipalBundle where
  parallel_transport _ _ p := p

instance trivialCurvatureForm {R g : Type _} [CommRing R] [LieRing g] [LieAlgebra R g] :
    CurvatureForm R trivialPrincipalBundle g where
  Omega _ := 0

instance trivialBergman : BergmanLineBundle Unit Unit :=
  { trivialPrincipalBundle with }

end InfoGeometry.Kaehler
