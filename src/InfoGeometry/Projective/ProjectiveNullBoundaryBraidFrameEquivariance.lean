import InfoGeometry.Projective.ProjectiveNullBoundaryBraidFrameBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ArtinBraidS3Quotient
import Mathlib.GroupTheory.PresentedGroup

/-!
# Permutation-level equivariance for marked boundary configurations

This owner supplies only the finite `B₃ → S₃` permutation action and its
equivariance on marked configurations.  It does not assert a topological
fundamental-group realization or an operator-frame conjugation theorem.
-/

namespace InfoGeometry.Projective.ProjectiveNullBoundaryBraidEquivariance

open InfoGeometry.Projective.ProjectiveNullBoundaryBraidFrameBridge
open InfoGeometry.Physics.B3PresentedGroup
open PresentedGroup

abbrev BoundaryBraidGroup :=
  InfoGeometry.Canonical.BoundaryBraidRepresentation.BoundaryBraidGroup
abbrev BraidPermutation := Equiv.Perm (Fin 3)

def permutationGenerator : B3Gen → BraidPermutation
  | B3Gen.sig0 => Equiv.swap 0 1
  | B3Gen.sig1 => Equiv.swap 1 2

theorem permutationRelation :
    FreeGroup.lift permutationGenerator InfoGeometry.Physics.B3PresentedGroup.b3Relation = 1 := by
  simp only [InfoGeometry.Physics.B3PresentedGroup.b3Relation, map_mul, map_inv,
    FreeGroup.lift_apply_of]
  simp only [permutationGenerator]
  apply Equiv.ext
  intro x
  fin_cases x <;> rfl

def braidPermutation : BoundaryBraidGroup →* BraidPermutation :=
  PresentedGroup.toGroup (f := permutationGenerator)
    (rels := InfoGeometry.Physics.B3PresentedGroup.b3Relations) (by
    intro r hr
    simp [InfoGeometry.Physics.B3PresentedGroup.b3Relations] at hr
    subst r
    exact permutationRelation)

theorem braidPermutation_one :
    braidPermutation (1 : BoundaryBraidGroup) = 1 := by
  exact map_one braidPermutation

theorem braidPermutation_mul (g h : BoundaryBraidGroup) :
    braidPermutation (g * h) = braidPermutation g * braidPermutation h := by
  exact map_mul braidPermutation g h

def permuteMarkedConfiguration {S : BoundarySurface}
    (p : BraidPermutation) (x : MarkedConfiguration S 3) : MarkedConfiguration S 3 :=
  ⟨fun i => x.1 (p.symm i), by
    intro i j hij hEq
    apply x.2 (p.symm i) (p.symm j)
    · intro h
      apply hij
      exact p.symm.injective h
    · exact hEq⟩

def markedConfigAction {S : BoundarySurface}
    (g : BoundaryBraidGroup) (x : MarkedConfiguration S 3) :
    MarkedConfiguration S 3 :=
  permuteMarkedConfiguration (braidPermutation g) x

theorem markedConfigAction_underlyingPoints {S : BoundarySurface}
    (g : BoundaryBraidGroup) (x : MarkedConfiguration S 3) (i : Fin 3) :
    underlyingPoints (markedConfigAction g x) i =
      underlyingPoints x ((braidPermutation g).symm i) := by
  rfl

theorem markedConfigAction_eq_of_braidPermutation_eq {S : BoundarySurface}
    {g h : BoundaryBraidGroup}
    (hperm : braidPermutation g = braidPermutation h)
    (x : MarkedConfiguration S 3) :
    markedConfigAction g x = markedConfigAction h x := by
  unfold markedConfigAction
  rw [hperm]

theorem markedConfigAction_eq_self_of_mem_kernel {S : BoundarySurface}
    {g : BoundaryBraidGroup}
    (hg : braidPermutation g = 1)
    (x : MarkedConfiguration S 3) :
    markedConfigAction g x = x := by
  unfold markedConfigAction
  rw [hg]
  apply Subtype.ext
  funext i
  rfl

theorem markedConfigAction_pairwiseDistinct {S : BoundarySurface}
    (g : BoundaryBraidGroup) (x : MarkedConfiguration S 3) :
    PairwiseDistinct (underlyingPoints (markedConfigAction g x)) := by
  exact (markedConfigAction g x).2

def colorReadout {S : BoundarySurface}
    (x : MarkedConfiguration S 3) : Fin 3 → Fin 3 :=
  fun i => (x.1 i).2

def permuteFrameReadout (p : BraidPermutation) (c : Fin 3 → Fin 3) : Fin 3 → Fin 3 :=
  fun i => c (p.symm i)

def frameReadout {S : BoundarySurface}
    (x : MarkedConfiguration S 3) : Fin 3 → Fin 3 :=
  colorReadout x

theorem colorReadout_equivariant {S : BoundarySurface}
    (p : BraidPermutation) (x : MarkedConfiguration S 3) :
    colorReadout (permuteMarkedConfiguration p x) =
      permuteFrameReadout p (colorReadout x) := by
  rfl

theorem frameReadout_equivariant {S : BoundarySurface}
    (g : BoundaryBraidGroup) (x : MarkedConfiguration S 3) :
    frameReadout (markedConfigAction g x) =
      permuteFrameReadout (braidPermutation g) (frameReadout x) := by
  rfl

theorem permuteMarkedConfiguration_one {S : BoundarySurface}
    (x : MarkedConfiguration S 3) :
    permuteMarkedConfiguration (1 : BraidPermutation) x = x := by
  apply Subtype.ext
  funext i
  rfl

theorem permuteMarkedConfiguration_mul {S : BoundarySurface}
    (p q : BraidPermutation) (x : MarkedConfiguration S 3) :
    permuteMarkedConfiguration (p * q) x =
      permuteMarkedConfiguration p (permuteMarkedConfiguration q x) := by
  apply Subtype.ext
  funext i
  rfl

theorem markedConfig_action_one {S : BoundarySurface}
    (x : MarkedConfiguration S 3) :
    markedConfigAction (1 : BoundaryBraidGroup) x = x := by
  rw [markedConfigAction, braidPermutation_one]
  exact permuteMarkedConfiguration_one x

theorem markedConfig_action_mul {S : BoundarySurface}
    (g h : BoundaryBraidGroup) (x : MarkedConfiguration S 3) :
    markedConfigAction (g * h) x =
      markedConfigAction g (markedConfigAction h x) := by
  rw [markedConfigAction, braidPermutation_mul]
  exact permuteMarkedConfiguration_mul _ _ x

instance markedConfigurationMulAction {S : BoundarySurface} :
    MulAction BoundaryBraidGroup (MarkedConfiguration S 3) where
  smul := markedConfigAction
  one_smul := markedConfig_action_one
  mul_smul := markedConfig_action_mul

end InfoGeometry.Projective.ProjectiveNullBoundaryBraidEquivariance
