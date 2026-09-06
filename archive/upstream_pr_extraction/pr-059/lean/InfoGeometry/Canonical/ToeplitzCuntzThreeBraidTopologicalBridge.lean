import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Canonical.ToeplitzCuntzThreeArtinBraidBridge

/-!
# Topological realization of the three-strand Cuntz braid shadow

The algebraic Artin generators act on a topological coefficient algebra by
left multiplication.  This owner records those actions as `TopCat`
endomorphisms and transports the Artin relation to an equality of continuous
maps.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeBraidTopologicalBridge

open CategoryTheory
open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeArtinBraidBridge
open ToeplitzCuntzThreeGenerators

variable {R : Type*} [Ring R] [StarRing R]
variable [TopologicalSpace R] [ContinuousMul R]
variable (g : ToeplitzCuntzThreeGenerators R)

/-- Continuous left multiplication by the first Artin generator. -/
def braidGenerator1LeftTopCatHom : TopCat.of R ⟶ TopCat.of R :=
  TopCat.ofHom
    { toFun := fun x => braidGenerator1 g * x
      continuous_toFun := continuous_const.mul continuous_id }

/-- Continuous left multiplication by the second Artin generator. -/
def braidGenerator2LeftTopCatHom : TopCat.of R ⟶ TopCat.of R :=
  TopCat.ofHom
    { toFun := fun x => braidGenerator2 g * x
      continuous_toFun := continuous_const.mul continuous_id }

@[simp]
theorem braidGenerator1LeftTopCatHom_apply (x : R) :
    braidGenerator1LeftTopCatHom g x = braidGenerator1 g * x := rfl

@[simp]
theorem braidGenerator2LeftTopCatHom_apply (x : R) :
    braidGenerator2LeftTopCatHom g x = braidGenerator2 g * x := rfl

theorem braidGenerator_left_artin_relation :
    braidGenerator1LeftTopCatHom g ≫ braidGenerator2LeftTopCatHom g ≫
        braidGenerator1LeftTopCatHom g =
      braidGenerator2LeftTopCatHom g ≫ braidGenerator1LeftTopCatHom g ≫
        braidGenerator2LeftTopCatHom g := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change braidGenerator1 g * (braidGenerator2 g * (braidGenerator1 g * x)) =
    braidGenerator2 g * (braidGenerator1 g * (braidGenerator2 g * x))
  simpa only [mul_assoc] using
    congrArg (fun z : R => z * x) (artin_braid_relation g)

theorem braidGenerator1LeftTopCatHom_involutive :
    braidGenerator1LeftTopCatHom g ≫ braidGenerator1LeftTopCatHom g =
      𝟙 (TopCat.of R) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change braidGenerator1 g * (braidGenerator1 g * x) = x
  rw [← mul_assoc, braidGenerator1_sq, one_mul]

theorem braidGenerator2LeftTopCatHom_involutive :
    braidGenerator2LeftTopCatHom g ≫ braidGenerator2LeftTopCatHom g =
      𝟙 (TopCat.of R) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change braidGenerator2 g * (braidGenerator2 g * x) = x
  rw [← mul_assoc, braidGenerator2_sq, one_mul]

end InfoGeometry.Canonical.ToeplitzCuntzThreeBraidTopologicalBridge
