import InfoGeometry.Physics.CStarCuntzTensorQuotient
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Topological actions of Cuntz generators

For an existing Mathlib `CStarCuntzFamily`, multiplication supplies the
topological action maps of each generator.  This is deliberately parameterized
by an actual C⋆ realization; it does not manufacture a norm or a completion
for the algebraic quotient.
-/

noncomputable section

namespace InfoGeometry.Physics.CStarCuntzTensorQuotient.CStarCuntzFamily

open CategoryTheory

variable {A ι : Type*} [CStarAlgebra A] [Fintype ι] [DecidableEq ι]

def leftGeneratorAction (F : CStarCuntzFamily A ι) (i : ι) : ContinuousMap A A :=
  ContinuousMap.mulLeft (F.S i)

def rightAdjointGeneratorAction (F : CStarCuntzFamily A ι) (i : ι) : ContinuousMap A A :=
  ContinuousMap.mulRight (star (F.S i))

@[simp] theorem leftGeneratorAction_apply
    (F : CStarCuntzFamily A ι) (i : ι) (a : A) :
    F.leftGeneratorAction i a = F.S i * a :=
  rfl

@[simp] theorem rightAdjointGeneratorAction_apply
    (F : CStarCuntzFamily A ι) (i : ι) (a : A) :
    F.rightAdjointGeneratorAction i a = a * star (F.S i) :=
  rfl

theorem leftGeneratorAction_continuous
    (F : CStarCuntzFamily A ι) (i : ι) :
    Continuous (F.leftGeneratorAction i) :=
  (F.leftGeneratorAction i).continuous_toFun

theorem rightAdjointGeneratorAction_continuous
    (F : CStarCuntzFamily A ι) (i : ι) :
    Continuous (F.rightAdjointGeneratorAction i) :=
  (F.rightAdjointGeneratorAction i).continuous_toFun

def leftGeneratorActionTopCatHom
    (F : CStarCuntzFamily A ι) (i : ι) :
    TopCat.of A ⟶ TopCat.of A :=
  TopCat.ofHom (F.leftGeneratorAction i)

def rightAdjointGeneratorActionTopCatHom
    (F : CStarCuntzFamily A ι) (i : ι) :
    TopCat.of A ⟶ TopCat.of A :=
  TopCat.ofHom (F.rightAdjointGeneratorAction i)

@[simp] theorem leftGeneratorActionTopCatHom_apply
    (F : CStarCuntzFamily A ι) (i : ι) (a : A) :
    F.leftGeneratorActionTopCatHom i a = F.S i * a :=
  rfl

@[simp] theorem rightAdjointGeneratorActionTopCatHom_apply
    (F : CStarCuntzFamily A ι) (i : ι) (a : A) :
    F.rightAdjointGeneratorActionTopCatHom i a = a * star (F.S i) :=
  rfl

theorem generator_corner_at_one
    (F : CStarCuntzFamily A ι) (i j : ι) :
    F.leftGeneratorAction i (F.rightAdjointGeneratorAction j 1) =
      F.S i * star (F.S j) := by
  simp [leftGeneratorAction, rightAdjointGeneratorAction]

theorem generator_corner_partition_at_one
    (F : CStarCuntzFamily A ι) :
    (∑ i : ι, F.leftGeneratorAction i (F.rightAdjointGeneratorAction i 1)) = 1 := by
  simp_rw [F.generator_corner_at_one]
  exact F.partition

def generatedSubalgebraInclusionTopCatHom
    (F : CStarCuntzFamily A ι) :
    TopCat.of F.generatedCStarSubalgebra ⟶ TopCat.of A :=
  TopCat.ofHom
    { toFun := fun a => (a : A)
      continuous_toFun := continuous_subtype_val }

theorem generatedSubalgebraInclusion_closedEmbedding
    (F : CStarCuntzFamily A ι) :
    Topology.IsClosedEmbedding
      ((↑) : F.generatedCStarSubalgebra → A) := by
  apply IsClosed.isClosedEmbedding_subtypeVal
  exact StarSubalgebra.isClosed_topologicalClosure _

end InfoGeometry.Physics.CStarCuntzTensorQuotient.CStarCuntzFamily
