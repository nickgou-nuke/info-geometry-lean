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

/-! The left adjoint action is the continuous retraction of the left
generator action.  It is distinct from the right-adjoint action above. -/

def leftAdjointGeneratorAction (F : CStarCuntzFamily A ι) (i : ι) : ContinuousMap A A :=
  ContinuousMap.mulLeft (star (F.S i))

@[simp] theorem leftGeneratorAction_apply
    (F : CStarCuntzFamily A ι) (i : ι) (a : A) :
    F.leftGeneratorAction i a = F.S i * a :=
  rfl

@[simp] theorem rightAdjointGeneratorAction_apply
    (F : CStarCuntzFamily A ι) (i : ι) (a : A) :
    F.rightAdjointGeneratorAction i a = a * star (F.S i) :=
  rfl

@[simp] theorem leftAdjointGeneratorAction_apply
    (F : CStarCuntzFamily A ι) (i : ι) (a : A) :
    F.leftAdjointGeneratorAction i a = star (F.S i) * a :=
  rfl

theorem leftGeneratorAction_continuous
    (F : CStarCuntzFamily A ι) (i : ι) :
    Continuous (F.leftGeneratorAction i) :=
  (F.leftGeneratorAction i).continuous_toFun

theorem rightAdjointGeneratorAction_continuous
    (F : CStarCuntzFamily A ι) (i : ι) :
    Continuous (F.rightAdjointGeneratorAction i) :=
  (F.rightAdjointGeneratorAction i).continuous_toFun

theorem leftAdjointGeneratorAction_continuous
    (F : CStarCuntzFamily A ι) (i : ι) :
    Continuous (F.leftAdjointGeneratorAction i) :=
  (F.leftAdjointGeneratorAction i).continuous_toFun

theorem leftGeneratorAction_comp_rightAdjointGeneratorAction
    (F : CStarCuntzFamily A ι) (i j : ι) :
    (F.leftGeneratorAction i).comp
        (F.rightAdjointGeneratorAction j) =
      (F.rightAdjointGeneratorAction j).comp
        (F.leftGeneratorAction i) := by
  apply ContinuousMap.ext
  intro a
  change F.S i * (a * star (F.S j)) =
    (F.S i * a) * star (F.S j)
  rw [mul_assoc]

theorem leftAdjointGeneratorAction_leftGeneratorAction
    (F : CStarCuntzFamily A ι) (i : ι) (a : A) :
    F.leftAdjointGeneratorAction i (F.leftGeneratorAction i a) = a := by
  change star (F.S i) * (F.S i * a) = a
  rw [← mul_assoc, CStarCuntzFamily.isometry_relation (F := F) i, one_mul]

theorem leftGeneratorAction_range_eq_projection_fixed
    (F : CStarCuntzFamily A ι) (i : ι) :
    Set.range (F.leftGeneratorAction i) =
      {x : A | F.S i * (star (F.S i) * x) = x} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change F.S i * (star (F.S i) * (F.S i * a)) = F.S i * a
    calc
      F.S i * (star (F.S i) * (F.S i * a)) =
          F.S i * ((star (F.S i) * F.S i) * a) := by rw [mul_assoc]
      _ = F.S i * a := by
        rw [CStarCuntzFamily.isometry_relation (F := F) i, one_mul]
  · intro hx
    refine ⟨star (F.S i) * x, ?_⟩
    change F.S i * (star (F.S i) * x) = x
    exact hx

theorem leftAdjointGeneratorAction_comp_leftGeneratorAction_of_ne
    (F : CStarCuntzFamily A ι) {i j : ι} (hij : i ≠ j) :
    (F.leftAdjointGeneratorAction i).comp
        (F.leftGeneratorAction j) = ContinuousMap.const A 0 := by
  apply ContinuousMap.ext
  intro a
  change star (F.S i) * (F.S j * a) = 0
  rw [← mul_assoc, CStarCuntzFamily.orthogonal_relation (F := F) hij,
    zero_mul]

theorem generator_action_partition
    (F : CStarCuntzFamily A ι) (a : A) :
    ∑ i : ι,
      F.leftGeneratorAction i (F.leftAdjointGeneratorAction i a) = a := by
  change (∑ i : ι, F.S i * (star (F.S i) * a)) = a
  simp only [← mul_assoc]
  rw [← Finset.sum_mul]
  rw [F.partition]
  simp

/-! The pointwise partition lifts to an equality of continuous maps.  This is
the topological form of finite branch reconstruction. -/

theorem generator_action_partition_continuous
    (F : CStarCuntzFamily A ι) :
    (∑ i : ι,
      (F.leftGeneratorAction i).comp
        (F.leftAdjointGeneratorAction i)) = ContinuousMap.id A := by
  ext a
  rw [ContinuousMap.sum_apply]
  simp only [ContinuousMap.comp_apply, ContinuousMap.id_apply]
  exact F.generator_action_partition a

/-! A Cuntz isometry acts by an isometric left translation.  The proof uses
only the C*-identity and `S* S = 1`; no concrete operator realization is
introduced. -/

theorem leftGeneratorAction_isometry
    (F : CStarCuntzFamily A ι) (i : ι) :
    Isometry (F.leftGeneratorAction i) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm]
  change ‖F.S i * x - F.S i * y‖ = dist x y
  rw [← mul_sub]
  have hnorm (z : A) : ‖F.S i * z‖ = ‖z‖ := by
    have hs := CStarCuntzFamily.isometry_relation (F := F) i
    have hsq : ‖F.S i * z‖ * ‖F.S i * z‖ = ‖z‖ * ‖z‖ := by
      calc
        ‖F.S i * z‖ * ‖F.S i * z‖ =
            ‖star (F.S i * z) * (F.S i * z)‖ := by
          symm
          exact CStarRing.norm_star_mul_self
        _ = ‖star z * (star (F.S i) * F.S i) * z‖ := by
          rw [star_mul]
          simp only [mul_assoc]
        _ = ‖z‖ * ‖z‖ := by
          rw [hs, mul_one, CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg (F.S i * z), norm_nonneg z]
  simpa [dist_eq_norm] using hnorm (x - y)

theorem leftGeneratorAction_isClosedEmbedding
    (F : CStarCuntzFamily A ι) (i : ι) :
    Topology.IsClosedEmbedding (F.leftGeneratorAction i) :=
  (leftGeneratorAction_isometry F i).isClosedEmbedding

theorem leftGeneratorAction_range_isClosed
    (F : CStarCuntzFamily A ι) (i : ι) :
    IsClosed (Set.range (F.leftGeneratorAction i)) :=
  (leftGeneratorAction_isClosedEmbedding F i).isClosed_range

theorem leftGeneratorAction_projection_fixed_isClosed
    (F : CStarCuntzFamily A ι) (i : ι) :
    IsClosed {x : A | F.S i * (star (F.S i) * x) = x} := by
  rw [← F.leftGeneratorAction_range_eq_projection_fixed i]
  exact F.leftGeneratorAction_range_isClosed i

def leftGeneratorActionTopCatHom
    (F : CStarCuntzFamily A ι) (i : ι) :
    TopCat.of A ⟶ TopCat.of A :=
  TopCat.ofHom (F.leftGeneratorAction i)

def rightAdjointGeneratorActionTopCatHom
    (F : CStarCuntzFamily A ι) (i : ι) :
    TopCat.of A ⟶ TopCat.of A :=
  TopCat.ofHom (F.rightAdjointGeneratorAction i)

def leftAdjointGeneratorActionTopCatHom
    (F : CStarCuntzFamily A ι) (i : ι) :
    TopCat.of A ⟶ TopCat.of A :=
  TopCat.ofHom (F.leftAdjointGeneratorAction i)

def zeroTopCatHom : TopCat.of A ⟶ TopCat.of A :=
  TopCat.ofHom (ContinuousMap.const A 0)

def generatorActionPartitionTopCatHom
    (F : CStarCuntzFamily A ι) : TopCat.of A ⟶ TopCat.of A :=
  TopCat.ofHom
    (∑ i : ι,
      (F.leftGeneratorAction i).comp
        (F.leftAdjointGeneratorAction i))

@[simp] theorem leftGeneratorActionTopCatHom_apply
    (F : CStarCuntzFamily A ι) (i : ι) (a : A) :
    F.leftGeneratorActionTopCatHom i a = F.S i * a :=
  rfl

@[simp] theorem rightAdjointGeneratorActionTopCatHom_apply
    (F : CStarCuntzFamily A ι) (i : ι) (a : A) :
    F.rightAdjointGeneratorActionTopCatHom i a = a * star (F.S i) :=
  rfl

@[simp] theorem leftAdjointGeneratorActionTopCatHom_apply
    (F : CStarCuntzFamily A ι) (i : ι) (a : A) :
    F.leftAdjointGeneratorActionTopCatHom i a = star (F.S i) * a :=
  rfl

theorem leftGeneratorActionTopCatHom_comp_rightAdjointGeneratorActionTopCatHom
    (F : CStarCuntzFamily A ι) (i j : ι) :
    F.leftGeneratorActionTopCatHom i ≫
        F.rightAdjointGeneratorActionTopCatHom j =
      F.rightAdjointGeneratorActionTopCatHom j ≫
        F.leftGeneratorActionTopCatHom i := by
  apply TopCat.hom_ext
  simpa [leftGeneratorActionTopCatHom, rightAdjointGeneratorActionTopCatHom,
    TopCat.ofHom] using
    (leftGeneratorAction_comp_rightAdjointGeneratorAction F i j).symm

theorem leftGeneratorActionTopCatHom_comp_leftAdjointGeneratorActionTopCatHom
    (F : CStarCuntzFamily A ι) (i : ι) :
    F.leftGeneratorActionTopCatHom i ≫
        F.leftAdjointGeneratorActionTopCatHom i = 𝟙 (TopCat.of A) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  rw [TopCat.comp_app, TopCat.id_app]
  exact leftAdjointGeneratorAction_leftGeneratorAction F i a

theorem leftGeneratorActionTopCatHom_comp_leftAdjointGeneratorActionTopCatHom_of_ne
    (F : CStarCuntzFamily A ι) {i j : ι} (hij : i ≠ j) :
    F.leftGeneratorActionTopCatHom j ≫
        F.leftAdjointGeneratorActionTopCatHom i = zeroTopCatHom := by
  apply TopCat.hom_ext
  simpa [leftGeneratorActionTopCatHom, leftAdjointGeneratorActionTopCatHom,
    zeroTopCatHom, TopCat.ofHom] using
    (F.leftAdjointGeneratorAction_comp_leftGeneratorAction_of_ne hij)

theorem generatorActionPartitionTopCatHom_eq_id
    (F : CStarCuntzFamily A ι) :
    generatorActionPartitionTopCatHom F = 𝟙 (TopCat.of A) := by
  apply TopCat.hom_ext
  exact F.generator_action_partition_continuous

theorem leftAdjointGeneratorActionTopCatHom_comp_leftGeneratorActionTopCatHom_idempotent
    (F : CStarCuntzFamily A ι) (i : ι) :
    (F.leftAdjointGeneratorActionTopCatHom i ≫
        F.leftGeneratorActionTopCatHom i) ≫
      (F.leftAdjointGeneratorActionTopCatHom i ≫
        F.leftGeneratorActionTopCatHom i) =
      F.leftAdjointGeneratorActionTopCatHom i ≫
        F.leftGeneratorActionTopCatHom i := by
  calc
    (F.leftAdjointGeneratorActionTopCatHom i ≫
        F.leftGeneratorActionTopCatHom i) ≫
        (F.leftAdjointGeneratorActionTopCatHom i ≫
          F.leftGeneratorActionTopCatHom i) =
      F.leftAdjointGeneratorActionTopCatHom i ≫
        (F.leftGeneratorActionTopCatHom i ≫
          F.leftAdjointGeneratorActionTopCatHom i) ≫
          F.leftGeneratorActionTopCatHom i := by
            simp only [Category.assoc]
    _ = F.leftAdjointGeneratorActionTopCatHom i ≫
        (𝟙 (TopCat.of A)) ≫
          F.leftGeneratorActionTopCatHom i := by
            rw [leftGeneratorActionTopCatHom_comp_leftAdjointGeneratorActionTopCatHom]
    _ = F.leftAdjointGeneratorActionTopCatHom i ≫
        F.leftGeneratorActionTopCatHom i := by
            simp

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

theorem generatedSubalgebraInclusion_comp_leftGeneratorAction
    (F : CStarCuntzFamily A ι) (i : ι) :
    F.generatedSubalgebraInclusionTopCatHom ≫
        F.leftGeneratorActionTopCatHom i =
      F.generatedFamily.leftGeneratorActionTopCatHom i ≫
        F.generatedSubalgebraInclusionTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  rw [TopCat.comp_app, TopCat.comp_app]
  rfl

theorem generatedSubalgebraInclusion_comp_leftAdjointGeneratorAction
    (F : CStarCuntzFamily A ι) (i : ι) :
    F.generatedSubalgebraInclusionTopCatHom ≫
        F.leftAdjointGeneratorActionTopCatHom i =
      F.generatedFamily.leftAdjointGeneratorActionTopCatHom i ≫
        F.generatedSubalgebraInclusionTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  rw [TopCat.comp_app, TopCat.comp_app]
  rfl

theorem generatedSubalgebraInclusion_comp_rightAdjointGeneratorAction
    (F : CStarCuntzFamily A ι) (i : ι) :
    F.generatedSubalgebraInclusionTopCatHom ≫
        F.rightAdjointGeneratorActionTopCatHom i =
      F.generatedFamily.rightAdjointGeneratorActionTopCatHom i ≫
        F.generatedSubalgebraInclusionTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  rw [TopCat.comp_app, TopCat.comp_app]
  rfl

theorem generatedSubalgebraInclusion_comp_generatorActionPartition
    (F : CStarCuntzFamily A ι) :
    F.generatedSubalgebraInclusionTopCatHom ≫
        generatorActionPartitionTopCatHom F =
      generatorActionPartitionTopCatHom F.generatedFamily ≫
        F.generatedSubalgebraInclusionTopCatHom := by
  rw [generatorActionPartitionTopCatHom_eq_id F,
    generatorActionPartitionTopCatHom_eq_id F.generatedFamily]
  simp

theorem generatedSubalgebraInclusion_closedEmbedding
    (F : CStarCuntzFamily A ι) :
    Topology.IsClosedEmbedding
      ((↑) : F.generatedCStarSubalgebra → A) := by
  apply IsClosed.isClosedEmbedding_subtypeVal
  exact StarSubalgebra.isClosed_topologicalClosure _

end InfoGeometry.Physics.CStarCuntzTensorQuotient.CStarCuntzFamily
