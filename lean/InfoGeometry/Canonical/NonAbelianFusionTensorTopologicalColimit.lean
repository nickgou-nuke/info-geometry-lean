import Mathlib.LinearAlgebra.Matrix.Kronecker
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.TopCat.Limits.Basic
import InfoGeometry.Canonical.NonAbelianFusionFRTopologicalBridge
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit

/-!
# Kronecker tensor actions through a topological direct colimit

This owner supplies the missing topological tensor wire for the finite fusion
carrier.  The tensor carrier is the genuine matrix carrier indexed by
`Fin 2 × Fin 2`; its actions are left multiplication by a Kronecker product.
The resulting continuous maps descend through the native `TopCat` direct
colimit.  No completion or coordinate approximation is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.NonAbelianFusionTensorTopologicalColimit

open CategoryTheory CategoryTheory.Limits
open Matrix
open scoped Kronecker
open InfoGeometry.Canonical.NonAbelianFusionFRBridge
open InfoGeometry.Canonical.NonAbelianFusionFRTopologicalBridge
open FilteredColimit.Native.Topological

variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [ContinuousAdd K] [ContinuousMul K]

abbrev FusionCarrier (K : Type) := Matrix (Fin 2) (Fin 2) K
abbrev FusionTensorCarrier (K : Type) :=
  Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K

abbrev fusionTensorTopologicalDiagram : ℕ ⥤ TopCat :=
  (Functor.const ℕ).obj (TopCat.of (FusionTensorCarrier K))

/-- Continuous left multiplication by a Kronecker product. -/
def tensorLeftTopCatHom (M N : FusionCarrier K) :
    TopCat.of (FusionTensorCarrier K) ⟶ TopCat.of (FusionTensorCarrier K) :=
  TopCat.ofHom
    { toFun := fun X => (M ⊗ₖ N) * X
      continuous_toFun := continuous_const.mul continuous_id }

@[simp]
theorem tensorLeftTopCatHom_apply (M N : FusionCarrier K)
    (X : FusionTensorCarrier K) :
    tensorLeftTopCatHom M N X = (M ⊗ₖ N) * X := rfl

theorem tensorLeftTopCatHom_comp
    (M N M' N' : FusionCarrier K) :
    tensorLeftTopCatHom M N ≫ tensorLeftTopCatHom M' N' =
      tensorLeftTopCatHom (M' * M) (N' * N) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro X
  change (M' ⊗ₖ N') * ((M ⊗ₖ N) * X) =
    ((M' * M) ⊗ₖ (N' * N)) * X
  rw [← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul]

def tensorActionCocone
    (action : TopCat.of (FusionTensorCarrier K) ⟶
      TopCat.of (FusionTensorCarrier K)) :
    Cocone (fusionTensorTopologicalDiagram (K := K)) where
  pt := TopCat.of (FusionTensorCarrier K)
  ι :=
    { app := fun _ => action
      naturality := by
        intro i j f
        change 𝟙 (TopCat.of (FusionTensorCarrier K)) ≫ action = action
        simp }

noncomputable def tensorActionColimitMap
    (action : TopCat.of (FusionTensorCarrier K) ⟶
      TopCat.of (FusionTensorCarrier K)) :
    topologicalDirectColimit (fusionTensorTopologicalDiagram (K := K)) ⟶
      TopCat.of (FusionTensorCarrier K) :=
  topologicalDirectDescend (fusionTensorTopologicalDiagram (K := K))
    (tensorActionCocone (K := K) action)

omit [CommRing K] [ContinuousAdd K] [ContinuousMul K] in
theorem tensorActionColimitMap_stage
    (action : TopCat.of (FusionTensorCarrier K) ⟶
      TopCat.of (FusionTensorCarrier K)) (n : ℕ)
    (X : FusionTensorCarrier K) :
    tensorActionColimitMap (K := K) action
        (topologicalDirectInjection
          (fusionTensorTopologicalDiagram (K := K)) n X) = action X := by
  have h := topologicalDirectDescend_stage
    (fusionTensorTopologicalDiagram (K := K))
    (tensorActionCocone (K := K) action) n
  exact congrArg (fun f => f X) h

def tensorActionColimitCocone
    (action : TopCat.of (FusionTensorCarrier K) ⟶
      TopCat.of (FusionTensorCarrier K)) :
    Cocone (fusionTensorTopologicalDiagram (K := K)) where
  pt := topologicalDirectColimit (fusionTensorTopologicalDiagram (K := K))
  ι :=
    { app := fun n => action ≫
        topologicalDirectInjection
          (fusionTensorTopologicalDiagram (K := K)) n
      naturality := by
        intro i j f
        dsimp [fusionTensorTopologicalDiagram]
        simp only [Category.id_comp, Category.comp_id]
        have h := topologicalDirectInjection_naturality
          (fusionTensorTopologicalDiagram (K := K)) f
        dsimp [fusionTensorTopologicalDiagram] at h
        simp only [Category.id_comp] at h
        rw [← h] }

noncomputable def tensorActionColimitEndomorphism
    (action : TopCat.of (FusionTensorCarrier K) ⟶
      TopCat.of (FusionTensorCarrier K)) :
    topologicalDirectColimit (fusionTensorTopologicalDiagram (K := K)) ⟶
      topologicalDirectColimit (fusionTensorTopologicalDiagram (K := K)) :=
  topologicalDirectDescend (fusionTensorTopologicalDiagram (K := K))
    (tensorActionColimitCocone (K := K) action)

omit [CommRing K] [ContinuousAdd K] [ContinuousMul K] in
theorem tensorActionColimitEndomorphism_stage
    (action : TopCat.of (FusionTensorCarrier K) ⟶
      TopCat.of (FusionTensorCarrier K)) (n : ℕ) :
    topologicalDirectInjection
        (fusionTensorTopologicalDiagram (K := K)) n ≫
        tensorActionColimitEndomorphism (K := K) action =
      action ≫ topologicalDirectInjection
        (fusionTensorTopologicalDiagram (K := K)) n := by
  exact topologicalDirectDescend_stage
    (fusionTensorTopologicalDiagram (K := K))
    (tensorActionColimitCocone (K := K) action) n

omit [CommRing K] [ContinuousAdd K] [ContinuousMul K] in
theorem tensorActionColimitEndomorphism_comp_stage
    (action₁ action₂ : TopCat.of (FusionTensorCarrier K) ⟶
      TopCat.of (FusionTensorCarrier K)) (n : ℕ) :
    topologicalDirectInjection
        (fusionTensorTopologicalDiagram (K := K)) n ≫
        (tensorActionColimitEndomorphism (K := K) action₁ ≫
          tensorActionColimitEndomorphism (K := K) action₂) =
      (action₁ ≫ action₂) ≫
        topologicalDirectInjection
          (fusionTensorTopologicalDiagram (K := K)) n := by
  rw [← Category.assoc, tensorActionColimitEndomorphism_stage,
    Category.assoc, tensorActionColimitEndomorphism_stage,
    ← Category.assoc]

def fusionCoxeterTensorColimitEndomorphism
    (a b q1 q2 : K) :
    topologicalDirectColimit
        (fusionTensorTopologicalDiagram (K := K)) ⟶
      topologicalDirectColimit
        (fusionTensorTopologicalDiagram (K := K)) :=
  tensorActionColimitEndomorphism (K := K)
    (tensorLeftTopCatHom
      (braidGen2 K a b q1 q2) (braidGen1 K q1 q2))

theorem fusionCoxeterTensorColimitEndomorphism_stage
    (a b q1 q2 : K) (n : ℕ) :
    topologicalDirectInjection
        (fusionTensorTopologicalDiagram (K := K)) n ≫
        fusionCoxeterTensorColimitEndomorphism (K := K) a b q1 q2 =
      tensorLeftTopCatHom
          (braidGen2 K a b q1 q2) (braidGen1 K q1 q2) ≫
        topologicalDirectInjection
          (fusionTensorTopologicalDiagram (K := K)) n := by
  exact tensorActionColimitEndomorphism_stage (K := K)
    (tensorLeftTopCatHom
      (braidGen2 K a b q1 q2) (braidGen1 K q1 q2)) n

def fusionCoxeterTensorFullTwistColimitEndomorphism
    (a b q1 q2 : K) :
    topologicalDirectColimit
        (fusionTensorTopologicalDiagram (K := K)) ⟶
      topologicalDirectColimit
        (fusionTensorTopologicalDiagram (K := K)) :=
  fusionCoxeterTensorColimitEndomorphism (K := K) a b q1 q2 ≫
    fusionCoxeterTensorColimitEndomorphism (K := K) a b q1 q2 ≫
    fusionCoxeterTensorColimitEndomorphism (K := K) a b q1 q2

theorem fusionCoxeterTensorFullTwist_stage
    (a b q1 q2 : K) (n : ℕ) :
    topologicalDirectInjection
        (fusionTensorTopologicalDiagram (K := K)) n ≫
        fusionCoxeterTensorFullTwistColimitEndomorphism
          (K := K) a b q1 q2 =
      (tensorLeftTopCatHom
          (braidGen2 K a b q1 q2) (braidGen1 K q1 q2) ≫
        tensorLeftTopCatHom
          (braidGen2 K a b q1 q2) (braidGen1 K q1 q2) ≫
        tensorLeftTopCatHom
          (braidGen2 K a b q1 q2) (braidGen1 K q1 q2)) ≫
        topologicalDirectInjection
          (fusionTensorTopologicalDiagram (K := K)) n := by
  dsimp [fusionCoxeterTensorFullTwistColimitEndomorphism,
    fusionCoxeterTensorColimitEndomorphism]
  let e := tensorActionColimitEndomorphism (K := K)
    (tensorLeftTopCatHom
      (braidGen2 K a b q1 q2) (braidGen1 K q1 q2))
  let t := tensorLeftTopCatHom
    (braidGen2 K a b q1 q2) (braidGen1 K q1 q2)
  change topologicalDirectInjection
      (fusionTensorTopologicalDiagram (K := K)) n ≫ (e ≫ e ≫ e) =
    (t ≫ t ≫ t) ≫ topologicalDirectInjection
      (fusionTensorTopologicalDiagram (K := K)) n
  rw [← Category.assoc, tensorActionColimitEndomorphism_stage,
    Category.assoc, tensorActionColimitEndomorphism_comp_stage,
    ← Category.assoc]

theorem fusionCoxeterTensorFullTwist_stage_apply
    (a b q1 q2 : K) (n : ℕ) (X : FusionTensorCarrier K) :
    fusionCoxeterTensorFullTwistColimitEndomorphism
        (K := K) a b q1 q2
      (topologicalDirectInjection
        (fusionTensorTopologicalDiagram (K := K)) n X) =
      topologicalDirectInjection
        (fusionTensorTopologicalDiagram (K := K)) n
        (((braidGen2 K a b q1 q2 ⊗ₖ braidGen1 K q1 q2) *
          (braidGen2 K a b q1 q2 ⊗ₖ braidGen1 K q1 q2) *
          (braidGen2 K a b q1 q2 ⊗ₖ braidGen1 K q1 q2)) * X) := by
  have h := fusionCoxeterTensorFullTwist_stage
    (K := K) a b q1 q2 n
  have hx := ConcreteCategory.congr_hom h X
  simp only [CategoryTheory.comp_apply] at hx
  dsimp [tensorLeftTopCatHom] at hx
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  exact hx

end InfoGeometry.Canonical.NonAbelianFusionTensorTopologicalColimit
