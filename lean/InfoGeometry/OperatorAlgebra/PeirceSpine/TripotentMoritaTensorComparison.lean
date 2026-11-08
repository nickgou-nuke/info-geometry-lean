/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentGradedMorita
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Tower
noncomputable section
open CategoryTheory TensorProduct
open scoped Matrix.Module
namespace InfoGeometry.OperatorAlgebra.PeirceSpine
variable {V : Type} [AddCommGroup V] [Module ℝ V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def tensorCoordinates (b : Module.Basis ι ℝ V) (W : ModuleCat ℝ) :
    V ⊗[ℝ] W ≃ₗ[ℝ] (ι → W) :=
  (TensorProduct.comm ℝ V W).trans
    ((TensorProduct.congr (LinearEquiv.refl ℝ W) b.equivFun).trans
      (TensorProduct.piScalarRight ℝ ℝ W ι))

theorem tensorCoordinates_tmul (b : Module.Basis ι ℝ V) (W : ModuleCat ℝ)
    (v : V) (w : W) (j : ι) : tensorCoordinates b W (v ⊗ₜ[ℝ] w) j = b.repr v j • w := by
  simp [tensorCoordinates]

def inverseRealCarrier (b : Module.Basis ι ℝ V) (i : ι) : ModuleCat ℝ ⥤ ModuleCat ℝ :=
  (endomorphismMorita b i).eqv.inverse ⋙
    ModuleCat.restrictScalars (algebraMap ℝ (Module.End ℝ V))

def inverseCoordinates (b : Module.Basis ι ℝ V) (i : ι) (W : ModuleCat ℝ) :
    (inverseRealCarrier b i).obj W ≃ₗ[ℝ] (ι → W) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change (LinearMap.toMatrixAlgEquiv b (algebraMap ℝ _ r)) • (show ι → W from x) =
      r • (show ι → W from x)
    rw [AlgEquiv.commutes]
    exact Matrix.Module.scalar_smul r x

def tensorInverseComparison (b : Module.Basis ι ℝ V) (i : ι) (W : ModuleCat ℝ) :
    V ⊗[ℝ] W ≃ₗ[ℝ] (inverseRealCarrier b i).obj W :=
  (tensorCoordinates b W).trans (inverseCoordinates b i W).symm

def tensorCarrierFunctor : ModuleCat ℝ ⥤ ModuleCat ℝ where
  obj W := ModuleCat.of ℝ (V ⊗[ℝ] W)
  map f := ModuleCat.ofHom (TensorProduct.map LinearMap.id f.hom)
  map_id W := by apply ModuleCat.hom_ext; ext v w; rfl
  map_comp f g := by apply ModuleCat.hom_ext; ext v w; rfl

def tensorInverseNatIso (b : Module.Basis ι ℝ V) (i : ι) :
    tensorCarrierFunctor (V := V) ≅ inverseRealCarrier b i :=
  NatIso.ofComponents (fun W => (tensorInverseComparison b i W).toModuleIso) (by
    intro X Y f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext v w
    change (fun j => b.repr v j • f.hom w) = (fun j => f.hom (b.repr v j • w))
    funext j
    exact (f.hom.map_smul _ _).symm)


theorem tensorInverseComparison_operator (b : Module.Basis ι ℝ V) (i : ι)
    (W : ModuleCat ℝ) (a : Module.End ℝ V) (x : V ⊗[ℝ] W) :
    tensorInverseComparison b i W (TensorProduct.map a LinearMap.id x) =
      a • (show (endomorphismMorita b i).eqv.inverse.obj W from
        tensorInverseComparison b i W x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    change (0 : (endomorphismMorita b i).eqv.inverse.obj W) = a • 0
    exact (smul_zero a).symm
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    exact (smul_add a
      (show (endomorphismMorita b i).eqv.inverse.obj W from tensorInverseComparison b i W x)
      (show (endomorphismMorita b i).eqv.inverse.obj W from tensorInverseComparison b i W y)).symm
  | tmul v w =>
    change (fun j => b.repr (a v) j • w) =
      (fun j => ∑ k, (LinearMap.toMatrix b b a) j k • (b.repr v k • w))
    funext j
    rw [← LinearMap.toMatrix_mulVec_repr b b a v]
    simp [Matrix.mulVec, dotProduct, Finset.sum_smul, smul_smul]


theorem tensor_operator_map (W : ModuleCat ℝ) (a : Module.End ℝ V) (x : V ⊗[ℝ] W) :
    TensorProduct.map a LinearMap.id x = a • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy, smul_add]
  | tmul v w => rfl

def tensorInverseOperatorEquiv (b : Module.Basis ι ℝ V) (i : ι) (W : ModuleCat ℝ) :
    V ⊗[ℝ] W ≃ₗ[Module.End ℝ V] (endomorphismMorita b i).eqv.inverse.obj W :=
  { (tensorInverseComparison b i W).toAddEquiv with
    map_smul' := by
      intro a x
      change tensorInverseComparison b i W (a • x) =
        a • (show (endomorphismMorita b i).eqv.inverse.obj W from tensorInverseComparison b i W x)
      rw [← tensor_operator_map]
      exact tensorInverseComparison_operator b i W a x }

def tensorOperatorFunctor : ModuleCat ℝ ⥤ ModuleCat (Module.End ℝ V) where
  obj W := ModuleCat.of (Module.End ℝ V) (V ⊗[ℝ] W)
  map f := ModuleCat.ofHom (AlgebraTensorModule.map LinearMap.id f.hom)
  map_id W := by apply ModuleCat.hom_ext; ext v w; rfl
  map_comp f g := by apply ModuleCat.hom_ext; ext v w; rfl

def tensorInverseOperatorNatIso (b : Module.Basis ι ℝ V) (i : ι) :
    tensorOperatorFunctor (V := V) ≅ (endomorphismMorita b i).eqv.inverse :=
  NatIso.ofComponents (fun W => (tensorInverseOperatorEquiv b i W).toModuleIso) (by
    intro X Y f
    apply ModuleCat.hom_ext
    ext x
    exact congrArg (fun k : (tensorCarrierFunctor (V := V)).obj X ⟶
      (inverseRealCarrier b i).obj Y => k x) ((tensorInverseNatIso b i).hom.naturality f))

open InnerGradedMorita

/-- Tensor induction on graded modules, encoded by the untwisted C₂ action. -/
def gradedTensorFunctor : Action (ModuleCat ℝ) C2 ⥤
    Action (ModuleCat (Module.End ℝ V)) C2 :=
  (tensorOperatorFunctor (V := V)).mapAction C2

/-- Natural identification of the actual tensor functor with the inverse Morita
functor, in the category of modules with even morphisms. -/
def gradedTensorInverseNatIso (b : Module.Basis ι ℝ V) (i : ι) :
    gradedTensorFunctor (V := V) ≅ (tripotentGradedMorita b i).inverse :=
  Functor.mapActionCongr C2 (tensorInverseOperatorNatIso b i)

/-- The induced grading is ΓV tensor ΓW, on arbitrary tensors. -/
theorem gradedTensor_grading (T : Module.End ℝ V) (Y : Action (ModuleCat ℝ) C2)
    (x : V ⊗[ℝ] Y.V) :
    grading (moduleReflection T) (gradedTensorFunctor.obj Y) x =
      TensorProduct.map (moduleReflection T) (involution Y) x := by
  change moduleReflection T •
    (AlgebraTensorModule.map LinearMap.id (involution Y) x) = _
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy, smul_add]
  | tmul v w => rfl

/-- The natural comparison intertwines the tensor grading and the concrete
matrix-Morita grading; no commuting-operator hypothesis is imposed. -/
theorem gradedTensorInverse_even (b : Module.Basis ι ℝ V) (i : ι)
    (T : Module.End ℝ V) (Y : Action (ModuleCat ℝ) C2) (x : V ⊗[ℝ] Y.V) :
    ((gradedTensorInverseNatIso b i).hom.app Y).hom
      (TensorProduct.map (moduleReflection T) (involution Y) x) =
    grading (moduleReflection T) ((tripotentGradedMorita b i).inverse.obj Y)
      (((gradedTensorInverseNatIso b i).hom.app Y).hom x) := by
  rw [← gradedTensor_grading]
  change ((gradedTensorInverseNatIso b i).hom.app Y).hom.hom
      (grading (moduleReflection T) ((gradedTensorFunctor (V := V)).obj Y) x) = _
  exact morphism_even (moduleReflection T) ((gradedTensorInverseNatIso b i).hom.app Y) x

end InfoGeometry.OperatorAlgebra.PeirceSpine
