/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentGradedHom
import Mathlib.LinearAlgebra.Coevaluation
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
Balanced evaluation over the full endomorphism algebra, tensor/operator parity,
and the reconstructed duality unit with both snake identities.

The scalar pairing is invertible for nonzero real vector spaces. The full
tensor/operator pairing and duality unit require finite dimensionality.
These constructions do not yet define functors between graded module categories.
-/

noncomputable section
open TensorProduct
namespace InfoGeometry.OperatorAlgebra.PeirceSpine.OperatorMorita
variable (V : Type*) [AddCommGroup V] [Module ℝ V]

-- Fix the additive-group dictionaries before synthesizing the quotient instance.
local instance : AddCommGroup (Module.Dual ℝ V) := inferInstance
local instance : AddCommGroup (Module.Dual ℝ V ⊗[ℝ] V) := inferInstance

def relations : Submodule ℝ (Module.Dual ℝ V ⊗[ℝ] V) :=
  Submodule.span ℝ (Set.range (fun t : Module.Dual ℝ V × Module.End ℝ V × V =>
    (t.1.comp t.2.1) ⊗ₜ[ℝ] t.2.2 - t.1 ⊗ₜ[ℝ] (t.2.1 t.2.2)))

abbrev Balanced : Type _ := (Module.Dual ℝ V ⊗[ℝ] V) ⧸ (relations V)

theorem relations_le_ker : relations V ≤ LinearMap.ker (contractLeft ℝ V) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨φ, a, v⟩, rfl⟩
  simp

def evaluate : Balanced V →ₗ[ℝ] ℝ :=
  (relations V).liftQ (contractLeft ℝ V) (relations_le_ker V)

variable {V}

theorem balance (φ : Module.Dual ℝ V) (a : Module.End ℝ V) (v : V) :
    (relations V).mkQ ((φ.comp a) ⊗ₜ[ℝ] v) =
      (relations V).mkQ (φ ⊗ₜ[ℝ] a v) := by
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  apply (Submodule.Quotient.eq (relations V)).mpr
  exact Submodule.subset_span ⟨(φ, a, v), rfl⟩

theorem normal_form (φ₀ : Module.Dual ℝ V) (v₀ : V) (h : φ₀ v₀ = 1)
    (φ : Module.Dual ℝ V) (v : V) :
    (relations V).mkQ (φ ⊗ₜ[ℝ] v) =
      (φ v) • (relations V).mkQ (φ₀ ⊗ₜ[ℝ] v₀) := by
  have he : φ₀.comp (φ.smulRight v₀) = φ := by
    ext x
    simp [h]
  rw [← he, balance, he]
  simp [TensorProduct.tmul_smul]

def evaluateEquiv (φ₀ : Module.Dual ℝ V) (v₀ : V) (h : φ₀ v₀ = 1) :
    Balanced V ≃ₗ[ℝ] ℝ :=
  { evaluate V with
    invFun := fun r => r • (relations V).mkQ (φ₀ ⊗ₜ[ℝ] v₀)
    left_inv := by
      intro q
      induction q using Submodule.Quotient.induction_on with
      | _ x =>
        induction x using TensorProduct.induction_on with
        | zero => simp [evaluate]
        | tmul φ v =>
          simpa [evaluate] using (normal_form φ₀ v₀ h φ v).symm
        | add x y hx hy =>
          change (evaluate V) ((relations V).mkQ (x + y)) • _ =
            (relations V).mkQ (x + y)
          rw [map_add, map_add, add_smul]
          exact congrArg₂ (· + ·) hx hy
    right_inv := by
      intro r
      simp [evaluate, h] }

/-- Nonzero vector spaces supply the normalization internally. -/
theorem evaluate_bijective [Nontrivial V] : Function.Bijective (evaluate V) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℝ hv
  exact (evaluateEquiv φ v hφ).bijective

/-- The balanced evaluation isomorphism needs no supplied normalization packet. -/
def balancedEvaluationEquiv [Nontrivial V] : Balanced V ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective (evaluate V) evaluate_bijective

theorem relations_eq_ker [Nontrivial V] :
    relations V = LinearMap.ker (contractLeft ℝ V) := by
  apply le_antisymm (relations_le_ker V)
  intro x hx
  have he : evaluate V ((relations V).mkQ x) = evaluate V 0 := by
    simpa [evaluate] using hx
  have hq := evaluate_bijective.injective he
  exact (Submodule.Quotient.mk_eq_zero (relations V)).mp hq

/-- First Morita associativity law, with the descended balanced evaluation. -/
theorem operator_evaluation_assoc (φ : Module.Dual ℝ V) (v w : V) :
    dualTensorHom ℝ V V (φ ⊗ₜ[ℝ] v) w =
      evaluate V ((relations V).mkQ (φ ⊗ₜ[ℝ] w)) • v := by
  simp [evaluate]

/-- Second Morita associativity law on the dual right module. -/
theorem dual_operator_evaluation_assoc (φ ψ : Module.Dual ℝ V) (v : V) :
    ψ.comp (dualTensorHom ℝ V V (φ ⊗ₜ[ℝ] v)) =
      evaluate V ((relations V).mkQ (ψ ⊗ₜ[ℝ] v)) • φ := by
  ext w
  simp [evaluate, mul_comm]

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Tensor parity uses the dual source reflection and the target reflection. -/
def tensorParity (T : Module.End ℝ V) (S : Module.End ℝ W) :
    Module.Dual ℝ V ⊗[ℝ] W →ₗ[ℝ] Module.Dual ℝ V ⊗[ℝ] W :=
  TensorProduct.map (moduleReflection T).dualMap (moduleReflection S)

theorem tensorParity_involutive {T : Module.End ℝ V} {S : Module.End ℝ W}
    (hT : T * T * T = T) (hS : S * S * S = S)
    (x : Module.Dual ℝ V ⊗[ℝ] W) : tensorParity T S (tensorParity T S x) = x := by
  have hh : (tensorParity T S).comp (tensorParity T S) = LinearMap.id := by
    ext φ w
    change tensorParity T S (tensorParity T S (φ ⊗ₜ[ℝ] w)) = φ ⊗ₜ[ℝ] w
    simp only [tensorParity, TensorProduct.map_tmul]
    have hd : (moduleReflection T).dualMap ((moduleReflection T).dualMap φ) = φ := by
      ext v
      simp [LinearMap.dualMap_apply, moduleReflection_apply_apply hT]
    rw [hd, moduleReflection_apply_apply hS]
  exact LinearMap.congr_fun hh x

/-- The tensor-to-operator pairing intertwines the actual two parity actions. -/
theorem tensorHom_parity (T : Module.End ℝ V) (S : Module.End ℝ W)
    (x : Module.Dual ℝ V ⊗[ℝ] W) :
    dualTensorHom ℝ V W (tensorParity T S x) =
      gradedHomParity T S (dualTensorHom ℝ V W x) := by
  induction x using TensorProduct.induction_on with
  | zero => ext v; simp [tensorParity, gradedHomParity]
  | tmul φ w => ext v; simp [tensorParity, gradedHomParity, LinearMap.dualMap_apply]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ext v
    simp [gradedHomParity]

/-- Evaluation is even for the dual/source tensor parity. -/
theorem evaluation_parity {T : Module.End ℝ V} (hT : T * T * T = T)
    (x : Module.Dual ℝ V ⊗[ℝ] V) :
    contractLeft ℝ V (tensorParity T T x) = contractLeft ℝ V x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v => simp [tensorParity, LinearMap.dualMap_apply, moduleReflection_apply_apply hT]
  | add x y hx hy => simp [hx, hy]

/-- The vector bimodule action is compatible with the operator grading: reflecting
`a • v` equals acting by the reflected endomorphism on the reflected vector. -/
theorem vector_bimodule_grading_compatibility {T : Module.End ℝ V}
    (hT : T * T * T = T) (a : Module.End ℝ V) (v : V) :
    moduleReflection T (a v) =
      gradedHomParity T T a (moduleReflection T v) := by
  simp only [gradedHomParity, LinearMap.comp_apply]
  rw [moduleReflection_apply_apply hT]

/-- The dual bimodule action is compatible with the induced grading on the
dual: precomposition on either side gives the same functional. -/
theorem dual_bimodule_grading_compatibility {T : Module.End ℝ V}
    (hT : T * T * T = T) (φ : Module.Dual ℝ V) (a : Module.End ℝ V) :
    (moduleReflection T).dualMap (φ.comp a) =
      ((moduleReflection T).dualMap φ).comp (gradedHomParity T T a) := by
  ext v
  simp only [LinearMap.dualMap_apply, LinearMap.comp_apply, gradedHomParity,
    LinearMap.comp_apply]
  rw [moduleReflection_apply_apply hT]

/-- Parity descends to the balanced quotient and acts trivially there,
as required by its evaluation isomorphism to the purely even base field. -/
theorem balanced_parity {T : Module.End ℝ V} (hT : T * T * T = T)
    (x : Module.Dual ℝ V ⊗[ℝ] V) :
    (relations V).mkQ (tensorParity T T x) = (relations V).mkQ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    change (relations V).mkQ ((φ.comp (moduleReflection T)) ⊗ₜ[ℝ] moduleReflection T v) = _
    rw [balance, moduleReflection_apply_apply hT]
  | add x y hx hy => simp only [map_add, hx, hy]

section Finite
variable [FiniteDimensional ℝ V]

/-- The full finite-rank operator reconstruction, not a scalar shadow. -/
def tensorHomEquiv : Module.Dual ℝ V ⊗[ℝ] W ≃ₗ[ℝ] (V →ₗ[ℝ] W) :=
  dualTensorHomEquiv ℝ V W

theorem tensorHomEquiv_parity (T : Module.End ℝ V) (S : Module.End ℝ W)
    (x : Module.Dual ℝ V ⊗[ℝ] W) :
    tensorHomEquiv (tensorParity T S x) = gradedHomParity T S (tensorHomEquiv x) :=
  tensorHom_parity T S x

theorem tensorHomEquiv_symm_parity (T : Module.End ℝ V) (S : Module.End ℝ W)
    (f : V →ₗ[ℝ] W) :
    tensorParity T S (tensorHomEquiv.symm f) =
      tensorHomEquiv.symm (gradedHomParity T S f) := by
  apply tensorHomEquiv.injective
  rw [tensorHomEquiv_parity, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Canonical coevaluation tensor, defined as the inverse image of the identity. -/
def coevaluationTensor : Module.Dual ℝ V ⊗[ℝ] V :=
  tensorHomEquiv.symm LinearMap.id

theorem coevaluationTensor_reconstruct :
    tensorHomEquiv (coevaluationTensor (V := V)) = LinearMap.id :=
  tensorHomEquiv.apply_symm_apply _

theorem coevaluationTensor_even {T : Module.End ℝ V} (hT : T * T * T = T) :
    tensorParity T T coevaluationTensor = coevaluationTensor := by
  rw [coevaluationTensor, tensorHomEquiv_symm_parity, gradedHomParity_id hT]

theorem coevaluationTensor_eq :
    coevaluationTensor (V := V) =
      TensorProduct.comm ℝ V (Module.Dual ℝ V) (coevaluation ℝ V 1) := by
  apply tensorHomEquiv.injective
  rw [coevaluationTensor_reconstruct]
  ext v
  change v = dualTensorHom ℝ V V
    (TensorProduct.comm ℝ V (Module.Dual ℝ V) (coevaluation ℝ V 1)) v
  simp only [coevaluation_apply_one, map_sum, TensorProduct.comm_tmul,
    LinearMap.sum_apply, dualTensorHom_apply]
  exact ((Module.Basis.ofVectorSpace ℝ V).sum_repr v).symm

/-- The unit obtained by reconstructing the identity operator. -/
def reconstructedUnit : ℝ →ₗ[ℝ] V ⊗[ℝ] Module.Dual ℝ V :=
  LinearMap.toSpanSingleton ℝ _
    (TensorProduct.comm ℝ (Module.Dual ℝ V) V coevaluationTensor)

theorem reconstructedUnit_eq : reconstructedUnit (V := V) = coevaluation ℝ V := by
  apply LinearMap.ext_ring
  simp [reconstructedUnit, coevaluationTensor_eq]

theorem reconstructedUnit_even {T : Module.End ℝ V} (hT : T * T * T = T) (r : ℝ) :
    TensorProduct.map (moduleReflection T) (moduleReflection T).dualMap
      (reconstructedUnit r) = reconstructedUnit r := by
  change TensorProduct.map (moduleReflection T) (moduleReflection T).dualMap
    (r • TensorProduct.comm ℝ (Module.Dual ℝ V) V coevaluationTensor) = _
  rw [map_smul, TensorProduct.map_comm]
  change r • TensorProduct.comm ℝ (Module.Dual ℝ V) V
    (tensorParity T T coevaluationTensor) = _
  rw [coevaluationTensor_even hT]
  rfl

/-- The vector snake identity uses the descended quotient evaluation. -/
theorem vector_triangle :
    ((evaluate V).comp (relations V).mkQ).lTensor V ∘ₗ
      (TensorProduct.assoc ℝ V (Module.Dual ℝ V) V).toLinearMap ∘ₗ
        (reconstructedUnit (V := V)).rTensor V =
    (TensorProduct.rid ℝ V).symm.toLinearMap ∘ₗ (TensorProduct.lid ℝ V).toLinearMap := by
  rw [reconstructedUnit_eq]
  simpa [evaluate] using contractLeft_assoc_coevaluation' ℝ V

/-- The dual snake identity uses the same constructed unit and quotient evaluation. -/
theorem dual_triangle :
    ((evaluate V).comp (relations V).mkQ).rTensor (Module.Dual ℝ V) ∘ₗ
      (TensorProduct.assoc ℝ (Module.Dual ℝ V) V (Module.Dual ℝ V)).symm.toLinearMap ∘ₗ
        (reconstructedUnit (V := V)).lTensor (Module.Dual ℝ V) =
    (TensorProduct.lid ℝ (Module.Dual ℝ V)).symm.toLinearMap ∘ₗ
      (TensorProduct.rid ℝ (Module.Dual ℝ V)).toLinearMap := by
  rw [reconstructedUnit_eq]
  simpa [evaluate] using contractLeft_assoc_coevaluation ℝ V

/-- The concrete tripotent-graded Morita context on `V` and its dual.
The action laws express the bimodule grading; evaluation and coevaluation are
even, and the final conjuncts are the vector and dual triangle identities.
Nontriviality excludes the zero carrier, where balanced evaluation is not an
isomorphism to the base field. -/
theorem tripotent_graded_morita_context [Nontrivial V]
    {T : Module.End ℝ V} (hT : T * T * T = T) :
    (∀ a : Module.End ℝ V, ∀ v : V,
      moduleReflection T (a v) =
        gradedHomParity T T a (moduleReflection T v)) ∧
    (∀ φ : Module.Dual ℝ V, ∀ a : Module.End ℝ V,
      (moduleReflection T).dualMap (φ.comp a) =
        ((moduleReflection T).dualMap φ).comp (gradedHomParity T T a)) ∧
    (∀ x : Module.Dual ℝ V ⊗[ℝ] V,
      evaluate V ((relations V).mkQ (tensorParity T T x)) =
        evaluate V ((relations V).mkQ x)) ∧
    (∀ r : ℝ,
      TensorProduct.map (moduleReflection T) (moduleReflection T).dualMap
        (reconstructedUnit (V := V) r) = reconstructedUnit r) ∧
    (((evaluate V).comp (relations V).mkQ).lTensor V ∘ₗ
      (TensorProduct.assoc ℝ V (Module.Dual ℝ V) V).toLinearMap ∘ₗ
        (reconstructedUnit (V := V)).rTensor V =
      (TensorProduct.rid ℝ V).symm.toLinearMap ∘ₗ
        (TensorProduct.lid ℝ V).toLinearMap) ∧
    (((evaluate V).comp (relations V).mkQ).rTensor (Module.Dual ℝ V) ∘ₗ
      (TensorProduct.assoc ℝ (Module.Dual ℝ V) V (Module.Dual ℝ V)).symm.toLinearMap ∘ₗ
        (reconstructedUnit (V := V)).lTensor (Module.Dual ℝ V) =
      (TensorProduct.lid ℝ (Module.Dual ℝ V)).symm.toLinearMap ∘ₗ
        (TensorProduct.rid ℝ (Module.Dual ℝ V)).toLinearMap) := by
  refine ⟨vector_bimodule_grading_compatibility hT,
    dual_bimodule_grading_compatibility hT, ?_,
    reconstructedUnit_even hT, ?_, ?_⟩
  · intro x
    exact congrArg (evaluate V) (balanced_parity hT x)
  · exact vector_triangle
  · exact dual_triangle

end Finite
end InfoGeometry.OperatorAlgebra.PeirceSpine.OperatorMorita
