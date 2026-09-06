import InfoGeometry.Topology.ChiralOperatorTopologicalBraidAction
import InfoGeometry.Topology.ChiralOperatorQuotientBraidTransport
import InfoGeometry.Topology.ChiralOperatorSageLatentTensorBraid

/-!
# Homeomorphism-level external braid action

The coordinate permutations already have continuous pointwise actions and
Yang--Baxter laws.  This owner promotes those facts to native `Homeomorph`s
on the operator carrier, the Sage feature carrier, and the observational
quotient.  No multiplication is added to any tensor carrier.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Algebra

noncomputable section

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]

def chiralOperatorTensorSwapHomeomorph :
    ChiralOperatorTensor2 A ≃ₜ ChiralOperatorTensor2 A :=
  { toFun := chiralOperatorTensorSwap
    invFun := chiralOperatorTensorSwap
    left_inv := by intro p; exact chiralOperatorTensorSwap_involutive p
    right_inv := by intro p; exact chiralOperatorTensorSwap_involutive p
    continuous_toFun := continuous_chiralOperatorTensorSwap
    continuous_invFun := continuous_chiralOperatorTensorSwap }

def chiralOperatorTensorR12Homeomorph :
    ChiralOperatorTensor3 A ≃ₜ ChiralOperatorTensor3 A :=
  { toFun := chiralOperatorTensorR12
    invFun := chiralOperatorTensorR12
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl
    continuous_toFun := continuous_chiralOperatorTensorR12
    continuous_invFun := continuous_chiralOperatorTensorR12 }

def chiralOperatorTensorR23Homeomorph :
    ChiralOperatorTensor3 A ≃ₜ ChiralOperatorTensor3 A :=
  { toFun := chiralOperatorTensorR23
    invFun := chiralOperatorTensorR23
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl
    continuous_toFun := continuous_chiralOperatorTensorR23
    continuous_invFun := continuous_chiralOperatorTensorR23 }

@[simp] theorem chiralOperatorTensorSwapHomeomorph_apply
    (p : ChiralOperatorTensor2 A) :
    chiralOperatorTensorSwapHomeomorph p =
      chiralOperatorTensorSwap p := rfl

@[simp] theorem chiralOperatorTensorR12Homeomorph_apply
    (p : ChiralOperatorTensor3 A) :
    chiralOperatorTensorR12Homeomorph p =
      chiralOperatorTensorR12 p := rfl

@[simp] theorem chiralOperatorTensorR23Homeomorph_apply
    (p : ChiralOperatorTensor3 A) :
    chiralOperatorTensorR23Homeomorph p =
      chiralOperatorTensorR23 p := rfl

theorem chiralOperatorTensorR12Homeomorph_yang_baxter :
    (chiralOperatorTensorR12Homeomorph (A := A)).trans
        ((chiralOperatorTensorR23Homeomorph (A := A)).trans
          (chiralOperatorTensorR12Homeomorph (A := A))) =
      (chiralOperatorTensorR23Homeomorph (A := A)).trans
        ((chiralOperatorTensorR12Homeomorph (A := A)).trans
          (chiralOperatorTensorR23Homeomorph (A := A))) := by
  apply Homeomorph.ext
  intro p
  exact chiralOperatorTensorR12_yang_baxter p

theorem chiralOperatorTensorR12Homeomorph_quadratic :
    (chiralOperatorTensorR12Homeomorph (A := A)).trans
        (chiralOperatorTensorR12Homeomorph (A := A)) =
      Homeomorph.refl _ := by
  apply Homeomorph.ext
  intro p
  exact chiralOperatorTensorR12_quadratic p

theorem chiralOperatorTensorR23Homeomorph_quadratic :
    (chiralOperatorTensorR23Homeomorph (A := A)).trans
        (chiralOperatorTensorR23Homeomorph (A := A)) =
      Homeomorph.refl _ := by
  apply Homeomorph.ext
  intro p
  exact chiralOperatorTensorR23_quadratic p

def operatorSageFeatureTensorSwapHomeomorph :
    OperatorSageFeatureTensor2 A ≃ₜ OperatorSageFeatureTensor2 A :=
  { toFun := operatorSageFeatureTensorSwap
    invFun := operatorSageFeatureTensorSwap
    left_inv := by intro p; exact operatorSageFeatureTensorSwap_involutive p
    right_inv := by intro p; exact operatorSageFeatureTensorSwap_involutive p
    continuous_toFun := continuous_operatorSageFeatureTensorSwap
    continuous_invFun := continuous_operatorSageFeatureTensorSwap }

def operatorSageFeatureTensorR12Homeomorph :
    OperatorSageFeatureTensor3 A ≃ₜ OperatorSageFeatureTensor3 A :=
  { toFun := operatorSageFeatureTensorR12
    invFun := operatorSageFeatureTensorR12
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl
    continuous_toFun := continuous_operatorSageFeatureTensorR12
    continuous_invFun := continuous_operatorSageFeatureTensorR12 }

def operatorSageFeatureTensorR23Homeomorph :
    OperatorSageFeatureTensor3 A ≃ₜ OperatorSageFeatureTensor3 A :=
  { toFun := operatorSageFeatureTensorR23
    invFun := operatorSageFeatureTensorR23
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl
    continuous_toFun := continuous_operatorSageFeatureTensorR23
    continuous_invFun := continuous_operatorSageFeatureTensorR23 }

theorem operatorSageFeatureTensorR12Homeomorph_yang_baxter :
    (operatorSageFeatureTensorR12Homeomorph (A := A)).trans
        ((operatorSageFeatureTensorR23Homeomorph (A := A)).trans
          (operatorSageFeatureTensorR12Homeomorph (A := A))) =
      (operatorSageFeatureTensorR23Homeomorph (A := A)).trans
        ((operatorSageFeatureTensorR12Homeomorph (A := A)).trans
          (operatorSageFeatureTensorR23Homeomorph (A := A))) := by
  apply Homeomorph.ext
  intro p
  exact operatorSageFeatureTensorR12_yang_baxter p

def chiralOperatorQuotientTensorSwapHomeomorph :
    ChiralOperatorQuotientTensor2 A ≃ₜ ChiralOperatorQuotientTensor2 A :=
  { toFun := chiralOperatorQuotientTensorSwap
    invFun := chiralOperatorQuotientTensorSwap
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl
    continuous_toFun := continuous_chiralOperatorQuotientTensorSwap
    continuous_invFun := continuous_chiralOperatorQuotientTensorSwap }

def chiralOperatorQuotientTensorR12Homeomorph :
    ChiralOperatorQuotientTensor3 A ≃ₜ ChiralOperatorQuotientTensor3 A :=
  { toFun := chiralOperatorQuotientTensorR12
    invFun := chiralOperatorQuotientTensorR12
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl
    continuous_toFun := continuous_chiralOperatorQuotientTensorR12
    continuous_invFun := continuous_chiralOperatorQuotientTensorR12 }

def chiralOperatorQuotientTensorR23Homeomorph :
    ChiralOperatorQuotientTensor3 A ≃ₜ ChiralOperatorQuotientTensor3 A :=
  { toFun := chiralOperatorQuotientTensorR23
    invFun := chiralOperatorQuotientTensorR23
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl
    continuous_toFun := continuous_chiralOperatorQuotientTensorR23
    continuous_invFun := continuous_chiralOperatorQuotientTensorR23 }

theorem chiralOperatorQuotientTensorR12Homeomorph_yang_baxter :
    (chiralOperatorQuotientTensorR12Homeomorph (A := A)).trans
        ((chiralOperatorQuotientTensorR23Homeomorph (A := A)).trans
          (chiralOperatorQuotientTensorR12Homeomorph (A := A))) =
      (chiralOperatorQuotientTensorR23Homeomorph (A := A)).trans
        ((chiralOperatorQuotientTensorR12Homeomorph (A := A)).trans
          (chiralOperatorQuotientTensorR23Homeomorph (A := A))) := by
  apply Homeomorph.ext
  intro p
  exact chiralOperatorQuotientTensorR12_yang_baxter p

end
end InfoGeometry.Topology
