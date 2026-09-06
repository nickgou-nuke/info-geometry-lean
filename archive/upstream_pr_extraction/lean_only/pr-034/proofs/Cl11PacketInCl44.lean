import Mathlib
import InfoGeometry.Clifford.SplitCl44CausalEnvelope
import InfoGeometry.Clifford.Cl11Matrix

noncomputable section

namespace InfoGeometry.Unified

open scoped TensorProduct
open InfoGeometry.Clifford
open InfoGeometry.Clifford.BottPeriodicity
open InfoGeometry.Clifford.SplitCl44CausalEnvelope

private theorem q11_eq_cl11Matrix_q11 :
    InfoGeometry.CliffordTower.Q11 = InfoGeometry.Clifford.Cl11Matrix.q11 := by
  ext v
  simp [InfoGeometry.CliffordTower.Q11,
    InfoGeometry.Clifford.Cl11Matrix.q11,
    InfoGeometry.Clifford.splitQ11_apply, CliffordAlgebraQuaternion.Q]
  ring

private noncomputable def cl11ToQ11 :
    CliffordAlgebra InfoGeometry.CliffordTower.Q11 ≃ₐ[ℝ]
      CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11 :=
  AlgEquiv.cast q11_eq_cl11Matrix_q11

private noncomputable def cl11MatrixToQ11 :
    Matrix (Fin 2) (Fin 2) ℝ →ₐ[ℝ]
      CliffordAlgebra InfoGeometry.CliffordTower.Q11 :=
  cl11ToQ11.symm.toAlgHom.comp
    InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat.symm.toAlgHom

private noncomputable def cl11ToTensor :
    CliffordAlgebra InfoGeometry.CliffordTower.Q11 →ₐ[ℝ]
      (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11 ᵍ⊗[ℝ]
        CliffordAlgebra.evenOdd (SplitBottQuad 3)) :=
  GradedTensorProduct.includeLeft
    (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
    (CliffordAlgebra.evenOdd (SplitBottQuad 3))

noncomputable def cl11PacketAlgHom :
    Matrix (Fin 2) (Fin 2) ℝ →ₐ[ℝ] SplitCl44Algebra :=
  splitCl44_as_head_cl11_tensor_tail_cl33.symm.toAlgHom.comp
    (cl11ToTensor.comp cl11MatrixToQ11)

private theorem cl11ToTensor_injective : Function.Injective cl11ToTensor := by
  intro a b h
  have hh := congrArg
    ((GradedTensorProduct.of ℝ
      (CliffordAlgebra.evenOdd InfoGeometry.CliffordTower.Q11)
      (CliffordAlgebra.evenOdd (SplitBottQuad 3))).symm) h
  have hinj := Algebra.TensorProduct.includeLeft_injective
      (R := ℝ) (S := ℝ)
      (A := CliffordAlgebra InfoGeometry.CliffordTower.Q11)
      (B := CliffordAlgebra (SplitBottQuad 3))
      (algebraMap ℝ (CliffordAlgebra (SplitBottQuad 3))).injective
  apply hinj
  simpa [GradedTensorProduct.includeLeft_apply] using hh

theorem cl11PacketAlgHom_injective : Function.Injective cl11PacketAlgHom := by
  intro a b h
  apply cl11MatrixToQ11.injective
  apply cl11ToTensor_injective
  apply splitCl44_as_head_cl11_tensor_tail_cl33.symm.injective
  exact h

/-!
The public contract is stated for the explicit map above.  This avoids an
existential wrapper: the theorem records which algebra homomorphism realizes
the selected packet and proves its injectivity directly.
-/
def Cl11PacketInCl44Subset : Prop :=
  Function.Injective cl11PacketAlgHom

theorem cl11PacketInCl44Subset : Cl11PacketInCl44Subset :=
  cl11PacketAlgHom_injective

end InfoGeometry.Unified
