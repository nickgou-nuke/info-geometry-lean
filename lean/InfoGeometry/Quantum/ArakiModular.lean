import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Clifford.SplitOctonionsDualProduct
import InfoGeometry.Clifford.HestenesNaturalConeStandardForm
import InfoGeometry.Quantum.KitaevMajorana

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {R : Type*} [Field R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) (v0 : M)

namespace InfoGeometry.Quantum.TomitaTakesakiBridge

open CliffordAlgebra
open InfoGeometry.Clifford.Hestenes
open InfoGeometry.Riemannian
open InfoGeometry.Quantum

def arakiRelativeModularOp (P : ClPlus Q) (X : ClPlus Q) : ClPlus Q :=
  L_action Q P (R_action Q (hestenesAdjoint Q v0 P) X)

theorem arakiModular_one (hv0_norm : Q v0 = 1) (X : ClPlus Q) : arakiRelativeModularOp Q v0 1 X = X := by
  dsimp [arakiRelativeModularOp]
  have h_adj : hestenesAdjoint Q v0 (1 : ClPlus Q) = 1 := hestenesAdjoint_one Q v0 hv0_norm
  rw [h_adj]
  dsimp [L_action, R_action]
  apply Subtype.ext
  dsimp
  rw [mul_one, one_mul]

lemma val_mul_eq_mul_val (a b : ClPlus Q) : (a * b).val = a.val * b.val := rfl
lemma val_add_eq_add_val (a b : ClPlus Q) : (a + b).val = a.val + b.val := rfl
lemma val_sub_eq_sub_val (a b : ClPlus Q) : (a - b).val = a.val - b.val := rfl
lemma val_smul_eq_smul_val (r : R) (a : ClPlus Q) : (r • a).val = r • a.val := rfl
lemma val_one_eq_one_val : (1 : ClPlus Q).val = 1 := rfl

lemma hestenesAdjoint_add (A B : ClPlus Q) : 
  hestenesAdjoint Q v0 (A + B) = hestenesAdjoint Q v0 A + hestenesAdjoint Q v0 B := by
  apply Subtype.ext
  dsimp [hestenesAdjoint]
  rw [map_add, mul_add, add_mul]

theorem modular_collapse_eq_kitaev_symmetric (hv0_norm : Q v0 = 1) (γ1 γ2 : MajoranaOperator Q v0) 
    (h_anti : γ1.val * γ2.val = - (γ2.val * γ1.val))
    (h_γ1_sq : γ1.val * γ1.val = -1) (h_γ2_sq : γ2.val * γ2.val = -1) :
    let P := @KitaevProjectorPlus R _ M _ _ Q v0 γ1 γ2
    (arakiRelativeModularOp Q v0 P P).val = (2 : R) • P.val := by
  intro P
  have h_anti_rev : γ2.val * γ1.val = - (γ1.val * γ2.val) := by
    calc γ2.val * γ1.val 
      _ = - (- (γ2.val * γ1.val)) := by simp
      _ = - (γ1.val * γ2.val) := by rw [← h_anti]

  have h_adj_bivec : hestenesAdjoint Q v0 (γ1.val * γ2.val) = - (γ1.val * γ2.val) := by
    have h_mul := hestenesAdjoint_mul Q v0 hv0_norm γ1.val γ2.val
    rw [h_mul]
    have h_g1 : hestenesAdjoint Q v0 γ1.val = γ1.val := γ1.property
    have h_g2 : hestenesAdjoint Q v0 γ2.val = γ2.val := γ2.property
    rw [h_g1, h_g2]
    exact h_anti_rev

  have h_adj_P : hestenesAdjoint Q v0 P = 1 - γ1.val * γ2.val := by
    dsimp [P, KitaevProjectorPlus]
    rw [hestenesAdjoint_add]
    have h_one : hestenesAdjoint Q v0 1 = 1 := hestenesAdjoint_one Q v0 hv0_norm
    rw [h_one, h_adj_bivec]
    exact (sub_eq_add_neg 1 (γ1.val * γ2.val)).symm
    
  have h_G_sq : (γ1.val * γ2.val) * (γ1.val * γ2.val) = -1 := by
    have h1 : γ2.val * (γ1.val * γ2.val) = (γ2.val * γ1.val) * γ2.val := (mul_assoc γ2.val γ1.val γ2.val).symm
    have h2 : (γ2.val * γ1.val) * γ2.val = (-(γ1.val * γ2.val)) * γ2.val := by rw [h_anti_rev]
    have h3 : (-(γ1.val * γ2.val)) * γ2.val = - ((γ1.val * γ2.val) * γ2.val) := neg_mul (γ1.val * γ2.val) γ2.val
    have h4 : ((γ1.val * γ2.val) * γ2.val) = γ1.val * (γ2.val * γ2.val) := mul_assoc γ1.val γ2.val γ2.val
    have h5 : γ1.val * (γ2.val * γ2.val) = γ1.val * (-1) := by rw [h_γ2_sq]
    have h6 : γ1.val * (-1) = -γ1.val := mul_neg_one γ1.val
    
    calc (γ1.val * γ2.val) * (γ1.val * γ2.val)
      _ = γ1.val * (γ2.val * (γ1.val * γ2.val)) := mul_assoc γ1.val γ2.val (γ1.val * γ2.val)
      _ = γ1.val * ((γ2.val * γ1.val) * γ2.val) := by rw [h1]
      _ = γ1.val * ((-(γ1.val * γ2.val)) * γ2.val) := by rw [h2]
      _ = γ1.val * (- ((γ1.val * γ2.val) * γ2.val)) := by rw [h3]
      _ = γ1.val * (- (γ1.val * (γ2.val * γ2.val))) := by rw [h4]
      _ = γ1.val * (- (γ1.val * (-1))) := by rw [h5]
      _ = γ1.val * (- (-γ1.val)) := by rw [h6]
      _ = γ1.val * γ1.val := by simp
      _ = -1 := h_γ1_sq

  dsimp [arakiRelativeModularOp, L_action, R_action]
  rw [h_adj_P]
  
  have hP_val : P = 1 + γ1.val * γ2.val := rfl
  
  have h_diff_sq : (1 + γ1.val * γ2.val) * (1 - γ1.val * γ2.val) = (2 : ClPlus Q) := by
    have h_sub : (1 : ClPlus Q) - γ1.val * γ2.val = (1 : ClPlus Q) + -(γ1.val * γ2.val) := sub_eq_add_neg (1 : ClPlus Q) (γ1.val * γ2.val)
    have h_expand : ((1 : ClPlus Q) + γ1.val * γ2.val) * ((1 : ClPlus Q) + -(γ1.val * γ2.val)) = (1 : ClPlus Q) * ((1 : ClPlus Q) + -(γ1.val * γ2.val)) + (γ1.val * γ2.val) * ((1 : ClPlus Q) + -(γ1.val * γ2.val)) := add_mul (1 : ClPlus Q) (γ1.val * γ2.val) ((1 : ClPlus Q) + -(γ1.val * γ2.val))
    have h_term1 : (1 : ClPlus Q) * ((1 : ClPlus Q) + -(γ1.val * γ2.val)) = (1 : ClPlus Q) + -(γ1.val * γ2.val) := one_mul ((1 : ClPlus Q) + -(γ1.val * γ2.val))
    have h_term2 : (γ1.val * γ2.val) * ((1 : ClPlus Q) + -(γ1.val * γ2.val)) = γ1.val * γ2.val * (1 : ClPlus Q) + (γ1.val * γ2.val) * -(γ1.val * γ2.val) := mul_add (γ1.val * γ2.val) (1 : ClPlus Q) (-(γ1.val * γ2.val))
    have h_term2_1 : γ1.val * γ2.val * (1 : ClPlus Q) = γ1.val * γ2.val := mul_one (γ1.val * γ2.val)
    have h_term2_2 : (γ1.val * γ2.val) * -(γ1.val * γ2.val) = - ((γ1.val * γ2.val) * (γ1.val * γ2.val)) := mul_neg (γ1.val * γ2.val) (γ1.val * γ2.val)
    
    calc ((1 : ClPlus Q) + γ1.val * γ2.val) * ((1 : ClPlus Q) - γ1.val * γ2.val)
      _ = ((1 : ClPlus Q) + γ1.val * γ2.val) * ((1 : ClPlus Q) + -(γ1.val * γ2.val)) := by rw [h_sub]
      _ = (1 : ClPlus Q) * ((1 : ClPlus Q) + -(γ1.val * γ2.val)) + (γ1.val * γ2.val) * ((1 : ClPlus Q) + -(γ1.val * γ2.val)) := h_expand
      _ = (1 : ClPlus Q) + -(γ1.val * γ2.val) + (γ1.val * γ2.val) * ((1 : ClPlus Q) + -(γ1.val * γ2.val)) := by rw [h_term1]
      _ = (1 : ClPlus Q) + -(γ1.val * γ2.val) + (γ1.val * γ2.val * (1 : ClPlus Q) + (γ1.val * γ2.val) * -(γ1.val * γ2.val)) := by rw [h_term2]
      _ = (1 : ClPlus Q) + -(γ1.val * γ2.val) + (γ1.val * γ2.val + (γ1.val * γ2.val) * -(γ1.val * γ2.val)) := by rw [h_term2_1]
      _ = (1 : ClPlus Q) + -(γ1.val * γ2.val) + (γ1.val * γ2.val + - ((γ1.val * γ2.val) * (γ1.val * γ2.val))) := by rw [h_term2_2]
      _ = (1 : ClPlus Q) + (-(γ1.val * γ2.val) + γ1.val * γ2.val) + - ((γ1.val * γ2.val) * (γ1.val * γ2.val)) := by simp [add_assoc]
      _ = (1 : ClPlus Q) + 0 + - ((γ1.val * γ2.val) * (γ1.val * γ2.val)) := by rw [neg_add_cancel (γ1.val * γ2.val)]
      _ = (1 : ClPlus Q) - ((γ1.val * γ2.val) * (γ1.val * γ2.val)) := by simp [sub_eq_add_neg]
      _ = (1 : ClPlus Q) - (-1) := by rw [h_G_sq]
      _ = (2 : ClPlus Q) := by norm_num

  have h_P_mul_1 : P * (P * ((1 : ClPlus Q) - γ1.val * γ2.val)) = (P * P) * ((1 : ClPlus Q) - γ1.val * γ2.val) := (mul_assoc P P ((1 : ClPlus Q) - γ1.val * γ2.val)).symm
  have h_P_mul_2 : P * P = P * ((1 : ClPlus Q) + γ1.val * γ2.val) := by rw [hP_val]
  have h_P_mul_3 : P * ((1 : ClPlus Q) + γ1.val * γ2.val) * ((1 : ClPlus Q) - γ1.val * γ2.val) = P * (((1 : ClPlus Q) + γ1.val * γ2.val) * ((1 : ClPlus Q) - γ1.val * γ2.val)) := mul_assoc P ((1 : ClPlus Q) + γ1.val * γ2.val) ((1 : ClPlus Q) - γ1.val * γ2.val)
  
  have h_P_mul_4 : P * (((1 : ClPlus Q) + γ1.val * γ2.val) * ((1 : ClPlus Q) - γ1.val * γ2.val)) = P * (2 : ClPlus Q) := congrArg (fun x => P * x) h_diff_sq

  have h_P_mul_5 : P * 2 = 2 * P := by
    have h2 : (2 : ClPlus Q) = 1 + 1 := by norm_num
    rw [h2, mul_add, add_mul, mul_one, one_mul]
    
  have h_smul : 2 * P = (2 : R) • P := by exact Algebra.smul_def 2 P
  
  have h_final_val : (P * (P * (1 - γ1.val * γ2.val))).val = ((2 : R) • P).val := by
    have h_final : P * (P * (1 - γ1.val * γ2.val)) = (2 : R) • P := by
      calc P * (P * (1 - γ1.val * γ2.val))
        _ = (P * P) * (1 - γ1.val * γ2.val) := h_P_mul_1
        _ = (P * (1 + γ1.val * γ2.val)) * (1 - γ1.val * γ2.val) := by rw [h_P_mul_2]
        _ = P * ((1 + γ1.val * γ2.val) * (1 - γ1.val * γ2.val)) := h_P_mul_3
        _ = P * 2 := h_P_mul_4
        _ = 2 * P := h_P_mul_5
        _ = (2 : R) • P := h_smul
    rw [h_final]

  -- arakiRelativeModularOp evaluates to P * (1 - γ1.val * γ2.val) * P
  -- Wait, araki is P * ( (1 - γ1.val * γ2.val) * P) ... wait.
  -- R_action P X is X * P
  -- So R_action (1 - γ1.val * γ2.val) P is P * (1 - γ1.val * γ2.val)
  -- L_action P (R_action (1 - γ1.val * γ2.val) P) is P * (P * (1 - γ1.val * γ2.val))
  exact h_final_val

end InfoGeometry.Quantum.TomitaTakesakiBridge
