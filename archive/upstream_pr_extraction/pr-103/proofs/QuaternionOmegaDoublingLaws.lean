import proofs.QuaternionOmegaDoublingSquare

/-! # Algebra laws of the quaternionic two-bit doubling square -/

noncomputable section
namespace QuaternionOmegaDoublingLaws

open QuaternionAlgebra
open QuaternionOmegaDoublingSquare

theorem central_associative (ε : ℝ) (x y z : Carrier) :
    centralMul ε (centralMul ε x y) z =
      centralMul ε x (centralMul ε y z) := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  rcases z with ⟨e, f⟩
  apply Prod.ext <;>
    simp only [centralMul, add_mul, mul_add, mul_assoc, add_smul, smul_add,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm] <;> abel

theorem twisted_hyperbolic_eq (x y : Carrier) :
    twistedMul hyperbolic x y = x * y := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  apply Prod.ext <;>
    simp [twistedMul, hyperbolic, HestenesHyperbolicDoubling.splitMul_def]

theorem twisted_hyperbolic_left_alternative (x y : Carrier) :
    twistedMul hyperbolic x (twistedMul hyperbolic x y) =
      twistedMul hyperbolic (twistedMul hyperbolic x x) y := by
  simp only [twisted_hyperbolic_eq]
  exact HestenesHyperbolicDoubling.left_alternative _ _

theorem twisted_hyperbolic_right_alternative (x y : Carrier) :
    twistedMul hyperbolic (twistedMul hyperbolic x y) y =
      twistedMul hyperbolic x (twistedMul hyperbolic y y) := by
  simp only [twisted_hyperbolic_eq]
  exact HestenesHyperbolicDoubling.right_alternative _ _

set_option maxHeartbeats 1000000 in
theorem twisted_elliptic_left_alternative (x y : Carrier) :
    twistedMul elliptic x (twistedMul elliptic x y) =
      twistedMul elliptic (twistedMul elliptic x x) y := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  ext <;>
    simp only [twistedMul, elliptic, neg_smul, one_smul,
      Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
      Quaternion.imK_add, Quaternion.re_neg, Quaternion.imI_neg,
      Quaternion.imJ_neg, Quaternion.imK_neg, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
      Quaternion.imK_star] <;>
    ring

set_option maxHeartbeats 1000000 in
theorem twisted_elliptic_right_alternative (x y : Carrier) :
    twistedMul elliptic (twistedMul elliptic x y) y =
      twistedMul elliptic x (twistedMul elliptic y y) := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  ext <;>
    simp only [twistedMul, elliptic, neg_smul, one_smul,
      Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
      Quaternion.imK_add, Quaternion.re_neg, Quaternion.imI_neg,
      Quaternion.imJ_neg, Quaternion.imK_neg, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
      Quaternion.imK_star] <;>
    ring

def qi : H := (QuaternionAlgebra.Basis.self ℝ).i
def qj : H := (QuaternionAlgebra.Basis.self ℝ).j

theorem twisted_nonassociative (ε : ℝ) :
    twistedMul ε (twistedMul ε omega (qi, 0)) (qj, 0) ≠
      twistedMul ε omega (twistedMul ε (qi, 0) (qj, 0)) := by
  intro h
  have hr := congrArg Prod.snd h
  simp [twistedMul, omega, qi, qj] at hr
  have hk := congrArg (fun q : H => q.imK) hr
  norm_num at hk

theorem four_branch_law_packet :
    (∀ x y z, biquaternionMul (biquaternionMul x y) z =
      biquaternionMul x (biquaternionMul y z)) ∧
    (∀ x y z, splitBiquaternionMul (splitBiquaternionMul x y) z =
      splitBiquaternionMul x (splitBiquaternionMul y z)) ∧
    (∀ x y, octonionMul x (octonionMul x y) =
      octonionMul (octonionMul x x) y) ∧
    (∀ x y, splitOctonionMul x (splitOctonionMul x y) =
      splitOctonionMul (splitOctonionMul x x) y) := by
  exact ⟨central_associative elliptic, central_associative hyperbolic,
    twisted_elliptic_left_alternative, twisted_hyperbolic_left_alternative⟩

end QuaternionOmegaDoublingLaws
end noncomputable section
