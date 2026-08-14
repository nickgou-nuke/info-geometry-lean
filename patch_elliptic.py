import re

with open('lean/InfoGeometry/Physics/HestenesKreinOperatorCalculus.lean', 'r') as f:
    content = f.read()

proof = """theorem exp_anticommuting_elliptic (I K : A) 
    (hI : I ^ 2 = -1) (hK : K ^ 2 = 1) (h_anti : I * K = -(K * I)) 
    (θ η : ℝ) (hq : η^2 < θ^2) (r : ℝ) (hr : r^2 = θ^2 - η^2) :
    NormedSpace.exp (θ • I + η • K) = Real.cos r • (1 : A) + (Real.sin r / r) • (θ • I + η • K) := by
  have hqpos : 0 < θ ^ 2 - η ^ 2 := sub_pos.mpr hq
  have hrne : r ≠ 0 := by
    intro hr0
    apply (ne_of_gt hqpos)
    rw [← hr, hr0]
    simp
  let X : A := θ • I + η • K
  have hXsq : X * X = -(r ^ 2) • (1 : A) := by
    dsimp [X]
    calc
      (θ • I + η • K) * (θ • I + η • K) =
          (η ^ 2 - θ ^ 2) • (1 : A) := by
            simpa [pow_two] using
              (anticommuting_mixed_square I K hI hK h_anti θ η)
      _ = -(θ ^ 2 - η ^ 2) • (1 : A) := by
            congr 1
            ring
      _ = -(r ^ 2) • (1 : A) := by rw [hr]
  let G : A := r⁻¹ • X
  have hG : G ^ 2 = -(1 : A) := by
    dsimp [G]
    rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, hXsq, smul_smul]
    have hinv : r⁻¹ * r⁻¹ * -(r ^ 2) = -1 := by
      calc r⁻¹ * r⁻¹ * -(r ^ 2) = -(r⁻¹ * r⁻¹ * (r * r)) := by ring
        _ = -((r⁻¹ * r) * (r⁻¹ * r)) := by ring
        _ = -(1 * 1) := by
          rw [inv_mul_cancel₀ hrne]
        _ = -1 := by ring
    rw [hinv]
    exact neg_one_smul A (1 : A)
  have hGsq_mul : G * G = -(1 : A) := by
    simpa [pow_two] using hG
  have hexp := exp_of_sq_eq_neg_one G hGsq_mul r
  have hscale : r • G = X := by
    dsimp [G]
    rw [smul_smul, mul_inv_cancel₀ hrne, one_smul]
  rw [hscale] at hexp
  have hcoeff : Real.sin r • G = (Real.sin r / r) • X := by
    dsimp [G]
    rw [smul_smul, div_eq_mul_one_div, mul_comm]
  rw [hcoeff] at hexp
  simpa [X] using hexp"""

content = re.sub(r"theorem exp_anticommuting_elliptic.*?sorry", proof, content, flags=re.DOTALL)

with open('lean/InfoGeometry/Physics/HestenesKreinOperatorCalculus.lean', 'w') as f:
    f.write(content)
