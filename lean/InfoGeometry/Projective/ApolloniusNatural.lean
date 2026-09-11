import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

namespace InfoGeometry.Projective.ApolloniusNatural

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Homogeneous coordinates $[Z_0 : Z_1]$ on ℂP¹ in the natural Apollonian coordinates $(\xi, \theta)$. -/
def apolloniusRay (ξ θ : ℝ) : ℂ × ℂ :=
  (Complex.exp ((ξ : ℂ) + Complex.I * (θ : ℂ)), 1)

/-- The projective Fubini-Study / Cayley signature quotient $\mathcal{Q}([Z_0 : Z_1]) = (|Z_0|^2 - |Z_1|^2) / (|Z_0|^2 + |Z_1|^2)$. -/
def projectiveSignatureQuotient (Z : ℂ × ℂ) : ℝ :=
  (normSq Z.1 - normSq Z.2) / (normSq Z.1 + normSq Z.2)

/-!
### 1. Projective Norm Evaluation in Natural Coordinates
-/

/-- 🏆 THEOREM 1 (Modulus Factorization in Natural Coordinates):
    The norm squared of the first homogeneous coordinate is strictly $e^{2\xi}$. -/
theorem apollonius_ray_z0_normSq (ξ θ : ℝ) :
    normSq (apolloniusRay ξ θ).1 = Real.exp (2 * ξ) := by
  unfold apolloniusRay
  dsimp
  have h_split : Complex.exp ((ξ : ℂ) + Complex.I * (θ : ℂ)) =
                 Complex.exp (ξ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := Complex.exp_add _ _
  rw [h_split, map_mul]
  have h_norm1 : normSq (Complex.exp (ξ : ℂ)) = Real.exp (2 * ξ) := by
    rw [← Complex.ofReal_exp]
    simp only [normSq_ofReal, sq]
    rw [← Real.exp_add]
    ring_nf
  have h_norm2 : normSq (Complex.exp (Complex.I * (θ : ℂ))) = 1 := by
    have h_unit : ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 := by
      have h_comm : Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I := by ring
      rw [h_comm, Complex.norm_exp_ofReal_mul_I]
    rw [normSq_eq_norm_sq, h_unit, one_pow]
  rw [h_norm1, h_norm2, mul_one]

/-- The natural radial coordinate is recovered from the squared Apollonius
    modulus.  This is the inverse readback of `apollonius_ray_z0_normSq`. -/
theorem apollonius_ray_xi_recovery (ξ θ : ℝ) :
    (1 / 2 : ℝ) * Real.log (normSq (apolloniusRay ξ θ).1) = ξ := by
  rw [apollonius_ray_z0_normSq, Real.log_exp]
  ring

/-- The angular coordinate is recovered globally as the phase of the natural
    ray, without choosing a branch of `Complex.arg`. -/
theorem apollonius_ray_phase_recovery (ξ θ : ℝ) :
    Complex.exp (-(ξ : ℂ)) * (apolloniusRay ξ θ).1 =
      Complex.exp (Complex.I * (θ : ℂ)) := by
  unfold apolloniusRay
  rw [Complex.exp_add]
  rw [Complex.exp_neg]
  calc
    (Complex.exp (ξ : ℂ))⁻¹ *
        (Complex.exp (ξ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        ((Complex.exp (ξ : ℂ))⁻¹ * Complex.exp (ξ : ℂ)) *
          Complex.exp (Complex.I * (θ : ℂ)) := by ring
    _ = Complex.exp (Complex.I * (θ : ℂ)) := by
      rw [inv_mul_cancel₀ (Complex.exp_ne_zero (ξ : ℂ)), one_mul]

/-- 🏆 THEOREM 2 (Signature Quotient as Hyperbolic Tangent):
    In natural coordinates, the projective invariant $\mathcal{Q}$ is strictly $\tanh(\xi)$. -/
theorem projective_signature_eq_tanh (ξ θ : ℝ) :
    projectiveSignatureQuotient (apolloniusRay ξ θ) = Real.tanh ξ := by
  unfold projectiveSignatureQuotient apolloniusRay
  dsimp
  have h_z0 : normSq (Complex.exp ((ξ : ℂ) + Complex.I * (θ : ℂ))) = Real.exp (2 * ξ) :=
    apollonius_ray_z0_normSq ξ θ
  have h_z1 : normSq (1 : ℂ) = 1 := by simp only [map_one]
  rw [h_z0, h_z1]
  have h_den_pos : 0 < Real.exp (2 * ξ) + 1 := by positivity
  rw [Real.tanh_eq]
  have h_exp2 : Real.exp (2 * ξ) = (Real.exp ξ) ^ 2 := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have h_exp_neg : Real.exp (-ξ) = (Real.exp ξ)⁻¹ := Real.exp_neg ξ
  have h_pos : 0 < Real.exp ξ := Real.exp_pos ξ
  rw [h_exp_neg]
  have h_num : Real.exp ξ - (Real.exp ξ)⁻¹ = (Real.exp (2 * ξ) - 1) / Real.exp ξ := by
    rw [h_exp2]
    field_simp
  have h_den : Real.exp ξ + (Real.exp ξ)⁻¹ = (Real.exp (2 * ξ) + 1) / Real.exp ξ := by
    rw [h_exp2]
    field_simp
  rw [h_num, h_den]
  have h_ne : Real.exp ξ ≠ 0 := ne_of_gt h_pos
  field_simp [h_ne]

/-!
### 2. Projective Equator & Duality Involution
-/

/-- 🏆 THEOREM 3 (Projective Equator Equivalence):
    The projective signature vanishes $\mathcal{Q} = 0$ for the zero-scale equator $\xi = 0$. -/
theorem projective_equator_zero_scale (θ : ℝ) :
    projectiveSignatureQuotient (apolloniusRay 0 θ) = 0 := by
  rw [projective_signature_eq_tanh, Real.tanh_zero]

/-- 🏆 THEOREM 4 (Projective Inversion Duality):
    Swapping homogeneous coordinates $[Z_0 : Z_1] \mapsto [Z_1 : Z_0]$ negates the projective signature:
    $\mathcal{Q}([Z_1 : Z_0]) = -\mathcal{Q}([Z_0 : Z_1])$. -/
theorem projective_inversion_signature_neg (Z : ℂ × ℂ) :
    projectiveSignatureQuotient (Z.2, Z.1) = - projectiveSignatureQuotient Z := by
  unfold projectiveSignatureQuotient
  dsimp
  have h_add_comm : normSq Z.2 + normSq Z.1 = normSq Z.1 + normSq Z.2 := add_comm _ _
  rw [h_add_comm]
  ring

/-!
### 3. Master Capstone: Apollonian Projective Synthesis
-/

/-- 🏆 GRAND CAPSTONE: Complete synthesis of the natural projective coordinates on $\mathbb{CP}^1$,
    hyperbolic signature quotient $\tanh(\xi)$, zero-scale equator invariance, and duality involution -/
theorem grand_apollonius_natural_projective_synthesis (ξ θ : ℝ) :
    (normSq (apolloniusRay ξ θ).1 = Real.exp (2 * ξ)) ∧
    (projectiveSignatureQuotient (apolloniusRay ξ θ) = Real.tanh ξ) ∧
    (projectiveSignatureQuotient (apolloniusRay 0 θ) = 0) ∧
    (projectiveSignatureQuotient ((apolloniusRay ξ θ).2, (apolloniusRay ξ θ).1) = - Real.tanh ξ) := by
  have h1 := apollonius_ray_z0_normSq ξ θ
  have h2 := projective_signature_eq_tanh ξ θ
  have h3 := projective_equator_zero_scale θ
  have h_inv := projective_inversion_signature_neg (apolloniusRay ξ θ)
  refine ⟨h1, h2, h3, ?_⟩
  rw [h_inv, h2]

end
end InfoGeometry.Projective.ApolloniusNatural
