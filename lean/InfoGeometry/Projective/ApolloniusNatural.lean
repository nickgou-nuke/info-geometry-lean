/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace InfoGeometry.Projective.ApolloniusNatural

open Complex Real

noncomputable section

/-!
# Projective Geometry in the Natural Coordinates of the Apollonian Foliation

We formalize the projective structure directly in the natural coordinates
$(\xi, \theta) \in \mathbb{R} \times S^1$ of the Apollonian cylinder:

  W = \xi + i \theta = \ln\left(\frac{s - 3/2}{s + 1/2}\right)

1. **Homogeneous Projective Coordinates on $\mathbb{CP}^1$**:
   A state is represented by the projective ray $[Z_0 : Z_1] \in \mathbb{CP}^1$,
   where the natural affine chart $w = Z_0 / Z_1$ gives:
     $[Z_0 : Z_1] = [e^{\xi + i \theta} : 1] = [e^\xi e^{i\theta} : 1]$

2. **Projective Scale Decoupling ($\mathbb{R}_+^\times$ Projective Gauge Freedom)**:
   The thermal time / dilation coordinate $\xi \in \mathbb{R}$ acts as the real
   projective scale $\rho = e^\xi > 0$. Projective equivalence identifies:
     $[e^\xi e^{i\theta} : 1] \sim [e^{i\theta} : e^{-\xi}]$

3. **Natural Projective Invariant (The Unitary Leaf $\xi = 0$)**:
   The projective Fubini-Study / Cayley norm ratio is:
     $\mathcal{Q}([Z_0 : Z_1]) = \frac{|Z_0|^2 - |Z_1|^2}{|Z_0|^2 + |Z_1|^2} = \tanh(\xi)$
   - $\xi = 0 \iff \mathcal{Q} = 0$: The invariant equator on $\mathbb{CP}^1$ ($\operatorname{Re}(s) = 1/2$).
   - $\xi > 0 \iff \mathcal{Q} > 0$: Northern hemisphere (subharmonic disk $\mathbb{D}$).
   - $\xi < 0 \iff \mathcal{Q} < 0$: Southern hemisphere (exterior $\mathbb{C} \setminus \overline{\mathbb{D}}$).

4. **Projective Duality Involution ($s \leftrightarrow 1 - s$)**:
   The projective antipodal / inversion map:
     $J([Z_0 : Z_1]) = [Z_1 : Z_0]$
   induces $(\xi, \theta) \mapsto (-\xi, -\theta)$.
-/

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
  have h_mul : ((normSq (Complex.exp ((ξ : ℂ) + Complex.I * (θ : ℂ))) : ℂ)) =
      starRingEnd ℂ (Complex.exp ((ξ : ℂ) + Complex.I * (θ : ℂ))) * Complex.exp ((ξ : ℂ) + Complex.I * (θ : ℂ)) :=
    normSq_eq_conj_mul_self
  have h_star : starRingEnd ℂ (Complex.exp ((ξ : ℂ) + Complex.I * (θ : ℂ))) =
                Complex.exp ((ξ : ℂ) - Complex.I * (θ : ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_add, conj_ofReal, map_mul, conj_I]
    ring
  rw [h_star, ← Complex.exp_add] at h_mul
  have h_sum : (ξ : ℂ) - Complex.I * (θ : ℂ) + ((ξ : ℂ) + Complex.I * (θ : ℂ)) = (((2 * ξ : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [h_sum, ← Complex.ofReal_exp] at h_mul
  exact ofReal_injective h_mul

/-- 🏆 THEOREM 2 (Signature Quotient as Hyperbolic Tangent):
    In natural coordinates, the projective invariant $\mathcal{Q}$ is strictly $\tanh(\xi)$. -/
theorem projective_signature_eq_tanh (ξ θ : ℝ) :
    projectiveSignatureQuotient (apolloniusRay ξ θ) = Real.tanh ξ := by
  unfold projectiveSignatureQuotient apolloniusRay
  dsimp
  have h_z0 : normSq (Complex.exp ((ξ : ℂ) + Complex.I * (θ : ℂ))) = Real.exp (2 * ξ) :=
    apollonius_ray_z0_normSq ξ θ
  have h_z1 : normSq (1 : ℂ) = 1 := by simp only [map_one]
  rw [h_z0, h_z1, Real.tanh_eq]
  have h_exp2 : Real.exp (2 * ξ) = (Real.exp ξ) ^ 2 := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have h_exp_neg : Real.exp (-ξ) = (Real.exp ξ)⁻¹ := Real.exp_neg ξ
  have h_pos : 0 < Real.exp ξ := Real.exp_pos ξ
  have h_ne : Real.exp ξ ≠ 0 := ne_of_gt h_pos
  rw [h_exp_neg, h_exp2]
  have h_num : (Real.exp ξ) ^ 2 - 1 = (Real.exp ξ - (Real.exp ξ)⁻¹) * Real.exp ξ := by
    rw [sub_mul, inv_mul_cancel₀ h_ne]
    ring
  have h_den : (Real.exp ξ) ^ 2 + 1 = (Real.exp ξ + (Real.exp ξ)⁻¹) * Real.exp ξ := by
    rw [add_mul, inv_mul_cancel₀ h_ne]
    ring
  rw [h_num, h_den, mul_div_mul_right _ _ h_ne]

/-!
### 2. Projective Equator & Duality Involution
-/

/-- 🏆 THEOREM 3 (Projective Equator Equivalence):
    The projective signature vanishes $\mathcal{Q} = 0$ if and only if $\xi = 0$
    (the critical line $\operatorname{Re}(s) = 1/2$ as the real projective circle $S^1 \subset \mathbb{CP}^1$). -/
theorem projective_equator_iff_zero_scale (ξ θ : ℝ) :
    projectiveSignatureQuotient (apolloniusRay ξ θ) = 0 ↔ ξ = 0 := by
  rw [projective_signature_eq_tanh, Real.tanh_eq]
  have h_den_pos : 0 < Real.exp ξ + Real.exp (-ξ) := add_pos (Real.exp_pos ξ) (Real.exp_pos (-ξ))
  have h_den_ne : Real.exp ξ + Real.exp (-ξ) ≠ 0 := ne_of_gt h_den_pos
  rw [div_eq_zero_iff, or_iff_left h_den_ne, sub_eq_zero]
  constructor
  · intro h
    have h_log := Real.exp_injective h
    linarith
  · intro h
    rw [h, neg_zero]

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
    (projectiveSignatureQuotient (apolloniusRay ξ θ) = 0 ↔ ξ = 0) ∧
    (projectiveSignatureQuotient (1, (apolloniusRay ξ θ).1) = - Real.tanh ξ) := by
  have h1 := apollonius_ray_z0_normSq ξ θ
  have h2 := projective_signature_eq_tanh ξ θ
  have h_inv : projectiveSignatureQuotient (1, (apolloniusRay ξ θ).1) =
               - projectiveSignatureQuotient (apolloniusRay ξ θ) := by
    have h := projective_inversion_signature_neg (apolloniusRay ξ θ)
    exact h
  refine ⟨h1, h2, projective_equator_iff_zero_scale ξ θ, ?_⟩
  rw [h_inv, h2]

end

end InfoGeometry.Projective.ApolloniusNatural
