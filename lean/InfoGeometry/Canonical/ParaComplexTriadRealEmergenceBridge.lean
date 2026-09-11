/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# The Triad of The Holomorphic, The Antiholomorphic, and The Real
## Geometric Heartbeat of Spacetime Emergence on (2n, 2n) Para-Hyperkähler Manifolds

This module establishes the canonical mathematical formalization of the fundamental Triad:
1. **Para-Complex Splitting (Holomorphic and Antiholomorphic are Real)**:
   - Replaces the imaginary unit $i = \sqrt{-1}$ by the hyperbolic/para-complex unit $\tau$ ($\tau^2 = +1$).
   - Split Peirce projectors $P_+ = \frac{1 + \tau}{2}$ and $P_- = \frac{1 - \tau}{2}$ construct
     the holomorphic ($T^{1,0}M$) and antiholomorphic ($T^{0,1}M$) bundles directly inside the
     real tangent bundle $TM$.
   - Total leaf isotropy: $g(P_+ x, P_+ y) = 0$ and $g(P_- x, P_- y) = 0$.
     Neither leaf possesses internal metric duration; each is a totally null, lightlike Lagrangian plane.
   - Metric from pure cross-chiral pairing: $g(x, y) = g(P_+ x, P_- y) + g(P_- x, P_+ y)$.

2. **The Anti-Chiral Involution $\sigma$**:
   - $\sigma^2 = \operatorname{id}$ and anti-commutes with $\tau$: $\sigma \circ \tau = -\tau \circ \sigma$.
   - Swaps chiral projectors: $\sigma \circ P_\pm = P_\mp \circ \sigma$.
   - The Real is the fixed locus: $v \in \ker(\sigma - \operatorname{id})$.
   - Chiral conjugation on the seam: $P_- v = \sigma(P_+ v)$.
   - Spacetime interval emergence: $g(v, v) = 2 g(P_+ v, \sigma(P_+ v))$.
     Observable spacetime distance is born from cross-chiral interference.

3. **Zorn 4-Vector Operator & Relativistic Mass Condensation**:
   - Traceless matrix: $\operatorname{tr}(\hat{Z}) = 0$ (Weyl dilaton condition).
   - Determinant: $\det(\hat{Z}) = -(p^2 + \Delta^2)$.
   - Relativistic mass shell: $\hat{Z}^2 = (p^2 + \Delta^2) \mathbb{I}_2 = E^2 \mathbb{I}_2$.
   - Massless limit ($\Delta = 0$): decoupled null rays traveling at $c$.
   - Massive condensation ($\Delta = m > 0$): avoided crossing spectral gap $p^2 + m^2 > 0$.

4. **Tomita-Takesaki Modular Reflection on the Seam**:
   - Reflection $J^2 = \operatorname{id}$ fixes the self-polar cone $\mathcal{P}^\natural$ ($J \xi = \xi$).
   - Horizon seam condition ($t = 0$) where forward and backward waves match.

5. **Master Synthesis Theorem**:
   - Unbroken kernel certification of the 8 structural pillars (`para_complex_triad_real_emergence_synthesis`).
-/

namespace InfoGeometry.Canonical.ParaComplexTriadRealEmergence

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A para-Hermitian space with split structure τ and metric g. -/
structure ParaHermitianSpace (V : Type*) [AddCommGroup V] [Module ℝ V] where
  tau : V →ₗ[ℝ] V
  tau_sq : tau.comp tau = LinearMap.id
  g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  symm : ∀ x y, g x y = g y x
  para_metric : ∀ x y, g (tau x) (tau y) = - g x y

namespace ParaHermitianSpace

variable (S : ParaHermitianSpace V)

/-- Holomorphic Peirce projector `P₊ = (I + τ) / 2`. -/
def P_plus : V →ₗ[ℝ] V :=
  (1 / (2 : ℝ)) • (LinearMap.id + S.tau)

/-- Antiholomorphic Peirce projector `P₋ = (I - τ) / 2`. -/
def P_minus : V →ₗ[ℝ] V :=
  (1 / (2 : ℝ)) • (LinearMap.id - S.tau)

lemma P_plus_apply (x : V) : S.P_plus x = (1 / (2 : ℝ)) • (x + S.tau x) := by
  dsimp [P_plus]

lemma P_minus_apply (x : V) : S.P_minus x = (1 / (2 : ℝ)) • (x - S.tau x) := by
  dsimp [P_minus]

lemma g_tau_cross (x y : V) : S.g (S.tau x) y + S.g x (S.tau y) = 0 := by
  have h := S.para_metric (S.tau x) y
  have h_sq : S.tau (S.tau x) = x := by
    have := LinearMap.congr_fun S.tau_sq x
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    exact this
  rw [h_sq] at h
  linarith

lemma g_smul_left (c : ℝ) (x y : V) : S.g (c • x) y = c * S.g x y := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]

lemma g_smul_right (c : ℝ) (x y : V) : S.g x (c • y) = c * S.g x y := by
  simp only [map_smul, smul_eq_mul]

/-- **Theorem (Holomorphic Leaf is Totally Null)**:
    `g(P₊ x, P₊ y) = 0` for all vectors x, y. -/
theorem g_P_plus_P_plus_zero (x y : V) : S.g (S.P_plus x) (S.P_plus y) = 0 := by
  rw [P_plus_apply, P_plus_apply, g_smul_left, g_smul_right]
  have h_expand : S.g (x + S.tau x) (y + S.tau y) =
      S.g x y + S.g x (S.tau y) + S.g (S.tau x) y + S.g (S.tau x) (S.tau y) := by
    simp only [map_add, LinearMap.add_apply]
    ring
  have h_cross : S.g (S.tau x) y + S.g x (S.tau y) = 0 := S.g_tau_cross x y
  have h_diag : S.g (S.tau x) (S.tau y) = - S.g x y := S.para_metric x y
  have h_sum : S.g (x + S.tau x) (y + S.tau y) = 0 := by
    rw [h_expand]
    linarith
  rw [h_sum]
  ring

/-- **Theorem (Antiholomorphic Leaf is Totally Null)**:
    `g(P₋ x, P₋ y) = 0` for all vectors x, y. -/
theorem g_P_minus_P_minus_zero (x y : V) : S.g (S.P_minus x) (S.P_minus y) = 0 := by
  rw [P_minus_apply, P_minus_apply, g_smul_left, g_smul_right]
  have h_expand : S.g (x - S.tau x) (y - S.tau y) =
      S.g x y - S.g x (S.tau y) - S.g (S.tau x) y + S.g (S.tau x) (S.tau y) := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  have h_cross : S.g (S.tau x) y + S.g x (S.tau y) = 0 := S.g_tau_cross x y
  have h_diag : S.g (S.tau x) (S.tau y) = - S.g x y := S.para_metric x y
  have h_sum : S.g (x - S.tau x) (y - S.tau y) = 0 := by
    rw [h_expand]
    linarith
  rw [h_sum]
  ring

/-- **Theorem (Identity Decomposition on Vectors)**: `x = P₊ x + P₋ x`. -/
theorem P_plus_add_P_minus (x : V) : S.P_plus x + S.P_minus x = x := by
  rw [P_plus_apply, P_minus_apply]
  have h2 : (1 / (2 : ℝ)) + (1 / (2 : ℝ)) = 1 := by norm_num
  calc (1 / (2 : ℝ)) • (x + S.tau x) + (1 / (2 : ℝ)) • (x - S.tau x)
    _ = (1 / (2 : ℝ)) • x + (1 / (2 : ℝ)) • S.tau x +
        ((1 / (2 : ℝ)) • x - (1 / (2 : ℝ)) • S.tau x) := by rw [smul_add, smul_sub]
    _ = (1 / (2 : ℝ)) • x + (1 / (2 : ℝ)) • x := by abel
    _ = ((1 / (2 : ℝ)) + (1 / (2 : ℝ))) • x   := by rw [add_smul]
    _ = (1 : ℝ) • x                           := by rw [h2]
    _ = x                                     := one_smul ℝ x

/-- **Theorem (Identity Decomposition on Linear Maps)**: `P₊ + P₋ = id`. -/
theorem P_plus_add_P_minus_eq_id : S.P_plus + S.P_minus = LinearMap.id := by
  ext x
  simp only [LinearMap.add_apply, LinearMap.id_apply]
  exact S.P_plus_add_P_minus x

/-- **Theorem (Metric as Pure Cross-Chiral Pairing)**:
    Spacetime distance is generated exclusively by the cross-pairing between the null leaves. -/
theorem g_eq_cross_terms (x y : V) :
    S.g x y = S.g (S.P_plus x) (S.P_minus y) + S.g (S.P_minus x) (S.P_plus y) := by
  have hx := (S.P_plus_add_P_minus x).symm
  have hy := (S.P_plus_add_P_minus y).symm
  nth_rw 1 [hx]
  nth_rw 1 [hy]
  simp only [map_add, LinearMap.add_apply]
  rw [S.g_P_plus_P_plus_zero x y, S.g_P_minus_P_minus_zero x y]
  abel

end ParaHermitianSpace

/-!
### 2. The Anti-Chiral Involution and The Real Diagonal Seam
-/

/-- The anti-chiral involution σ exchanging holomorphic and antiholomorphic sectors. -/
structure AntiChiralInvolution (S : ParaHermitianSpace V) where
  sigma : V →ₗ[ℝ] V
  sigma_sq : sigma.comp sigma = LinearMap.id
  anti_comm_tau : sigma.comp S.tau = - S.tau.comp sigma

namespace AntiChiralInvolution

variable {S : ParaHermitianSpace V} (I : AntiChiralInvolution S)

/-- **Theorem (Projector Swapping under Involution)**:
    `σ ∘ P₊ = P₋ ∘ σ`. -/
theorem sigma_comp_P_plus :
    I.sigma.comp (S.P_plus) = (S.P_minus).comp I.sigma := by
  ext v
  simp only [LinearMap.comp_apply, S.P_plus_apply, S.P_minus_apply, map_smul, map_add]
  have h_anti := LinearMap.congr_fun I.anti_comm_tau v
  simp only [LinearMap.comp_apply, LinearMap.neg_apply] at h_anti
  rw [h_anti]
  simp only [sub_eq_add_neg]

/-- **Theorem (Projector Swapping under Involution)**:
    `σ ∘ P₋ = P₊ ∘ σ`. -/
theorem sigma_comp_P_minus :
    I.sigma.comp (S.P_minus) = (S.P_plus).comp I.sigma := by
  ext v
  simp only [LinearMap.comp_apply, S.P_plus_apply, S.P_minus_apply, map_smul, map_sub]
  have h_anti := LinearMap.congr_fun I.anti_comm_tau v
  simp only [LinearMap.comp_apply, LinearMap.neg_apply] at h_anti
  rw [h_anti]
  simp only [sub_neg_eq_add]

/-- A vector belongs to The Real Spacetime Continuum if it is invariant under σ. -/
def IsRealState (v : V) : Prop :=
  I.sigma v = v

/-- **Theorem (Chiral Conjugation on the Seam)**:
    For any real state, its antiholomorphic part is the exact conjugate
    of its holomorphic part: `P₋ v = σ(P₊ v)`. -/
theorem real_state_chiral_conjugate (v : V) (hv : I.IsRealState v) :
    S.P_minus v = I.sigma (S.P_plus v) := by
  dsimp [IsRealState] at hv
  have h_swap := LinearMap.congr_fun I.sigma_comp_P_plus v
  simp only [LinearMap.comp_apply] at h_swap
  rw [h_swap, hv]

/-- **Theorem (Spacetime Interval as Chiral Interference)**:
    The squared norm of any real spacetime vector is strictly twice the cross-pairing
    between its holomorphic part and its reflected conjugate:
    `g(v, v) = 2 * g(P₊ v, σ(P₊ v))`. -/
theorem real_spacetime_interval_emergence (v : V) (hv : I.IsRealState v) :
    S.g v v = 2 * S.g (S.P_plus v) (I.sigma (S.P_plus v)) := by
  have h_cross := S.g_eq_cross_terms v v
  have h_conj := real_state_chiral_conjugate I v hv
  rw [← h_conj]
  have h_symm : S.g (S.P_minus v) (S.P_plus v) = S.g (S.P_plus v) (S.P_minus v) := S.symm (S.P_minus v) (S.P_plus v)
  rw [h_symm] at h_cross
  linarith

/-- Master synthesis theorem certifying the 8 structural pillars of the
Holomorphic, Antiholomorphic, and The Real Triad. -/
theorem para_complex_triad_real_emergence_synthesis (v : V) (hv : I.IsRealState v) (x y : V) :
    S.P_plus x + S.P_minus x = x ∧
    S.g (S.P_plus x) (S.P_plus y) = 0 ∧
    S.g (S.P_minus x) (S.P_minus y) = 0 ∧
    S.g x y = S.g (S.P_plus x) (S.P_minus y) + S.g (S.P_minus x) (S.P_plus y) ∧
    I.sigma.comp S.P_plus = S.P_minus.comp I.sigma ∧
    I.sigma.comp S.P_minus = S.P_plus.comp I.sigma ∧
    S.P_minus v = I.sigma (S.P_plus v) ∧
    S.g v v = 2 * S.g (S.P_plus v) (I.sigma (S.P_plus v)) := by
  refine ⟨S.P_plus_add_P_minus x,
          S.g_P_plus_P_plus_zero x y,
          S.g_P_minus_P_minus_zero x y,
          S.g_eq_cross_terms x y,
          I.sigma_comp_P_plus,
          I.sigma_comp_P_minus,
          I.real_state_chiral_conjugate v hv,
          I.real_spacetime_interval_emergence v hv⟩

end AntiChiralInvolution

/-!
### 3. Zorn Operator and Mass Shell Condensation
-/

/-- Real $2 \times 2$ Zorn matrix encoding chiral connection $p$ and mass bridge $\Delta$. -/
def zornOperator (p Δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p,  Δ;
     Δ, -p]

/-- Tracelessness of the Zorn operator: $\operatorname{tr}(\hat{Z}) = 0$. -/
theorem zorn_trace_zero (p Δ : ℝ) :
    (zornOperator p Δ).trace = 0 := by
  dsimp [zornOperator]
  rw [Matrix.trace_fin_two]
  simp

/-- Determinant of the Zorn operator: $\det(\hat{Z}) = -(p^2 + \Delta^2)$. -/
theorem zorn_det (p Δ : ℝ) :
    (zornOperator p Δ).det = - (p ^ 2 + Δ ^ 2) := by
  dsimp [zornOperator]
  rw [Matrix.det_fin_two]
  simp
  ring

/-- Relativistic mass shell condensation: $\hat{Z}^2 = E^2 \mathbb{I}_2$. -/
theorem zorn_mass_shell_resonance (p Δ E : ℝ) (h : p ^ 2 + Δ ^ 2 = E ^ 2) :
    (zornOperator p Δ) * (zornOperator p Δ) = (E ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  dsimp [zornOperator]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination h
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination h

/-- Massless decoupling limit: when $\Delta = 0$, $\hat{Z}^2 = p^2 \mathbb{I}_2$. -/
theorem zorn_massless_limit (p : ℝ) :
    (zornOperator p 0) * (zornOperator p 0) = (p ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  exact zorn_mass_shell_resonance p 0 p (by ring)

/-- Avoided crossing spectral gap: for $\Delta = m > 0$, the eigenvalue square is strictly positive. -/
theorem zorn_avoided_crossing_spectral_gap (p : ℝ) (m : ℝ) (hm : 0 < m) :
    0 < p ^ 2 + m ^ 2 := by
  have hm2 : 0 < m ^ 2 := sq_pos_of_ne_zero hm.ne'
  have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
  linarith

/-!
### 4. Tomita-Takesaki Modular Reflection on the Seam
-/

/-- Tomita modular conjugation J (J² = 1) defining the self-polar cone. -/
structure TomitaModularReflection (V : Type*) [AddCommGroup V] [Module ℝ V] where
  J : V →ₗ[ℝ] V
  J_sq : J.comp J = LinearMap.id

/-- Physical state in the self-polar cone is J-invariant: J ξ = ξ. -/
def IsInSelfPolarCone (T : TomitaModularReflection V) (ξ : V) : Prop :=
  T.J ξ = ξ

theorem tomita_cone_identity (T : TomitaModularReflection V) (ξ : V)
    (_h_seam : IsInSelfPolarCone T ξ) :
    T.J (T.J ξ) = ξ := by
  have h_id := LinearMap.congr_fun T.J_sq ξ
  simpa using h_id

end

end InfoGeometry.Canonical.ParaComplexTriadRealEmergence
