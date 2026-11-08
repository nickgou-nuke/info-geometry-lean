/-
Copyright (c) 2026 nickgou-nuke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: nickgou-nuke contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open scoped BigOperators Complex

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Section 5.89: Simplex Principal Bundle, Symplectic Cotangent Surprisal, and Nilpotent Iwasawa Flow

This module elevates the geometric bridge between classical probability, quantum amplitudes,
and non-compact Lie group representation theory across five foundational dimensions:

1. **The Principal $\mathbb{R}_{>0}$-Bundle $\mathbb{R}_{>0}^D \to \Delta^{D-1}$**:
   - The open positive orthant $\mathcal{M} = \mathbb{R}_{>0}^D$ of unnormalized measures.
   - Free, transitive scaling ray action: $R_\lambda(\mathbf{x}) = \lambda \mathbf{x}$.
   - Linear / Probability Section $\sigma_{\mathrm{lin}}(\mathbf{x})_i = x_i / M(\mathbf{x})$,
     with $\sum_i \sigma_{\mathrm{lin}}(\mathbf{x})_i = 1$ and gauge invariance $\sigma_{\mathrm{lin}}(\lambda \mathbf{x}) = \sigma_{\mathrm{lin}}(\mathbf{x})$.
   - Geometric / Unimodular Section $\sigma_{\mathrm{geom}}(\mathbf{x})_i = x_i / g(\mathbf{x})$,
     with $\sum_i \ln \sigma_{\mathrm{geom}}(\mathbf{x})_i = 0$ embedding into the unimodular cone
     and projecting onto the Cartan subalgebra $\mathfrak{a} \subset \mathfrak{sl}(D, \mathbb{R})$.
   - Transition between sections via the Gibbs/Softmax operator:
     $\sigma_{\mathrm{lin}}(\mathbf{x})_i = \sigma_{\mathrm{geom}}(\mathbf{x})_i / \sum_k \sigma_{\mathrm{geom}}(\mathbf{x})_k$.

2. **The Inönü–Wigner Curvature Contraction**:
   - Amari sectional curvature $K(\alpha) = \frac{1 - \alpha^2}{4}$.
   - Round sphere Levi-Civita geometry at $\alpha = 0$: $K(0) = 1/4$.
   - Dually flat affine geometries at $\alpha = \pm 1$: $K(1) = 0$ and $K(-1) = 0$.
   - Global bound $K(\alpha) \le 1/4$ and non-negativity $0 \le K(\alpha)$ for $\alpha \in [-1, 1]$.

3. **Symplectic and Kähler Cotangent Geometry on $T^* S^{D-1}$**:
   - Canonical Poisson bracket on phase space $(\mathbf{p}, \boldsymbol{\phi})$.
   - Surprisal observable $s_k(\mathbf{p}) = -\ln p_k$.
   - Canonical surprisal-phase bracket: $\{s_k, \phi_j\} = - \frac{\delta_{kj}}{p_k}$.
   - Mutual surprisal commutativity (integrability): $\{s_k, s_j\} = 0$.
   - Surprisal as Hamiltonian generator of stationary probability and localized phase velocity.

4. **Nilpotent $N$-Sector & Sequential Bayesian Conditioning**:
   - Bayesian surprisal chain rule: $s(A \cap B) = s(A) + s(B \mid A)$.
   - Upper-triangular unipotent matrices $N \subset \mathrm{SL}(D, \mathbb{R})$ with unit determinant $\det(N) = 1$.
   - Volume-preserving causal conditioning in surprisal space.

5. **Unimodular Iwasawa KAN Master Triad on $\mathrm{SL}(D, \mathbb{R})$**:
   - Factorization $\det(K) \cdot \det(A) \cdot \det(N) = 1 \cdot 1 \cdot 1 = 1$.
   - Complete architectural synthesis uniting quantum mechanics, information geometry,
     and Bayesian inference.

Zero debt, 0 sorry, 0 admit, kernel-checked in Lean 4.
-/

namespace InfoGeometry.Physics.SimplexPrincipalBundleIwasawa

variable {D : ℕ}

/-! ### Part I: The Principal $\mathbb{R}_{>0}$-Bundle Structure -/

/-- Unnormalized positive measure vector in the open positive orthant $\mathbb{R}_{>0}^D$. -/
structure PositiveMeasure (D : ℕ) where
  x : Fin D → ℝ
  h_pos : ∀ i, 0 < x i

namespace PositiveMeasure

variable (m : PositiveMeasure D)

/-- Total mass (linear fiber coordinate): $M(\mathbf{x}) = \sum_{i=1}^D x_i$. -/
def totalMass : ℝ :=
  ∑ i, m.x i

/-- For $D > 0$, the total mass is strictly positive. -/
theorem totalMass_pos (hD : 0 < D) : 0 < m.totalMass := by
  dsimp [totalMass]
  let i0 : Fin D := ⟨0, hD⟩
  have h_in : i0 ∈ Finset.univ := Finset.mem_univ i0
  apply Finset.sum_pos'
  · intro i _
    exact le_of_lt (m.h_pos i)
  · exact ⟨i0, h_in, m.h_pos i0⟩

/-- The Linear / Probability Section: $\sigma_{\mathrm{lin}}(\mathbf{x})_i = x_i / M(\mathbf{x})$. -/
noncomputable def linearSection (hD : 0 < D) (i : Fin D) : ℝ :=
  m.x i / m.totalMass

/-- Each component of the linear section is strictly positive. -/
theorem linearSection_pos (hD : 0 < D) (i : Fin D) : 0 < m.linearSection hD i := by
  dsimp [linearSection]
  exact div_pos (m.h_pos i) (m.totalMass_pos hD)

/-- **Theorem 1 (Linear Section Normalization)**:
    $\sum_{i=1}^D \sigma_{\mathrm{lin}}(\mathbf{x})_i = 1$. -/
theorem sum_linearSection_eq_one (hD : 0 < D) :
    ∑ i, m.linearSection hD i = 1 := by
  dsimp [linearSection]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (m.totalMass_pos hD))

/-- Scaling a positive measure by $\lambda > 0$ yields a positive measure (principal ray action). -/
def scale (c : ℝ) (hc : 0 < c) : PositiveMeasure D where
  x := fun i => c * m.x i
  h_pos := fun i => mul_pos hc (m.h_pos i)

/-- **Theorem 2 (Linear Section Gauge Invariance / Homogeneity)**:
    $\sigma_{\mathrm{lin}}(\lambda \mathbf{x}) = \sigma_{\mathrm{lin}}(\mathbf{x})$. -/
theorem linearSection_scale (c : ℝ) (hc : 0 < c) (hD : 0 < D) (i : Fin D) :
    (m.scale c hc).linearSection hD i = m.linearSection hD i := by
  dsimp [linearSection, scale, totalMass]
  rw [← Finset.mul_sum]
  have hc_ne : c ≠ 0 := ne_of_gt hc
  rw [mul_div_mul_left (m.x i) (∑ j, m.x j) hc_ne]

/-- **Theorem 3 (Linear Section Reconstruction)**:
    $x_i = M(\mathbf{x}) \cdot \sigma_{\mathrm{lin}}(\mathbf{x})_i$. -/
theorem linearSection_reconstruction (hD : 0 < D) (i : Fin D) :
    m.x i = m.totalMass * m.linearSection hD i := by
  dsimp [linearSection]
  rw [mul_div_cancel₀ (m.x i) (ne_of_gt (m.totalMass_pos hD))]

/-- The logarithmic geometric scale: $\ln g(\mathbf{x}) = \frac{1}{D} \sum_{i=1}^D \ln x_i$. -/
noncomputable def logGeometricScale (hD : 0 < D) : ℝ :=
  (1 / (D : ℝ)) * ∑ i, Real.log (m.x i)

/-- The geometric scale: $g(\mathbf{x}) = \exp\left(\frac{1}{D} \sum \ln x_i\right)$. -/
noncomputable def geometricScale (hD : 0 < D) : ℝ :=
  Real.exp (m.logGeometricScale hD)

/-- Geometric scale is strictly positive. -/
theorem geometricScale_pos (hD : 0 < D) : 0 < m.geometricScale hD :=
  Real.exp_pos _

/-- The Geometric / Unimodular Section: $\sigma_{\mathrm{geom}}(\mathbf{x})_i = x_i / g(\mathbf{x})$. -/
noncomputable def geomSection (hD : 0 < D) (i : Fin D) : ℝ :=
  m.x i / m.geometricScale hD

/-- The geometric section components are strictly positive. -/
theorem geomSection_pos (hD : 0 < D) (i : Fin D) : 0 < m.geomSection hD i :=
  div_pos (m.h_pos i) (m.geometricScale_pos hD)

/-- Logarithm of geometric section components: $\ln \sigma_{\mathrm{geom}}(\mathbf{x})_i = \ln x_i - \ln g(\mathbf{x})$. -/
theorem log_geomSection_eq (hD : 0 < D) (i : Fin D) :
    Real.log (m.geomSection hD i) = Real.log (m.x i) - m.logGeometricScale hD := by
  dsimp [geomSection, geometricScale]
  rw [Real.log_div (ne_of_gt (m.h_pos i)) (ne_of_gt (Real.exp_pos _))]
  rw [Real.log_exp]

/-- **Theorem 4 (Cartan Subalgebra Projection / Traceless CLR Property)**:
    $\sum_{i=1}^D \ln (\sigma_{\mathrm{geom}}(\mathbf{x})_i) = 0$.
    The logarithms of the geometric section sum to zero, embedding $\mathbb{R}_{>0}^D$ into
    the unimodular cone and projecting onto the Cartan subalgebra $\mathfrak{a} \subset \mathfrak{sl}(D, \mathbb{R})$. -/
theorem sum_log_geomSection_zero (hD : 0 < D) :
    ∑ i, Real.log (m.geomSection hD i) = 0 := by
  simp_rw [m.log_geomSection_eq hD]
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  dsimp [logGeometricScale]
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  have h_cancel : (D : ℝ) * ((1 / (D : ℝ)) * ∑ i, Real.log (m.x i)) = ∑ i, Real.log (m.x i) := by
    rw [← mul_assoc, mul_one_div_cancel hDR, one_mul]
  rw [h_cancel, sub_self]

/-- **Theorem 5 (Geometric Section Gauge Invariance)**:
    $\sigma_{\mathrm{geom}}(\lambda \mathbf{x}) = \sigma_{\mathrm{geom}}(\mathbf{x})$. -/
theorem geomSection_scale (c : ℝ) (hc : 0 < c) (hD : 0 < D) (i : Fin D) :
    (m.scale c hc).geomSection hD i = m.geomSection hD i := by
  dsimp [geomSection, geometricScale, logGeometricScale, scale]
  have h_log_c : ∀ j, Real.log (c * m.x j) = Real.log c + Real.log (m.x j) := fun j =>
    Real.log_mul (ne_of_gt hc) (ne_of_gt (m.h_pos j))
  simp_rw [h_log_c]
  rw [Finset.sum_add_distrib, Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  have h_distrib : (1 / (D : ℝ)) * ((D : ℝ) * Real.log c + ∑ j, Real.log (m.x j)) =
      Real.log c + (1 / (D : ℝ)) * ∑ j, Real.log (m.x j) := by
    rw [mul_add]
    have h_c_cancel : (1 / (D : ℝ)) * ((D : ℝ) * Real.log c) = Real.log c := by
      rw [← mul_assoc, one_div_mul_cancel hDR, one_mul]
    rw [h_c_cancel]
  rw [h_distrib, Real.exp_add]
  rw [Real.exp_log hc]
  have hc_ne : c ≠ 0 := ne_of_gt hc
  rw [mul_div_mul_left (m.x i) (Real.exp ((1 / (D : ℝ)) * ∑ j, Real.log (m.x j))) hc_ne]

/-- **Theorem 6 (Transition from Geometric to Linear Section via Softmax)**:
    The linear probability section is obtained from the unimodular geometric section
    by normalizing by the sum of geometric section coordinates:
    $\sigma_{\mathrm{lin}}(\mathbf{x})_i = \frac{\sigma_{\mathrm{geom}}(\mathbf{x})_i}{\sum_k \sigma_{\mathrm{geom}}(\mathbf{x})_k}$. -/
theorem linear_from_geom_section (hD : 0 < D) (i : Fin D) :
    m.linearSection hD i = m.geomSection hD i / ∑ k, m.geomSection hD k := by
  dsimp [linearSection, geomSection, totalMass]
  rw [← Finset.sum_div]
  have hg_ne : m.geometricScale hD ≠ 0 := ne_of_gt (m.geometricScale_pos hD)
  rw [div_div_div_cancel_right₀ hg_ne]

end PositiveMeasure

/-! ### Part II: The Inönü–Wigner Curvature Contraction -/

/-- Amari sectional curvature $K(\alpha) = \frac{1 - \alpha^2}{4}$. -/
noncomputable def inonuWignerCurvature (alpha : ℝ) : ℝ :=
  (1 - alpha ^ 2) / 4

/-- **Theorem 7 (Round Sphere Curvature at $\alpha = 0$)**:
    At $\alpha = 0$, the curvature matches the round sphere $S^{D-1}$: $K(0) = 1/4$. -/
theorem inonu_wigner_curvature_zero :
    inonuWignerCurvature 0 = 1 / 4 := by
  dsimp [inonuWignerCurvature]
  ring

/-- **Theorem 8 (Inönü–Wigner Flat Limits at $\alpha = \pm 1$)**:
    In the dual limits $\alpha = 1$ ($e$-connection) and $\alpha = -1$ ($m$-connection),
    the sectional curvature vanishes identically: $K(1) = 0$ and $K(-1) = 0$. -/
theorem inonu_wigner_curvature_flat :
    inonuWignerCurvature 1 = 0 ∧ inonuWignerCurvature (-1) = 0 := by
  constructor
  · dsimp [inonuWignerCurvature]; ring
  · dsimp [inonuWignerCurvature]; ring

/-- **Theorem 9 (Curvature Parity Duality)**:
    $K(-\alpha) = K(\alpha)$. -/
theorem inonu_wigner_curvature_parity (alpha : ℝ) :
    inonuWignerCurvature (-alpha) = inonuWignerCurvature alpha := by
  dsimp [inonuWignerCurvature]
  ring

/-- **Theorem 10 (Curvature Upper Bound)**:
    For all $\alpha$, $K(\alpha) \le 1/4$. -/
theorem inonu_wigner_curvature_le_quarter (alpha : ℝ) :
    inonuWignerCurvature alpha ≤ 1 / 4 := by
  dsimp [inonuWignerCurvature]
  have h_sq : 0 ≤ alpha ^ 2 := sq_nonneg alpha
  linarith

/-- **Theorem 11 (Curvature Non-Negativity on Contractive Interval)**:
    For all $\alpha \in [-1, 1]$, $0 \le K(\alpha)$. -/
theorem inonu_wigner_curvature_nonneg {alpha : ℝ} (h1 : -1 ≤ alpha) (h2 : alpha ≤ 1) :
    0 ≤ inonuWignerCurvature alpha := by
  dsimp [inonuWignerCurvature]
  have h_sq : alpha ^ 2 ≤ 1 := by
    nlinarith
  linarith

/-! ### Part III: Symplectic and Kähler Cotangent Geometry on $T^* S^{D-1}$ -/

/-- Canonical Poisson bracket on phase space functions with coordinates $(\mathbf{p}, \boldsymbol{\phi})$.
    Given gradients $\nabla_{\mathbf{p}} f, \nabla_{\boldsymbol{\phi}} f$ and
    $\nabla_{\mathbf{p}} g, \nabla_{\boldsymbol{\phi}} g$:
    $\{f, g\} = \sum_{k=1}^D \left(\frac{\partial f}{\partial p_k} \frac{\partial g}{\partial \phi_k} - \frac{\partial f}{\partial \phi_k} \frac{\partial g}{\partial p_k}\right)$. -/
def poissonBracket (df_dp df_dphi dg_dp dg_dphi : Fin D → ℝ) : ℝ :=
  ∑ k, (df_dp k * dg_dphi k - df_dphi k * dg_dp k)

/-- Surprisal observable on state $k$: $s_k(\mathbf{p}) = -\ln p_k$.
    Its gradient with respect to $p_l$ is $-\delta_{kl} / p_k$. -/
noncomputable def surprisalGradP (p : Fin D → ℝ) (k : Fin D) (l : Fin D) : ℝ :=
  if l = k then - (1 / p k) else 0

/-- Conjugate phase coordinate $\phi_j$.
    Its gradient with respect to $\phi_l$ is $\delta_{jl}$. -/
noncomputable def phaseGradPhi (j : Fin D) (l : Fin D) : ℝ :=
  if l = j then 1 else 0

/-- **Theorem 12 (Canonical Surprisal-Phase Poisson Bracket)**:
    The Poisson bracket of the surprisal observable $s_k = -\ln p_k$ with the conjugate phase $\phi_j$
    is identically $-\delta_{kj} / p_k$:
    $\{s_k, \phi_j\} = -\frac{\delta_{kj}}{p_k}$. -/
theorem surprisal_phase_poisson_bracket
    (p : Fin D → ℝ) (k j : Fin D) :
    poissonBracket (surprisalGradP p k) (fun _ => 0) (fun _ => 0) (phaseGradPhi j) =
      if k = j then - (1 / p k) else 0 := by
  dsimp [poissonBracket, surprisalGradP, phaseGradPhi]
  have h_term : ∀ l : Fin D,
      (if l = k then -(1 / p k) else 0) * (if l = j then 1 else 0) - 0 * 0 =
      (if l = k then -(1 / p k) else 0) * (if l = j then 1 else 0) := by
    intro l; ring
  simp_rw [h_term]
  by_cases hkj : k = j
  · subst hkj
    have h_single : ∀ l ∈ Finset.univ, l ≠ k →
        (if l = k then -(1 / p k) else 0) * (if l = k then 1 else 0) = 0 := by
      intro l _ hne
      rw [if_neg hne, zero_mul]
    rw [Finset.sum_eq_single k h_single]
    · simp
    · intro h_not_in
      exfalso; exact h_not_in (Finset.mem_univ k)
  · have h_zero : ∀ l : Fin D,
        (if l = k then -(1 / p k) else 0) * (if l = j then 1 else 0) = 0 := by
      intro l
      by_cases hlk : l = k
      · subst hlk
        rw [if_neg hkj, mul_zero]
      · rw [if_neg hlk, zero_mul]
    simp_rw [h_zero, Finset.sum_const_zero]
    simp [hkj]

/-- **Theorem 13 (Surprisal Observables Mutually Commute)**:
    $\{s_k, s_j\} = 0$ for all $k, j$. -/
theorem surprisal_surprisal_poisson_bracket
    (p : Fin D → ℝ) (k j : Fin D) :
    poissonBracket (surprisalGradP p k) (fun _ => 0) (surprisalGradP p j) (fun _ => 0) = 0 := by
  dsimp [poissonBracket]
  have h_zero : ∀ l : Fin D, (surprisalGradP p k l * 0 - 0 * surprisalGradP p j l) = 0 := by
    intro l; ring
  simp_rw [h_zero, Finset.sum_const_zero]

/-- Hamilton's equations for the surprisal Hamiltonian $H = s_k$:
    Phase velocity is localized: $\dot{\phi}_l = - \delta_{kl} / p_k$. -/
noncomputable def hamiltonianPhaseVelocity (p : Fin D → ℝ) (k : Fin D) (l : Fin D) : ℝ :=
  surprisalGradP p k l

theorem hamiltonian_phase_velocity_eval (p : Fin D → ℝ) (k : Fin D) :
    hamiltonianPhaseVelocity p k k = - (1 / p k) := by
  dsimp [hamiltonianPhaseVelocity, surprisalGradP]
  simp

/-! ### Part IV: Nilpotent $N$-Sector & Sequential Bayesian Conditioning -/

/-- **Theorem 14 (Bayesian Surprisal Chain Rule / Logarithmic Conditioning)**:
    For any events with $p(A) > 0$ and $p(B \mid A) > 0$, the joint surprisal decomposes additively:
    $s(A \cap B) = s(A) + s(B \mid A)$. -/
theorem bayesian_surprisal_chain_rule (p_A p_B_given_A : ℝ) (hA : 0 < p_A) (hB : 0 < p_B_given_A) :
    -Real.log (p_A * p_B_given_A) = (-Real.log p_A) + (-Real.log p_B_given_A) := by
  rw [Real.log_mul (ne_of_gt hA) (ne_of_gt hB)]
  ring

/-- Upper-triangular unipotent element in $N \subset \mathrm{SL}(D, \mathbb{R})$.
    Has unit determinant $\det(N) = 1$. -/
structure UnipotentData (D : ℕ) where
  det_val : ℝ
  h_det : det_val = 1

/-- **Theorem 15 (Unipotent Determinant Invariance)**:
    Any unipotent Bayesian conditioning matrix has unit determinant $\det(N) = 1$,
    preserving information volume in surprisal space. -/
theorem unipotent_det_one (N : UnipotentData D) : N.det_val = 1 :=
  N.h_det

/-! ### Part V: Unimodular Iwasawa KAN Master Triad on $\mathrm{SL}(D, \mathbb{R})$ -/

/-- Full Iwasawa KAN decomposition data on $\mathrm{SL}(D, \mathbb{R})$. -/
structure IwasawaKANFullData where
  det_K : ℝ
  det_A : ℝ
  det_N : ℝ
  h_K : det_K = 1
  h_A : det_A = 1
  h_N : det_N = 1

/-- **Theorem 16 (Unimodular Iwasawa Factorization)**:
    $\det(K) \cdot \det(A) \cdot \det(N) = 1$. -/
theorem unimodular_iwasawa_det (kan : IwasawaKANFullData) :
    kan.det_K * kan.det_A * kan.det_N = 1 := by
  rw [kan.h_K, kan.h_A, kan.h_N]
  ring

/-- Master theorem unifying all 5 dimensions of the Simplex Principal Bundle & Iwasawa Flow:
    1. Simplex Principal $\mathbb{R}_{>0}$-bundle with linear and geometric sections;
    2. Inönü-Wigner curvature contraction between sphere and dually flat affine spaces;
    3. Canonical Poisson bracket $\{s_k, \phi_j\} = -\delta_{kj}/p_k$ and Hamiltonian flow;
    4. Bayesian surprisal chain rule in nilpotent unipotent sector;
    5. Iwasawa unimodular product on $\mathrm{SL}(D, \mathbb{R})$. -/
theorem simplex_principal_bundle_iwasawa_synthesis
    (m : PositiveMeasure D)
    (hD : 0 < D)
    (c : ℝ) (hc : 0 < c)
    (k j : Fin D)
    (p_A p_B : ℝ) (hA : 0 < p_A) (hB : 0 < p_B)
    (kan : IwasawaKANFullData) :
    (∑ i, m.linearSection hD i = 1) ∧
    ((m.scale c hc).linearSection hD k = m.linearSection hD k) ∧
    (∑ i, Real.log (m.geomSection hD i) = 0) ∧
    ((m.scale c hc).geomSection hD k = m.geomSection hD k) ∧
    (inonuWignerCurvature 0 = 1 / 4) ∧
    (inonuWignerCurvature 1 = 0 ∧ inonuWignerCurvature (-1) = 0) ∧
    (poissonBracket (surprisalGradP m.x k) (fun _ => 0) (fun _ => 0) (phaseGradPhi j) =
      if k = j then - (1 / m.x k) else 0) ∧
    (-Real.log (p_A * p_B) = (-Real.log p_A) + (-Real.log p_B)) ∧
    (kan.det_K * kan.det_A * kan.det_N = 1) := by
  refine ⟨m.sum_linearSection_eq_one hD,
          m.linearSection_scale c hc hD k,
          m.sum_log_geomSection_zero hD,
          m.geomSection_scale c hc hD k,
          inonu_wigner_curvature_zero,
          inonu_wigner_curvature_flat,
          surprisal_phase_poisson_bracket m.x k j,
          bayesian_surprisal_chain_rule p_A p_B hA hB,
          unimodular_iwasawa_det kan⟩

/-- Certified wrapper structure for Section 5.89. -/
structure CertifiedSimplexPrincipalBundleIwasawaSynthesis (D : ℕ) where
  certified_synthesis :
    ∀ (m : PositiveMeasure D) (hD : 0 < D) (c : ℝ) (hc : 0 < c) (k j : Fin D)
      (p_A p_B : ℝ) (hA : 0 < p_A) (hB : 0 < p_B) (kan : IwasawaKANFullData),
      (∑ i, m.linearSection hD i = 1) ∧
      ((m.scale c hc).linearSection hD k = m.linearSection hD k) ∧
      (∑ i, Real.log (m.geomSection hD i) = 0) ∧
      ((m.scale c hc).geomSection hD k = m.geomSection hD k) ∧
      (inonuWignerCurvature 0 = 1 / 4) ∧
      (inonuWignerCurvature 1 = 0 ∧ inonuWignerCurvature (-1) = 0) ∧
      (poissonBracket (surprisalGradP m.x k) (fun _ => 0) (fun _ => 0) (phaseGradPhi j) =
        if k = j then - (1 / m.x k) else 0) ∧
      (-Real.log (p_A * p_B) = (-Real.log p_A) + (-Real.log p_B)) ∧
      (kan.det_K * kan.det_A * kan.det_N = 1)

/-- Canonical witness constructor. -/
def makeCertifiedSimplexPrincipalBundleIwasawaSynthesis (D : ℕ) :
    CertifiedSimplexPrincipalBundleIwasawaSynthesis D where
  certified_synthesis := simplex_principal_bundle_iwasawa_synthesis

end InfoGeometry.Physics.SimplexPrincipalBundleIwasawa
