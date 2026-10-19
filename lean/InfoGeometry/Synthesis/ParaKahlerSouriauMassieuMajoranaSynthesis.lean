/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import InfoGeometry.Analytic.LogSumExp
import InfoGeometry.Synthesis.TransactionalQueryKeyRoPEPhaseSpaceBridge

/-!
# Para-Kähler Potential, Homogeneous Majorana Klein Quadric, and Souriau–Massieu–Planck Free Entropy Synthesis

This module formalizes the four coupled pillars uniting neutral para-Kähler differential geometry,
homogeneous Majorana coordinates on the split carrier, and the Massieu–Planck–Souriau
thermodynamic potential of causal attention:

1. **Neutral Para-Kähler Carrier & Gauge Invariance of the Para-Kähler Potential**:
   - Defines the para-complex involution `paraComplexEndJ` ($J^2 = +\mathrm{id}$) and the neutral
     signature $(p,p)$ off-diagonal metric `paraKahlerNeutralMetric` on
     `(Fin p → ℝ) × (Fin p → ℝ)`.
   - Proves compatibility $g(JX, JY) = -g(X, Y)$, recovery of the canonical symplectic 2-form
     $\omega(X, Y) = g(JX, Y)$, and anti-invariance $\omega(JX, JY) = -\omega(X, Y)$
     (`paraKahlerCompatibility_and_involution`).
   - Defines the mixed cross-sheet difference operator `paraKahlerMixedVariation` and proves that
     gauge shifts $\mathcal{K}(x,y) \mapsto \mathcal{K}(x,y) + f(x) + h(y)$ by pure primal-sheet
     and dual-sheet functions leave the mixed variation strictly invariant, while the
     Legendre–Bregman potential $\mathcal{K}(x,y) = \langle x, y\rangle - \psi(x) - \psi^*(y)$
     has mixed variation equal to the exact canonical pairing $\langle \delta x, \delta y\rangle$
     (`paraKahlerMixedVariation_gauge_invariant_and_bregman_pairing`).

2. **Homogeneous Majorana Rays $Z = [u^+ : u^-]$ & Projective Klein Null Quadric**:
   - Defines `majoranaCrossPairing` and `majoranaKreinInterval` on the split carrier.
   - Proves total isotropy of both primal and dual sheets, homogeneous degree-2 scaling under
     $(u^+, u^-) \mapsto (\lambda u^+, \lambda u^-)$, and projective ray invariance of the Klein
     null quadric $\mathcal{Q}_{2p-2}$ for $\lambda \neq 0$
     (`majorana_kleinQuadric_projective_ray_invariance`).

3. **Massieu (1869) – Planck – Souriau (1974) Free Entropy Potential $\Phi = \ln Z$**:
   - Defines `gibbsPartitionSum`, `souriauMassieuPotential`, and `souriauAttentionWeight`.
   - Proves Massieu's characteristic Legendre identity
     $S(A) + \langle s \rangle_A = -\sum_j A_j \ln A_j + \sum_j A_j s_j = \ln Z = \Phi(s)$
     (`massieu_free_entropy_legendre_identity`) and projective additive logit-shift gauge
     invariance (`souriauMassieu_shift_and_attention_scale_invariance`).

4. **Souriau Moment Map (First Gradient) & Fisher–Souriau Information Metric (Second Hessian)**:
   - Proves that the coordinate derivative of $\Phi(s)$ is the attention weight $A_j(s)$
     (`hasDerivAt_souriauMassieuPotential_coord`), so the directional derivative along value
     vectors $v$ equals the Souriau moment map readout $M(s, v) = \sum_j A_j(s) v_j$.
   - Defines the Fisher–Souriau Hessian tensor $g^S_{jk}(s) = A_j(s)\delta_{jk} - A_j(s)A_k(s)$,
     proves the full coordinate Jacobian $\partial A_j/\partial s_k = g^S_{jk}(s)$
     (`hasDerivAt_souriauAttentionWeight_coord`, whose diagonal specialization is
     `hasDerivAt_souriauAttentionWeight_diag`), and its directional derivative is
     `A_j(s) (v_j - M(s,v))`
     (`deriv_souriauAttentionWeight_directional`). The quadratic form on any
     perturbation $\delta s$ equals the non-negative Fisher–Souriau variance
     $\sum_j A_j(s)(\delta s_j - M(s, \delta s))^2 \ge 0$
     (`fisherSouriau_quadratic_eq_variance_and_nonneg`). The second directional
     derivative of $\Phi$ at every point along a score line equals the
     Fisher–Souriau Hessian quadratic form
     (`souriauMassieu_directionalSecondDeriv_eq_fisherSouriauHessian_at`). It is
     strictly positive exactly in nonconstant score directions
     (`souriauMassieu_directionalSecondDeriv_pos_iff_nonconstant`).
-/

set_option autoImplicit false

namespace InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis

noncomputable section

open scoped BigOperators
open Finset
open InfoGeometry.Synthesis.TransactionalQueryKeyRoPEPhaseSpaceBridge

/-!
## Section 1: Neutral Para-Kähler Carrier & Gauge Invariance of the Para-Kähler Potential
-/

/-- Para-complex polarization endomorphism $J(x, y) = (x, -y)$ splitting the double phase space
into the $+1$ primal eigenbundle $T^+$ and $-1$ dual eigenbundle $T^-$. -/
def paraComplexEndJ {p : ℕ} (z : (Fin p → ℝ) × (Fin p → ℝ)) :
    (Fin p → ℝ) × (Fin p → ℝ) :=
  (z.1, -z.2)

/-- Neutral $(p, p)$-signature para-Kähler metric $g((x_1, y_1), (x_2, y_2)) = \langle x_1, y_2 \rangle + \langle x_2, y_1 \rangle$. -/
def paraKahlerNeutralMetric {p : ℕ}
    (z₁ z₂ : (Fin p → ℝ) × (Fin p → ℝ)) : ℝ :=
  featureInner z₁.1 z₂.2 + featureInner z₂.1 z₁.2

/-- Fundamental para-Kähler structural compatibility identities:
1. $J^2 = +\mathrm{id}$,
2. $g(JX, JY) = -g(X, Y)$,
3. $\omega(X, Y) = g(JX, Y)$ recovers `cotangentSymplecticForm`,
4. $\omega(JX, JY) = -\omega(X, Y)$, and
5. Both eigen-distributions $T^+ = \{(x, 0)\}$ and $T^- = \{(0, y)\}$ are totally $g$-isotropic. -/
theorem paraKahlerCompatibility_and_involution {p : ℕ}
    (z z₁ z₂ : (Fin p → ℝ) × (Fin p → ℝ)) (x₁ x₂ y₁ y₂ : Fin p → ℝ) :
    paraComplexEndJ (paraComplexEndJ z) = z ∧
    paraKahlerNeutralMetric (paraComplexEndJ z₁) (paraComplexEndJ z₂) =
      -paraKahlerNeutralMetric z₁ z₂ ∧
    paraKahlerNeutralMetric (paraComplexEndJ z₁) z₂ =
      cotangentSymplecticForm z₁ z₂ ∧
    cotangentSymplecticForm (paraComplexEndJ z₁) (paraComplexEndJ z₂) =
      -cotangentSymplecticForm z₁ z₂ ∧
    (paraKahlerNeutralMetric (x₁, 0) (x₂, 0) = 0 ∧
      paraKahlerNeutralMetric (0, y₁) (0, y₂) = 0) := by
  have hneg : ∀ (u v : Fin p → ℝ), featureInner u (-v) = -featureInner u v := by
    intro u v
    dsimp [featureInner]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    change u a * (-v a) = -(u a * v a)
    ring
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_⟩⟩
  · cases z
    simp [paraComplexEndJ]
  · dsimp [paraKahlerNeutralMetric, paraComplexEndJ]
    rw [hneg z₁.1 z₂.2, hneg z₂.1 z₁.2]
    ring
  · dsimp [paraKahlerNeutralMetric, paraComplexEndJ, cotangentSymplecticForm]
    rw [hneg z₂.1 z₁.2]
    ring
  · dsimp [cotangentSymplecticForm, paraComplexEndJ]
    rw [hneg z₁.1 z₂.2, hneg z₂.1 z₁.2]
    ring
  · dsimp [paraKahlerNeutralMetric]
    rw [featureInner_zero_right, featureInner_zero_right, add_zero]
  · dsimp [paraKahlerNeutralMetric]
    rw [featureInner_zero_left, featureInner_zero_left, add_zero]

/-- Mixed cross-sheet difference operator
$\Delta_x \Delta_y \mathcal{K}(x_0, x_1; y_0, y_1) = \mathcal{K}(x_1, y_1) - \mathcal{K}(x_1, y_0) - \mathcal{K}(x_0, y_1) + \mathcal{K}(x_0, y_0)$. -/
def paraKahlerMixedVariation {p : ℕ}
    (K : (Fin p → ℝ) → (Fin p → ℝ) → ℝ)
    (x₀ x₁ y₀ y₁ : Fin p → ℝ) : ℝ :=
  K x₁ y₁ - K x₁ y₀ - K x₀ y₁ + K x₀ y₀

/-- Para-Kähler gauge transformation $\mathcal{K}(x, y) \mapsto \mathcal{K}(x, y) + f(x) + h(y)$
by pure primal-sheet and dual-sheet potentials $f(x)$ and $h(y)$. -/
def paraKahlerGaugeShift {p : ℕ}
    (K : (Fin p → ℝ) → (Fin p → ℝ) → ℝ)
    (f h : (Fin p → ℝ) → ℝ) (x y : Fin p → ℝ) : ℝ :=
  K x y + f x + h y

/-- Legendre–Bregman canonical para-Kähler potential
$\mathcal{K}(x, y) = \langle x, y \rangle - \psi(x) - \psi^*(y)$. -/
def bregmanParaKahlerPotential {p : ℕ}
    (ψ ψ_star : (Fin p → ℝ) → ℝ) (x y : Fin p → ℝ) : ℝ :=
  featureInner x y - ψ x - ψ_star y

/-- Para-Kähler Gauge Invariance and Bregman Cross-Sheet Hessian Law:
1. Adding any pure primal potential $f(x)$ and pure dual potential $h(y)$ leaves the mixed
   cross-sheet variation $\Delta_x \Delta_y \mathcal{K}$ strictly invariant.
2. The mixed cross-sheet variation of the Legendre–Bregman potential
   $\mathcal{K}(x, y) = \langle x, y \rangle - \psi(x) - \psi^*(y)$ equals the exact bilinear
   cross-sheet pairing $\langle x_1 - x_0, y_1 - y_0 \rangle$. -/
theorem paraKahlerMixedVariation_gauge_invariant_and_bregman_pairing {p : ℕ}
    (K : (Fin p → ℝ) → (Fin p → ℝ) → ℝ)
    (f h ψ ψ_star : (Fin p → ℝ) → ℝ)
    (x₀ x₁ y₀ y₁ : Fin p → ℝ) :
    paraKahlerMixedVariation (paraKahlerGaugeShift K f h) x₀ x₁ y₀ y₁ =
      paraKahlerMixedVariation K x₀ x₁ y₀ y₁ ∧
    paraKahlerMixedVariation (bregmanParaKahlerPotential ψ ψ_star) x₀ x₁ y₀ y₁ =
      featureInner (x₁ - x₀) (y₁ - y₀) := by
  refine ⟨?_, ?_⟩
  · dsimp [paraKahlerMixedVariation, paraKahlerGaugeShift]
    ring
  · dsimp [paraKahlerMixedVariation, bregmanParaKahlerPotential]
    have h_lin :
        featureInner x₁ y₁ - featureInner x₁ y₀ - featureInner x₀ y₁ + featureInner x₀ y₀ =
          featureInner (x₁ - x₀) (y₁ - y₀) := by
      dsimp [featureInner]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      change x₁ a * y₁ a - x₁ a * y₀ a - x₀ a * y₁ a + x₀ a * y₀ a =
        (x₁ a - x₀ a) * (y₁ a - y₀ a)
      ring
    linarith [h_lin]

/-!
## Section 2: Homogeneous Majorana Rays $Z = [u^+ : u^-]$ & Projective Klein Null Quadric
-/

/-- Weighted Majorana cross-sheet pairing $g_\pi(u^+, u^-) = \sum_{\alpha=1}^p \pi_\alpha u_\alpha^+ u_\alpha^-$. -/
def majoranaCrossPairing {p : ℕ} (π u_plus u_minus : Fin p → ℝ) : ℝ :=
  ∑ a : Fin p, π a * u_plus a * u_minus a

/-- Full off-diagonal Krein quadratic interval $ds^2_\pi(u^+, u^-) = 2 g_\pi(u^+, u^-)$ on the
homogeneous Majorana carrier $\mathcal{K}_p = T^+ \oplus T^-$. -/
def majoranaKreinInterval {p : ℕ} (π : Fin p → ℝ)
    (Z : (Fin p → ℝ) × (Fin p → ℝ)) : ℝ :=
  2 * majoranaCrossPairing π Z.1 Z.2

/-- Projective Ray Invariance of the Majorana Klein Null Quadric $\mathcal{Q}_{2p-2}$:
1. Both pure Majorana sheets $T^+ = \{(u^+, 0)\}$ and $T^- = \{(0, u^-)\}$ have identically
   zero Krein interval.
2. Under homogeneous rescaling $[u^+ : u^-] \mapsto [\lambda u^+ : \lambda u^-]$, the Krein
   interval scales homogeneously of degree 2 by $\lambda^2$.
3. For any $\lambda \neq 0$, the Klein null quadric incidence condition $g_\pi(u^+, u^-) = 0$
   is strictly invariant under projective rescaling. -/
theorem majorana_kleinQuadric_projective_ray_invariance {p : ℕ}
    (π u_plus u_minus : Fin p → ℝ) (lam : ℝ) (hlam : lam ≠ 0) :
    (majoranaKreinInterval π (u_plus, 0) = 0 ∧
      majoranaKreinInterval π (0, u_minus) = 0) ∧
    majoranaKreinInterval π (lam • u_plus, lam • u_minus) =
      lam ^ 2 * majoranaKreinInterval π (u_plus, u_minus) ∧
    (majoranaCrossPairing π (lam • u_plus) (lam • u_minus) = 0 ↔
      majoranaCrossPairing π u_plus u_minus = 0) := by
  have h_scale :
      majoranaCrossPairing π (lam • u_plus) (lam • u_minus) =
        lam ^ 2 * majoranaCrossPairing π u_plus u_minus := by
    dsimp [majoranaCrossPairing]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => by ring)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · dsimp [majoranaKreinInterval, majoranaCrossPairing]
    simp
  · dsimp [majoranaKreinInterval, majoranaCrossPairing]
    simp
  · dsimp [majoranaKreinInterval]
    rw [h_scale]
    ring
  · rw [h_scale]
    have hlam2 : lam ^ 2 ≠ 0 := pow_ne_zero 2 hlam
    exact mul_eq_zero_iff_left hlam2

/-!
## Section 3: Massieu (1869) – Planck – Souriau (1974) Free Entropy Potential $\Phi = \ln Z$
-/

/-- Discrete Gibbs partition sum $Z(s) = \sum_{j} \exp(s_j)$. -/
def gibbsPartitionSum {m : ℕ} (s : Fin m → ℝ) : ℝ :=
  ∑ j : Fin m, Real.exp (s j)

/-- Souriau–Massieu–Planck free entropy potential (surprisal generating function)
$\Phi(s) = \ln \sum_{j} \exp(s_j)$. -/
def souriauMassieuPotential {m : ℕ} (s : Fin m → ℝ) : ℝ :=
  Real.log (gibbsPartitionSum s)

/-- Canonical Gibbs / Softmax attention weight $A_j(s) = \exp(s_j) / Z(s)$. -/
def souriauAttentionWeight {m : ℕ} (s : Fin m → ℝ) (j : Fin m) : ℝ :=
  Real.exp (s j) / gibbsPartitionSum s

/-- For any non-empty finite context, the Gibbs partition sum is strictly positive. -/
theorem gibbsPartitionSum_pos {m : ℕ} [Nonempty (Fin m)] (s : Fin m → ℝ) :
    0 < gibbsPartitionSum s := by
  dsimp [gibbsPartitionSum]
  obtain ⟨j₀⟩ := ‹Nonempty (Fin m)›
  exact Finset.sum_pos (fun j _ => Real.exp_pos (s j)) ⟨j₀, Finset.mem_univ j₀⟩

/-- Strict positivity of every canonical attention weight $A_j(s) > 0$. -/
theorem souriauAttentionWeight_pos {m : ℕ} [Nonempty (Fin m)]
    (s : Fin m → ℝ) (j : Fin m) :
    0 < souriauAttentionWeight s j := by
  dsimp [souriauAttentionWeight]
  exact div_pos (Real.exp_pos (s j)) (gibbsPartitionSum_pos s)

/-- Massieu's Characteristic Free-Entropy Legendre Identity (1869):
1. The canonical weights normalize to unity: $\sum_j A_j(s) = 1$.
2. Pointwise surprisal satisfies $-\ln A_j(s) = \Phi(s) - s_j$.
3. The Legendre transform of Shannon entropy with respect to the score $s_j$ equals the
   Souriau–Massieu free entropy potential:
   $$S(A) + \sum_{j} A_j(s) s_j = -\sum_{j} A_j(s) \ln A_j(s) + \sum_{j} A_j(s) s_j = \Phi(s).$$ -/
theorem massieu_free_entropy_legendre_identity {m : ℕ} [Nonempty (Fin m)]
    (s : Fin m → ℝ) (j : Fin m) :
    (∑ k : Fin m, souriauAttentionWeight s k = 1) ∧
    (-Real.log (souriauAttentionWeight s j) = souriauMassieuPotential s - s j) ∧
    ((-∑ k : Fin m, souriauAttentionWeight s k * Real.log (souriauAttentionWeight s k)) +
      (∑ k : Fin m, souriauAttentionWeight s k * s k) =
        souriauMassieuPotential s) := by
  have hZ_pos : 0 < gibbsPartitionSum s := gibbsPartitionSum_pos s
  have hZ_ne : gibbsPartitionSum s ≠ 0 := ne_of_gt hZ_pos
  have h_sum : ∑ k : Fin m, souriauAttentionWeight s k = 1 := by
    dsimp [souriauAttentionWeight]
    rw [← Finset.sum_div]
    exact div_self hZ_ne
  have h_pt : ∀ k : Fin m,
      -Real.log (souriauAttentionWeight s k) = souriauMassieuPotential s - s k := by
    intro k
    dsimp [souriauAttentionWeight, souriauMassieuPotential]
    rw [Real.log_div (ne_of_gt (Real.exp_pos (s k))) hZ_ne, Real.log_exp]
    ring
  refine ⟨h_sum, h_pt j, ?_⟩
  have h_ent :
      -∑ k : Fin m, souriauAttentionWeight s k * Real.log (souriauAttentionWeight s k) =
        ∑ k : Fin m, souriauAttentionWeight s k * (souriauMassieuPotential s - s k) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hk := h_pt k
    linarith [congrArg (fun t => souriauAttentionWeight s k * t) hk]
  rw [h_ent, ← Finset.sum_add_distrib]
  have h_combine :
      (∑ k : Fin m,
        (souriauAttentionWeight s k * (souriauMassieuPotential s - s k) +
          souriauAttentionWeight s k * s k)) =
        (∑ k : Fin m, souriauAttentionWeight s k) * souriauMassieuPotential s := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => by ring)
  rw [h_combine, h_sum, one_mul]

/-- Projective Shift Gauge Law: shifting all scores by a constant $c \in \mathbb{R}$ shifts the
Souriau–Massieu potential by $+c$ (`Φ(s + c·1) = Φ(s) + c`) while leaving the attention weights
$A_j(s)$ strictly invariant (`A_j(s + c·1) = A_j(s)`). -/
theorem souriauMassieu_shift_and_attention_scale_invariance
    {m : ℕ} [Nonempty (Fin m)] (s : Fin m → ℝ) (c : ℝ) (j : Fin m) :
    souriauMassieuPotential (fun k => s k + c) = souriauMassieuPotential s + c ∧
    souriauAttentionWeight (fun k => s k + c) j = souriauAttentionWeight s j := by
  have hZ_pos : 0 < gibbsPartitionSum s := gibbsPartitionSum_pos s
  have hZ_ne : gibbsPartitionSum s ≠ 0 := ne_of_gt hZ_pos
  have hexp_ne : Real.exp c ≠ 0 := ne_of_gt (Real.exp_pos c)
  have hZ_shift :
      gibbsPartitionSum (fun k => s k + c) = gibbsPartitionSum s * Real.exp c := by
    dsimp [gibbsPartitionSum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => Real.exp_add (s k) c)
  refine ⟨?_, ?_⟩
  · dsimp [souriauMassieuPotential]
    rw [hZ_shift, Real.log_mul hZ_ne hexp_ne, Real.log_exp]
  · dsimp [souriauAttentionWeight]
    rw [hZ_shift, Real.exp_add (s j) c]
    exact mul_div_mul_right (Real.exp (s j)) (gibbsPartitionSum s) hexp_ne

/-- The fiber of the finite softmax map consists exactly of uniform score shifts.
This is the finite algebraic gauge orbit, not a natural-gradient dynamical theorem. -/
theorem souriauAttentionWeights_eq_iff_additive_constant
    {m : ℕ} [Nonempty (Fin m)] (s t : Fin m → ℝ) :
    (∀ j : Fin m, souriauAttentionWeight s j = souriauAttentionWeight t j) ↔
      ∃ c : ℝ, ∀ j : Fin m, t j = s j + c := by
  constructor
  · intro h
    refine ⟨souriauMassieuPotential t - souriauMassieuPotential s, ?_⟩
    intro j
    have hs := (massieu_free_entropy_legendre_identity s j).2.1
    have ht := (massieu_free_entropy_legendre_identity t j).2.1
    have hsurp :
        -Real.log (souriauAttentionWeight s j) =
          -Real.log (souriauAttentionWeight t j) :=
      congrArg (fun x : ℝ => -Real.log x) (h j)
    rw [hs, ht] at hsurp
    linarith
  · rintro ⟨c, hc⟩ j
    have hshift : t = fun k : Fin m => s k + c := by
      funext k
      exact hc k
    rw [hshift]
    exact
      (souriauMassieu_shift_and_attention_scale_invariance s c j).2.symm

/-!
## Section 4: Souriau Moment Map (First Gradient) & Fisher–Souriau Information Metric (Second Hessian)
-/

/-- Souriau Moment Map (Noether expectation value readout):
$M(s, v) = \sum_{j} A_j(s) v_j$. -/
def souriauMomentMap {m : ℕ} (s v : Fin m → ℝ) : ℝ :=
  ∑ j : Fin m, souriauAttentionWeight s j * v j

/-- Fisher–Souriau Information Metric Hessian tensor:
$g^S_{jk}(s) = A_j(s)\delta_{jk} - A_j(s) A_k(s)$. -/
def fisherSouriauHessian {m : ℕ} [DecidableEq (Fin m)]
    (s : Fin m → ℝ) (j k : Fin m) : ℝ :=
  (if j = k then souriauAttentionWeight s j else 0) -
    souriauAttentionWeight s j * souriauAttentionWeight s k

/-- Coordinate derivative of the Gibbs partition sum along score coordinate $j$:
$\frac{\partial}{\partial t} Z(\mathrm{update}\, s\, j\, t)\big|_{t = s_j} = \exp(s_j)$. -/
theorem hasDerivAt_gibbsPartitionSum_coord {m : ℕ}
    (s : Fin m → ℝ) (j : Fin m) :
    HasDerivAt (fun t : ℝ => gibbsPartitionSum (Function.update s j t))
      (Real.exp (s j)) (s j) := by
  have h_decomp :
      (fun t : ℝ => gibbsPartitionSum (Function.update s j t)) =
        fun t : ℝ => Real.exp t + ∑ k ∈ Finset.univ.erase j, Real.exp (s k) := by
    funext t
    dsimp [gibbsPartitionSum]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), Function.update_self]
    congr 1
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [h_decomp]
  exact (Real.hasDerivAt_exp (s j)).add_const (∑ k ∈ Finset.univ.erase j, Real.exp (s k))

/-- First Derivative (Souriau Moment Map Theorem): differentiating the Souriau–Massieu free
entropy potential $\Phi(s) = \ln Z(s)$ with respect to score coordinate $s_j$ yields the exact
canonical attention weight $A_j(s)$. -/
theorem hasDerivAt_souriauMassieuPotential_coord {m : ℕ} [Nonempty (Fin m)]
    (s : Fin m → ℝ) (j : Fin m) :
    HasDerivAt (fun t : ℝ => souriauMassieuPotential (Function.update s j t))
      (souriauAttentionWeight s j) (s j) := by
  have hZ_ne : gibbsPartitionSum s ≠ 0 := ne_of_gt (gibbsPartitionSum_pos s)
  have h_upd : Function.update s j (s j) = s := Function.update_eq_self j s
  have h_part := hasDerivAt_gibbsPartitionSum_coord s j
  have h_log := HasDerivAt.log h_part (by simpa [h_upd] using hZ_ne)
  simpa [souriauMassieuPotential, souriauAttentionWeight, h_upd] using h_log

/-- The directional derivative of the finite Massieu potential along a score
vector is the softmax-weighted moment of that vector. -/
theorem hasDerivAt_souriauMassieuPotential_directional {m : ℕ}
    [Nonempty (Fin m)] (s v : Fin m → ℝ) :
    HasDerivAt
      (fun t : ℝ => souriauMassieuPotential (fun i => s i + t * v i))
      (souriauMomentMap s v) 0 := by
  have hterm (i : Fin m) :
      HasDerivAt (fun t : ℝ => Real.exp (s i + t * v i))
        (Real.exp (s i) * v i) 0 := by
    have hlinear :
        HasDerivAt (fun t : ℝ => s i + t * v i) (v i) 0 :=
      (hasDerivAt_mul_const (v i)).const_add (s i)
    simpa using HasDerivAt.exp hlinear
  have hsum :
      HasDerivAt
        (fun t : ℝ => ∑ i : Fin m, Real.exp (s i + t * v i))
        (∑ i : Fin m, Real.exp (s i) * v i) 0 := by
    exact HasDerivAt.fun_sum (u := Finset.univ) (fun i hi => hterm i)
  have hZ_ne : gibbsPartitionSum s ≠ 0 :=
    ne_of_gt (gibbsPartitionSum_pos s)
  have hphi :
      HasDerivAt
        (fun t : ℝ => souriauMassieuPotential (fun i => s i + t * v i))
        ((∑ i : Fin m, Real.exp (s i) * v i) / gibbsPartitionSum s) 0 := by
    have hlog := HasDerivAt.log hsum (by
      simpa [gibbsPartitionSum] using hZ_ne)
    simpa [souriauMassieuPotential, gibbsPartitionSum] using hlog
  have hratio :
      (∑ i : Fin m, Real.exp (s i) * v i) / gibbsPartitionSum s =
        souriauMomentMap s v := by
    unfold souriauMomentMap souriauAttentionWeight
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [hZ_ne]
  rw [hratio] at hphi
  exact hphi

/-- Diagonal Second Derivative (Fisher–Souriau Diagonal Susceptibility): differentiating the
attention weight $A_j$ with respect to $s_j$ yields the diagonal Fisher–Souriau Hessian entry
$g^S_{jj}(s) = A_j(s)(1 - A_j(s)) = A_j(s) - A_j(s)^2$. -/
theorem hasDerivAt_souriauAttentionWeight_diag {m : ℕ} [Nonempty (Fin m)]
    (s : Fin m → ℝ) (j : Fin m) :
    HasDerivAt (fun t : ℝ => souriauAttentionWeight (Function.update s j t) j)
      (fisherSouriauHessian s j j) (s j) := by
  have hZ_ne : gibbsPartitionSum s ≠ 0 := ne_of_gt (gibbsPartitionSum_pos s)
  have h_upd : Function.update s j (s j) = s := Function.update_eq_self j s
  have h_num : HasDerivAt (fun t : ℝ => Real.exp (Function.update s j t j))
      (Real.exp (s j)) (s j) := by
    simpa [Function.update_self] using Real.hasDerivAt_exp (s j)
  have h_den := hasDerivAt_gibbsPartitionSum_coord s j
  have h_quot :
      HasDerivAt
        (fun t : ℝ =>
          Real.exp (Function.update s j t j) / gibbsPartitionSum (Function.update s j t))
        ((Real.exp (s j) * gibbsPartitionSum (Function.update s j (s j)) -
            Real.exp (Function.update s j (s j) j) * Real.exp (s j)) /
          gibbsPartitionSum (Function.update s j (s j)) ^ 2)
        (s j) :=
    HasDerivAt.div h_num h_den (by simpa [h_upd] using hZ_ne)
  have h_alg :
      (Real.exp (s j) * gibbsPartitionSum (Function.update s j (s j)) -
          Real.exp (Function.update s j (s j) j) * Real.exp (s j)) /
        gibbsPartitionSum (Function.update s j (s j)) ^ 2 =
        fisherSouriauHessian s j j := by
    rw [h_upd]
    dsimp [fisherSouriauHessian, souriauAttentionWeight]
    simp only [↓reduceIte]
    field_simp [hZ_ne]
  rw [h_alg] at h_quot
  exact h_quot

/-- Varying any one finite score coordinate differentiates every attention
weight by the corresponding Fisher–Souriau Hessian entry. -/
theorem hasDerivAt_souriauAttentionWeight_coord {m : ℕ} [Nonempty (Fin m)]
    (s : Fin m → ℝ) (j k : Fin m) :
    HasDerivAt
      (fun t : ℝ => souriauAttentionWeight (Function.update s k t) j)
      (fisherSouriauHessian s j k) (s k) := by
  by_cases hjk : j = k
  · subst k
    simpa using hasDerivAt_souriauAttentionWeight_diag s j
  · have hZ_ne : gibbsPartitionSum s ≠ 0 :=
      ne_of_gt (gibbsPartitionSum_pos s)
    have h_upd : Function.update s k (s k) = s :=
      Function.update_eq_self k s
    have h_num_fun :
        (fun t : ℝ => Real.exp (Function.update s k t j)) =
          fun _ => Real.exp (s j) := by
      funext t
      simp [Function.update_of_ne hjk]
    have h_num :
        HasDerivAt (fun t : ℝ => Real.exp (Function.update s k t j))
          0 (s k) := by
      rw [h_num_fun]
      exact hasDerivAt_const (s k) (Real.exp (s j))
    have h_den := hasDerivAt_gibbsPartitionSum_coord s k
    have h_quot :
        HasDerivAt
          (fun t : ℝ =>
            Real.exp (Function.update s k t j) /
              gibbsPartitionSum (Function.update s k t))
          ((0 * gibbsPartitionSum (Function.update s k (s k)) -
              Real.exp (Function.update s k (s k) j) * Real.exp (s k)) /
            gibbsPartitionSum (Function.update s k (s k)) ^ 2)
          (s k) :=
      HasDerivAt.div h_num h_den (by simpa [h_upd] using hZ_ne)
    have h_alg :
        (0 * gibbsPartitionSum (Function.update s k (s k)) -
            Real.exp (Function.update s k (s k) j) * Real.exp (s k)) /
          gibbsPartitionSum (Function.update s k (s k)) ^ 2 =
          fisherSouriauHessian s j k := by
      rw [h_upd]
      dsimp [fisherSouriauHessian, souriauAttentionWeight]
      simp only [if_neg hjk]
      field_simp [hZ_ne]
      <;> ring
    rw [h_alg] at h_quot
    exact h_quot

/-- The derivative of a finite softmax weight along a score direction is its
weighted centered score response. -/
theorem deriv_souriauAttentionWeight_directional {m : ℕ}
    [Nonempty (Fin m)] (s v : Fin m → ℝ) (j : Fin m) :
    deriv (fun t : ℝ => souriauAttentionWeight (fun i => s i + t * v i) j) 0 =
      souriauAttentionWeight s j * (v j - souriauMomentMap s v) := by
  let w : Fin m → ℝ := fun i => Real.exp (s i)
  have hw : ∀ i : Fin m, 0 < w i := fun i => Real.exp_pos (s i)
  have hpartition (t : ℝ) :
      gibbsPartitionSum (fun i => s i + t * v i) =
        InfoGeometry.Analytic.logSumExpPartition w v t := by
    unfold gibbsPartitionSum InfoGeometry.Analytic.logSumExpPartition w
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.exp_add]
  have hweight (t : ℝ) (i : Fin m) :
      souriauAttentionWeight (fun k => s k + t * v k) i =
        InfoGeometry.Analytic.logSumExpWeight w v t i := by
    unfold souriauAttentionWeight InfoGeometry.Analytic.logSumExpWeight
    rw [Real.exp_add, hpartition t]
  have hweight0 : ∀ i : Fin m,
      InfoGeometry.Analytic.logSumExpWeight w v 0 i =
        souriauAttentionWeight s i := by
    intro i
    simpa using (hweight 0 i).symm
  have hmean : InfoGeometry.Analytic.logSumExpMean w v 0 = souriauMomentMap s v := by
    rw [InfoGeometry.Analytic.logSumExpMean_eq_weighted_sum w v hw 0]
    unfold souriauMomentMap
    apply Finset.sum_congr rfl
    intro i hi
    rw [hweight0 i]
  have hfun :
      (fun t : ℝ => souriauAttentionWeight (fun i => s i + t * v i) j) =
        fun t => InfoGeometry.Analytic.logSumExpWeight w v t j := by
    funext t
    exact hweight t j
  calc
    deriv (fun t : ℝ => souriauAttentionWeight (fun i => s i + t * v i) j) 0 =
        deriv (fun t => InfoGeometry.Analytic.logSumExpWeight w v t j) 0 := by
          rw [hfun]
    _ = InfoGeometry.Analytic.logSumExpWeight w v 0 j *
          (v j - InfoGeometry.Analytic.logSumExpMean w v 0) :=
      InfoGeometry.Analytic.logSumExpWeight_deriv w v hw 0 j
    _ = souriauAttentionWeight s j * (v j - souriauMomentMap s v) := by
      rw [hweight0 j, hmean]

/-- Fisher–Souriau Metric Covariance Identity and Positive Semi-Definiteness:
For any score fluctuation $\delta s : \operatorname{Fin} m \to \mathbb{R}$,
1. The quadratic form of the Fisher–Souriau Hessian equals the second central moment (variance)
   of $\delta s$ under the canonical attention distribution $A(s)$:
   $$\sum_{j, k} \delta s_j \, g^S_{jk}(s) \, \delta s_k
     = \sum_{j} A_j(s) (\delta s_j)^2 - M(s, \delta s)^2
     = \sum_{j} A_j(s) \left(\delta s_j - M(s, \delta s)\right)^2.$$
2. Consequently, the Fisher–Souriau information metric quadratic form is strictly non-negative:
   $$0 \le \sum_{j, k} \delta s_j \, g^S_{jk}(s) \, \delta s_k.$$ -/
theorem fisherSouriau_quadratic_eq_variance_and_nonneg {m : ℕ} [Nonempty (Fin m)]
    (s δs : Fin m → ℝ) :
    (∑ j : Fin m, ∑ k : Fin m, δs j * fisherSouriauHessian s j k * δs k =
      ∑ j : Fin m, souriauAttentionWeight s j * (δs j - souriauMomentMap s δs) ^ 2) ∧
    0 ≤ ∑ j : Fin m, ∑ k : Fin m, δs j * fisherSouriauHessian s j k * δs k := by
  have h_sum_one : ∑ j : Fin m, souriauAttentionWeight s j = 1 :=
    (massieu_free_entropy_legendre_identity s (Classical.arbitrary (Fin m))).1
  have h_quad :
      ∑ j : Fin m, ∑ k : Fin m, δs j * fisherSouriauHessian s j k * δs k =
        (∑ j : Fin m, souriauAttentionWeight s j * δs j ^ 2) -
          souriauMomentMap s δs ^ 2 := by
    have h_inner : ∀ j : Fin m,
        (∑ k : Fin m, δs j * fisherSouriauHessian s j k * δs k) =
          souriauAttentionWeight s j * δs j ^ 2 -
            (souriauAttentionWeight s j * δs j) * souriauMomentMap s δs := by
      intro j
      dsimp [fisherSouriauHessian, souriauMomentMap]
      have h_split :
          (∑ k : Fin m,
            δs j * ((if j = k then souriauAttentionWeight s j else 0) -
              souriauAttentionWeight s j * souriauAttentionWeight s k) * δs k) =
          (∑ k : Fin m,
            if j = k then δs j * souriauAttentionWeight s j * δs k else 0) -
          (∑ k : Fin m,
            (souriauAttentionWeight s j * δs j) * (souriauAttentionWeight s k * δs k)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        by_cases hjk : j = k
        · simp [hjk]; ring
        · simp [hjk]; ring
      rw [h_split, Finset.sum_ite_eq Finset.univ j]
      simp only [Finset.mem_univ, ↓reduceIte, ← Finset.mul_sum]
      ring
    simp_rw [h_inner]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    dsimp [souriauMomentMap]
    ring
  have h_var :
      ∑ j : Fin m, souriauAttentionWeight s j * (δs j - souriauMomentMap s δs) ^ 2 =
        (∑ j : Fin m, souriauAttentionWeight s j * δs j ^ 2) -
          souriauMomentMap s δs ^ 2 := by
    have h_expand :
        (∑ j : Fin m, souriauAttentionWeight s j * (δs j - souriauMomentMap s δs) ^ 2) =
          (∑ j : Fin m, souriauAttentionWeight s j * δs j ^ 2) -
          2 * souriauMomentMap s δs * (∑ j : Fin m, souriauAttentionWeight s j * δs j) +
          souriauMomentMap s δs ^ 2 * (∑ j : Fin m, souriauAttentionWeight s j) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [h_expand, h_sum_one]
    dsimp [souriauMomentMap]
    ring
  have h_eq :
      ∑ j : Fin m, ∑ k : Fin m, δs j * fisherSouriauHessian s j k * δs k =
        ∑ j : Fin m, souriauAttentionWeight s j * (δs j - souriauMomentMap s δs) ^ 2 :=
    h_quad.trans h_var.symm
  refine ⟨h_eq, ?_⟩
  rw [h_eq]
  refine Finset.sum_nonneg (fun j _ => ?_)
  exact mul_nonneg (le_of_lt (souriauAttentionWeight_pos s j)) (sq_nonneg _)

/-- On a nonempty finite score space, the Fisher–Souriau quadratic form
vanishes exactly on constant-score gauge directions. This is an algebraic
kernel statement, not a natural-gradient dynamical or complexity theorem. -/
theorem fisherSouriau_quadratic_eq_zero_iff_constant {m : ℕ}
    [Nonempty (Fin m)] (s v : Fin m → ℝ) :
    (∑ j : Fin m, ∑ k : Fin m,
      v j * fisherSouriauHessian s j k * v k) = 0 ↔
      ∃ c : ℝ, ∀ j : Fin m, v j = c := by
  rw [(fisherSouriau_quadratic_eq_variance_and_nonneg s v).1]
  constructor
  · intro hzero
    have h_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin m)),
        0 ≤ souriauAttentionWeight s j *
          (v j - souriauMomentMap s v) ^ 2 := by
      intro j hj
      exact mul_nonneg
        (le_of_lt (souriauAttentionWeight_pos s j))
        (sq_nonneg _)
    have h_terms := (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp hzero
    refine ⟨souriauMomentMap s v, ?_⟩
    intro j
    have hz := h_terms j (Finset.mem_univ j)
    have hsq : (v j - souriauMomentMap s v) ^ 2 = 0 :=
      (mul_eq_zero.mp hz).resolve_left
        (ne_of_gt (souriauAttentionWeight_pos s j))
    have hcenter : v j - souriauMomentMap s v = 0 :=
      (sq_eq_zero_iff.mp hsq)
    linarith
  · rintro ⟨c, hc⟩
    have hnorm : ∑ j : Fin m, souriauAttentionWeight s j = 1 :=
      (massieu_free_entropy_legendre_identity s
        (Classical.choice ‹Nonempty (Fin m)›)).1
    have hmean : souriauMomentMap s v = c := by
      unfold souriauMomentMap
      calc
        (∑ j : Fin m, souriauAttentionWeight s j * v j) =
            ∑ j : Fin m, souriauAttentionWeight s j * c := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hc j]
        _ = (∑ j : Fin m, souriauAttentionWeight s j) * c := by
          rw [Finset.sum_mul]
        _ = c := by rw [hnorm]; ring
    rw [hmean]
    apply Finset.sum_eq_zero
    intro j hj
    rw [hc j]
    simp


/-- Along an affine score line, the second derivative of the finite Massieu
    potential at parameter `t` is the Fisher–Souriau Hessian quadratic form
    evaluated at the score `s + t v`. -/
theorem souriauMassieu_directionalSecondDeriv_eq_fisherSouriauHessian_at
    {m : ℕ} [Nonempty (Fin m)] (s v : Fin m → ℝ) (t : ℝ) :
    deriv (fun τ : ℝ => deriv
      (fun τ' => souriauMassieuPotential (fun i => s i + τ' * v i)) τ) t =
      ∑ j : Fin m, ∑ k : Fin m,
        v j * fisherSouriauHessian (fun i => s i + t * v i) j k * v k := by
  let w : Fin m → ℝ := fun i => Real.exp (s i)
  have hw : ∀ i : Fin m, 0 < w i := fun i => Real.exp_pos (s i)
  have hpartition (τ : ℝ) :
      gibbsPartitionSum (fun i => s i + τ * v i) =
        InfoGeometry.Analytic.logSumExpPartition w v τ := by
    unfold gibbsPartitionSum InfoGeometry.Analytic.logSumExpPartition w
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.exp_add]
  have hline :
      (fun τ : ℝ => souriauMassieuPotential (fun i => s i + τ * v i)) =
        fun τ => InfoGeometry.Analytic.logSumExp w v τ := by
    funext τ
    unfold souriauMassieuPotential InfoGeometry.Analytic.logSumExp
    rw [hpartition τ]
  have hweight (τ : ℝ) (i : Fin m) :
      souriauAttentionWeight (fun k => s k + τ * v k) i =
        InfoGeometry.Analytic.logSumExpWeight w v τ i := by
    unfold souriauAttentionWeight InfoGeometry.Analytic.logSumExpWeight
    rw [Real.exp_add, hpartition τ]
  have hweightAt : ∀ i : Fin m,
      InfoGeometry.Analytic.logSumExpWeight w v t i =
        souriauAttentionWeight (fun k => s k + t * v k) i := by
    intro i
    simpa using (hweight t i).symm
  have hmean :
      InfoGeometry.Analytic.logSumExpMean w v t =
        souriauMomentMap (fun i => s i + t * v i) v := by
    rw [InfoGeometry.Analytic.logSumExpMean_eq_weighted_sum w v hw t]
    unfold souriauMomentMap
    apply Finset.sum_congr rfl
    intro i hi
    rw [hweightAt i]
  have hmoment :
      (∑ j : Fin m, InfoGeometry.Analytic.logSumExpWeight w v t j * v j) =
        souriauMomentMap (fun i => s i + t * v i) v := by
    rw [← InfoGeometry.Analytic.logSumExpMean_eq_weighted_sum w v hw t, hmean]
  have hcenter :
      (∑ i : Fin m, InfoGeometry.Analytic.logSumExpWeight w v t i *
        (v i - ∑ j : Fin m, InfoGeometry.Analytic.logSumExpWeight w v t j * v j) ^ 2) =
      ∑ i : Fin m, souriauAttentionWeight (fun k => s k + t * v k) i *
        (v i - souriauMomentMap (fun k => s k + t * v k) v) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hweightAt i, hmoment]
  rw [hline]
  rw [InfoGeometry.Analytic.logSumExp_secondDeriv_eq_variance w v hw t]
  rw [InfoGeometry.Analytic.logSumExpVariance_eq_centered w v hw t]
  rw [hcenter]
  exact (fisherSouriau_quadratic_eq_variance_and_nonneg
    (fun i => s i + t * v i) v).1.symm

/-- The second derivative at parameter zero is the Fisher–Souriau Hessian
    quadratic form at the initial score. -/
theorem souriauMassieu_directionalSecondDeriv_eq_fisherSouriauHessian
    {m : ℕ} [Nonempty (Fin m)] (s v : Fin m → ℝ) :
    deriv (fun t : ℝ => deriv
      (fun t' => souriauMassieuPotential (fun i => s i + t' * v i)) t) 0 =
      ∑ j : Fin m, ∑ k : Fin m,
        v j * fisherSouriauHessian s j k * v k := by
  simpa using souriauMassieu_directionalSecondDeriv_eq_fisherSouriauHessian_at s v 0

/-- At any point of a score line, the Massieu curvature is positive exactly
    when the direction is not an additive-constant gauge direction. -/
theorem souriauMassieu_directionalSecondDeriv_pos_iff_nonconstant
    {m : ℕ} [Nonempty (Fin m)] (s v : Fin m → ℝ) (t : ℝ) :
    0 < deriv (fun τ : ℝ => deriv
      (fun τ' => souriauMassieuPotential (fun i => s i + τ' * v i)) τ) t ↔
      ¬ ∃ c : ℝ, ∀ j : Fin m, v j = c := by
  rw [souriauMassieu_directionalSecondDeriv_eq_fisherSouriauHessian_at s v t]
  constructor
  · intro hpos hconstant
    have hzero := (fisherSouriau_quadratic_eq_zero_iff_constant
      (fun i => s i + t * v i) v).2 hconstant
    linarith
  · intro hnonconstant
    have hnonneg := (fisherSouriau_quadratic_eq_variance_and_nonneg
      (fun i => s i + t * v i) v).2
    have hne :
        (∑ j : Fin m, ∑ k : Fin m,
          v j * fisherSouriauHessian (fun i => s i + t * v i) j k * v k) ≠ 0 := by
      intro hzero
      exact hnonconstant ((fisherSouriau_quadratic_eq_zero_iff_constant
        (fun i => s i + t * v i) v).1 hzero)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)


end

end InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis
