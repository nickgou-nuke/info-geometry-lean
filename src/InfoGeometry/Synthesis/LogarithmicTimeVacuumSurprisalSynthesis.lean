/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import InfoGeometry.Synthesis.RecoveredPhysicalInvariantsSynthesis

/-!
# Logarithmic Time Paradigms, Vacuum Modular Surprisal, the First Law of Entanglement, and Bekenstein–Fisher Covariance

This module unifies the four foundational logarithmic-time paradigms of mathematical physics
with the Connes–Rovelli–Bisognano–Wichmann–Jacobson modular surprisal identity
$\mathcal{I} \equiv K \equiv -\ln \rho$:

1. **Section 1 (Milne's Two-Clock Kinematic Relativity: Static Comoving Coordinates & Dirac–Milne Coupling Drift)**:
   - Extends `milneKinematicTime` ($\tau(t) = t_0 \ln(t / t_0) + t_0$) with its inverse
     dynamical clock `milneDynamicalTime` ($t(\tau) = t_0 \exp((\tau - t_0) / t_0)$),
     proving exact mutual inversion (`milneDynamicalTime_milneKinematicTime`,
     `milneKinematicTime_milneDynamicalTime`).
   - Proves that the comoving kinematic coordinate $x(t) = (t_0 / t) r(t)$ transforms a
     uniformly expanding Milne trajectory $r(t) = v_0 t$ into a time-independent static
     position $x(t) = v_0 t_0$ (`milneComovingCoord_static_of_hubblesLaw`), and that the
     effective gravitational coupling $G(\tau) = G_0 \exp((\tau - t_0)/t_0)$ equals
     $G_0 (t / t_0)$ (`milneGravitationalCoupling_eq_linear_dynamical`).

2. **Section 2 (Misner's Minisuperspace & Mixmaster Logarithmic Volume Time $\Omega = -\ln a$)**:
   - Defines `misnerOmega (a : ℝ) : ℝ := -Real.log a` and `misnerScaleFactor (Omega : ℝ) : ℝ := Real.exp (-Omega)`.
   - Proves mutual inversion for $a > 0$, additive logarithmic era composition
     `misnerScaleFactor_add` ($a(\Omega_1 + \Omega_2) = a(\Omega_1) a(\Omega_2)$), and the
     exact derivative law `hasDerivAt_misnerOmega` ($d\Omega / da = -a^{-1}$).

3. **Section 3 (Conformal Radial Quantization: Plane Dilatation $r \frac{d}{dr}$ as Cylinder Hamiltonian $\frac{d}{d\tau}$)**:
   - For any radial observable $f : \mathbb{R} \to \mathbb{R}$ differentiable at $r = e^\tau$,
     defines the radial Euler dilatation operator `radialDilatation f r := r * deriv f r` and
     the cylinder pullback `cylinderObservable f tau := f (Real.exp tau)`.
   - Proves the exact CFT radial-quantization intertwining identity
     `deriv_cylinderObservable_eq_radialDilatation`:
     $$\frac{d}{d\tau} (f(e^\tau)) = \big(r \frac{d f}{dr}\big)\Big|_{r = e^\tau}.$$

4. **Section 4 (Connes–Rovelli Modular Surprisal $K = -\ln \rho$, Mean Surprisal Entropy, and the First Law of Entanglement $\delta S = \beta \delta\langle E \rangle$)**:
   - Defines the pointwise modular surprisal `modularSurprisal (p : ℝ) : ℝ := -Real.log p`
     and the discrete Boltzmann–Gibbs entropy as the expectation value of surprisal
     `meanSurprisalEntropy ρ := ∑ i, ρ i * modularSurprisal (ρ i)`.
   - For a Gibbs canonical state $\rho_i = \exp(-\beta E_i) / Z$ ($Z > 0$), proves the exact
     state-level Connes–Rovelli decomposition
     `modularSurprisal_gibbsState` ($K_i(\rho) = \beta E_i + \ln Z$), the thermodynamic free-energy
     identity `meanSurprisalEntropy_gibbsState` ($S(\rho) = \beta \langle E \rangle_\rho + \ln Z$),
     and the **First Law of Entanglement** (`first_law_of_entanglement_gibbs`): for any
     trace-preserving perturbation $\sum_i \delta\rho_i = 0$,
     $$\sum_{i} \delta\rho_i \, K_i(\rho) = \beta \sum_{i} \delta\rho_i \, E_i.$$

5. **Section 5 (Bekenstein–Fisher Covariance of Surprisal Fluctuations & Softmax Attention Surprisal)**:
   - Defines the Bekenstein–Fisher surprisal variance / covariance functional
     `surprisalVariance ρ K := ∑ i, ρ i * (K i - expectedValue ρ K) ^ 2`.
   - Proves the exact second-moment decomposition
     `surprisalVariance_eq_second_moment_sub_sq` ($\operatorname{Var}_\rho(K) = \langle K^2 \rangle_\rho - \langle K \rangle_\rho^2$
     for $\sum_i \rho_i = 1$), non-negativity `surprisalVariance_nonneg`, and the exact
     attention softmax surprisal identity `attentionSoftmax_surprisal_eq`
     ($-\ln(e^{s_j} / Z) = -s_j + \ln Z$).
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset
open InfoGeometry.Synthesis.RecoveredPhysicalInvariantsSynthesis

namespace InfoGeometry.Synthesis.LogarithmicTimeVacuumSurprisalSynthesis

/-!
## Section 1: Milne's Two-Clock Kinematic Relativity
-/

/-- Inverse Milne dynamical (ephemeris) time $t(\tau) = t_0 \exp((\tau - t_0) / t_0)$
recovered from the atomic/kinematic logarithmic clock $\tau$. -/
def milneDynamicalTime (t₀ tau : ℝ) : ℝ :=
  t₀ * Real.exp ((tau - t₀) / t₀)

/-- **Theorem 1.1 (Exact Mutual Inversion Between Milne Kinematic Time $\tau$ and Dynamical Time $t$)**:
For $t_0 > 0$ and $t > 0$, `milneDynamicalTime` and `milneKinematicTime` are exact inverses:
$$t(\tau(t)) = t \quad \text{and} \quad \tau(t(\tau)) = \tau.$$ -/
theorem milne_two_clock_mutual_inversion (t₀ t tau : ℝ) (ht₀ : 0 < t₀) (ht : 0 < t) :
    milneDynamicalTime t₀ (milneKinematicTime t₀ t) = t ∧
    milneKinematicTime t₀ (milneDynamicalTime t₀ tau) = tau := by
  have ht₀_ne : t₀ ≠ 0 := ne_of_gt ht₀
  have h_quot_pos : 0 < t / t₀ := div_pos ht ht₀
  constructor
  · unfold milneDynamicalTime milneKinematicTime
    have h_simp : (t₀ * Real.log (t / t₀) + t₀ - t₀) / t₀ = Real.log (t / t₀) := by
      rw [add_sub_cancel_right, mul_div_cancel_left₀ _ ht₀_ne]
    rw [h_simp, Real.exp_log h_quot_pos, mul_div_cancel₀ _ ht₀_ne]
  · unfold milneKinematicTime milneDynamicalTime
    have h_div : t₀ * Real.exp ((tau - t₀) / t₀) / t₀ = Real.exp ((tau - t₀) / t₀) :=
      mul_div_cancel_left₀ _ ht₀_ne
    rw [h_div, Real.log_exp]
    field_simp [ht₀_ne]
    ring

/-- Milne comoving kinematic spatial coordinate $x(t, r) = (t_0 / t) r$. -/
def milneComovingCoord (t₀ t r : ℝ) : ℝ := (t₀ / t) * r

/-- **Theorem 1.2 (Elimination of Hubble Expansion in Milne Comoving Kinematic Coordinates)**:
A galaxy receding with uniform dynamical velocity $r(t) = v_0 t$ ($t \neq 0$) has a strictly
static comoving kinematic coordinate $x(t, v_0 t) = v_0 t_0$. -/
theorem milneComovingCoord_static_of_hubblesLaw (t₀ t v₀ : ℝ) (ht : t ≠ 0) :
    milneComovingCoord t₀ t (v₀ * t) = v₀ * t₀ := by
  unfold milneComovingCoord
  field_simp [ht]

/-- Secular drift of the effective gravitational coupling $G(\tau) = G_0 \exp((\tau - t_0) / t_0)$
in Milne kinematic time. -/
def milneGravitationalCoupling (G₀ t₀ tau : ℝ) : ℝ :=
  G₀ * Real.exp ((tau - t₀) / t₀)

/-- **Theorem 1.3 (Linear Dynamical Time Scaling of Milne's Gravitational Coupling $G(\tau(t)) = G_0 (t / t_0)$)**:
Evaluated at the kinematic time $\tau(t)$ corresponding to dynamical time $t > 0$ ($t_0 > 0$),
the exponential coupling drift reduces to the linear Dirac–Milne law $G(\tau(t)) = G_0 (t / t_0)$. -/
theorem milneGravitationalCoupling_eq_linear_dynamical
    (G₀ t₀ t : ℝ) (ht₀ : 0 < t₀) (ht : 0 < t) :
    milneGravitationalCoupling G₀ t₀ (milneKinematicTime t₀ t) = G₀ * (t / t₀) := by
  have ht₀_ne : t₀ ≠ 0 := ne_of_gt ht₀
  have h_quot_pos : 0 < t / t₀ := div_pos ht ht₀
  unfold milneGravitationalCoupling milneKinematicTime
  have h_simp : (t₀ * Real.log (t / t₀) + t₀ - t₀) / t₀ = Real.log (t / t₀) := by
    rw [add_sub_cancel_right, mul_div_cancel_left₀ _ ht₀_ne]
  rw [h_simp, Real.exp_log h_quot_pos]

/-!
## Section 2: Misner's Minisuperspace & Mixmaster Logarithmic Volume Time $\Omega = -\ln a$
-/

/-- Misner's logarithmic volume time $\Omega(a) = -\ln a$ mapping $a \to 0^+$ to $\Omega \to +\infty$. -/
def misnerOmega (a : ℝ) : ℝ := -Real.log a

/-- Spatial scale factor $a(\Omega) = e^{-\Omega}$ as a function of Misner time $\Omega$. -/
def misnerScaleFactor (Omega : ℝ) : ℝ := Real.exp (-Omega)

/-- **Theorem 2.1 (Misner Volume Time Inversion & Additive Kasner Era Multiplicativity)**:
1. For $a > 0$, $a(\Omega(a)) = a$ and $\Omega(a(\Omega)) = \Omega$.
2. Additive translations in Misner time $\Omega_1 + \Omega_2$ correspond to multiplicative
   contractions of the spatial scale factor: $a(\Omega_1 + \Omega_2) = a(\Omega_1) a(\Omega_2)$. -/
theorem misnerOmega_inversion_and_homomorphism (a Omega₁ Omega₂ : ℝ) (ha : 0 < a) :
    misnerScaleFactor (misnerOmega a) = a ∧
    misnerOmega (misnerScaleFactor Omega₁) = Omega₁ ∧
    misnerScaleFactor (Omega₁ + Omega₂) = misnerScaleFactor Omega₁ * misnerScaleFactor Omega₂ := by
  refine ⟨?_, ?_, ?_⟩
  · unfold misnerScaleFactor misnerOmega
    rw [neg_neg, Real.exp_log ha]
  · unfold misnerOmega misnerScaleFactor
    rw [Real.log_exp, neg_neg]
  · unfold misnerScaleFactor
    rw [neg_add, Real.exp_add]

/-- **Theorem 2.2 (Derivative of Misner Logarithmic Volume Time $d\Omega / da = -a^{-1}$)**:
For any $a \neq 0$, $\Omega(a) = -\ln a$ has derivative $-a^{-1}$. -/
theorem hasDerivAt_misnerOmega {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt misnerOmega (-a⁻¹) a := by
  unfold misnerOmega
  exact (Real.hasDerivAt_log ha).neg

/-!
## Section 3: Conformal Radial Quantization ($r \frac{d}{dr} \leftrightarrow \frac{d}{d\tau}$)
-/

/-- Radial Euler dilatation operator $(D_{\mathrm{rad}} f)(r) = r f'(r)$ on the plane. -/
def radialDilatation (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * deriv f r

/-- Cylinder pullback $(f \circ \exp)(\tau) = f(e^\tau)$ under the conformal map $r = e^\tau$. -/
def cylinderObservable (f : ℝ → ℝ) (tau : ℝ) : ℝ :=
  f (Real.exp tau)

/-- **Theorem 3.1 (Radial Quantization Intertwining: Cylinder Hamiltonian $\frac{d}{d\tau}$ Equals Planar Dilatation $r \frac{d}{dr}$)**:
For any observable $f : \mathbb{R} \to \mathbb{R}$ differentiable at $r = e^\tau$,
$$\frac{d}{d\tau}\big(f(e^\tau)\big) = (D_{\mathrm{rad}} f)(e^\tau) = e^\tau f'(e^\tau).$$ -/
theorem hasDerivAt_cylinderObservable_eq_radialDilatation
    (f : ℝ → ℝ) (tau : ℝ) (hf : DifferentiableAt ℝ f (Real.exp tau)) :
    HasDerivAt (cylinderObservable f) (radialDilatation f (Real.exp tau)) tau ∧
    deriv (cylinderObservable f) tau = radialDilatation f (Real.exp tau) := by
  have h_chain : HasDerivAt (cylinderObservable f) (deriv f (Real.exp tau) * Real.exp tau) tau :=
    HasDerivAt.comp tau hf.hasDerivAt (Real.hasDerivAt_exp tau)
  have h_comm : deriv f (Real.exp tau) * Real.exp tau = radialDilatation f (Real.exp tau) := by
    unfold radialDilatation
    ring
  rw [h_comm] at h_chain
  exact ⟨h_chain, h_chain.deriv⟩

/-!
## Section 4: Connes–Rovelli Modular Surprisal $K = -\ln \rho$ & The First Law of Entanglement
-/

/-- Pointwise self-information / modular surprisal $I(p) = -\ln p$. -/
def modularSurprisal (p : ℝ) : ℝ := -Real.log p

/-- Finite-state Boltzmann–Gibbs entropy defined as the expectation value of modular surprisal:
$$S(\rho) = \sum_{i} \rho_i \, K_i(\rho) = -\sum_{i} \rho_i \ln \rho_i.$$ -/
def meanSurprisalEntropy {n : ℕ} (ρ : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ρ i * modularSurprisal (ρ i)

/-- Finite-state expectation value $\langle O \rangle_\rho = \sum_i \rho_i O_i$. -/
def expectedObservable {n : ℕ} (ρ O : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ρ i * O i

/-- Canonical Gibbs thermal state $\rho_i = \exp(-\beta E_i) / Z$. -/
def gibbsState {n : ℕ} (beta Z : ℝ) (E : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (-beta * E i) / Z

/-- **Theorem 4.1 (Connes–Rovelli Thermal Surprisal Decomposition $K_i(\rho) = \beta E_i + \ln Z$)**:
For a Gibbs state $\rho_i = e^{-\beta E_i} / Z$ with partition function $Z > 0$, the modular
surprisal at state $i$ is exactly $\beta E_i + \ln Z$. -/
theorem modularSurprisal_gibbsState {n : ℕ} (beta Z : ℝ) (E : Fin n → ℝ)
    (hZ : 0 < Z) (i : Fin n) :
    modularSurprisal (gibbsState beta Z E i) = beta * E i + Real.log Z := by
  have h_exp_ne : Real.exp (-beta * E i) ≠ 0 := Real.exp_ne_zero (-beta * E i)
  have hZ_ne : Z ≠ 0 := ne_of_gt hZ
  unfold modularSurprisal gibbsState
  rw [Real.log_div h_exp_ne hZ_ne, Real.log_exp]
  ring

/-- **Theorem 4.2 (Thermodynamic Entropy–Energy–Free-Energy Identity $S(\rho) = \beta \langle E \rangle_\rho + \ln Z$)**:
For any normalized state $\rho$ ($\sum_i \rho_i = 1$) whose modular surprisal equals that of a
Gibbs ensemble with $Z > 0$, the mean surprisal entropy satisfies
$$S(\rho) = \beta \langle E \rangle_\rho + \ln Z.$$ -/
theorem meanSurprisalEntropy_gibbsState {n : ℕ} (beta Z : ℝ) (E : Fin n → ℝ)
    (hZ : 0 < Z) (h_norm : ∑ i : Fin n, gibbsState beta Z E i = 1) :
    meanSurprisalEntropy (gibbsState beta Z E) =
      beta * expectedObservable (gibbsState beta Z E) E + Real.log Z := by
  unfold meanSurprisalEntropy expectedObservable
  have h_pointwise :
      ∀ i : Fin n,
        gibbsState beta Z E i * modularSurprisal (gibbsState beta Z E i) =
          beta * (gibbsState beta Z E i * E i) + gibbsState beta Z E i * Real.log Z := by
    intro i
    rw [modularSurprisal_gibbsState beta Z E hZ i]
    ring
  calc
    ∑ i : Fin n, gibbsState beta Z E i * modularSurprisal (gibbsState beta Z E i)
        = ∑ i : Fin n, (beta * (gibbsState beta Z E i * E i) + gibbsState beta Z E i * Real.log Z) := by
          apply Finset.sum_congr rfl
          intro i _
          exact h_pointwise i
    _ = beta * (∑ i : Fin n, gibbsState beta Z E i * E i) +
          (∑ i : Fin n, gibbsState beta Z E i) * Real.log Z := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    _ = beta * (∑ i : Fin n, gibbsState beta Z E i * E i) + Real.log Z := by
          rw [h_norm, one_mul]

/-- **Theorem 4.3 (The First Law of Entanglement $\delta S = \delta \langle K \rangle = \beta \, \delta \langle E \rangle$)**:
For any probability-preserving deformation $\delta\rho : \mathrm{Fin}\ n \to \mathbb{R}$
satisfying $\sum_{i} \delta\rho_i = 0$ around a Gibbs vacuum/thermal state ($Z > 0$), the
partition-function constant $\ln Z$ cancels identically, yielding the exact Clausius/Bisognano–Wichmann
entanglement first law:
$$\sum_{i} \delta\rho_i \, K_i(\rho) = \beta \sum_{i} \delta\rho_i \, E_i.$$ -/
theorem first_law_of_entanglement_gibbs {n : ℕ} (beta Z : ℝ) (E deltaRho : Fin n → ℝ)
    (hZ : 0 < Z) (h_trace_zero : ∑ i : Fin n, deltaRho i = 0) :
    (∑ i : Fin n, deltaRho i * modularSurprisal (gibbsState beta Z E i)) =
      beta * (∑ i : Fin n, deltaRho i * E i) := by
  have h_pointwise :
      ∀ i : Fin n,
        deltaRho i * modularSurprisal (gibbsState beta Z E i) =
          beta * (deltaRho i * E i) + deltaRho i * Real.log Z := by
    intro i
    rw [modularSurprisal_gibbsState beta Z E hZ i]
    ring
  calc
    ∑ i : Fin n, deltaRho i * modularSurprisal (gibbsState beta Z E i)
        = ∑ i : Fin n, (beta * (deltaRho i * E i) + deltaRho i * Real.log Z) := by
          apply Finset.sum_congr rfl
          intro i _
          exact h_pointwise i
    _ = beta * (∑ i : Fin n, deltaRho i * E i) + (∑ i : Fin n, deltaRho i) * Real.log Z := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    _ = beta * (∑ i : Fin n, deltaRho i * E i) := by
          rw [h_trace_zero, zero_mul, add_zero]

/-!
## Section 5: Bekenstein–Fisher Covariance of Surprisal Fluctuations & Attention Softmax Surprisal
-/

/-- Bekenstein–Fisher metric / variance of modular surprisal fluctuations:
$$\operatorname{Var}_\rho(K) = \sum_{i} \rho_i \big(K_i - \langle K \rangle_\rho\big)^2.$$ -/
def surprisalVariance {n : ℕ} (ρ K : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ρ i * (K i - expectedObservable ρ K) ^ 2

/-- **Theorem 5.1 (Bekenstein–Fisher Surprisal Variance Decomposition & Non-Negativity)**:
1. For any normalized state $\sum_i \rho_i = 1$, the variance of surprisal fluctuations equals
   both the Riesz natural-gradient dissipation pairing $\sum_i K_i (\mathrm{grad}_{\mathrm{Riesz}} K)_i$
   and the second-moment cumulant $\langle K^2 \rangle_\rho - \langle K \rangle_\rho^2$.
2. If $\rho_i \ge 0$ for all $i$, then $\operatorname{Var}_\rho(K) \ge 0$. -/
theorem surprisalVariance_riesz_and_cumulant_identities {n : ℕ} (ρ K : Fin n → ℝ)
    (h_sum : ∑ i : Fin n, ρ i = 1) (h_nonneg : ∀ i : Fin n, 0 ≤ ρ i) :
    (∑ i : Fin n, K i * rieszNaturalGradient ρ K i) = surprisalVariance ρ K ∧
    surprisalVariance ρ K = (∑ i : Fin n, ρ i * K i ^ 2) - (expectedObservable ρ K) ^ 2 ∧
    0 ≤ surprisalVariance ρ K := by
  have h_riesz : (∑ i : Fin n, K i * rieszNaturalGradient ρ K i) = surprisalVariance ρ K :=
    rieszNaturalGradient_pairing_eq_variance ρ K h_sum
  have h_cumulant :
      surprisalVariance ρ K = (∑ i : Fin n, ρ i * K i ^ 2) - (expectedObservable ρ K) ^ 2 := by
    rw [← h_riesz]
    unfold rieszNaturalGradient expectedObservable
    have h_pt :
        ∀ i : Fin n,
          K i * (ρ i * (K i - ∑ j : Fin n, ρ j * K j)) =
            ρ i * K i ^ 2 - (ρ i * K i) * (∑ j : Fin n, ρ j * K j) := by
      intro i
      ring
    calc
      ∑ i : Fin n, K i * (ρ i * (K i - ∑ j : Fin n, ρ j * K j))
          = ∑ i : Fin n, (ρ i * K i ^ 2 - (ρ i * K i) * (∑ j : Fin n, ρ j * K j)) := by
            apply Finset.sum_congr rfl
            intro i _
            exact h_pt i
      _ = (∑ i : Fin n, ρ i * K i ^ 2) -
            (∑ i : Fin n, ρ i * K i) * (∑ j : Fin n, ρ j * K j) := by
            rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      _ = (∑ i : Fin n, ρ i * K i ^ 2) - (∑ i : Fin n, ρ i * K i) ^ 2 := by
            ring
  have h_pos : 0 ≤ surprisalVariance ρ K := by
    rw [← h_riesz]
    exact rieszNaturalGradient_dissipation_nonneg ρ K h_sum h_nonneg
  exact ⟨h_riesz, h_cumulant, h_pos⟩

/-- Attention softmax weight $A_{ij} = \exp(s_j) / Z$ for logit score $s_j$ and partition function $Z$. -/
def attentionSoftmaxWeight (Z : ℝ) (s : ℝ) : ℝ :=
  Real.exp s / Z

/-- **Theorem 5.2 (Attention Softmax as Modular Surprisal $-\ln A_{ij} = -s_j + \ln Z$)**:
For any partition function $Z > 0$ and logit score $s_j \in \mathbb{R}$, the modular surprisal
of the attention weight $A_{ij} = e^{s_j} / Z$ equals $-s_j + \ln Z$, identifying the log-partition
function $\Phi = \ln Z$ as the local conformal modular potential. -/
theorem attentionSoftmax_surprisal_eq (Z s : ℝ) (hZ : 0 < Z) :
    modularSurprisal (attentionSoftmaxWeight Z s) = -s + Real.log Z := by
  have h_exp_ne : Real.exp s ≠ 0 := Real.exp_ne_zero s
  have hZ_ne : Z ≠ 0 := ne_of_gt hZ
  unfold modularSurprisal attentionSoftmaxWeight
  rw [Real.log_div h_exp_ne hZ_ne, Real.log_exp]
  ring

end InfoGeometry.Synthesis.LogarithmicTimeVacuumSurprisalSynthesis
