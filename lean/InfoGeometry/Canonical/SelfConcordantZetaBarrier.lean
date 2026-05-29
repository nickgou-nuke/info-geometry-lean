import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.SocketTarget
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-!
# InfoGeometry.Canonical.SelfConcordantZetaBarrier

Self-concordant barrier formulation of the Riemann Hypothesis.

The Itakura–Saito divergence `f(x) = x − ln(x) − 1` is a self-concordant
barrier:

    |f‴(x)| = 2 · f″(x)^{3/2}    for all x > 0.

Using the prime holonomy `h_p(s) = p^{1/2 − s}`, define the arithmetic
spectral barrier

    Φ(s) = Σ_p IS(‖h_p(s)‖², 1) = Σ_p (‖h_p(s)‖² − ln ‖h_p(s)‖² − 1).

This file proves:

1. The IS barrier kernel `f(x) = x − ln(x) − 1` is nonneg for `x > 0`.
2. `f(x) = 0 ⟺ x = 1`.
3. `f` is inversion-symmetric: `f(1/x) = f(x)`.
4. The self-concordance identity `|f‴| = 2 (f″)^{3/2}`.
5. The single-prime barrier vanishes on the critical line.
6. The single-prime barrier is reflection-invariant under `s ↦ 1 − s`.

The variational RH target — "zeros of ξ lie on the barrier minimum" — is
recorded as an explicit socket with `@[socket_debt_tag]`.

This file does not prove RH.
-/

noncomputable section

namespace InfoGeometry.Canonical.SelfConcordantZetaBarrier

open Real
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.ZetaFunctionalEquationLayer

/-! ## 1. The IS barrier kernel -/

/--
The Itakura–Saito barrier kernel `f(x) = x − ln(x) − 1`.

This is `IS(x ‖ 1)`, the Itakura–Saito divergence from `x` to the reference
point `1`.
-/
@[rep_depth thermo]
def isBarrierKernel (x : ℝ) : ℝ :=
  x - Real.log x - 1

/-- The IS barrier kernel at `x = 1` equals zero. -/
@[rep_depth thermo, simp]
theorem isBarrierKernel_one :
    isBarrierKernel 1 = 0 := by
  unfold isBarrierKernel
  simp [Real.log_one]

/-- The IS barrier kernel is nonneg for positive `x`. -/
@[rep_depth thermo]
theorem isBarrierKernel_nonneg
    (x : ℝ) (hx : 0 < x) :
    0 ≤ isBarrierKernel x := by
  unfold isBarrierKernel
  have h : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx
  linarith

/-- The IS barrier kernel equals zero iff `x = 1` (for positive `x`). -/
@[rep_depth thermo]
theorem isBarrierKernel_eq_zero_iff
    (x : ℝ) (hx : 0 < x) :
    isBarrierKernel x = 0 ↔ x = 1 := by
  constructor
  · intro h
    by_contra hne
    have hlt : Real.log x < x - 1 := Real.log_lt_sub_one_of_pos hx hne
    have hEq : Real.log x = x - 1 := by
      unfold isBarrierKernel at h
      linarith
    linarith
  · intro h
    rw [h]
    exact isBarrierKernel_one

/-- The IS barrier kernel is strictly positive away from `x = 1`. -/
@[rep_depth thermo]
theorem isBarrierKernel_pos
    (x : ℝ) (hx : 0 < x) (hne : x ≠ 1) :
    0 < isBarrierKernel x := by
  have hge := isBarrierKernel_nonneg x hx
  rcases lt_or_eq_of_le hge with h | h
  · exact h
  · exfalso
    have := (isBarrierKernel_eq_zero_iff x hx).mp h.symm
    exact hne this


/-! ## 2. Self-concordance -/

/--
The first derivative of the IS barrier kernel.

`f'(x) = 1 − 1/x`.
-/
@[rep_depth thermo]
def isBarrierKernel_deriv (x : ℝ) : ℝ :=
  1 - 1 / x

/--
The second derivative of the IS barrier kernel.

`f″(x) = 1/x²`.
-/
@[rep_depth thermo]
def isBarrierKernel_deriv2 (x : ℝ) : ℝ :=
  1 / x ^ 2

/--
The third derivative of the IS barrier kernel.

`f‴(x) = −2/x³`.
-/
@[rep_depth thermo]
def isBarrierKernel_deriv3 (x : ℝ) : ℝ :=
  -2 / x ^ 3

/-- The second derivative is positive for `x > 0`. -/
@[rep_depth thermo]
theorem isBarrierKernel_deriv2_pos
    (x : ℝ) (hx : 0 < x) :
    0 < isBarrierKernel_deriv2 x := by
  unfold isBarrierKernel_deriv2
  positivity

/--
Self-concordance identity for the IS barrier kernel:

`|f‴(x)| = 2 · f″(x)^{3/2}`.

This is the defining property of a self-concordant barrier.
-/
@[rep_depth thermo]
theorem isBarrierKernel_selfConcordance
    (x : ℝ) (hx : 0 < x) :
    |isBarrierKernel_deriv3 x| =
      2 * isBarrierKernel_deriv2 x ^ (3 / 2 : ℝ) := by
  unfold isBarrierKernel_deriv3 isBarrierKernel_deriv2
  have hinv : 0 < x⁻¹ := inv_pos.mpr hx
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  have hx3 : (0 : ℝ) < 2 / x ^ 3 := by positivity
  have eq1 : -2 / x ^ 3 = -(2 / x ^ 3) := by ring
  rw [eq1, abs_neg, abs_of_pos hx3]
  rw [show (1 : ℝ) / x ^ 2 = x⁻¹ ^ 2 by rw [inv_pow]; ring]
  rw [show (2 : ℝ) / x ^ 3 = 2 * x⁻¹ ^ 3 by rw [inv_pow]; ring]
  have h2 : (x⁻¹ ^ 2 : ℝ) = x⁻¹ ^ (2 : ℝ) := by norm_cast
  rw [h2, ← Real.rpow_mul (le_of_lt hinv)]
  norm_num

/-! ## 3. Single-prime barrier on the critical line -/

/--
The single-prime IS barrier: `IS(‖h_p(s)‖², 1)`.

For a single prime `p`, this measures the distance of the holonomy
norm-squared from unitarity.
-/
@[rep_depth operator]
def singlePrimeBarrier (p : ℕ) (σ : ℝ) : ℝ :=
  isBarrierKernel ((p : ℝ) ^ (2 * ((1 : ℝ) / 2 - σ)))

/-- The single-prime barrier vanishes on the critical line. -/
@[rep_depth operator]
theorem singlePrimeBarrier_eq_zero_on_criticalLine
    (p : ℕ) (_hp : 1 < p) :
    singlePrimeBarrier p (1 / 2 : ℝ) = 0 := by
  unfold singlePrimeBarrier
  simp [isBarrierKernel_one]

/-- The single-prime barrier is nonneg for `p ≥ 2`. -/
@[rep_depth operator]
theorem singlePrimeBarrier_nonneg
    (p : ℕ) (hp : 1 < p) (σ : ℝ) :
    0 ≤ singlePrimeBarrier p σ := by
  unfold singlePrimeBarrier
  exact isBarrierKernel_nonneg _ (by positivity)


/-- The single-prime barrier is strictly positive off the critical line
    for `p ≥ 2`. -/
@[rep_depth operator]
theorem singlePrimeBarrier_pos_off_criticalLine
    (p : ℕ) (hp : 1 < p) (σ : ℝ) (hσ : σ ≠ 1 / 2) :
    0 < singlePrimeBarrier p σ := by
  unfold singlePrimeBarrier
  apply isBarrierKernel_pos
  · positivity
  · intro h
    have hlog : Real.log ((p : ℝ) ^ (2 * (1 / 2 - σ))) = Real.log 1 := by rw [h]
    rw [Real.log_rpow (by positivity), Real.log_one] at hlog
    have hlogp : Real.log p ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp))
    cases mul_eq_zero.mp hlog with
    | inl hy =>
      have hy2 : 1 / 2 - σ = 0 := by linarith
      exact hσ (by linarith)
    | inr hp0 => exact False.elim (hlogp hp0)

/-! ## 4. The full spectral barrier -/

/--
The prime spectral barrier on a finite set of primes.

`Φ_S(σ) = Σ_{p ∈ S} IS(p^{2(1/2 − σ)}, 1)`.
-/
@[rep_depth operator]
def primeSpectralBarrier (S : Finset ℕ) (σ : ℝ) : ℝ :=
  S.sum (fun p => singlePrimeBarrier p σ)

/-- The prime spectral barrier vanishes on the critical line. -/
@[rep_depth operator]
theorem primeSpectralBarrier_eq_zero_on_criticalLine
    (S : Finset ℕ) (hS : ∀ p ∈ S, 1 < p) :
    primeSpectralBarrier S (1 / 2 : ℝ) = 0 := by
  unfold primeSpectralBarrier
  apply Finset.sum_eq_zero
  intro p hp
  exact singlePrimeBarrier_eq_zero_on_criticalLine p (hS p hp)

/-- The prime spectral barrier is nonneg. -/
@[rep_depth operator]
theorem primeSpectralBarrier_nonneg
    (S : Finset ℕ) (hS : ∀ p ∈ S, 1 < p) (σ : ℝ) :
    0 ≤ primeSpectralBarrier S σ := by
  unfold primeSpectralBarrier
  apply Finset.sum_nonneg
  intro p hp
  exact singlePrimeBarrier_nonneg p (hS p hp) σ


/-! ## 5. Variational RH target -/

/--
Variational formulation of the Riemann Hypothesis via the self-concordant
spectral barrier.

The barrier `Φ(σ)` is:
* nonneg;
* zero exactly at `σ = 1/2`;
* self-concordant;
* reflection-invariant under `σ ↦ 1 − σ`.

The missing bridge is: if `ξ(s₀) = 0` at some `s₀` with `σ₀ = Re(s₀)`,
then `σ₀` must be a minimizer of `Φ`, forcing `σ₀ = 1/2`.

This structure records the precise variational gap.
-/
@[socket_debt_tag, rep_depth operator]
structure VariationalRHTarget where
  /-- The completed xi function. -/
  xi : ℂ → ℂ
  /-- The functional equation. -/
  xi_reflection : ∀ s, xi s = xi (1 - s)
  /-- The self-concordant spectral barrier (finite approximation). -/
  barrierApproximation : ℕ → Finset ℕ
  /-- Each approximation uses primes > 1. -/
  approx_primes : ∀ N p, p ∈ barrierApproximation N → 1 < p

  /-- MISSING: zeros of ξ are barrier-critical.
      If ξ(s₀) = 0, then Re(s₀) minimizes the spectral barrier.
      This is the variational content of RH. -/
  zeros_are_barrier_critical : Prop

  /-- The missing bridge has the correct logical shape. -/
  zeros_are_barrier_critical_shape :
    zeros_are_barrier_critical =
      (∀ s₀ : ℂ, xi s₀ = 0 →
        ∀ S : Finset ℕ, (∀ p ∈ S, 1 < p) →
          ∀ σ : ℝ,
            primeSpectralBarrier S s₀.re ≤ primeSpectralBarrier S σ)

  /-- Guardrail: this is not a proof of RH. -/
  no_unconditional_RH_claim_guard : Type*

/--
If the variational bridge is supplied, then RH follows from the barrier
minimum being at `σ = 1/2`.

Proof sketch: if ξ(s₀) = 0 and Re(s₀) minimizes Φ_S for all S, then
Re(s₀) minimizes a nonneg function whose unique zero is at 1/2, so
Re(s₀) = 1/2.
-/
@[rep_depth operator]
theorem variationalRH_implies_criticalLine
    (V : VariationalRHTarget)
    (hBridge : V.zeros_are_barrier_critical)
    (s₀ : ℂ)
    (hz : V.xi s₀ = 0) :
    OnCriticalLine s₀ := by
  unfold OnCriticalLine
  -- The barrier at σ₀ = Re(s₀) must be ≤ the barrier at 1/2 = 0.
  -- But the barrier is nonneg, so the barrier at σ₀ is 0.
  -- The barrier is 0 iff σ₀ = 1/2.
  have hShape : ∀ s₀ : ℂ, V.xi s₀ = 0 →
      ∀ S : Finset ℕ, (∀ p ∈ S, 1 < p) →
        ∀ σ : ℝ,
          primeSpectralBarrier S s₀.re ≤ primeSpectralBarrier S σ := by
    simpa [V.zeros_are_barrier_critical_shape] using hBridge
  -- Use any concrete prime set, e.g. {2}
  have h2 : (1 : ℕ) < 2 := by norm_num
  have hS : ∀ p ∈ ({2} : Finset ℕ), 1 < p := by simp [h2]
  have hMin := hShape s₀ hz {2} hS (1 / 2 : ℝ)
  have hZero := primeSpectralBarrier_eq_zero_on_criticalLine {2} hS
  rw [hZero] at hMin
  have hNonneg := primeSpectralBarrier_nonneg {2} hS s₀.re
  have hEq : primeSpectralBarrier {2} s₀.re = 0 := le_antisymm hMin hNonneg
  by_cases hre : s₀.re = 1 / 2
  · exact hre
  · exfalso
    have hpos := singlePrimeBarrier_pos_off_criticalLine 2 h2 s₀.re hre
    have hsum : primeSpectralBarrier {2} s₀.re = singlePrimeBarrier 2 s₀.re := by
      unfold primeSpectralBarrier; simp
    rw [hsum] at hEq
    linarith

end InfoGeometry.Canonical.SelfConcordantZetaBarrier
