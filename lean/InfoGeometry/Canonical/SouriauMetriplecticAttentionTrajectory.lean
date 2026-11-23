/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Star
import InfoGeometry.Canonical.SouriauMetriplecticAttentionCasimirPoset

/-!
# Trajectory-level Souriau metriplectic theorems in a noncommutative normed algebra

Carrier: an arbitrary (noncommutative) normed `ℝ`-algebra `B`
(`[NormedRing B] [NormedAlgebra ℝ B]`), with a continuous linear cyclic functional
`τ : B →L[ℝ] ℝ`. A trajectory is any `w : ℝ → B` with
`HasDerivAt w (brockettSouriauWeightFlow Ω H (w t)) t` for all `t`.

* `hasDerivAt_pow_powDeriv` – noncommutative chain rule: `d/dt (w t)^k = powDeriv (w t) (w' t) k`.
* `trajectory_moments_conserved` – every spectral moment `t ↦ τ (w t ^ k)` is constant.
* `trajectory_lyapunov_monotone` – with `[StarRing B]`, positive `τ`, `[Ω, H] = 0`,
  `H` self-adjoint and `w t` self-adjoint for all `t`: `t ↦ τ (w t * H)` is monotone.
* `conj_exp_solves_flow`, `conj_exp_moments_conserved` – in a complete algebra, the
  noncommutative conjugation orbit `w t = exp (t Ω) W₀ exp (-t Ω)` is an explicit solution of
  the Hamiltonian (`H = 0`) flow, so the trajectory hypothesis is satisfiable.

* `trajectory_star_self` – for skew-adjoint `Ω` and self-adjoint `H`, self-adjointness at one
  time propagates to all times (local ODE uniqueness + connectedness of `ℝ`);
  `trajectory_lyapunov_monotone_of_initial` uses only `w 0` self-adjoint.

Existence of solutions for `H ≠ 0` is not proved here.
-/

namespace SouriauMetriplecticAttentionCasimirPoset.Trajectory

open NormedSpace Filter Topology

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]

/-- Noncommutative chain rule for powers: the derivative of `s ↦ w s ^ k` is the
Leibniz expansion `powDeriv (w t) w' k = Σ_{i<k} W^i w' W^(k-1-i)`. -/
theorem hasDerivAt_pow_powDeriv {w : ℝ → B} {w' : B} {t : ℝ} (hw : HasDerivAt w w' t)
    (k : ℕ) : HasDerivAt (fun s => w s ^ k) (powDeriv (w t) w' k) t := by
  induction k with
  | zero =>
    simp only [pow_zero]
    exact hasDerivAt_const t (1 : B)
  | succ k ih =>
    simp only [pow_succ']
    exact hw.mul ih

/-- **Isospectrality along trajectories**: every spectral moment `τ (w t ^ k)` is constant
in time along any solution of the Brockett–Souriau flow. -/
theorem trajectory_moments_conserved (τ : B →L[ℝ] ℝ)
    (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x)) (Ω H : B) (w : ℝ → B)
    (hw : ∀ t, HasDerivAt w (brockettSouriauWeightFlow Ω H (w t)) t) (k : ℕ) (s t : ℝ) :
    τ (w s ^ k) = τ (w t ^ k) := by
  have hd : ∀ u, HasDerivAt (fun r => τ (w r ^ k)) 0 u := by
    intro u
    have h := τ.hasFDerivAt.comp_hasDerivAt u (hasDerivAt_pow_powDeriv (hw u) k)
    have h0 : τ (powDeriv (w u) (brockettSouriauWeightFlow Ω H (w u)) k) = 0 :=
      brockett_souriau_all_moments_conserved (τ : B →ₗ[ℝ] ℝ).toAddMonoidHom h_cyc Ω H (w u) k
    rw [h0] at h
    exact h
  exact is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) s t

/-- **Lyapunov monotonicity along trajectories**: if `[Ω, H] = 0`, `H` is self-adjoint, `τ` is
positive and the trajectory stays self-adjoint, then `t ↦ τ (w t * H)` is monotone. -/
theorem trajectory_lyapunov_monotone [StarRing B] (τ : B →L[ℝ] ℝ)
    (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (hpos : ∀ Y : B, 0 ≤ τ (star Y * Y))
    (Ω H : B) (hΩH : comm Ω H = 0) (hH : star H = H) (w : ℝ → B)
    (hw : ∀ t, HasDerivAt w (brockettSouriauWeightFlow Ω H (w t)) t)
    (hself : ∀ t, star (w t) = w t) :
    Monotone (fun t => τ (w t * H)) := by
  have hd : ∀ u, HasDerivAt (fun r => τ (w r * H))
      (τ (brockettSouriauWeightFlow Ω H (w u) * H)) u := fun u =>
    τ.hasFDerivAt.comp_hasDerivAt u ((hw u).mul_const H)
  apply monotone_of_deriv_nonneg (fun u => (hd u).differentiableAt)
  intro u
  rw [(hd u).deriv]
  exact brockett_souriau_rate_nonneg (τ : B →ₗ[ℝ] ℝ).toAddMonoidHom h_cyc hpos Ω H (w u)
    hΩH hH (hself u)

/-- The Brockett–Souriau vector field is `C¹` (it is a cubic polynomial in `W`). -/
lemma brockettSouriauWeightFlow_contDiff (Ω H : B) :
    ContDiff ℝ 1 (brockettSouriauWeightFlow Ω H) := by
  have hF : brockettSouriauWeightFlow Ω H =
      fun W => Ω * W - W * Ω + (W * (W * H - H * W) - (W * H - H * W) * W) := rfl
  rw [hF]
  fun_prop

/-- **Self-adjointness is preserved along trajectories.** If `Ω` is skew-adjoint, `H` is
self-adjoint and `w t₀` is self-adjoint at one time, then `w t` is self-adjoint for all `t`.
Proof: `t ↦ (w t)⋆` is another solution (`brockettSouriauWeightFlow_star`); the vector field is
locally Lipschitz (`C¹`), so local ODE uniqueness makes `{t | (w t)⋆ = w t}` open; it is closed
by continuity and nonempty, hence all of `ℝ`. -/
theorem trajectory_star_self [StarRing B] [StarModule ℝ B] [ContinuousStar B]
    {Ω H : B} (hΩ : star Ω = -Ω) (hH : star H = H) (w : ℝ → B)
    (hw : ∀ t, HasDerivAt w (brockettSouriauWeightFlow Ω H (w t)) t)
    (t₀ : ℝ) (h0 : star (w t₀) = w t₀) (t : ℝ) : star (w t) = w t := by
  have hws : ∀ u, HasDerivAt (fun s => star (w s))
      (brockettSouriauWeightFlow Ω H (star (w u))) u := by
    intro u
    have h := (hw u).star
    rwa [brockettSouriauWeightFlow_star hΩ hH] at h
  have hcont : Continuous w := continuous_iff_continuousAt.2 fun u => (hw u).continuousAt
  have hscont : Continuous (fun s => star (w s)) := continuous_star.comp hcont
  have hclosed : IsClosed {u | star (w u) = w u} := isClosed_eq hscont hcont
  have hopen : IsOpen {u | star (w u) = w u} := by
    rw [isOpen_iff_mem_nhds]
    intro t₁ ht₁
    have ht₁' : star (w t₁) = w t₁ := ht₁
    obtain ⟨K, U, hU, hLip⟩ :=
      ((brockettSouriauWeightFlow_contDiff Ω H).contDiffAt (x := w t₁)).exists_lipschitzOnWith
    have hwU : ∀ᶠ u in 𝓝 t₁, w u ∈ U := hcont.continuousAt.preimage_mem_nhds hU
    have hsU : ∀ᶠ u in 𝓝 t₁, star (w u) ∈ U := by
      have hU' : U ∈ 𝓝 (star (w t₁)) := by rw [ht₁']; exact hU
      exact hscont.continuousAt.preimage_mem_nhds hU'
    have heq := ODE_solution_unique_of_eventually (v := fun _ => brockettSouriauWeightFlow Ω H)
      (s := fun _ => U) (Filter.Eventually.of_forall fun _ => hLip)
      (hsU.mono fun u hu => ⟨hws u, hu⟩) (hwU.mono fun u hu => ⟨hw u, hu⟩) ht₁'
    exact heq
  have hS : {u | star (w u) = w u} = Set.univ :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨t₀, h0⟩
  have ht : t ∈ {u | star (w u) = w u} := hS ▸ Set.mem_univ t
  exact ht

/-- **Lyapunov monotonicity from initial data only**: if `Ω` is skew-adjoint and commutes
with the self-adjoint energy `H`, `τ` is positive, and `w 0` is self-adjoint, then
`t ↦ τ (w t * H)` is monotone along any trajectory. -/
theorem trajectory_lyapunov_monotone_of_initial [StarRing B] [StarModule ℝ B]
    [ContinuousStar B] (τ : B →L[ℝ] ℝ)
    (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (hpos : ∀ Y : B, 0 ≤ τ (star Y * Y))
    (Ω H : B) (hΩ : star Ω = -Ω) (hΩH : comm Ω H = 0) (hH : star H = H) (w : ℝ → B)
    (hw : ∀ t, HasDerivAt w (brockettSouriauWeightFlow Ω H (w t)) t)
    (h0 : star (w 0) = w 0) :
    Monotone (fun t => τ (w t * H)) := by
  have hself : ∀ t, star (w t) = w t :=
    fun t => trajectory_star_self hΩ hH w hw 0 h0 t
  have hd : ∀ u, HasDerivAt (fun r => τ (w r * H))
      (τ (brockettSouriauWeightFlow Ω H (w u) * H)) u := fun u =>
    τ.hasFDerivAt.comp_hasDerivAt u ((hw u).mul_const H)
  apply monotone_of_deriv_nonneg (fun u => (hd u).differentiableAt)
  intro u
  rw [(hd u).deriv]
  exact brockett_souriau_rate_nonneg (τ : B →ₗ[ℝ] ℝ).toAddMonoidHom h_cyc hpos Ω H (w u)
    hΩH hH (hself u)

variable [CompleteSpace B]

/-- The conjugation orbit `exp (t Ω) W₀ exp (-t Ω)` has derivative `[Ω, w t]`. -/
theorem conj_exp_hasDerivAt (Ω W₀ : B) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • Ω) * W₀ * exp (s • (-Ω)))
      (comm Ω (exp (t • Ω) * W₀ * exp (t • (-Ω)))) t := by
  have h1 := (hasDerivAt_exp_smul_const' Ω t).mul_const W₀
  have h2 := hasDerivAt_exp_smul_const (-Ω) t
  convert h1.mul h2 using 1
  simp only [comm]
  noncomm_ring

/-- **Explicit noncommutative solution**: the conjugation orbit solves the zero-energy
Brockett–Souriau flow. -/
theorem conj_exp_solves_flow (Ω W₀ : B) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • Ω) * W₀ * exp (s • (-Ω)))
      (brockettSouriauWeightFlow Ω 0 (exp (t • Ω) * W₀ * exp (t • (-Ω)))) t := by
  rw [brockettSouriauWeightFlow_zero_energy]
  exact conj_exp_hasDerivAt Ω W₀ t

/-- Spectral moments of `W₀` are preserved along the conjugation orbit, obtained from the
trajectory theorem applied to this explicit solution. -/
theorem conj_exp_moments_conserved (τ : B →L[ℝ] ℝ)
    (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x)) (Ω W₀ : B) (k : ℕ) (t : ℝ) :
    τ ((exp (t • Ω) * W₀ * exp (t • (-Ω))) ^ k) = τ (W₀ ^ k) := by
  have h := trajectory_moments_conserved τ h_cyc Ω 0 _ (conj_exp_solves_flow Ω W₀) k t 0
  simpa using h

end SouriauMetriplecticAttentionCasimirPoset.Trajectory
