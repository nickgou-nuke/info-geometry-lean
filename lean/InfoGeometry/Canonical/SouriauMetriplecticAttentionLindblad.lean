/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import InfoGeometry.Canonical.SouriauMetriplecticAttentionDissipator

/-!
# Explicit metriplectic Lindblad semigroup in a noncommutative Banach algebra

Carrier: a normed (noncommutative) `ℝ`-algebra `B` (complete for `lindbladSol_hasDerivAt`), an idempotent `P`, a symplectic
generator `Ω` commuting with `P`, and a dissipation rate `γ : ℝ`. The linear metriplectic
(GKSL-type) equation is

  `X' = [Ω, X] - γ • Δ_diss X`,   `Δ_diss X = [P, [P, X]]`.

Because `Δ_diss` is an idempotent (`Delta_diss_orthogonal_projection`) commuting with
conjugation by `exp (t Ω)`, the equation has the explicit solution

  `X(t) = exp (t Ω) (X₀ - (1 - e^{-γ t}) • Δ_diss X₀) exp (-t Ω)`.

* `lindbladSol_hasDerivAt` – `X(t)` solves the equation for every `t`.
* `Delta_diss_lindbladSol` – the off-diagonal (dissipative) part decays:
  `Δ_diss X(t) = e^{-γ t} • exp (t Ω) (Δ_diss X₀) exp (-t Ω)`.
* `lindbladSol_casimir_part` – the block-diagonal (Casimir) part is only rotated:
  `X(t) - Δ_diss X(t) = exp (t Ω) (X₀ - Δ_diss X₀) exp (-t Ω)`.
* `lindbladSol_pure_dissipation_tendsto` – for `Ω = 0` and `γ > 0`, `X(t) → X₀ - Δ_diss X₀`,
  which lies in the commutant of `P` (`lindblad_limit_in_commutant`).

This is the *linear* dissipative flow; it is not the cubic Brockett–Souriau flow.
-/

namespace SouriauMetriplecticAttentionCasimirPoset.Lindblad

open NormedSpace Filter Topology
open InfoGeometry.Canonical.SouriauMetriplecticParabolicWeitzenbockPoset
  (Delta_diss metriplectic_lindblad_modular_synthesis)

section Algebra

variable {B : Type*} [Ring B]

/-- Additivity of the dissipator on differences. -/
lemma Delta_diss_sub (P A D : B) : Delta_diss P (A - D) = Delta_diss P A - Delta_diss P D := by
  change comm P (comm P (A - D)) = comm P (comm P A) - comm P (comm P D)
  simp only [comm, mul_sub, sub_mul]
  abel

/-- Conjugation by elements commuting with `P` commutes with `ad_P`. -/
lemma comm_conj {P U V : B} (hU : P * U = U * P) (hV : P * V = V * P) (Y : B) :
    comm P (U * Y * V) = U * comm P Y * V := by
  have h1 : P * (U * Y * V) = U * (P * Y) * V := by
    rw [← mul_assoc, ← mul_assoc, hU, mul_assoc U P Y]
  have h2 : U * Y * V * P = U * (Y * P) * V := by
    rw [mul_assoc (U * Y) V P, ← hV, ← mul_assoc, mul_assoc U Y P]
  simp only [comm]
  rw [h1, h2, ← sub_mul, ← mul_sub]

/-- Conjugation by elements commuting with `P` commutes with the dissipator. -/
lemma Delta_diss_conj {P U V : B} (hU : P * U = U * P) (hV : P * V = V * P) (Y : B) :
    Delta_diss P (U * Y * V) = U * Delta_diss P Y * V := by
  change comm P (comm P (U * Y * V)) = U * comm P (comm P Y) * V
  rw [comm_conj hU hV, comm_conj hU hV]

end Algebra

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]

/-- `ℝ`-linearity of the dissipator on `A - c • D`. -/
lemma Delta_diss_sub_smul (P A D : B) (c : ℝ) :
    Delta_diss P (A - c • D) = Delta_diss P A - c • Delta_diss P D := by
  change comm P (comm P (A - c • D)) = comm P (comm P A) - c • comm P (comm P D)
  simp only [comm, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
  abel

/-- The block-diagonal-shifted state `Y(t) = X₀ - (1 - e^{-γ t}) • Δ_diss X₀`. -/
noncomputable def lindbladCore (P : B) (γ : ℝ) (X₀ : B) (s : ℝ) : B :=
  X₀ - (1 - Real.exp (-(γ * s))) • Delta_diss P X₀

/-- `Δ_diss Y(t) = e^{-γ t} • Δ_diss X₀`. -/
lemma Delta_diss_lindbladCore {P : B} (hP : P * P = P) (γ : ℝ) (X₀ : B) (s : ℝ) :
    Delta_diss P (lindbladCore P γ X₀ s) = Real.exp (-(γ * s)) • Delta_diss P X₀ := by
  have hidem : Delta_diss P (Delta_diss P X₀) = Delta_diss P X₀ :=
    (metriplectic_lindblad_modular_synthesis hP X₀ X₀).2.2.2.2.2.1
  rw [lindbladCore, Delta_diss_sub_smul, hidem, sub_smul, one_smul, sub_sub_cancel]

/-- Derivative of the core: `Y'(t) = -(γ e^{-γ t}) • Δ_diss X₀ = -γ • Δ_diss Y(t)`. -/
lemma lindbladCore_hasDerivAt (P : B) (γ : ℝ) (X₀ : B) (t : ℝ) :
    HasDerivAt (lindbladCore P γ X₀)
      (-((γ * Real.exp (-(γ * t))) • Delta_diss P X₀)) t := by
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (-(γ * s))) (Real.exp (-(γ * t)) * (-(γ * 1))) t :=
    (((hasDerivAt_id t).const_mul γ).neg).exp
  have h2 := ((h1.const_sub 1).smul_const (Delta_diss P X₀)).const_sub X₀
  refine h2.congr_deriv ?_
  rw [show -(Real.exp (-(γ * t)) * -(γ * 1)) = γ * Real.exp (-(γ * t)) by ring]

/-- If `P` commutes with `Ω`, it commutes with exponentials of both signed multiples of `Ω`. -/
lemma commute_P_exp {P Ω : B} (hΩP : Ω * P = P * Ω) (s : ℝ) :
    P * exp (s • Ω) = exp (s • Ω) * P ∧ P * exp (s • (-Ω)) = exp (s • (-Ω)) * P := by
  have hc : Commute P Ω := hΩP.symm
  exact ⟨((hc.smul_right s).exp_right).eq, (((hc.neg_right).smul_right s).exp_right).eq⟩

/-- The explicit metriplectic Lindblad trajectory. -/
noncomputable def lindbladSol (P Ω : B) (γ : ℝ) (X₀ : B) (s : ℝ) : B :=
  exp (s • Ω) * lindbladCore P γ X₀ s * exp (s • (-Ω))

/-- **The off-diagonal part decays exponentially**:
`Δ_diss X(t) = e^{-γ t} • exp (t Ω) (Δ_diss X₀) exp (-t Ω)`. -/
theorem Delta_diss_lindbladSol {P Ω : B} (hP : P * P = P) (hΩP : Ω * P = P * Ω)
    (γ : ℝ) (X₀ : B) (s : ℝ) :
    Delta_diss P (lindbladSol P Ω γ X₀ s) =
      Real.exp (-(γ * s)) • (exp (s • Ω) * Delta_diss P X₀ * exp (s • (-Ω))) := by
  obtain ⟨hU, hV⟩ := commute_P_exp hΩP s
  rw [lindbladSol, Delta_diss_conj hU hV, Delta_diss_lindbladCore hP, mul_smul_comm,
    smul_mul_assoc]

/-- **Explicit solution**: `X(t)` solves `X' = [Ω, X] - γ • Δ_diss X`. -/
theorem lindbladSol_hasDerivAt [CompleteSpace B] {P Ω : B} (hP : P * P = P) (hΩP : Ω * P = P * Ω)
    (γ : ℝ) (X₀ : B) (t : ℝ) :
    HasDerivAt (lindbladSol P Ω γ X₀)
      (comm Ω (lindbladSol P Ω γ X₀ t) - γ • Delta_diss P (lindbladSol P Ω γ X₀ t)) t := by
  have hU := hasDerivAt_exp_smul_const' (𝕂 := ℝ) Ω t
  have hV := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-Ω) t
  have h := (hU.mul (lindbladCore_hasDerivAt P γ X₀ t)).mul hV
  rw [Delta_diss_lindbladSol hP hΩP]
  refine h.congr_deriv ?_
  simp only [lindbladSol, Pi.mul_apply, comm, smul_smul, smul_mul_assoc, mul_smul_comm, mul_neg, neg_mul,
    smul_neg, mul_assoc, add_mul]
  abel

/-- **The Casimir (block-diagonal) part is only rotated, never dissipated**:
`X(t) - Δ_diss X(t) = exp (t Ω) (X₀ - Δ_diss X₀) exp (-t Ω)`. -/
theorem lindbladSol_casimir_part {P Ω : B} (hP : P * P = P) (hΩP : Ω * P = P * Ω)
    (γ : ℝ) (X₀ : B) (s : ℝ) :
    lindbladSol P Ω γ X₀ s - Delta_diss P (lindbladSol P Ω γ X₀ s) =
      exp (s • Ω) * (X₀ - Delta_diss P X₀) * exp (s • (-Ω)) := by
  rw [Delta_diss_lindbladSol hP hΩP, lindbladSol, lindbladCore]
  simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, sub_smul, one_smul]
  abel

/-- With `Ω = 0` the trajectory is `X₀ - (1 - e^{-γ t}) • Δ_diss X₀`. -/
lemma lindbladSol_zero_Omega (P : B) (γ : ℝ) (X₀ : B) (s : ℝ) :
    lindbladSol P 0 γ X₀ s = X₀ - (1 - Real.exp (-(γ * s))) • Delta_diss P X₀ := by
  simp [lindbladSol, lindbladCore]

/-- **Relaxation to equilibrium** (pure dissipation, `γ > 0`): `X(t) → X₀ - Δ_diss X₀`. -/
theorem lindbladSol_pure_dissipation_tendsto (P : B) {γ : ℝ} (hγ : 0 < γ) (X₀ : B) :
    Tendsto (lindbladSol P 0 γ X₀) atTop (𝓝 (X₀ - Delta_diss P X₀)) := by
  have he : Tendsto (fun s : ℝ => Real.exp (-(γ * s))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => γ * s) atTop atTop :=
      tendsto_id.const_mul_atTop hγ
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  have h1' : Tendsto (fun s : ℝ => (1 : ℝ) - Real.exp (-(γ * s))) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub he
  have h1'' : Tendsto (fun s : ℝ => (1 - Real.exp (-(γ * s))) • Delta_diss P X₀) atTop
      (𝓝 ((1 - 0 : ℝ) • Delta_diss P X₀)) := h1'.smul_const _
  have h2 : Tendsto (fun s : ℝ => X₀ - (1 - Real.exp (-(γ * s))) • Delta_diss P X₀) atTop
      (𝓝 (X₀ - (1 - 0 : ℝ) • Delta_diss P X₀)) :=
    tendsto_const_nhds.sub h1''
  rw [sub_zero, one_smul] at h2
  have hfun : lindbladSol P 0 γ X₀ =
      fun s : ℝ => X₀ - (1 - Real.exp (-(γ * s))) • Delta_diss P X₀ :=
    funext (lindbladSol_zero_Omega P γ X₀)
  rw [hfun]
  exact h2

end SouriauMetriplecticAttentionCasimirPoset.Lindblad

namespace SouriauMetriplecticAttentionCasimirPoset.Lindblad

open InfoGeometry.Canonical.SouriauMetriplecticParabolicWeitzenbockPoset
  (Delta_diss metriplectic_lindblad_modular_synthesis)

/-- The relaxation limit `X₀ - Δ_diss X₀` lies in the commutant of `P`
(it is Peirce block diagonal). -/
theorem lindblad_limit_in_commutant {B : Type*} [Ring B] {P : B} (hP : P * P = P) (X₀ : B) :
    comm P (X₀ - Delta_diss P X₀) = 0 := by
  have hidem : Delta_diss P (Delta_diss P X₀) = Delta_diss P X₀ :=
    (metriplectic_lindblad_modular_synthesis hP X₀ X₀).2.2.2.2.2.1
  have h0 : Delta_diss P (X₀ - Delta_diss P X₀) = 0 := by
    rw [Delta_diss_sub, hidem, sub_self]
  exact (Dissipator.Delta_diss_eq_zero_iff hP _).mp h0

end SouriauMetriplecticAttentionCasimirPoset.Lindblad
