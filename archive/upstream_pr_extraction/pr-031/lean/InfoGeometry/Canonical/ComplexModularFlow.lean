import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.ComplexModularFlow

Finite complex-parameter modular/Weyl flow seed.

This file keeps only finite, explicit real formulas:

* a unitary phase channel (`time`),
* a dissipative Weyl channel (`beta`),
* exact algebraic identities (no analytic continuation theorem claims).
-/

namespace InfoGeometry.Canonical.ComplexModularFlow

noncomputable section

structure ComplexModularGenerator where
  unitaryK : ℝ
  weylScale : ℝ

structure ComplexParameter where
  time : ℝ
  beta : ℝ

/--
Finite modular/Weyl scale map:
phase rotation at frequency `unitaryK` with amplitude scaled by `exp(-weylScale * beta)`.
-/
def modularScale (G : ComplexModularGenerator) (p : ComplexParameter) : ℝ × ℝ :=
  let amp := Real.exp (-G.weylScale * p.beta)
  (amp * Real.cos (G.unitaryK * p.time), amp * Real.sin (G.unitaryK * p.time))

/-- Zero inverse-temperature slice (`beta = 0`) is exactly unitary on the cosine channel. -/
theorem zero_beta_cos (G : ComplexModularGenerator) (t : ℝ) :
    (modularScale G ⟨t, 0⟩).1 = Real.cos (G.unitaryK * t) := by
  simp [modularScale]

/-- Zero inverse-temperature slice (`beta = 0`) is exactly unitary on the sine channel. -/
theorem zero_beta_sin (G : ComplexModularGenerator) (t : ℝ) :
    (modularScale G ⟨t, 0⟩).2 = Real.sin (G.unitaryK * t) := by
  simp [modularScale]

/--
Norm-square law:
the squared radius of `modularScale` is exactly `exp(-2 * weylScale * beta)`.
-/
theorem modularScale_norm_sq (G : ComplexModularGenerator) (p : ComplexParameter) :
    (modularScale G p).1 ^ 2 + (modularScale G p).2 ^ 2
      = Real.exp (-2 * G.weylScale * p.beta) := by
  rcases p with ⟨t, β⟩
  simp [modularScale, pow_two]
  ring_nf
  rw [← mul_add]
  rw [Real.cos_sq_add_sin_sq]
  ring_nf
  rw [pow_two, ← Real.exp_add]
  ring_nf

/--
Beta-additivity of amplitudes:
at fixed time, shifting `beta` by `β₁ + β₂` multiplies amplitudes.
-/
theorem modularScale_beta_add_fst (G : ComplexModularGenerator) (t β₁ β₂ : ℝ) :
    (modularScale G ⟨t, β₁ + β₂⟩).1
      = Real.exp (-G.weylScale * β₁) * (modularScale G ⟨t, β₂⟩).1 := by
  have hβ : -(G.weylScale * (β₁ + β₂)) = -(G.weylScale * β₁) + -(G.weylScale * β₂) := by
    ring
  have hneg1 : -(G.weylScale * β₁) = -G.weylScale * β₁ := by ring
  calc
    (modularScale G ⟨t, β₁ + β₂⟩).1
        = Real.exp (-(G.weylScale * (β₁ + β₂))) * Real.cos (G.unitaryK * t) := by
            simp [modularScale]
    _ = Real.exp (-(G.weylScale * β₁) + -(G.weylScale * β₂)) * Real.cos (G.unitaryK * t) := by
            rw [hβ]
    _ = (Real.exp (-(G.weylScale * β₁)) * Real.exp (-(G.weylScale * β₂)))
          * Real.cos (G.unitaryK * t) := by
            rw [Real.exp_add]
    _ = Real.exp (-(G.weylScale * β₁)) * (modularScale G ⟨t, β₂⟩).1 := by
            simp [modularScale, mul_assoc]
    _ = Real.exp (-G.weylScale * β₁) * (modularScale G ⟨t, β₂⟩).1 := by
            rw [hneg1]

/--
Beta-additivity of amplitudes on the sine channel.
-/
theorem modularScale_beta_add_snd (G : ComplexModularGenerator) (t β₁ β₂ : ℝ) :
    (modularScale G ⟨t, β₁ + β₂⟩).2
      = Real.exp (-G.weylScale * β₁) * (modularScale G ⟨t, β₂⟩).2 := by
  have hβ : -(G.weylScale * (β₁ + β₂)) = -(G.weylScale * β₁) + -(G.weylScale * β₂) := by
    ring
  have hneg1 : -(G.weylScale * β₁) = -G.weylScale * β₁ := by ring
  calc
    (modularScale G ⟨t, β₁ + β₂⟩).2
        = Real.exp (-(G.weylScale * (β₁ + β₂))) * Real.sin (G.unitaryK * t) := by
            simp [modularScale]
    _ = Real.exp (-(G.weylScale * β₁) + -(G.weylScale * β₂)) * Real.sin (G.unitaryK * t) := by
            rw [hβ]
    _ = (Real.exp (-(G.weylScale * β₁)) * Real.exp (-(G.weylScale * β₂)))
          * Real.sin (G.unitaryK * t) := by
            rw [Real.exp_add]
    _ = Real.exp (-(G.weylScale * β₁)) * (modularScale G ⟨t, β₂⟩).2 := by
            simp [modularScale, mul_assoc]
    _ = Real.exp (-G.weylScale * β₁) * (modularScale G ⟨t, β₂⟩).2 := by
            rw [hneg1]

/-- Scalar exponential Bregman divergence (`ψ(x)=exp x`). -/
def expBregman (x y : ℝ) : ℝ :=
  Real.exp x - Real.exp y - Real.exp y * (x - y)

/-- Exact origin slice: `D(x,0)=exp x - 1 - x`. -/
theorem expBregman_zero (x : ℝ) :
    expBregman x 0 = Real.exp x - 1 - x := by
  simp [expBregman]

/-- Nonnegativity of the exponential Bregman divergence. -/
theorem expBregman_nonneg (x y : ℝ) :
    0 ≤ expBregman x y := by
  let z : ℝ := x - y
  have hy : 0 < Real.exp y := Real.exp_pos y
  have hz : 0 ≤ Real.exp z - 1 - z := by
    have h := Real.add_one_le_exp z
    linarith
  have hfactor : expBregman x y = Real.exp y * (Real.exp z - 1 - z) := by
    have hx : x = y + z := by
      dsimp [z]
      linarith
    rw [hx]
    dsimp [expBregman]
    rw [Real.exp_add]
    ring
  rw [hfactor]
  exact mul_nonneg (le_of_lt hy) hz

/--
Weyl quench log-amplitude law at fixed generator:
the logarithmic amplitude jump is linear in the beta jump.
-/
theorem log_amplitude_quench
    (G : ComplexModularGenerator) (β₀ β₁ : ℝ) :
    Real.log (Real.exp (-G.weylScale * β₁))
      - Real.log (Real.exp (-G.weylScale * β₀))
      = -G.weylScale * (β₁ - β₀) := by
  rw [Real.log_exp, Real.log_exp]
  ring

end

end InfoGeometry.Canonical.ComplexModularFlow
