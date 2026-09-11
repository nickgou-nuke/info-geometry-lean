import Mathlib.Analysis.SpecialFunctions.Exp
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic

/-!
# Canonical rapidity--angle metriplectic flow

The dissipative rapidity equation is `u' = -γ u`, not `u' = -γ`:
the former has the critical line `u = 0` as an attractor.  This file records
the exact algebraic flow map and its invariant/equilibrium consequences.
No arithmetic claim about zeta zeros is part of this owner.
-/

namespace InfoGeometry.Topology.CanonicalRapidityAngleMetriplecticFlow

open Filter

noncomputable section

abbrev Cylinder := ℝ × ℝ

def totalFlow (γ ω : ℝ) (x : Cylinder) : Cylinder :=
  (-γ * x.1, ω)

def flowMap (γ ω t : ℝ) (x : Cylinder) : Cylinder :=
  (Real.exp (-γ * t) * x.1, x.2 + ω * t)

@[simp] theorem flowMap_zero (γ ω : ℝ) (x : Cylinder) :
    flowMap γ ω 0 x = x := by
  simp [flowMap]

@[simp] theorem flowMap_rapidity (γ ω t : ℝ) (u θ : ℝ) :
    (flowMap γ ω t (u, θ)).1 = Real.exp (-γ * t) * u := rfl

theorem flowMap_critical_rapidity (γ ω t θ : ℝ) :
    (flowMap γ ω t (0, θ)).1 = 0 := by
  simp [flowMap]

theorem flowMap_critical_layer (γ ω t θ : ℝ) :
    flowMap γ ω t (0, θ) = (0, θ + ω * t) := by
  simp [flowMap]

theorem flowMap_critical_equilibrium (γ t θ : ℝ) :
    flowMap γ 0 t (0, θ) = (0, θ) := by
  simp [flowMap]

theorem totalFlow_critical_equilibrium (γ θ : ℝ) :
    totalFlow γ 0 (0, θ) = 0 := by
  ext <;> simp [totalFlow]

theorem flowMap_angle_increment (γ ω t u θ : ℝ) :
    (flowMap γ ω t (u, θ)).2 - θ = ω * t := by
  simp [flowMap]

theorem flowMap_add (γ ω s t : ℝ) (x : Cylinder) :
    flowMap γ ω (s + t) x = flowMap γ ω s (flowMap γ ω t x) := by
  simp only [flowMap]
  congr 1
  · rw [show -γ * (s + t) = (-γ * s) + (-γ * t) by ring, Real.exp_add]
    ring
  · ring

theorem flowMap_inverse (γ ω t : ℝ) (x : Cylinder) :
    flowMap γ ω (-t) (flowMap γ ω t x) = x := by
  rw [← flowMap_add]
  simp

theorem flowMap_rapidity_is_exponential_boost (γ t u : ℝ) :
    (flowMap γ 0 t (u, 0)).1 = Real.exp (-γ * t) * u := rfl

theorem flowMap_rapidity_abs_le_one
    {γ t u θ : ℝ} (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    |(flowMap γ 0 t (u, θ)).1| ≤ |u| := by
  rw [flowMap_rapidity, abs_mul]
  have hExp : Real.exp (-γ * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simpa [neg_mul] using (neg_nonpos.mpr (mul_nonneg hγ ht))
  simpa [abs_of_nonneg (Real.exp_nonneg _)] using
    (mul_le_mul_of_nonneg_right hExp (abs_nonneg u))

theorem flowMap_rapidity_sign_preserved
    {γ t u θ : ℝ} :
    0 < (flowMap γ 0 t (u, θ)).1 ↔ 0 < u := by
  rw [flowMap_rapidity]
  constructor
  · intro h
    rcases mul_pos_iff.mp h with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge (le_of_lt (Real.exp_pos _))) h.1)
  · intro h
    exact mul_pos (Real.exp_pos _) h

theorem flowMap_rapidity_zero_iff
    {γ t u θ : ℝ} :
    (flowMap γ 0 t (u, θ)).1 = 0 ↔ u = 0 := by
  rw [flowMap_rapidity]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hExp | hu
    · exact False.elim ((ne_of_gt (Real.exp_pos _)) hExp)
    · exact hu
  · intro hu
    simp [hu]

theorem flowMap_rapidity_strict_contraction
    {γ t u θ : ℝ} (hγ : 0 < γ) (ht : 0 < t) (hu : u ≠ 0) :
    |(flowMap γ 0 t (u, θ)).1| < |u| := by
  rw [flowMap_rapidity, abs_mul]
  have hExp : Real.exp (-γ * t) < 1 := by
    rw [Real.exp_lt_one_iff]
    simpa [neg_mul] using (neg_lt_zero.mpr (mul_pos hγ ht))
  have hu' : 0 < |u| := abs_pos.mpr hu
  simpa [abs_of_pos (Real.exp_pos _)] using
    (mul_lt_mul_of_pos_right hExp hu')

theorem flowMap_rapidity_tendsto_critical
    {γ u θ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun t : ℝ => (flowMap γ 0 t (u, θ)).1) atTop (nhds 0) := by
  have hlinear : Tendsto (fun t : ℝ => γ * t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hγ Filter.tendsto_id
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinear
  have hexp' : Tendsto (fun t : ℝ => Real.exp (-γ * t)) atTop (nhds 0) := by
    simpa [Function.comp_def] using hexp
  have hmul : Tendsto (fun t : ℝ => Real.exp (-γ * t) * u) atTop
      (nhds (0 * u)) := hexp'.mul tendsto_const_nhds
  simpa only [flowMap_rapidity, Function.comp_apply, zero_mul] using hmul

theorem totalFlow_decomposition (γ ω u : ℝ) :
    totalFlow γ ω (u, 0) = γ • (-u, 0) + (0, ω) := by
  ext <;> simp [totalFlow, smul_eq_mul]

/- The total vector field is the infinitesimal generator of the explicit
   rapidity--angle flow at the initial time. -/
theorem hasDerivAt_flowMap_zero (γ ω u θ : ℝ) :
    HasDerivAt (fun t : ℝ => flowMap γ ω t (u, θ))
      (totalFlow γ ω (u, θ)) 0 := by
  have h₁ : HasDerivAt (fun t : ℝ => Real.exp (-γ * t) * u)
      (-γ * u) 0 := by
    have hinner : HasDerivAt (fun t : ℝ => -γ * t) (-γ) 0 := by
      simpa [mul_comm] using (hasDerivAt_id' (0 : ℝ)).const_mul (-γ)
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-γ * t)) (-γ) 0 := by
      convert hinner.exp using 1
      simp
    convert hexp.const_mul u using 1 <;>
      simp [mul_comm]
  have h₂ : HasDerivAt (fun t : ℝ => θ + ω * t) ω 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) θ).add
      ((hasDerivAt_id (x := (0 : ℝ))).const_mul ω) using 1
    simp
  simpa [flowMap, totalFlow] using h₁.hasFDerivAt.prodMk h₂.hasFDerivAt

/- The same generator identity holds at every time along the flow. -/
theorem hasDerivAt_flowMap (γ ω t u θ : ℝ) :
    HasDerivAt (fun s : ℝ => flowMap γ ω s (u, θ))
      (totalFlow γ ω (flowMap γ ω t (u, θ))) t := by
  have hinner : HasDerivAt (fun s : ℝ => -γ * s) (-γ) t := by
    simpa [mul_comm] using (hasDerivAt_id' t).const_mul (-γ)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-γ * s))
      (Real.exp (-γ * t) * (-γ)) t := by
    exact (Real.hasDerivAt_exp (-γ * t)).comp t hinner
  have h₁ : HasDerivAt (fun s : ℝ => Real.exp (-γ * s) * u)
      (Real.exp (-γ * t) * (-γ) * u) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hexp.const_mul u
  have h₂ : HasDerivAt (fun s : ℝ => θ + ω * s) ω t := by
    convert (hasDerivAt_const (x := t) θ).add
      ((hasDerivAt_id' t).const_mul ω) using 1
    simp
  simpa [flowMap, totalFlow, mul_assoc, mul_comm, mul_left_comm] using
    h₁.hasFDerivAt.prodMk h₂.hasFDerivAt

end

end InfoGeometry.Topology.CanonicalRapidityAngleMetriplecticFlow
