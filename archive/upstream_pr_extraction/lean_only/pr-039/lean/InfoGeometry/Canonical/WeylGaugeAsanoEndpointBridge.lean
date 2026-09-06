import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import InfoGeometry.AsanoRuelle.TopologicalEndpoint

/-!
# InfoGeometry.Canonical.WeylGaugeAsanoEndpointBridge

Weyl Gauge Scaling, Inverting Möbius Gauge Transport, and Inductive Colimit Endpoint Obstruction.

This module formalizes:
1. **Weyl Gauge Orbit:**
   $$z_1(s, v) = p + s \cdot v, \quad \text{where } p = -C/D, \ s \neq 0, \ v \neq 0$$
2. **Affine Gauge Denominator Linearity:**
   $$C + D z_1(s, v) = s \cdot (D v)$$
3. **Exact Inverting Weyl Gauge Transport of the Möbius Morphism:**
   $$M(z_1(s, v)) = s^{-1} \cdot w_0 - \frac{B}{D}, \quad \text{where } w_0 = -\frac{AD - BC}{D^2 v}$$
4. **Non-vanishing Generator under Nondegeneracy:**
   $$AD - BC \neq 0 \wedge v \neq 0 \implies w_0 \neq 0$$
5. **Modulus Inversion Law:**
   $$\|s^{-1} w_0\| = \|s\|^{-1} \|w_0\|$$
-/

noncomputable section

namespace InfoGeometry.Canonical.WeylGaugeAsanoEndpoint

open Complex
open InfoGeometry.AsanoRuelle

/-- Weyl gauge scaled coordinate around pole p = -C/D with complex scale s and direction v -/
def weylGaugeOrbit (C D s v : ℂ) : ℂ :=
  -C / D + s * v

/-! The orbit notation is the displacement form of the affine dilation action. -/

def weylGaugeAction (C D s z : ℂ) : ℂ :=
  -C / D + s * (z + C / D)

@[simp] theorem weylGaugeAction_one (C D z : ℂ) :
    weylGaugeAction C D 1 z = z := by
  dsimp [weylGaugeAction]
  ring

theorem weylGaugeAction_mul (C D s t z : ℂ) :
    weylGaugeAction C D s (weylGaugeAction C D t z) =
      weylGaugeAction C D (s * t) z := by
  dsimp [weylGaugeAction]
  ring

theorem weylGaugeAction_inv_left (C D s z : ℂ) (hs : s ≠ 0) :
    weylGaugeAction C D s⁻¹ (weylGaugeAction C D s z) = z := by
  dsimp [weylGaugeAction]
  field_simp [hs]
  ring

theorem weylGaugeAction_inv_right (C D s z : ℂ) (hs : s ≠ 0) :
    weylGaugeAction C D s (weylGaugeAction C D s⁻¹ z) = z := by
  dsimp [weylGaugeAction]
  field_simp [hs]
  ring

@[simp] theorem weylGaugeAction_fixed (C D s : ℂ) :
    weylGaugeAction C D s (-C / D) = -C / D := by
  dsimp [weylGaugeAction]
  ring

theorem weylGaugeOrbit_eq_action (C D s v : ℂ) :
    weylGaugeAction C D s (-C / D + v) = weylGaugeOrbit C D s v := by
  dsimp [weylGaugeAction, weylGaugeOrbit]
  ring

theorem weylGaugeAction_realScale_mul
    (C D : ℂ) (lambda mu : ℝ) (z : ℂ) :
    weylGaugeAction C D (lambda : ℂ)
        (weylGaugeAction C D (mu : ℂ) z) =
      weylGaugeAction C D ((lambda * mu : ℝ) : ℂ) z := by
  simpa using weylGaugeAction_mul C D (lambda : ℂ) (mu : ℂ) z

theorem weylGaugeAction_realScale_inv
    (C D : ℂ) (lambda : ℝ) (hlambda : 0 < lambda) (z : ℂ) :
    weylGaugeAction C D (lambda⁻¹ : ℂ)
        (weylGaugeAction C D (lambda : ℂ) z) = z := by
  have hlambda' : (lambda : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hlambda
  simpa using weylGaugeAction_inv_left C D (lambda : ℂ) z hlambda'

/-- Base gauge generator w₀ = -(AD - BC) / (D² v) -/
def weylMöbiusGenerator (A B C D : ℂ) (v : ℂ) : ℂ :=
  -(A * D - B * C) / (D ^ 2 * v)

/-- 🏆 THEOREM 1: Denominator Linearity under Weyl Gauge Scaling:
    C + D z₁(s, v) = s * (D v) -/
theorem weyl_gauge_denominator (C D s v : ℂ) (hD : D ≠ 0) :
    C + D * (weylGaugeOrbit C D s v) = s * (D * v) := by
  dsimp [weylGaugeOrbit]
  calc C + D * (-C / D + s * v) = C + D * (-C / D) + D * (s * v) := by ring
  _ = C - C + s * (D * v) := by
    have : D * (-C / D) = -C := by
      calc D * (-C / D) = (D * -C) / D := by ring
      _ = -C := by rw [mul_div_cancel_left₀ (-C) hD]
    rw [this]
    ring
  _ = s * (D * v) := by ring

/-- 🏆 THEOREM 2: Exact Inverting Weyl Gauge Transport of the Möbius Morphism:
    M(z₁(s, v)) = s⁻¹ · w₀ - B/D -/
theorem weyl_gauge_mobius_transport
    (A B C D s v : ℂ)
    (hD : D ≠ 0) (hs : s ≠ 0) (hv : v ≠ 0) :
    -(A + B * (weylGaugeOrbit C D s v)) / (C + D * (weylGaugeOrbit C D s v)) =
    (1 / s) * (weylMöbiusGenerator A B C D v) - B / D := by
  dsimp [weylGaugeOrbit, weylMöbiusGenerator]
  have hε : s * v ≠ 0 := mul_ne_zero hs hv
  have h_id := mobius_pole_identity A B C D (s * v) hD hε
  rw [h_id]
  congr 1
  have h_mul : D ^ 2 * (s * v) = s * (D ^ 2 * v) := by ring
  rw [h_mul]
  ring

/-- 🏆 THEOREM 3: Non-vanishing of the Weyl Möbius Generator under Nondegeneracy:
    AD - BC ≠ 0 ∧ v ≠ 0 ==> w₀ ≠ 0 -/
theorem weyl_generator_ne_zero
    (A B C D : ℂ) (v : ℂ)
    (hD : D ≠ 0) (hNondeg : A * D - B * C ≠ 0) (hv : v ≠ 0) :
    weylMöbiusGenerator A B C D v ≠ 0 := by
  dsimp [weylMöbiusGenerator]
  have hNum : -(A * D - B * C) ≠ 0 := neg_ne_zero.mpr hNondeg
  have hDen : D ^ 2 * v ≠ 0 := mul_ne_zero (pow_ne_zero 2 hD) hv
  exact div_ne_zero hNum hDen

/-- 🏆 THEOREM 4: Modulus Inversion Scaling:
    ‖(1 / s) * w₀‖ = (1 / ‖s‖) * ‖w₀‖ for s ≠ 0 -/
theorem weyl_norm_inversion_scaling (s w₀ : ℂ) :
    ‖(1 / s) * w₀‖ = (1 / ‖s‖) * ‖w₀‖ := by
  rw [norm_mul, norm_div, norm_one]

end InfoGeometry.Canonical.WeylGaugeAsanoEndpoint
