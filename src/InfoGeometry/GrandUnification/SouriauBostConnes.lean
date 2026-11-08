/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

/-!
# Grand Unification: Souriau–Bost–Connes Dirac–Hodge Boundary Operator

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * Formalizes an algebraic Dirac–Hodge boundary model on an explicitly supplied $\mathbb{C}$-module
    `H` with linear operators `S_L`, `S_L_adj`, and modular involution `J` (`J ∘ₗ J = id`).
- BUCKET 2 (Explicit Linear-Map Carrier):
  * Defines `S_R S_L J = J ∘ₗ S_L ∘ₗ J`, `S_R_adj S_L_adj J = J ∘ₗ S_L_adj ∘ₗ J`,
    `graph_Dirac S_L J = S_L + S_R S_L J`, and the chiral grading axis
    `tilt_axis S_L S_L_adj J = S_L ∘ₗ S_L_adj - S_R S_L J ∘ₗ S_R_adj S_L_adj J`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `S_R_mul_S_R_adj`, `J_S_R_proj_J`: conjugation identities relating the left and right shift
    projectors under `J`.
  * `J_flips_tilt`: `J ∘ₗ tilt_axis S_L S_L_adj J ∘ₗ J = -tilt_axis S_L S_L_adj J`.
  * `anomaly_cancellation`: for any $J$-invariant linear functional `trace`,
    `trace (tilt_axis S_L S_L_adj J) = 0`.
-/

namespace InfoGeometry.GrandUnification.SouriauBostConnes.Foundation

open Complex

variable {H : Type*} [AddCommGroup H] [Module ℂ H]

/-- The Right Shift is identically the Hodge Dual of the Left Shift. -/
def S_R (S_L J : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  J ∘ₗ S_L ∘ₗ J

/-- The companion linear map used to form the right-shift projector.
    No inner-product or adjoint law is assumed by this algebraic carrier. -/
def S_R_adj (S_L_adj J : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  J ∘ₗ S_L_adj ∘ₗ J

/-- The Dirac Operator on the Cantor Graph: $D = d + \delta = S_L + S_R$. -/
def graph_Dirac (S_L J : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  S_L + S_R S_L J

/-- The Chiral Grading (Phase Axis / Haar Psi): $K = S_L S_L^* - S_R S_R^*$. -/
def tilt_axis (S_L S_L_adj J : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  (S_L ∘ₗ S_L_adj) - (S_R S_L J ∘ₗ S_R_adj S_L_adj J)

/-- Product of Right Shift and its adjoint in terms of $J$ and Left Shift. -/
theorem S_R_mul_S_R_adj (S_L S_L_adj J : H →ₗ[ℂ] H) (hJ : J ∘ₗ J = LinearMap.id) :
    S_R S_L J ∘ₗ S_R_adj S_L_adj J = J ∘ₗ (S_L ∘ₗ S_L_adj) ∘ₗ J := by
  unfold S_R S_R_adj
  ext x
  simp only [LinearMap.comp_apply]
  have hj : J (J (S_L_adj (J x))) = S_L_adj (J x) :=
    LinearMap.congr_fun hJ (S_L_adj (J x))
  rw [hj]

/-- $J$-conjugation on Right Shift projector recovers Left Shift projector. -/
theorem J_S_R_proj_J (S_L S_L_adj J : H →ₗ[ℂ] H) (hJ : J ∘ₗ J = LinearMap.id) :
    J ∘ₗ (S_R S_L J ∘ₗ S_R_adj S_L_adj J) ∘ₗ J = S_L ∘ₗ S_L_adj := by
  rw [S_R_mul_S_R_adj S_L S_L_adj J hJ]
  ext x
  simp only [LinearMap.comp_apply]
  have hj1 : J (J x) = x := LinearMap.congr_fun hJ x
  have hj2 (y : H) : J (J y) = y := LinearMap.congr_fun hJ y
  rw [hj1, hj2]

/-- Applying the modular conjugation $J$ to the phase axis reverses the chirality:
    $J \circ K \circ J = -K$. -/
theorem J_flips_tilt (S_L S_L_adj J : H →ₗ[ℂ] H) (hJ : J ∘ₗ J = LinearMap.id) :
    J ∘ₗ tilt_axis S_L S_L_adj J ∘ₗ J = -tilt_axis S_L S_L_adj J := by
  unfold tilt_axis
  rw [LinearMap.sub_comp, LinearMap.comp_sub, ← S_R_mul_S_R_adj S_L S_L_adj J hJ,
    J_S_R_proj_J S_L S_L_adj J hJ]
  abel

/-- For any linear trace functional invariant under modular conjugation $J$,
    the expectation of the phase axis vanishes: $\operatorname{Tr}(K) = 0$. -/
theorem anomaly_cancellation (S_L S_L_adj J : H →ₗ[ℂ] H) (hJ : J ∘ₗ J = LinearMap.id)
    (trace : (H →ₗ[ℂ] H) →ₗ[ℂ] ℂ)
    (h_trace_J_inv : ∀ A : H →ₗ[ℂ] H, trace (J ∘ₗ A ∘ₗ J) = trace A) :
    trace (tilt_axis S_L S_L_adj J) = 0 := by
  have h1 : trace (J ∘ₗ tilt_axis S_L S_L_adj J ∘ₗ J) = trace (-tilt_axis S_L S_L_adj J) := by
    rw [J_flips_tilt S_L S_L_adj J hJ]
  have h2 : trace (J ∘ₗ tilt_axis S_L S_L_adj J ∘ₗ J) = trace (tilt_axis S_L S_L_adj J) :=
    h_trace_J_inv (tilt_axis S_L S_L_adj J)
  have h_neg : trace (-tilt_axis S_L S_L_adj J) = - trace (tilt_axis S_L S_L_adj J) :=
    trace.map_neg (tilt_axis S_L S_L_adj J)
  rw [h2, h_neg] at h1
  have h_two : 2 * trace (tilt_axis S_L S_L_adj J) = 0 := by
    linear_combination h1
  have h_two_ne : (2 : ℂ) ≠ 0 := by norm_num
  exact mul_eq_zero.mp h_two |>.resolve_left h_two_ne

end InfoGeometry.GrandUnification.SouriauBostConnes.Foundation
