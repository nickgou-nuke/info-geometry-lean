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
    `H` equipped with `CuntzDiracBoundary H` (`S_L`, `S_L_adj`, and modular involution `J` with
    `J ∘ₗ J = id`).
- BUCKET 2 (Explicit Linear-Map Carrier):
  * Defines `S_R = J ∘ₗ S_L ∘ₗ J`, `S_R_adj = J ∘ₗ S_L_adj ∘ₗ J`, `graph_Dirac = S_L + S_R`,
    and the chiral grading axis `tilt_axis = S_L ∘ₗ S_L_adj - S_R ∘ₗ S_R_adj`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `S_R_mul_S_R_adj`, `J_S_R_proj_J`: conjugation identities relating the left and right shift
    projectors under `J`.
  * `J_flips_tilt`: `J ∘ₗ tilt_axis H ∘ₗ J = -tilt_axis H`.
  * `anomaly_cancellation`: for any $J$-invariant linear functional `trace`,
    `trace (tilt_axis H) = 0`.
-/

namespace InfoGeometry.GrandUnification.SouriauBostConnes.Foundation

open Complex

/-- The Souriau-Bost-Connes Cuntz Boundary -/
class CuntzDiracBoundary (H : Type*) [AddCommGroup H] [Module ℂ H] where
  S_L : H →ₗ[ℂ] H
  S_L_adj : H →ₗ[ℂ] H
  J : H →ₗ[ℂ] H
  J_sq : J ∘ₗ J = LinearMap.id
  partition : (S_L ∘ₗ S_L_adj) + (J ∘ₗ S_L ∘ₗ J) ∘ₗ (J ∘ₗ S_L_adj ∘ₗ J) = LinearMap.id

variable (H : Type*) [AddCommGroup H] [Module ℂ H] [CuntzDiracBoundary H]

/-- The Right Shift is identically the Hodge Dual of the Left Shift. -/
def S_R : H →ₗ[ℂ] H :=
  (CuntzDiracBoundary.J : H →ₗ[ℂ] H) ∘ₗ CuntzDiracBoundary.S_L ∘ₗ CuntzDiracBoundary.J

/-- The companion linear map used to form the right-shift projector.
    No inner-product or adjoint law is assumed by this algebraic carrier. -/
def S_R_adj : H →ₗ[ℂ] H :=
  (CuntzDiracBoundary.J : H →ₗ[ℂ] H) ∘ₗ CuntzDiracBoundary.S_L_adj ∘ₗ CuntzDiracBoundary.J

/-- The Dirac Operator on the Cantor Graph: $D = d + \delta = S_L + S_R$. -/
def graph_Dirac : H →ₗ[ℂ] H :=
  (CuntzDiracBoundary.S_L : H →ₗ[ℂ] H) + S_R H

/-- The Chiral Grading (Phase Axis / Haar Psi): $K = S_L S_L^* - S_R S_R^*$. -/
def tilt_axis : H →ₗ[ℂ] H :=
  ((CuntzDiracBoundary.S_L : H →ₗ[ℂ] H) ∘ₗ CuntzDiracBoundary.S_L_adj) - (S_R H ∘ₗ S_R_adj H)

/-- Product of Right Shift and its adjoint in terms of $J$ and Left Shift. -/
theorem S_R_mul_S_R_adj :
    S_R H ∘ₗ S_R_adj H = (CuntzDiracBoundary.J : H →ₗ[ℂ] H) ∘ₗ (CuntzDiracBoundary.S_L ∘ₗ CuntzDiracBoundary.S_L_adj) ∘ₗ CuntzDiracBoundary.J := by
  unfold S_R S_R_adj
  ext x
  simp only [LinearMap.comp_apply]
  have hj : (CuntzDiracBoundary.J : H →ₗ[ℂ] H) (CuntzDiracBoundary.J (CuntzDiracBoundary.S_L_adj (CuntzDiracBoundary.J x))) =
      CuntzDiracBoundary.S_L_adj (CuntzDiracBoundary.J x) := by
    have h_id := LinearMap.congr_fun (CuntzDiracBoundary.J_sq (H := H)) (CuntzDiracBoundary.S_L_adj (CuntzDiracBoundary.J x))
    exact h_id
  rw [hj]

/-- $J$-conjugation on Right Shift projector recovers Left Shift projector. -/
theorem J_S_R_proj_J :
    (CuntzDiracBoundary.J : H →ₗ[ℂ] H) ∘ₗ (S_R H ∘ₗ S_R_adj H) ∘ₗ CuntzDiracBoundary.J =
      CuntzDiracBoundary.S_L ∘ₗ CuntzDiracBoundary.S_L_adj := by
  rw [S_R_mul_S_R_adj H]
  ext x
  simp only [LinearMap.comp_apply]
  have hj1 : (CuntzDiracBoundary.J : H →ₗ[ℂ] H) (CuntzDiracBoundary.J x) = x :=
    LinearMap.congr_fun (CuntzDiracBoundary.J_sq (H := H)) x
  have hj2 (y : H) : (CuntzDiracBoundary.J : H →ₗ[ℂ] H) (CuntzDiracBoundary.J y) = y :=
    LinearMap.congr_fun (CuntzDiracBoundary.J_sq (H := H)) y
  rw [hj1, hj2]

/-- Applying the modular conjugation $J$ to the phase axis reverses the chirality:
    $J \circ K \circ J = -K$. -/
theorem J_flips_tilt :
    (CuntzDiracBoundary.J : H →ₗ[ℂ] H) ∘ₗ tilt_axis H ∘ₗ CuntzDiracBoundary.J = -tilt_axis H := by
  unfold tilt_axis
  rw [LinearMap.sub_comp, LinearMap.comp_sub, ← S_R_mul_S_R_adj H, J_S_R_proj_J H]
  abel

/-- For any linear trace functional invariant under modular conjugation $J$,
    the expectation of the phase axis vanishes: $\operatorname{Tr}(K) = 0$. -/
theorem anomaly_cancellation
    (trace : (H →ₗ[ℂ] H) →ₗ[ℂ] ℂ)
    (h_trace_J_inv : ∀ A : H →ₗ[ℂ] H, trace ((CuntzDiracBoundary.J : H →ₗ[ℂ] H) ∘ₗ A ∘ₗ CuntzDiracBoundary.J) = trace A) :
    trace (tilt_axis H) = 0 := by
  have h1 : trace ((CuntzDiracBoundary.J : H →ₗ[ℂ] H) ∘ₗ tilt_axis H ∘ₗ CuntzDiracBoundary.J) = trace (-tilt_axis H) := by
    rw [J_flips_tilt H]
  have h2 : trace ((CuntzDiracBoundary.J : H →ₗ[ℂ] H) ∘ₗ tilt_axis H ∘ₗ CuntzDiracBoundary.J) = trace (tilt_axis H) :=
    h_trace_J_inv (tilt_axis H)
  have h_neg : trace (-tilt_axis H) = - trace (tilt_axis H) :=
    trace.map_neg (tilt_axis H)
  rw [h2, h_neg] at h1
  have h_two : 2 * trace (tilt_axis H) = 0 := by
    linear_combination h1
  have h_two_ne : (2 : ℂ) ≠ 0 := by norm_num
  exact mul_eq_zero.mp h_two |>.resolve_left h_two_ne

end InfoGeometry.GrandUnification.SouriauBostConnes.Foundation
