/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic
import InfoGeometry.Analysis.JaynesRelativeStates

/-!
# Souriau–Bost–Connes Algebraic Dirac–Hodge Capstone

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * Formalizes a finite algebraic Dirac–Hodge boundary datum `CuntzDiracBoundary H`
    with linear operators `S_L`, `S_L_adj`, and `J` on a complex module `H`.
- BUCKET 2 (Explicit Linear-Map Carrier):
  * Defines `S_R B = B.J.comp (B.S_L.comp B.J)`,
    `S_R_adj B = B.J.comp (B.S_L_adj.comp B.J)`, `graph_Dirac B = B.S_L + S_R B`,
    and `tilt_axis B = (B.S_L.comp B.S_L_adj) - ((S_R B).comp (S_R_adj B))`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `J_comp_J`: `B.J (B.J x) = x` when `B.J.comp B.J = LinearMap.id`.
  * `J_flips_tilt`: `B.J.comp ((tilt_axis B).comp B.J) = -tilt_axis B`.
  * `anomaly_cancellation`: `trace (tilt_axis B) = 0` for any $J$-invariant additive trace.
-/

noncomputable section

namespace InfoGeometry.GrandUnification.SouriauBostConnes

open Complex
open Matrix
open InfoGeometry.Analysis.JaynesRelativeStates

/-- Linear operator carrier for the Souriau–Bost–Connes Cuntz boundary on a complex module `H`. -/
structure CuntzDiracBoundary (H : Type*) [AddCommGroup H] [Module ℂ H] where
  S_L : H →ₗ[ℂ] H
  S_L_adj : H →ₗ[ℂ] H
  J : H →ₗ[ℂ] H

/-- Canonical zero-shift, identity-reflection model for `CuntzDiracBoundary H`. -/
def trivialCuntzDiracBoundary (H : Type*) [AddCommGroup H] [Module ℂ H] :
    CuntzDiracBoundary H where
  S_L := 0
  S_L_adj := 0
  J := LinearMap.id

instance instInhabitedCuntzDiracBoundary (H : Type*) [AddCommGroup H] [Module ℂ H] :
    Inhabited (CuntzDiracBoundary H) :=
  ⟨trivialCuntzDiracBoundary H⟩

variable {H : Type*} [AddCommGroup H] [Module ℂ H] (B : CuntzDiracBoundary H)

/-- The Right Shift is identically the Hodge Dual of the Left Shift via Modular Conjugation $J$. -/
def S_R : H →ₗ[ℂ] H := B.J.comp (B.S_L.comp B.J)

/-- The companion right-shift linear map. -/
def S_R_adj : H →ₗ[ℂ] H := B.J.comp (B.S_L_adj.comp B.J)

/-- The Graph Dirac Operator on the Cantor Boundary: $D = S_L + S_R$. -/
def graph_Dirac : H →ₗ[ℂ] H := B.S_L + S_R B

/-- The Chiral Grading / Phase Axis (Haar Wavelet): $K = S_L S_L^* - S_R S_R^*$. -/
def tilt_axis : H →ₗ[ℂ] H :=
  (B.S_L.comp B.S_L_adj) - ((S_R B).comp (S_R_adj B))

/-- Conjugation $J$ on a vector satisfies $J(J x) = x$ when $J \circ J = \mathrm{id}$. -/
theorem J_comp_J (hJ : B.J.comp B.J = LinearMap.id) (x : H) : B.J (B.J x) = x := by
  have hx := LinearMap.congr_fun hJ x
  exact Eq.trans hx (Eq.refl x)

/-- Applying the modular reflection $J$ to the phase axis reverses chirality:
    $J \cdot K \cdot J = -K$. -/
theorem J_flips_tilt (hJ : B.J.comp B.J = LinearMap.id) :
    B.J.comp ((tilt_axis B).comp B.J) = -tilt_axis B := by
  ext x
  dsimp [tilt_axis, S_R, S_R_adj]
  rw [map_sub, J_comp_J B hJ (B.S_L_adj (B.J x)), J_comp_J B hJ (B.S_L_adj (B.J (B.J x))),
    J_comp_J B hJ x, J_comp_J B hJ (B.S_L (B.S_L_adj x))]
  abel

/-- For any $J$-invariant additive trace functional on the operator algebra, the expectation of the
    phase axis / chiral tilt vanishes identically: $\operatorname{Tr}(K) = 0$. -/
theorem anomaly_cancellation (hJ : B.J.comp B.J = LinearMap.id)
    (trace : (H →ₗ[ℂ] H) →+ ℂ)
    (h_trace_J_inv : ∀ A : H →ₗ[ℂ] H, trace (B.J.comp (A.comp B.J)) = trace A) :
    trace (tilt_axis B) = 0 := by
  have h1 : trace (B.J.comp ((tilt_axis B).comp B.J)) = trace (-tilt_axis B) := by
    rw [J_flips_tilt B hJ]
  have h2 : trace (tilt_axis B) = - trace (tilt_axis B) := by
    calc
      trace (tilt_axis B) = trace (B.J.comp ((tilt_axis B).comp B.J)) := (h_trace_J_inv (tilt_axis B)).symm
      _ = trace (-tilt_axis B) := h1
      _ = - trace (tilt_axis B) := trace.map_neg (tilt_axis B)
  have h3 : trace (tilt_axis B) + trace (tilt_axis B) = 0 := by
    calc
      trace (tilt_axis B) + trace (tilt_axis B) =
        - trace (tilt_axis B) + trace (tilt_axis B) := by nth_rw 1 [h2]
      _ = 0 := neg_add_cancel (trace (tilt_axis B))
  have h4 : (2 : ℂ) * trace (tilt_axis B) = 0 := by
    calc
      (2 : ℂ) * trace (tilt_axis B) = trace (tilt_axis B) + trace (tilt_axis B) := by ring
      _ = 0 := h3
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  exact mul_eq_zero.mp h4 |>.resolve_left htwo

end InfoGeometry.GrandUnification.SouriauBostConnes
