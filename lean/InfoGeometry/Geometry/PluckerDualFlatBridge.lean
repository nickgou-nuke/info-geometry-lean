/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Basic.Real.Basic
import InfoGeometry.Projective.Quadrics.PluckerKlein
import InfoGeometry.Geometry.DualFlat

/-!
# Plücker-Grassmannian Dual-Flat Bridge

This module supplies a normalized Plücker chart and potential-dependent
Bregman expressions. Regularity and convexity of the potential are additional
requirements; they are not fields of `PluckerHessianGeometry` below.

1. **Plücker Affine Chart**:
   Standard 4D affine chart on the Klein quadric $Gr(2,4) \hookrightarrow \mathbb{P}(\Lambda^2 \mathbb{R}^4)$
   under the gauge choice $p_{01} = 1$:
   $$u = (u_0, u_1, u_2, u_3) = (p_{02}, p_{03}, p_{12}, p_{13})$$

2. **Klein Quadric Relation**:
   The 6th coordinate $p_{23}$ is determined algebraically by:
   $$p_{23} = u_0 u_3 - u_1 u_2$$
   satisfying the Klein quadric relation:
   $$p_{01} p_{23} - p_{02} p_{13} + p_{03} p_{12} = 0$$

3. **Potential and derivative expression**:
   A chosen function $\psi(u)$ determines `fderiv`-based covectors and a
   Bregman expression. A positive Hessian metric or dual affine connections
   are not constructed here. `PluckerPotentialBoundary` proves regularity
   and strict convexity for one explicit independent-coordinate potential.

4. **Three-point identity**:
   The algebraic identity includes its covector correction term. A
   Pythagorean equality follows only when that term vanishes.
-/

noncomputable section

namespace InfoGeometry.Geometry.PluckerDualFlatBridge

open InfoGeometry.Projective.Quadrics.PluckerKlein
open InfoGeometry.Geometry

/-- The standard 4D affine chart coordinates for the Klein quadric:
    `u = (p₀₂, p₀₃, p₁₂, p₁₃)` when `p₀₁ = 1`. -/
abbrev PluckerAffineChart := InfoGeometry.Algebra.FiniteSpin.Vec4R

/-- Reconstructed normalized Plücker vector `(p₀₁, p₀₂, p₀₃, p₁₂, p₁₃, p₂₃)` from affine chart coordinates. -/
def reconstructPlucker (u : PluckerAffineChart) : Fin 6 → ℝ :=
  fun i => match i with
  | 0 => 1                    -- p₀₁
  | 1 => u 0                  -- p₀₂
  | 2 => u 1                  -- p₀₃
  | 3 => u 2                  -- p₁₂
  | 4 => u 3                  -- p₁₃
  | 5 => u 0 * u 3 - u 1 * u 2 -- p₂₃ (from Klein relation: 1 * p₂₃ - u₀*u₃ + u₁*u₂ = 0)

/-- 🏆 THEOREM: The reconstructed Plücker vector satisfies the Klein quadric relation:
    `p₀₁ * p₂₃ - p₀₂ * p₁₃ + p₀₃ * p₁₂ = 0`. -/
theorem reconstructPlucker_satisfies_klein (u : PluckerAffineChart) :
    reconstructPlucker u 0 * reconstructPlucker u 5 -
    reconstructPlucker u 1 * reconstructPlucker u 4 +
    reconstructPlucker u 2 * reconstructPlucker u 3 = 0 := by
  dsimp [reconstructPlucker]
  ring

/-- Potential data on the Plücker chart. The historical name does not supply
regularity, convexity, a Hessian metric, or dual affine connections. -/
structure PluckerHessianGeometry where
  potential : PluckerAffineChart → ℝ

/-- Gradient dual coordinate map on the Plücker affine chart. -/
def pluckerDualCoord (H : PluckerHessianGeometry) (u : PluckerAffineChart) :
    PluckerAffineChart →L[ℝ] ℝ :=
  fderiv ℝ H.potential u

/-- Bregman divergence on the Plücker affine chart. -/
def pluckerBregman (H : PluckerHessianGeometry) (u v : PluckerAffineChart) : ℝ :=
  H.potential u - H.potential v - (pluckerDualCoord H v) (u - v)

/-- 🏆 THEOREM: Bregman divergence vanishes on the diagonal: `D(u, u) = 0`. -/
@[simp] theorem pluckerBregman_self (H : PluckerHessianGeometry) (u : PluckerAffineChart) :
    pluckerBregman H u u = 0 := by
  dsimp [pluckerBregman]
  simp

/-- 🏆 THEOREM: Three-point Pythagorean identity on the Plücker affine chart. -/
theorem pluckerBregman_three_point (H : PluckerHessianGeometry) (u v w : PluckerAffineChart) :
    pluckerBregman H u v =
      pluckerBregman H u w + pluckerBregman H w v +
        (pluckerDualCoord H w - pluckerDualCoord H v) (u - w) := by
  dsimp [pluckerBregman]
  have hsplit : u - v = (u - w) + (w - v) := by ring
  have hlin : (pluckerDualCoord H v) (u - v) =
      (pluckerDualCoord H v) (u - w) + (pluckerDualCoord H v) (w - v) := by
    rw [hsplit, map_add]
  rw [hlin]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  ring

end InfoGeometry.Geometry.PluckerDualFlatBridge
