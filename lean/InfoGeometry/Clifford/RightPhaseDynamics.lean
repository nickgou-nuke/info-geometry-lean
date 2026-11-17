/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Squaring a real first-order equation with a fixed right coefficient

The operator is a real-linear map on algebra-valued functions. Its compatibility
with the fixed right coefficient is an explicit hypothesis. The second-order
equation follows from that compatibility and the coefficient's actual square;
the coefficient need not commute with the values of the function.

No differential, metric, or causality interpretation of the operator is assumed.
-/

namespace InfoGeometry.Clifford.RightPhaseDynamics

variable {X A : Type*} [Ring A] [Algebra ℝ A]

/-- A first-order right-mass equation determines the second iterate when the
operator commutes with the actual fixed right multiplication. The sign is the
square of that coefficient, with no centrality assumption on the coefficient. -/
theorem second_iterate_of_right_mass_equation
    (D : (X → A) →ₗ[ℝ] (X → A)) (ψ : X → A) (m s : ℝ) (C : A)
    (hC : C * C = s • (1 : A))
    (hright : ∀ f : X → A,
      D (fun x => f x * C) = fun x => D f x * C)
    (hψ : D ψ = fun x => m • (ψ x * C)) :
    D (D ψ) = fun x => (s * m ^ 2) • ψ x := by
  calc
    D (D ψ) = D (m • (fun x => ψ x * C)) := congrArg D hψ
    _ = m • D (fun x => ψ x * C) := D.map_smul m _
    _ = m • (fun x => D ψ x * C) :=
      congrArg (fun f : X → A => m • f) (hright ψ)
    _ = fun x => (s * m ^ 2) • ψ x := by
      funext x
      change m • (D ψ x * C) = (s * m ^ 2) • ψ x
      rw [hψ]
      change m • ((m • (ψ x * C)) * C) = (s * m ^ 2) • ψ x
      rw [smul_mul_assoc, mul_assoc, hC, mul_smul_comm, mul_one,
        smul_smul, smul_smul]
      congr 1
      ring

/-- Right multiplication by a square-minus-one phase can be eliminated from
the first-order equation by multiplying on the right by `-B`, its inverse.
The order `ψ * g * B` is retained; no commutation law between `g` and `B` is used. -/
theorem right_phase_equation_iff
    (D : (X → A) →ₗ[ℝ] (X → A)) (ψ : X → A) (m : ℝ) (g B : A)
    (hB : B * B = -(1 : A)) :
    (fun x => D ψ x * B) = (fun x => m • (ψ x * g)) ↔
      D ψ = fun x => (-m) • (ψ x * g * B) := by
  constructor
  · intro h
    funext x
    have hx : D ψ x * B = m • (ψ x * g) := congrFun h x
    calc
      D ψ x = -((D ψ x * B) * B) := by
        rw [mul_assoc, hB, mul_neg, mul_one, neg_neg]
      _ = -((m • (ψ x * g)) * B) := by rw [hx]
      _ = (-m) • (ψ x * g * B) := by
        rw [smul_mul_assoc, neg_smul]
  · intro h
    funext x
    have hx : D ψ x = (-m) • (ψ x * g * B) := congrFun h x
    change D ψ x * B = m • (ψ x * g)
    rw [hx, smul_mul_assoc, mul_assoc, hB, mul_neg, mul_one,
      smul_neg, neg_smul, neg_neg]

end InfoGeometry.Clifford.RightPhaseDynamics
