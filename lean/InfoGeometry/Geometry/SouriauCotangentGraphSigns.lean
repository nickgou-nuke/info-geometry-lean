/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.DualFlatKreinLegendreGraph
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Exact graph signs for a twisted cotangent pairing

On the existing algebraic primal/dual carrier, add a skew bilinear form `B`
to the canonical evaluation pairing. The graph of `c B` has pullback
`(1 - 2 c) B`. Thus the positive graph gives `-B`, whereas the negative
graph in the supplied draft gives `3 B`.

This is a bilinear algebra statement. Closedness, multiplicativity, and a
smooth symplectic-groupoid construction are separate questions.
-/

namespace InfoGeometry.Geometry.SouriauCotangentGraphSigns

open InfoGeometry.Geometry.DualFlatKreinLegendreGraph

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The canonical cotangent pairing with a bilinear twist on primal coordinates. -/
def twistedPairing (B : LinearMap.BilinForm ℝ V) (X Y : DualCarrier V) : ℝ :=
  canonicalSymplectic X Y + B X.1 Y.1

theorem twistedPairing_skew (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ u v, B u v = -B v u) (X Y : DualCarrier V) :
    twistedPairing B X Y = -twistedPairing B Y X := by
  unfold twistedPairing
  rw [canonicalSymplectic_skew X Y, hB X.1 Y.1]
  exact (neg_add _ _).symm

/-- Pullback along a scaled skew graph, with its coefficient fixed exactly. -/
theorem twistedPairing_graph_scaled (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ u v, B u v = -B v u) (c : ℝ) (u v : V) :
    twistedPairing B (graphLift (c • B) u) (graphLift (c • B) v) =
      (1 - 2 * c) * B u v := by
  simp only [twistedPairing, canonicalSymplectic, graphLift,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hB v u]
  simp only [mul_neg, sub_mul, one_mul, two_mul, add_mul]
  abel

/-- The positive graph has the negative KKS coefficient for the displayed convention. -/
theorem twistedPairing_positive_graph (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ u v, B u v = -B v u) (u v : V) :
    twistedPairing B (graphLift B u) (graphLift B v) = -B u v := by
  have h := twistedPairing_graph_scaled B hB 1 u v
  norm_num at h
  exact h

/-- The negative graph in the supplied draft gives `3 B`, not `-B`. -/
theorem twistedPairing_negative_graph (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ u v, B u v = -B v u) (u v : V) :
    twistedPairing B (graphLift (-B) u) (graphLift (-B) v) = 3 * B u v := by
  have h := twistedPairing_graph_scaled B hB (-1) u v
  rw [show (-1 : ℝ) • B = -B from neg_one_smul ℝ B] at h
  norm_num at h
  exact h

/-- At a nonzero coefficient the two proposed graph reductions cannot be identified. -/
theorem negative_graph_ne_negative_pairing (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ u v, B u v = -B v u) (u v : V) (hne : B u v ≠ 0) :
    twistedPairing B (graphLift (-B) u) (graphLift (-B) v) ≠ -B u v := by
  rw [twistedPairing_negative_graph B hB u v]
  intro h
  apply hne
  have h4 : (4 : ℝ) * B u v = 0 := by
    rw [show (4 : ℝ) = 3 + 1 by norm_num, add_mul, one_mul, h, neg_add_cancel]
  exact (mul_eq_zero.mp h4).resolve_left (by norm_num)

end InfoGeometry.Geometry.SouriauCotangentGraphSigns
