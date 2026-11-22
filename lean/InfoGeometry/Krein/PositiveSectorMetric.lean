/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.PontryaginSpace
import InfoGeometry.Krein.State
import Mathlib.Tactic

/-!
# Real Fubini–Study-type metric on the positive Krein sector

This module uses only the real Krein pairing.  It does **not** treat the global
Krein form as positive definite and does **not** introduce complex scalars.

On a nonzero positive-sector vector `x ∈ K₊`, the Krein pairing is strictly
positive (`KreinSpace.kreinInner_pos_on_posSubspace`), so `[u,v]_x = [u,v]_J / [x,x]_J` is a
real inner product on `K₊` that is invariant under rescaling of `x`.  This is the
exact metric on the positive sector supported by the current owners; a
Fubini–Study quotient would additionally need a phase structure preserving
`K₊`, which the repo does not establish here.
-/

noncomputable section

namespace InfoGeometry.Krein.PositiveSectorMetric

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [KreinSpace H]

/-- The normalized real Krein metric at a positive-sector base vector `x`. -/
def sectorMetric (x v w : H) : ℝ :=
  KreinSpace.kreinInner v w / KreinSpace.kreinInner x x

/-- Symmetry inherited from the Krein pairing. -/
theorem sectorMetric_symm (x v w : H) :
    sectorMetric x v w = sectorMetric x w v := by
  unfold sectorMetric
  rw [KreinSpace.kreinInner_symm]

/-- Linearity in the first inserted vector. -/
theorem sectorMetric_add_left (x v₁ v₂ w : H) :
    sectorMetric x (v₁ + v₂) w = sectorMetric x v₁ w + sectorMetric x v₂ w := by
  unfold sectorMetric
  rw [KreinSpace.kreinInner_add_left]
  ring

/-- Linearity in the second inserted vector. -/
theorem sectorMetric_add_right (x v w₁ w₂ : H) :
    sectorMetric x v (w₁ + w₂) = sectorMetric x v w₁ + sectorMetric x v w₂ := by
  unfold sectorMetric
  rw [KreinSpace.kreinInner_add_right]
  ring

/-- Strict positivity on nonzero positive-sector tangent vectors. -/
theorem sectorMetric_self_pos {x v : H}
    (hx : x ∈ KreinSpace.posSubspace H) (hx0 : x ≠ 0)
    (hv : v ∈ KreinSpace.posSubspace H) (hv0 : v ≠ 0) :
    0 < sectorMetric x v v := by
  dsimp [sectorMetric]
  have hxpos := KreinSpace.kreinInner_pos_on_posSubspace hx hx0
  have hvpos := KreinSpace.kreinInner_pos_on_posSubspace hv hv0
  positivity

/-- The metric is unchanged by rescaling the positive-sector base vector. -/
theorem sectorMetric_scale_invariant (c : ℝ) (hc : c ≠ 0) (x v w : H) :
    sectorMetric (c • x) (c • v) (c • w) = sectorMetric x v w := by
  unfold sectorMetric
  simp only [KreinSpace.kreinInner_smul_left, KreinSpace.kreinInner_smul_right]
  field_simp [hc]

/-- The horizontal component of `y` relative to the positive-sector ray of `x`. -/
def horizontalPart (x y : H) : H :=
  y - (KreinSpace.kreinInner x y / KreinSpace.kreinInner x x) • x

/-- The horizontal component stays in the positive sector. -/
theorem horizontalPart_mem_posSubspace {x y : H}
    (hx : x ∈ KreinSpace.posSubspace H)
    (hy : y ∈ KreinSpace.posSubspace H) :
    horizontalPart x y ∈ KreinSpace.posSubspace H := by
  exact (KreinSpace.posSubspace H).sub_mem hy
    ((KreinSpace.posSubspace H).smul_mem _ hx)

/-- The horizontal component is Krein-orthogonal to the base ray. -/
theorem kreinInner_base_horizontalPart_eq_zero {x y : H}
    (hx : x ∈ KreinSpace.posSubspace H) (hx0 : x ≠ 0) :
    KreinSpace.kreinInner x (horizontalPart x y) = 0 := by
  have hxx : KreinSpace.kreinInner x x ≠ 0 :=
    ne_of_gt (KreinSpace.kreinInner_pos_on_posSubspace hx hx0)
  dsimp [horizontalPart]
  change KreinSpace.kreinInner x
      (y - (KreinSpace.kreinInner x y / KreinSpace.kreinInner x x) • x) = 0
  simp_rw [KreinSpace.kreinInner_def] at hxx ⊢
  simp only [inner_sub_right, real_inner_smul_right]
  field_simp [hxx]
  ring

/-- Normalized positive-sheet horizontal decomposition. -/
theorem horizontal_decomposition (x y : H) :
    y = (KreinSpace.kreinInner x y / KreinSpace.kreinInner x x) • x +
      horizontalPart x y := by
  dsimp [horizontalPart]
  abel

end InfoGeometry.Krein.PositiveSectorMetric
