/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.BinaryPauli
import InfoGeometry.Incidence.BinaryProjectiveGeometry

/-!
# Binary projective incidence and real operator rays

The four-bit binary labels of the real Pauli words determine the 15 points of
`PG(3,2)`. Their real matrix rays are distinct, and a binary line records the
ordered operator product up to its exact central sign. The binary symplectic
form controls whether the operators on such a line commute.

`operatorPoint` is an injective map of point sets. It is not asserted to be a
projective linear map or to preserve collinearity over the real numbers.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Incidence.BinaryPauliGeometry

open InfoGeometry.Clifford.BinaryPauli
open InfoGeometry.Algebra.Zorn.Z2ThreeCochainBridge

abbrev Point := Projectivization (ZMod 2) Label

/-- The real operator ray associated to the unique nonzero binary representative. -/
def operatorPoint (p : Point) : Projectivization ℝ Mat :=
  Projectivization.mk ℝ (word p.rep) (word_ne_zero p.rep)

@[simp] theorem operatorPoint_mk (v : Label) (hv : v ≠ 0) :
    operatorPoint (Projectivization.mk (ZMod 2) v hv) =
      Projectivization.mk ℝ (word v) (word_ne_zero v) := by
  simp [operatorPoint]

/-- Different binary projective points give different real operator rays. -/
theorem operatorPoint_injective : Function.Injective operatorPoint := by
  intro p q h
  obtain ⟨c, hc⟩ :=
    (Projectivization.mk_eq_mk_iff' ℝ (word p.rep) (word q.rep)
      (word_ne_zero _) (word_ne_zero _)).1 h
  have hr : p.rep = q.rep := ((word_eq_smul_iff _ _ c).1 hc.symm).1
  calc
    p = Projectivization.mk (ZMod 2) p.rep p.rep_nonzero := p.mk_rep.symm
    _ = Projectivization.mk (ZMod 2) q.rep q.rep_nonzero :=
      (BinaryProjective.mk_eq_mk_iff _ _ _ _).2 hr
    _ = q := q.mk_rep

/-- The two local binary pairs form a four-dimensional label space. -/
theorem label_finrank : Module.finrank (ZMod 2) Label = 4 := by
  norm_num [Label, LocalLabel, Module.finrank_prod]

/-- There are 15 nonzero binary projective labels. -/
theorem point_card : Nat.card Point = 15 :=
  BinaryProjective.projective_card_of_finrank_four label_finrank

/-- The operator-ray image has exactly 15 points. -/
theorem operatorPoint_range_card : Nat.card (Set.range operatorPoint) = 15 := by
  rw [← Nat.card_congr (Equiv.ofInjective operatorPoint operatorPoint_injective)]
  exact point_card

/-- None of the nonzero label points represents the identity ray. -/
theorem operatorPoint_ne_identity (p : Point) :
    operatorPoint p ≠ Projectivization.mk ℝ (1 : Mat) one_ne_zero := by
  intro h
  obtain ⟨c, hc⟩ :=
    (Projectivization.mk_eq_mk_iff' ℝ (word p.rep) (1 : Mat)
      (word_ne_zero _) one_ne_zero).1 h
  exact word_not_scalar_identity p.rep p.rep_nonzero c hc.symm

/-- The third point on a binary projective line gives an exactly signed
scalar triple product in the real matrix algebra. -/
theorem product_of_third_point {u v x : Label} (hx : x ≠ 0) (hxu : x ≠ u)
    (hxv : x ≠ v)
    (hline : x ∈ Submodule.span (ZMod 2) ({u, v} : Set Label)) :
    word u * word v * word x =
      (signUnit (exponent u v + exponent x x) : ℝ) • (1 : Mat) := by
  have he : x = u + v := by
    rcases (BinaryProjective.nonzero_mem_span_pair_iff u v x hx).1 hline with h | h | h
    · exact (hxu h).elim
    · exact (hxv h).elim
    · exact h
  subst x
  exact word_line_product u v

/-- The three unordered operator pairs on a binary line share their
commutation type. -/
theorem line_commutation (u v : Label) :
    (Commute (word u) (word v) ↔ Commute (word u) (word (u + v))) ∧
      (Commute (word u) (word v) ↔ Commute (word v) (word (u + v))) := by
  constructor
  · simpa only [word_commute_iff, (symplectic_line u v).1] using
      (Iff.rfl : Commute (word u) (word v) ↔ Commute (word u) (word v))
  · simpa only [word_commute_iff, (symplectic_line u v).2] using
      (Iff.rfl : Commute (word u) (word v) ↔ Commute (word u) (word v))

end InfoGeometry.Incidence.BinaryPauliGeometry
