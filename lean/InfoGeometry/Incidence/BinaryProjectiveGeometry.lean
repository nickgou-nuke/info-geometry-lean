/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Projectivization.Collinear
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Binary projective lines

Over `ZMod 2`, a nonzero vector is the unique representative of its projective
point. The span of two distinct nonzero vectors has exactly the three nonzero
vectors `u`, `v`, and `u + v`. This module proves that description in Mathlib's
native `Projectivization` and `Submodule` carriers.

The construction is generic in the binary vector space. In dimension four it
gives the 15 projective points of `PG(3,2)`. No operator multiplication or Lie
bracket is introduced here; the distinction between line incidence and
commutation belongs to the operator representation.
-/

set_option autoImplicit false

namespace InfoGeometry.Incidence.BinaryProjective

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The binary coefficient field has precisely its zero and unit elements. -/
theorem bit_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Every vector in a binary vector space is its own additive inverse. -/
theorem add_self_eq_zero (v : V) : v + v = 0 := by
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  calc
    v + v = (2 : ZMod 2) • v := (two_smul (ZMod 2) v).symm
    _ = 0 := by rw [htwo, zero_smul]

/-- Two binary projective points agree exactly when their nonzero vectors agree. -/
theorem mk_eq_mk_iff (u v : V) (hu : u ≠ 0) (hv : v ≠ 0) :
    Projectivization.mk (ZMod 2) u hu = Projectivization.mk (ZMod 2) v hv ↔ u = v := by
  rw [Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩
    rcases bit_eq_zero_or_one a with rfl | rfl
    · exact (hu (by simpa using ha.symm)).elim
    · simpa using ha.symm
  · intro h
    exact ⟨1, by simpa using h.symm⟩

/-- The nonzero binary vectors are the native projective points, with no
remaining scalar identification. -/
noncomputable def nonzeroEquivProjectivization :
    {v : V // v ≠ 0} ≃ Projectivization (ZMod 2) V :=
  Equiv.ofBijective (Projectivization.mk' (ZMod 2)) (by
    constructor
    · intro u v h
      apply Subtype.ext
      exact (mk_eq_mk_iff u.val v.val u.property v.property).1 h
    · intro p
      exact ⟨⟨p.rep, p.rep_nonzero⟩, p.mk_rep⟩)

@[simp] theorem nonzeroEquivProjectivization_apply (v : {v : V // v ≠ 0}) :
    nonzeroEquivProjectivization v = Projectivization.mk (ZMod 2) v.val v.property :=
  rfl

/-- The representative chosen by Mathlib is forced to be the original binary vector. -/
@[simp] theorem rep_mk (v : V) (hv : v ≠ 0) :
    (Projectivization.mk (ZMod 2) v hv).rep = v := by
  exact (mk_eq_mk_iff _ _ _ _).1
    (Projectivization.mk_rep (Projectivization.mk (ZMod 2) v hv))

/-- Distinct binary vectors have a nonzero sum. -/
theorem add_ne_zero {u v : V} (huv : u ≠ v) : u + v ≠ 0 := by
  intro h
  apply huv
  have h' := congrArg (fun x : V => x + v) h
  simpa only [add_assoc, add_self_eq_zero, add_zero, zero_add] using h'

omit [Module (ZMod 2) V] in
theorem add_ne_left {u v : V} (hv : v ≠ 0) : u + v ≠ u := by
  intro h
  exact hv (add_left_cancel (h.trans (add_zero u).symm))

omit [Module (ZMod 2) V] in
theorem add_ne_right {u v : V} (hu : u ≠ 0) : u + v ≠ v := by
  intro h
  exact hu (add_right_cancel (h.trans (zero_add v).symm))

/-- A binary two-generator span has no vectors besides these four sums. -/
theorem mem_span_pair_iff (u v x : V) :
    x ∈ Submodule.span (ZMod 2) ({u, v} : Set V) ↔
      x = 0 ∨ x = u ∨ x = v ∨ x = u + v := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    rcases bit_eq_zero_or_one a with rfl | rfl <;>
      rcases bit_eq_zero_or_one b with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨1, 1, by simp⟩

/-- Removing zero gives the three projective representatives on the line. -/
theorem nonzero_mem_span_pair_iff (u v x : V) (hx : x ≠ 0) :
    x ∈ Submodule.span (ZMod 2) ({u, v} : Set V) ↔
      x = u ∨ x = v ∨ x = u + v := by
  rw [mem_span_pair_iff]
  simp only [hx, false_or]

/-- Distinct nonzero binary vectors are linearly independent. -/
theorem linearIndependent_pair {u v : V} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : u ≠ v) : LinearIndependent (ZMod 2) ![u, v] := by
  rw [LinearIndependent.pair_iff' hu]
  intro a
  rcases bit_eq_zero_or_one a with rfl | rfl
  · simpa using hv.symm
  · simpa using huv

/-- The corresponding native submodule has vector dimension two. -/
theorem finrank_span_pair {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({u, v} : Set V)) = 2 := by
  rw [← Matrix.range_cons_cons_empty u v ![]]
  simpa using finrank_span_eq_card (linearIndependent_pair hu hv huv)

/-- The projectivized native span is precisely the three-point binary line. -/
theorem projectivization_span_pair {u v : V} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : u ≠ v) :
    ((Submodule.span (ZMod 2) ({u, v} : Set V)).projectivization :
        Set (Projectivization (ZMod 2) V)) =
      {Projectivization.mk (ZMod 2) u hu,
       Projectivization.mk (ZMod 2) v hv,
       Projectivization.mk (ZMod 2) (u + v) (add_ne_zero huv)} := by
  ext p
  induction p using Projectivization.ind with
  | h x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, mk_eq_mk_iff]
      exact nonzero_mem_span_pair_iff u v x hx

/-- These three points are collinear in Mathlib's projective geometry. -/
theorem three_points_collinear {u v : V} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : u ≠ v) :
    Projectivization.IsCollinear
      {Projectivization.mk (ZMod 2) u hu,
       Projectivization.mk (ZMod 2) v hv,
       Projectivization.mk (ZMod 2) (u + v) (add_ne_zero huv)} := by
  rw [← projectivization_span_pair hu hv huv]
  refine ⟨(Submodule.span (ZMod 2) ({u, v} : Set V)).projectivization, ?_, ?_,
    Set.Subset.rfl⟩
  · rw [Projectivization.Subspace.submodule.apply_symm_apply]
    exact Module.Finite.span_of_finite _ (Set.toFinite _)
  · rw [Projectivization.Subspace.submodule.apply_symm_apply,
      finrank_span_pair hu hv huv]

/-- A native projective line containing the two points must be their span. -/
theorem line_eq_span_pair {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (p : Submodule (ZMod 2) V) (hp : Module.finrank (ZMod 2) p = 2)
    (hup : u ∈ p) (hvp : v ∈ p) :
    p = Submodule.span (ZMod 2) ({u, v} : Set V) := by
  exact Projectivization.line_unique' hu hv (linearIndependent_pair hu hv huv)
    p hp hup hvp

/-- The third nonzero vector on the binary line is uniquely determined. -/
theorem unique_third_point {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    ∃! x : V, x ≠ 0 ∧ x ∈ Submodule.span (ZMod 2) ({u, v} : Set V) ∧
      x ≠ u ∧ x ≠ v := by
  refine ⟨u + v, ⟨add_ne_zero huv, ?_, add_ne_left hv, add_ne_right hu⟩, ?_⟩
  · exact (mem_span_pair_iff u v (u + v)).2 (Or.inr (Or.inr (Or.inr rfl)))
  · intro x hx
    rcases (nonzero_mem_span_pair_iff u v x hx.1).1 hx.2.1 with h | h | h
    · exact (hx.2.2.1 h).elim
    · exact (hx.2.2.2 h).elim
    · exact h

/-- Each binary projective line has exactly three points, by the native
finite-field projectivization cardinality theorem. -/
theorem projective_line_card {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    Nat.card (Projectivization (ZMod 2)
      (Submodule.span (ZMod 2) ({u, v} : Set V))) = 3 := by
  rw [Projectivization.card_of_finrank (ZMod 2)
    (Submodule.span (ZMod 2) ({u, v} : Set V)) (finrank_span_pair hu hv huv)]
  norm_num [Finset.sum_range_succ]

/-- A four-dimensional binary vector space has 15 projective points. -/
theorem projective_card_of_finrank_four (h : Module.finrank (ZMod 2) V = 4) :
    Nat.card (Projectivization (ZMod 2) V) = 15 := by
  rw [Projectivization.card_of_finrank (ZMod 2) V h]
  norm_num [Finset.sum_range_succ]

end InfoGeometry.Incidence.BinaryProjective
