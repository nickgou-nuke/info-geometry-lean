/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# Binary symplectic labels and the lines of PG(3,2)

The four binary coordinates are ordered as `((a₁,b₁),(a₂,b₂))`, in the
same order as two tensor factors of a Weyl operator `Xᵃ Zᵇ`.  The cocycle
records the sign lost on passage from operators to binary labels.  Its
symmetrization records commutation.

Over `ZMod 2` each nonzero vector is its own projective representative.
`projectivePointEquiv` establishes this identification with Mathlib's native
projectivization. `mem_line_iff_mem_span_pair` identifies each finite line
with the nonzero vectors in the native linear span of its two generators.

This file concerns finite incidence and its symplectic form.  Matrix lifts
and commutator identities are established by the importing operator owner.
-/

namespace InfoGeometry.Projective.BinarySymplectic

abbrev Bit := ZMod 2

abbrev Label := (Bit × Bit) × (Bit × Bit)

theorem finrank_label : Module.finrank Bit Label = 4 := by
  simp [Label]

theorem bit_eq_zero_or_one (a : Bit) : a = 0 ∨ a = 1 := by
  exact (show ∀ a : Bit, a = 0 ∨ a = 1 by decide) a

@[simp] theorem bit_mul_two (a : Bit) : a * 2 = 0 := by
  rcases bit_eq_zero_or_one a with rfl | rfl <;> decide

/-- Binary projectivization never identifies two distinct nonzero vectors. -/
theorem projectivization_mk_eq_iff (v w : Label) (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk Bit v hv = Projectivization.mk Bit w hw ↔ v = w := by
  rw [Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩
    rcases bit_eq_zero_or_one a with rfl | rfl
    · exact (hv (by simpa using ha.symm)).elim
    · simpa using ha.symm
  · rintro rfl
    exact ⟨1, one_smul _ _⟩

/-- A constructive equivalence from nonzero labels to Mathlib projective points.
The inverse uses quotient lifting, with no chosen representative. -/
def projectivePointEquiv : {v : Label // v ≠ 0} ≃ Projectivization Bit Label where
  toFun := Projectivization.mk' Bit
  invFun := Projectivization.lift id (by
    intro a b t h
    apply Subtype.ext
    rcases bit_eq_zero_or_one t with rfl | rfl
    · exact (a.property (by simpa using h)).elim
    · simpa using h)
  left_inv := by intro v; rfl
  right_inv := by
    intro p
    induction p using Projectivization.ind with
    | h v hv => rfl

@[simp] theorem projectivePointEquiv_apply (v : {v : Label // v ≠ 0}) :
    projectivePointEquiv v = Projectivization.mk Bit (v : Label) v.property := rfl

theorem projectivization_card : Nat.card (Projectivization Bit Label) = 15 := by
  rw [← Nat.card_congr projectivePointEquiv, Nat.card_eq_fintype_card]
  decide

/-- The binary exponent in the ordered Weyl product. -/
def cocycle (v w : Label) : Bit :=
  v.1.2 * w.1.1 + v.2.2 * w.2.1

/-- The alternating pairing controlling the order of two Weyl operators. -/
def symplectic (v w : Label) : Bit :=
  cocycle v w + cocycle w v

@[simp] theorem label_add_self (v : Label) : v + v = 0 := by
  apply Prod.ext <;> apply Prod.ext <;> exact CharTwo.add_self_eq_zero _

@[simp] theorem label_add_add_left (v w : Label) : v + (v + w) = w := by
  rw [← add_assoc, label_add_self, zero_add]

@[simp] theorem label_add_add_right (v w : Label) : v + w + w = v := by
  rw [add_assoc, label_add_self, add_zero]

@[simp] theorem cocycle_zero_left (v : Label) : cocycle 0 v = 0 := by
  simp [cocycle]

@[simp] theorem cocycle_zero_right (v : Label) : cocycle v 0 = 0 := by
  simp [cocycle]

theorem cocycle_add_left (u v w : Label) :
    cocycle (u + v) w = cocycle u w + cocycle v w := by
  dsimp [cocycle]
  ring

theorem cocycle_add_right (u v w : Label) :
    cocycle u (v + w) = cocycle u v + cocycle u w := by
  dsimp [cocycle]
  ring

/-- This is the associativity identity required by the signed product. -/
theorem cocycle_assoc (u v w : Label) :
    cocycle u v + cocycle (u + v) w = cocycle v w + cocycle u (v + w) := by
  rw [cocycle_add_left, cocycle_add_right]
  ring

theorem symplectic_comm (v w : Label) : symplectic v w = symplectic w v := by
  exact add_comm _ _

@[simp] theorem symplectic_self (v : Label) : symplectic v v = 0 :=
  CharTwo.add_self_eq_zero _

@[simp] theorem symplectic_zero_left (v : Label) : symplectic 0 v = 0 := by
  simp [symplectic]

@[simp] theorem symplectic_zero_right (v : Label) : symplectic v 0 = 0 := by
  simp [symplectic]

theorem symplectic_add_left (u v w : Label) :
    symplectic (u + v) w = symplectic u w + symplectic v w := by
  simp only [symplectic, cocycle_add_left, cocycle_add_right]
  ring

theorem symplectic_add_right (u v w : Label) :
    symplectic u (v + w) = symplectic u v + symplectic u w := by
  simp only [symplectic, cocycle_add_left, cocycle_add_right]
  ring

@[simp] theorem symplectic_left_add (v w : Label) :
    symplectic v (v + w) = symplectic v w := by
  rw [symplectic_add_right, symplectic_self, zero_add]

@[simp] theorem symplectic_right_add (v w : Label) :
    symplectic w (v + w) = symplectic v w := by
  rw [symplectic_add_right, symplectic_self, add_zero, symplectic_comm]

/-- The parity of the number of `XZ` factors in an ordered word. -/
def quadraticPhase (v : Label) : Bit := cocycle v v

@[simp] theorem quadraticPhase_zero : quadraticPhase 0 = 0 := by
  simp [quadraticPhase]

/-- The symplectic pairing is the polarization of the square/transpose parity. -/
theorem quadraticPhase_add (v w : Label) :
    quadraticPhase (v + w) = quadraticPhase v + quadraticPhase w + symplectic v w := by
  simp only [quadraticPhase, cocycle_add_left, cocycle_add_right, symplectic]
  ring

/-- The product cocycle after multiplying the word at `v` by the sign `(-1)^(f v)`.
An arbitrary `f` need not give a bilinear cocycle. -/
def rephasedCocycle (f : Label → Bit) (v w : Label) : Bit :=
  cocycle v w + f v + f w + f (v + w)

@[simp] theorem rephasedCocycle_zero_left (f : Label → Bit) (v : Label) :
    rephasedCocycle f 0 v = f 0 := by
  simp [rephasedCocycle, add_assoc, CharTwo.add_self_eq_zero]

@[simp] theorem rephasedCocycle_zero_right (f : Label → Bit) (v : Label) :
    rephasedCocycle f v 0 = f 0 := by
  simp only [rephasedCocycle, cocycle_zero_right, zero_add, add_zero]
  ring_nf
  simp

/-- Rephasing preserves the associativity identity, without a normalization assumption. -/
theorem rephasedCocycle_assoc (f : Label → Bit) (u v w : Label) :
    rephasedCocycle f u v + rephasedCocycle f (u + v) w =
      rephasedCocycle f v w + rephasedCocycle f u (v + w) := by
  simp only [rephasedCocycle, cocycle_add_left, cocycle_add_right, add_assoc]
  ring_nf
  simp

/-- Real signs change the ordered cocycle but preserve its commutator pairing. -/
theorem rephasedCocycle_symplectic (f : Label → Bit) (v w : Label) :
    rephasedCocycle f v w + rephasedCocycle f w v = symplectic v w := by
  simp only [rephasedCocycle, symplectic, add_comm w v]
  ring_nf
  simp

theorem rephasedCocycle_self (f : Label → Bit) (v : Label) :
    rephasedCocycle f v v = quadraticPhase v + f 0 := by
  simp [rephasedCocycle, quadraticPhase, add_assoc, CharTwo.add_self_eq_zero]

/-- The quadratic real-sign convention reverses the cocycle; it does not replace it
with the symplectic pairing. -/
theorem rephasedCocycle_quadraticPhase (v w : Label) :
    rephasedCocycle quadraticPhase v w = cocycle w v := by
  rw [rephasedCocycle, quadraticPhase_add, symplectic]
  ring_nf
  simp

/-- The pairing has zero radical on the full four-dimensional binary space. -/
theorem symplectic_nondegenerate (v : Label) :
    (∀ w, symplectic v w = 0) ↔ v = 0 := by
  constructor
  · intro h
    apply Prod.ext
    · apply Prod.ext
      · simpa [symplectic, cocycle] using h ((0, 1), (0, 0))
      · simpa [symplectic, cocycle] using h ((1, 0), (0, 0))
    · apply Prod.ext
      · simpa [symplectic, cocycle] using h ((0, 0), (0, 1))
      · simpa [symplectic, cocycle] using h ((0, 0), (1, 0))
  · rintro rfl
    exact symplectic_zero_left

/-- The nonzero binary vectors, each representing one projective point. -/
def points : Finset Label := Finset.univ.erase 0

@[simp] theorem mem_points (v : Label) : v ∈ points ↔ v ≠ 0 := by
  simp [points]

/-- The three points on the line through distinct nonzero `v` and `w`. -/
def line (v w : Label) : Finset Label := {v, w, v + w}

@[simp] theorem mem_line (u v w : Label) :
    u ∈ line v w ↔ u = v ∨ u = w ∨ u = v + w := by
  simp [line]

theorem line_swap (v w : Label) : line v w = line w v := by
  apply Finset.ext
  intro u
  simp only [mem_line, add_comm w v]
  tauto

theorem line_add_right (v w : Label) : line v (v + w) = line v w := by
  apply Finset.ext
  intro u
  simp only [mem_line, label_add_add_left]
  tauto

theorem line_add_left (v w : Label) : line (v + w) w = line v w := by
  apply Finset.ext
  intro u
  simp only [mem_line, label_add_add_right]
  tauto

theorem add_ne_zero_of_ne {v w : Label} (h : v ≠ w) : v + w ≠ 0 := by
  intro hsum
  have hh := congrArg (fun z : Label => z + w) hsum
  apply h
  simpa only [label_add_add_right, zero_add] using hh

theorem left_ne_add {v w : Label} (hw : w ≠ 0) : v ≠ v + w := by
  intro h
  have hh := congrArg (fun z : Label => v + z) h
  apply hw
  simpa only [label_add_self, label_add_add_left] using hh.symm

theorem right_ne_add {v w : Label} (hv : v ≠ 0) : w ≠ v + w := by
  intro h
  have hh := congrArg (fun z : Label => z + w) h
  apply hv
  simpa only [label_add_self, label_add_add_right] using hh.symm

theorem line_card {v w : Label} (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w) :
    (line v w).card = 3 :=
  Finset.card_eq_three.mpr
    ⟨v, w, v + w, hvw, left_ne_add hw, right_ne_add hv, rfl⟩

theorem line_subset_points {v w : Label}
    (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w) : line v w ⊆ points := by
  intro u hu
  rw [mem_points]
  rcases (mem_line u v w).mp hu with rfl | rfl | rfl
  · exact hv
  · exact hw
  · exact add_ne_zero_of_ne hvw

/-- A binary span of two vectors contains precisely their four subset sums. -/
theorem mem_span_pair_iff (u v w : Label) :
    u ∈ Submodule.span Bit ({v, w} : Set Label) ↔
      u = 0 ∨ u = v ∨ u = w ∨ u = v + w := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, h⟩
    rcases bit_eq_zero_or_one a with rfl | rfl <;>
      rcases bit_eq_zero_or_one b with rfl | rfl <;> simp_all
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨1, 1, by simp⟩

/-- Finite lines are exactly the nonzero parts of native two-generator spans. -/
theorem mem_line_iff_mem_span_pair {v w : Label}
    (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w) (u : Label) :
    u ∈ line v w ↔ u ≠ 0 ∧ u ∈ Submodule.span Bit ({v, w} : Set Label) := by
  rw [mem_line, mem_span_pair_iff]
  constructor
  · intro hu
    refine ⟨?_, Or.inr hu⟩
    rcases hu with rfl | rfl | rfl
    · exact hv
    · exact hw
    · exact add_ne_zero_of_ne hvw
  · rintro ⟨hu, hspan⟩
    exact hspan.resolve_left hu

/-- Distinct nonzero binary generators span a native two-dimensional subspace. -/
theorem finrank_span_pair {v w : Label}
    (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w) :
    Module.finrank Bit (Submodule.span Bit ({v, w} : Set Label)) = 2 := by
  have hli : LinearIndepOn Bit id ({v, w} : Set Label) := by
    apply linearIndepOn_id_pair hv
    intro a
    rcases bit_eq_zero_or_one a with rfl | rfl
    · simpa only [zero_smul] using hw.symm
    · simpa only [one_smul] using hvw
  have hfin : LinearIndepOn Bit id (({v, w} : Finset Label) : Set Label) := by
    simpa only [Finset.coe_pair] using hli
  have hspan : Submodule.span Bit (({v, w} : Finset Label) : Set Label) =
      Submodule.span Bit ({v, w} : Set Label) :=
    congrArg (Submodule.span Bit) (Finset.coe_pair (a := v) (b := w))
  calc
    Module.finrank Bit (Submodule.span Bit ({v, w} : Set Label)) =
        Module.finrank Bit (Submodule.span Bit (({v, w} : Finset Label) : Set Label)) :=
      congrArg (fun S : Submodule Bit Label => Module.finrank Bit S) hspan.symm
    _ = ({v, w} : Finset Label).card := finrank_span_finset_eq_card hfin
    _ = 2 := Finset.card_pair hvw

/-- Every two different members of a binary projective line determine it. -/
theorem line_eq_of_mem {u t v w : Label}
    (hu : u ∈ line v w) (ht : t ∈ line v w) (hut : u ≠ t) :
    line u t = line v w := by
  rcases (mem_line u v w).mp hu with hu | hu | hu <;>
    rcases (mem_line t v w).mp ht with ht | ht | ht <;>
    subst u <;> subst t
  · exact (hut rfl).elim
  · rfl
  · exact line_add_right v w
  · exact line_swap w v
  · exact (hut rfl).elim
  · rw [line_swap, line_add_left]
  · rw [line_swap, line_add_right]
  · exact line_add_left v w
  · exact (hut rfl).elim

/-- Every pair of distinct points on a binary line has the same pairing. -/
theorem symplectic_eq_of_distinct_mem_line {u t v w : Label}
    (hu : u ∈ line v w) (ht : t ∈ line v w) (hut : u ≠ t) :
    symplectic u t = symplectic v w := by
  rcases (mem_line u v w).mp hu with hu | hu | hu <;>
    rcases (mem_line t v w).mp ht with ht | ht | ht <;>
    subst u <;> subst t
  · exact (hut rfl).elim
  · rfl
  · exact symplectic_left_add v w
  · exact symplectic_comm w v
  · exact (hut rfl).elim
  · exact symplectic_right_add v w
  · rw [symplectic_comm, symplectic_left_add]
  · rw [symplectic_comm, symplectic_right_add]
  · exact (hut rfl).elim

/-- All projective lines, deduplicated from ordered pairs of generators. -/
def lines : Finset (Finset Label) :=
  (Finset.univ.filter (fun p : Label × Label =>
    p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 ≠ p.2)).image (fun p => line p.1 p.2)

theorem mem_lines_iff (L : Finset Label) :
    L ∈ lines ↔ ∃ v w : Label, v ≠ 0 ∧ w ≠ 0 ∧ v ≠ w ∧ L = line v w := by
  simp only [lines, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨v, w⟩, ⟨hv, hw, hvw⟩, hL⟩
    exact ⟨v, w, hv, hw, hvw, hL.symm⟩
  · rintro ⟨v, w, hv, hw, hvw, hL⟩
    exact ⟨(v, w), ⟨hv, hw, hvw⟩, hL.symm⟩

theorem line_mem_lines {v w : Label} (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w) :
    line v w ∈ lines :=
  (mem_lines_iff _).mpr ⟨v, w, hv, hw, hvw, rfl⟩

theorem card_of_mem_lines {L : Finset Label} (hL : L ∈ lines) : L.card = 3 := by
  obtain ⟨v, w, hv, hw, hvw, rfl⟩ := (mem_lines_iff L).mp hL
  exact line_card hv hw hvw

/-- The unique line through any two distinct projective points. -/
theorem exists_unique_line {v w : Label}
    (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w) :
    ∃! L, L ∈ lines ∧ v ∈ L ∧ w ∈ L := by
  refine ⟨line v w, ⟨line_mem_lines hv hw hvw, ?_, ?_⟩, ?_⟩
  · simp
  · simp
  · intro L hL
    obtain ⟨a, b, _, _, _, rfl⟩ := (mem_lines_iff L).mp hL.1
    exact (line_eq_of_mem hL.2.1 hL.2.2 hvw).symm

/-- Pairwise isotropy of a line is equivalent to the pairing of its generators. -/
theorem line_isotropic_iff (v w : Label) :
    (∀ x ∈ line v w, ∀ y ∈ line v w, symplectic x y = 0) ↔
      symplectic v w = 0 := by
  constructor
  · intro h
    exact h v (by simp) w (by simp)
  · intro h x hx y hy
    by_cases hxy : x = y
    · subst y
      exact symplectic_self x
    · rw [symplectic_eq_of_distinct_mem_line hx hy hxy, h]

/-- The totally isotropic lines for the binary symplectic form. -/
def commutingLines : Finset (Finset Label) :=
  lines.filter (fun L => ∀ x ∈ L, ∀ y ∈ L, symplectic x y = 0)

theorem commutingLines_subset_lines : commutingLines ⊆ lines :=
  Finset.filter_subset _ _

theorem line_mem_commutingLines_iff {v w : Label}
    (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w) :
    line v w ∈ commutingLines ↔ symplectic v w = 0 := by
  simp only [commutingLines, Finset.mem_filter, line_mem_lines hv hw hvw, true_and,
    line_isotropic_iff]

theorem points_card : points.card = 15 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem lines_card : lines.card = 35 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem commutingLines_card : commutingLines.card = 15 := by decide +kernel

theorem noncommutingLines_card : (lines \ commutingLines).card = 20 := by
  rw [Finset.card_sdiff_of_subset commutingLines_subset_lines, lines_card, commutingLines_card]

end InfoGeometry.Projective.BinarySymplectic
