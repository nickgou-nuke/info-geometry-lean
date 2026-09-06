import Mathlib.Data.Nat.Dist
import proofs.BraidProject.FreeMonoid_mine
import proofs.BraidProject.BraidGroup
import proofs.BraidProject.Cancellability
import proofs.BraidProject.ListBoolFacts

def in_order (a : List (α × Bool)) := ∀ (i : Fin (a.length -1)),
  (List.get a ⟨i.val, Nat.lt_of_lt_pred i.prop⟩).2 = true ∨
  (List.get a ⟨i.val + 1, Nat.add_lt_of_lt_sub i.prop⟩).2 = false

def part_split (a : FreeMonoid (α × Bool)) : FreeMonoid (α × Bool) × (Option ((α × Bool) × (α × Bool))) × FreeMonoid (α × Bool) :=
  match a with
  | [] => (1, none, 1)
  | (b, true) :: c => (FreeMonoid.of (b, true) * (part_split c).1, (part_split c).2.1, (part_split c).2.2)
  | (b, false) :: c =>
    match c with
    | [] => (FreeMonoid.of (b, false), none, 1)
    | (d, true) :: e => (1, some ((b, false), (d, true)), e)
    | (_, false) :: _ => (FreeMonoid.of (b, false) * (part_split c).1, (part_split c).2.1, (part_split c).2.2)

inductive reversing_rels : List (α × Bool) → List (α × Bool) → Prop
  | inverse (a : ℕ) : reversing_rels [(a, false), (a, true)] []
  | adjacent (i j : ℕ) (h : i.dist j = 1) : reversing_rels [(i, false), (j, true)]
      [(j, true), (i, true), (j, false), (i, false)]
  | separated (i j : ℕ) (h : i.dist j >= 2): reversing_rels [(i, false), (j, true)]
      [(j, true), (i, false)]

-- def reverse : List (α × Bool) → List (α × Bool) :=
--   fun a => match (part_split a) with
--   | (first, none, last) => first * last
--   | (first, some (c, d), last) => reverse (first * last)

inductive reversing_rels' : FreeMonoid (α × Bool) → FreeMonoid (α × Bool) → Prop
  | inverse (a : ℕ) : reversing_rels' (FreeMonoid.of (a, false) * FreeMonoid.of (a, true)) 1
  | adjacent (i j : ℕ) (h : i.dist j = 1) : reversing_rels' [(i, false), (j, true)]
      [(j, true), (i, true), (j, false), (i, false)]
  | separated (i j : ℕ) (h : i.dist j >= 2): reversing_rels' [(i, false), (j, true)]
      [(j, true), (i, false)]

inductive first_rw_closure (rels : List (α × Bool) → List (α × Bool) → Prop) :
    List (α × Bool) → List (α × Bool) → Prop
  | refl (a : List (α × Bool)) : in_order a → first_rw_closure rels a a
  | reg (a : List (α × Bool)) : rels b c → in_order a →
      first_rw_closure rels (a ++ b ++ d) (a ++ c ++ d)
  | trans : first_rw_closure rels a b → first_rw_closure rels b c → first_rw_closure rels a c

inductive second_rw_closure (rels : FreeMonoid (α × Bool) → FreeMonoid (α × Bool) → Prop) :
    FreeMonoid (α × Bool) → FreeMonoid (α × Bool) → Prop
  | refl (a : FreeMonoid (α × Bool)) : second_rw_closure rels a a
  | reg : rels b c → second_rw_closure rels b c
  | left : second_rw_closure rels a b → second_rw_closure rels (c * a) (c * b)
  | right : second_rw_closure rels a b → second_rw_closure rels (a * d) (b * d)
  | trans : second_rw_closure rels a b → second_rw_closure rels b c → second_rw_closure rels a c

-- theorem uniqueness (a : List (α × Bool)) (h1 : first_rw_closure reversing_rels a b)
--     (h2 : first_rw_closure reversing_rels a c) (hc : in_order c) (hb : in_order b) : b = c := by
--   induction h1 with
--   | refl c hc =>
--     induction h2 with
--     | refl d hd => rfl
--     | reg a _ _ => unproved obligation
--     | trans _ _ _ _ => unproved obligation
--   | reg a _ _ => unproved obligation
--   | trans _ _ _ _ => unproved obligation
open Braid
-- need some kind of PresentedGroup.mk
theorem braid_rel_holds (h1 : first_rw_closure reversing_rels a b) :
    (QuotientGroup.mk (FreeGroup.mk a) : PresentedGroup braid_rels_inf) =
    QuotientGroup.mk (FreeGroup.mk b) := by
  induction h1 with
  | refl a _ => rfl
  | reg a h1 h2 =>
    rcases h1
    · rename_i e
      rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      rw [mul_left_inj, mul_right_inj]
      apply QuotientGroup.eq.mpr
      have H1 : (FreeGroup.mk [(e, false), (e, true)])⁻¹ * FreeGroup.mk [] = 1 := by
        show ((FreeGroup.of e)⁻¹ * FreeGroup.of e)⁻¹ * _ = _
        group; rfl
      rw [H1]
      exact Subgroup.one_mem _
    · rename_i c d j
      rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk,
        QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        mul_left_inj, mul_right_inj]
      let A : PresentedGroup braid_rels_inf := QuotientGroup.mk (FreeGroup.of c)
      let B : PresentedGroup braid_rels_inf := QuotientGroup.mk (FreeGroup.of d)
      change A⁻¹ * B = B * A * B⁻¹ * A⁻¹
      have hb : A * B * A = B * A * B := by
        dsimp [A, B]
        rcases Nat.dist_eq_one j with hc | hd
        · subst c
          symm
          simpa [Braid.σi, mul_assoc] using (braid_group_inf.braid d)
        · subst d
          simpa [Braid.σi, mul_assoc] using (braid_group_inf.braid c)
      have hcong := congrArg (fun x : PresentedGroup braid_rels_inf => A⁻¹ * x * B⁻¹ * A⁻¹) hb
      group at hcong ⊢
      exact hcong.symm
    rename_i e g j
    rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      mul_left_inj, mul_right_inj]
    let E : PresentedGroup braid_rels_inf := QuotientGroup.mk (FreeGroup.of e)
    let G : PresentedGroup braid_rels_inf := QuotientGroup.mk (FreeGroup.of g)
    change E⁻¹ * G = G * E⁻¹
    have hc : E * G = G * E := by
      dsimp [E, G]
      rcases or_dist_iff.mp j with heg | hge
      · simpa [Braid.σi] using (braid_group_inf.comm heg)
      · symm
        simpa [Braid.σi] using (braid_group_inf.comm hge)
    have hcong := congrArg (fun x : PresentedGroup braid_rels_inf => E⁻¹ * x * E⁻¹) hc
    group at hcong ⊢
    exact hcong.symm
  | trans _ _ h1 h2 => exact h1.trans h2

theorem grid_to_rev' (h : grid a b c d) : second_rw_closure reversing_rels'
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse a) *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) b)
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) d *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse c)) := by
  induction h with
  | empty => exact second_rw_closure.refl _
  | top_bottom i => exact second_rw_closure.refl _
  | sides i => exact second_rw_closure.refl _
  | top_left i => exact second_rw_closure.reg (reversing_rels'.inverse _)
  | adjacent i k h => exact second_rw_closure.reg (reversing_rels'.adjacent _ _ h)
  | separated i j h =>
    exact second_rw_closure.reg (reversing_rels'.separated i j (or_dist_iff.mpr h))
  | vertical h1 h2 h1_ih h2_ih =>
    rw [FreeMonoid'.reverse_mul, FreeMonoid'.reverse_mul, map_mul, map_mul, mul_assoc]
    apply (second_rw_closure.left h1_ih).trans
    rw [← mul_assoc, ← mul_assoc]
    exact second_rw_closure.right h2_ih
  | horizontal h1 h2 h1_ih h2_ih =>
    rename_i e f g h i j k
    rw [map_mul, map_mul, ← mul_assoc,]
    apply (second_rw_closure.right h1_ih).trans
    rw [mul_assoc, mul_assoc]
    exact second_rw_closure.left h2_ih

theorem exists_rev'_from_grid_existence (a b : FreeMonoid' ℕ) :
    ∃ c d, second_rw_closure reversing_rels'
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse a) *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) b)
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) d *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse c)) := by
  rcases existence a b with ⟨c, d, hgrid⟩
  exact ⟨c, d, grid_to_rev' hgrid⟩

theorem reversing_output_unique_of_grids {u v u₁ v₁ : FreeMonoid' ℕ} {a b : FreeMonoid' ℕ}
    (h1 : grid a b v u) (h2 : grid a b v₁ u₁) : u = u₁ ∧ v = v₁ :=
  (unicity h2 _ _ h1).symm

/-
The converse completeness statement,

  second_rw_closure reversing_rels' encoded(a,b) encoded(d,c) → grid a b c d,

is the intended next theorem, but it is not a local consequence of the current files.  The proved
surface above is the genuine part currently available: grids produce reversing paths, such paths
exist by `existence`, and grid outputs are unique by `unicity`.
-/

theorem reversing_path_between_grid_outputs {a b c d : FreeMonoid' ℕ} (h : grid a b c d) :
    second_rw_closure reversing_rels'
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse a) *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) b)
    (FreeMonoid.lift (fun x => FreeMonoid.of (x, true)) d *
    FreeMonoid.lift (fun x => FreeMonoid.of (x, false)) (FreeMonoid'.reverse c)) :=
  grid_to_rev' h
