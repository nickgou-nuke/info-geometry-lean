import Mathlib.Algebra.AddGroup.Defs
import Mathlib.Tactic.Abel

/-
#### BUCKET 1: CLOSED FINITE THEOREMS
- Setoid + quotient construction for K0 completion
- Well-defined addition and functorial map
- K0_map_add, K0_map_id, K0_map_comp, K0_map_congr
#### BUCKET 2: None. #### BUCKET 3: None.
-/

namespace InfoGeometry.Canonical.K0Functor

structure K0Pair (M : Type _) where
  fst : M
  snd : M

variable {M N : Type _} [AddCommMonoid M] [AddCommMonoid N]

def GrothendieckRel (p q : K0Pair M) : Prop :=
  ∃ k : M, p.fst + q.snd + k = p.snd + q.fst + k

theorem rel_refl (p : K0Pair M) : GrothendieckRel p p := by
  use 0
  rw [add_comm p.fst p.snd]

theorem rel_symm {p q : K0Pair M} (h : GrothendieckRel p q) : GrothendieckRel q p := by
  rcases h with ⟨k, hk⟩
  use k
  have h1 : q.fst + p.snd + k = p.snd + q.fst + k := by abel
  have h2 : q.snd + p.fst + k = p.fst + q.snd + k := by abel
  rw [h1, hk, h2]

theorem rel_trans {p q r : K0Pair M} (h1 : GrothendieckRel p q) (h2 : GrothendieckRel q r) :
    GrothendieckRel p r := by
  rcases h1 with ⟨k1, hk1⟩
  rcases h2 with ⟨k2, hk2⟩
  use (q.fst + q.snd + k1 + k2)
  have h_sum : (p.fst + q.snd + k1) + (q.fst + r.snd + k2) = (p.snd + q.fst + k1) + (q.snd + r.fst + k2) := by
    rw [hk1, hk2]
  have hl : (p.fst + q.snd + k1) + (q.fst + r.snd + k2) = p.fst + r.snd + (q.fst + q.snd + k1 + k2) := by abel
  have hr : (p.snd + q.fst + k1) + (q.snd + r.fst + k2) = p.snd + r.fst + (q.fst + q.snd + k1 + k2) := by abel
  rw [hl, hr] at h_sum
  exact h_sum

def GrothendieckSetoid (M : Type _) [AddCommMonoid M] : Setoid (K0Pair M) where
  r := GrothendieckRel
  iseqv := { refl := rel_refl, symm := rel_symm, trans := rel_trans }

def K0 (M : Type _) [AddCommMonoid M] : Type _ := Quotient (GrothendieckSetoid M)

def pair_add (p q : K0Pair M) : K0Pair M := ⟨p.fst + q.fst, p.snd + q.snd⟩

theorem pair_add_well_defined {p1 p2 q1 q2 : K0Pair M} (hp : GrothendieckRel p1 p2)
    (hq : GrothendieckRel q1 q2) : GrothendieckRel (pair_add p1 q1) (pair_add p2 q2) := by
  rcases hp with ⟨kp, hkp⟩; rcases hq with ⟨kq, hkq⟩; use (kp + kq)
  have h : (p1.fst + p2.snd + kp) + (q1.fst + q2.snd + kq) = (p1.snd + p2.fst + kp) + (q1.snd + q2.fst + kq) := by rw [hkp, hkq]
  have hl : (p1.fst + p2.snd + kp) + (q1.fst + q2.snd + kq) = (p1.fst + q1.fst) + (p2.snd + q2.snd) + (kp + kq) := by abel
  have hr : (p1.snd + p2.fst + kp) + (q1.snd + q2.fst + kq) = (p1.snd + q1.snd) + (p2.fst + q2.fst) + (kp + kq) := by abel
  rw [hl, hr] at h; exact h

def K0.add (M : Type _) [AddCommMonoid M] : K0 M → K0 M → K0 M :=
  Quotient.map₂ pair_add pair_add_well_defined

instance : Add (K0 M) where add := K0.add M

def K0Pair.map (f : M →+ N) (p : K0Pair M) : K0Pair N := ⟨f p.fst, f p.snd⟩

theorem K0Pair_map_well_defined (f : M →+ N) {p q : K0Pair M} (h : GrothendieckRel p q) :
    GrothendieckRel (K0Pair.map f p) (K0Pair.map f q) := by
  rcases h with ⟨k, hk⟩; use f k
  unfold K0Pair.map
  have hf : f (p.fst + q.snd + k) = f (p.snd + q.fst + k) := by rw [hk]
  rw [map_add, map_add] at hf; rw [map_add, map_add]; exact hf

def K0.map (f : M →+ N) : K0 M → K0 N :=
  Quotient.map (K0Pair.map f) (K0Pair_map_well_defined f)

theorem K0_map_add (f : M →+ N) (x y : K0 M) : K0.map f (x + y) = K0.map f x + K0.map f y := by
  refine Quotient.inductionOn₂ x y ?_
  intro p q
  have h : K0Pair.map f (pair_add p q) = pair_add (K0Pair.map f p) (K0Pair.map f q) := by
    unfold K0Pair.map pair_add
    ext
    · exact map_add f p.fst q.fst
    · exact map_add f p.snd q.snd
  rw [h]

theorem K0_map_id (x : K0 M) : K0.map (AddMonoidHom.id M) x = x := by
  refine Quotient.inductionOn x ?_; intro p; rfl

theorem K0_map_comp {P : Type _} [AddCommMonoid P] (f : M →+ N) (g : N →+ P) (x : K0 M) :
    K0.map (g.comp f) x = K0.map g (K0.map f x) := by
  refine Quotient.inductionOn x ?_; intro p; rfl

theorem K0_map_congr {f g : M →+ N} (h : ∀ x, f x = g x) (x : K0 M) : K0.map f x = K0.map g x := by
  refine Quotient.inductionOn x ?_
  intro p
  unfold K0.map
  have heq : K0Pair.map f p = K0Pair.map g p := by
    unfold K0Pair.map
    ext
    · exact h p.fst
    · exact h p.snd
  rw [heq]

end InfoGeometry.Canonical.K0Functor
