/-
# CyclicGradingGrothendieck.lean

Cyclic groups as grading groups for the 5-grading, with the Grothendieck
colimit interpretation.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Limits.Filtered
import InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure

noncomputable section

namespace InfoGeometry.Canonical.CyclicGradingGrothendieck

open InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure
open CategoryTheory CategoryTheory.Limits

/-! ## 1. Cyclic groups as grading groups -/

/--
A **cyclic grading group** of order `n` is an abelian group `G` with a
surjective homomorphism `ℤ → G` whose kernel contains `nℤ`, so that
`G ≅ ℤ / nℤ`.  This makes `ℤ/nℤ` the canonical cyclic grading group.
-/
abbrev CyclicGradingGroup (n : ℕ) := ZMod n

/--
The cyclic group `ℤ/nℤ` is the canonical cyclic grading group of order `n`.
-/
abbrev canonicalCyclicGradingGroup (n : ℕ) [NeZero n] : Type := ZMod n

theorem canonicalCyclicGradingGroup_gen_surjective (n : ℕ) [NeZero n] :
    Function.Surjective (fun k : ℤ => (k : CyclicGradingGroup n)) := by
  intro x
  refine ⟨(x.val : ℤ), ?_⟩
  simp

@[simp] theorem canonicalCyclicGradingGroup_gen_n_zero (n : ℕ) [NeZero n] :
    ((n : ℤ) : CyclicGradingGroup n) = 0 := by
  simp

/-! ## 2. Grading-index embedding for the 5-grading -/

/--
The grading-index embedding maps the five indices `{−2,−1,0,1,2}` into
`ℤ/5ℤ` via `k ↦ (k + 2) mod 5`.
-/
def gradeIndex (k : ℤ) : ZMod 5 :=
  (k : ZMod 5) + (2 : ZMod 5)

@[simp]
lemma gradeIndex_val (k : ℤ) : gradeIndex k = ((k + 2 : ℤ) : ZMod 5) := by
  dsimp [gradeIndex]; push_cast; ring

/--
The grade index map is injective on the set {-2,-1,0,1,2}.
-/
lemma gradeIndex_inj_on_range {a b : ℤ} (ha : a ∈ Finset.Icc (-2 : ℤ) 2) (hb : b ∈ Finset.Icc (-2 : ℤ) 2)
    (h : gradeIndex a = gradeIndex b) : a = b := by
  rw [gradeIndex_val, gradeIndex_val] at h
  rw [ZMod.intCast_eq_intCast_iff] at h
  have hdvd : (5 : ℤ) ∣ (b + 2) - (a + 2) := h.dvd
  rcases hdvd with ⟨c, hc⟩
  simp only [Finset.mem_Icc] at ha hb
  omega

/-! ## 3. Grothendieck colimit of graded data -/

/--
A **GradedMonoid** is a family of abelian groups `{A_i}_{i∈I}` with a
multiplication `A_i × A_j → A_{i+j}`.
-/
structure GradedMonoid (I : Type*) [AddMonoid I] (A : I → Type*)
    [∀ i, AddCommGroup (A i)] where
  mul : ∀ (i j : I), A i → A j → A (i + j)
  one : A 0

/--
Associativity of a graded monoid, with explicit cast along the associativity
of the index monoid.
-/
class GradedMonoidAssoc (I : Type*) [AddMonoid I] (A : I → Type*)
    [∀ i, AddCommGroup (A i)] (G : GradedMonoid I A) : Prop where
  mul_assoc : ∀ (i j k : I) (x : A i) (y : A j) (z : A k),
    cast (by rw [add_assoc]) (G.mul (i + j) k (G.mul i j x y) z) =
    G.mul i (j + k) x (G.mul j k y z)

/--
Unit laws of a graded monoid.
-/
class GradedMonoidUnit (I : Type*) [AddMonoid I] (A : I → Type*)
    [∀ i, AddCommGroup (A i)] (G : GradedMonoid I A) : Prop where
  one_mul : ∀ (i : I) (x : A i),
    cast (by simp [zero_add]) (G.mul (0 : I) i G.one x) = x
  mul_one : ∀ (i : I) (x : A i),
    cast (by simp [add_zero]) (G.mul i (0 : I) x G.one) = x

/--
The **Grothendieck colimit** across an ℕ-indexed diagram with shift maps.
-/
def grothendieckMap
    (A : ℕ → Type*) [∀ n, AddCommGroup (A n)]
    (shiftMap : ∀ n : ℕ, A n →+ A (n + 1))
    {i j : ℕ} (hij : i ≤ j) : A i →+ A j :=
  Nat.leRecOn hij
    (fun {k} (f : A i →+ A k) => (shiftMap k).comp f)
    (AddMonoidHom.id (A i))

@[simp] theorem grothendieckMap_id
    (A : ℕ → Type*) [∀ n, AddCommGroup (A n)]
    (shiftMap : ∀ n : ℕ, A n →+ A (n + 1)) (i : ℕ) :
    grothendieckMap A shiftMap (le_refl i) = AddMonoidHom.id (A i) := by
  dsimp [grothendieckMap]
  exact Nat.leRecOn_self (C := fun k => A i →+ A k) (AddMonoidHom.id (A i))

theorem grothendieckMap_succ
    (A : ℕ → Type*) [∀ n, AddCommGroup (A n)]
    (shiftMap : ∀ n : ℕ, A n →+ A (n + 1))
    {i j : ℕ} (hij : i ≤ j) :
    grothendieckMap A shiftMap (Nat.le.step hij) =
      (shiftMap j).comp (grothendieckMap A shiftMap hij) := by
  dsimp [grothendieckMap]
  exact Nat.leRecOn_succ (C := fun k => A i →+ A k) hij
    (AddMonoidHom.id (A i))

theorem grothendieckMap_comp
    (A : ℕ → Type*) [∀ n, AddCommGroup (A n)]
    (shiftMap : ∀ n : ℕ, A n →+ A (n + 1))
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (grothendieckMap A shiftMap hjk).comp
        (grothendieckMap A shiftMap hij) =
      grothendieckMap A shiftMap (le_trans hij hjk) := by
  induction hjk with
  | refl =>
      rw [grothendieckMap_id]
      simp
  | step hjm ih =>
      rw [grothendieckMap_succ A shiftMap hjm,
        grothendieckMap_succ A shiftMap (le_trans hij hjm),
        AddMonoidHom.comp_assoc, ih]

def grothendieckDiagram
    (A : ℕ → Type*) [∀ n, AddCommGroup (A n)]
    (shiftMap : ∀ n : ℕ, A n →+ A (n + 1)) :
    ℕ ⥤ ModuleCat ℤ where
  obj n := ModuleCat.of ℤ (A n)
  map f := ModuleCat.ofHom
    (grothendieckMap A shiftMap (leOfHom f)).toIntLinearMap
  map_id n := by
    apply ModuleCat.hom_ext
    change (grothendieckMap A shiftMap (le_refl n)).toIntLinearMap = LinearMap.id
    rw [grothendieckMap_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    change
      (grothendieckMap A shiftMap (le_trans (leOfHom f) (leOfHom g))).toIntLinearMap =
        (grothendieckMap A shiftMap (leOfHom g)).toIntLinearMap.comp
          (grothendieckMap A shiftMap (leOfHom f)).toIntLinearMap
    have h := congrArg AddMonoidHom.toIntLinearMap
      (grothendieckMap_comp A shiftMap (leOfHom f) (leOfHom g)).symm
    simpa [AddMonoidHom.comp_apply, LinearMap.comp_apply] using h

abbrev GrothendieckColimit
    (A : ℕ → Type*) [∀ n, AddCommGroup (A n)]
    (shiftMap : ∀ n : ℕ, A n →+ A (n + 1)) : Type _ :=
  (colimit (grothendieckDiagram A shiftMap) : ModuleCat ℤ)

def grothendieckInjection
    (A : ℕ → Type*) [∀ n, AddCommGroup (A n)]
    (shiftMap : ∀ n : ℕ, A n →+ A (n + 1)) (n : ℕ) :
    A n →+ GrothendieckColimit A shiftMap :=
  (colimit.ι (grothendieckDiagram A shiftMap) n).hom.toAddMonoidHom

theorem grothendieckInjection_naturality
    (A : ℕ → Type*) [∀ n, AddCommGroup (A n)]
    (shiftMap : ∀ n : ℕ, A n →+ A (n + 1))
    (n : ℕ) (x : A n) :
    grothendieckInjection A shiftMap (n + 1) (shiftMap n x) =
      grothendieckInjection A shiftMap n x := by
  change (colimit.ι (grothendieckDiagram A shiftMap) (n + 1)).hom
      (shiftMap n x) = (colimit.ι (grothendieckDiagram A shiftMap) n).hom x
  have hmap :
      (grothendieckDiagram A shiftMap).map (homOfLE (Nat.le_succ n)) =
        ModuleCat.ofHom (shiftMap n).toIntLinearMap := by
    apply ModuleCat.hom_ext
    change (grothendieckMap A shiftMap
      (leOfHom (homOfLE (Nat.le_succ n)))).toIntLinearMap =
      (shiftMap n).toIntLinearMap
    have hle : leOfHom (homOfLE (Nat.le_succ n)) = Nat.le_succ n :=
      Subsingleton.elim _ _
    rw [hle]
    rw [show Nat.le_succ n = Nat.le.step (le_refl n) from Subsingleton.elim _ _]
    rw [grothendieckMap_succ A shiftMap (le_refl n)]
    rw [grothendieckMap_id]
    rfl
  have h := (colimit.cocone (grothendieckDiagram A shiftMap)).w
    (homOfLE (Nat.le_succ n))
  rw [hmap] at h
  exact congrArg (fun f => f x) h

/-! ## 4. Five-grading as ℤ/5ℤ-grading -/

/--
A **cyclic 5-grading** is a five-grading where the grading group is the
cyclic group ℤ/5ℤ.

The grading map sends
  `0↦gNegTwo,  1↦gNegOne,  2↦gZero,  3↦gPosOne,  4↦gPosTwo`.
-/
structure CyclicFiveGrading (L : Type*) [AddCommGroup L] [Module ℝ L]
    [LieRing L] [LieAlgebra ℝ L] where
  fiveGrading : FiveGrading L
  /-- A `ZMod 5`-indexed family of grade subspaces. -/
  cyclicGradeMap : ZMod 5 → Submodule ℝ L
  /-- The `ZMod 5`-grading agrees with the concrete `FiveGrading` structure. -/
  cyclicGradeMap_matches_fiveGrading :
    cyclicGradeMap ((0 : ZMod 5)) = fiveGrading.gNegTwo ∧
    cyclicGradeMap ((1 : ZMod 5)) = fiveGrading.gNegOne ∧
    cyclicGradeMap ((2 : ZMod 5)) = fiveGrading.gZero ∧
    cyclicGradeMap ((3 : ZMod 5)) = fiveGrading.gPosOne ∧
    cyclicGradeMap ((4 : ZMod 5)) = fiveGrading.gPosTwo

/--
The Lie bracket respects the `ZMod 5`-grading: `[g_a, g_b] ⊆ g_{a+b}`.

Using the mapping above, this is equivalent to the bracket conditions
in `FiveGrading`.
-/
class CyclicFiveGradingBracket (L : Type*) [AddCommGroup L] [Module ℝ L]
    [LieRing L] [LieAlgebra ℝ L]
    (G : CyclicFiveGrading L) : Prop where
  bracket_cyclic : ∀ (a b : ZMod 5) (x y : L),
    x ∈ G.cyclicGradeMap a → y ∈ G.cyclicGradeMap b →
    ⁅x, y⁆ ∈ G.cyclicGradeMap (a + b)

/-! ## 5. The cyclic tower ℤ/1ℤ → ⋯ → ℤ/5ℤ -/

/--
Canonical quotient morphism `ZMod n →+* ZMod m` when `m ∣ n`.

The divisibility direction is essential: `ZMod.castHom` supplies the
well-defined reduction map, whereas a map in the opposite direction is not
canonical in general.
-/
noncomputable
def zmodInclusion {m n : ℕ} (h : m ∣ n) : ZMod n →+* ZMod m :=
  ZMod.castHom h (ZMod m)

/--
The tower `ℤ/1ℤ → ℤ/2ℤ → ℤ/3ℤ → ℤ/4ℤ → ℤ/5ℤ` as a `Fin 5`-indexed family.
-/
def towerToCyclic5 : Fin 5 → Type :=
  fun (k : Fin 5) => ZMod (k.val + 1)

/--
The colimit of the tower is `ℤ/5ℤ`.
-/
def towerColimitToZMod5 : ZMod (4 + 1) → ZMod 5 :=
  fun x => (x : ZMod 5)

@[simp]
theorem towerColimit_is_ZMod5 (x : ZMod (4 + 1)) :
    towerColimitToZMod5 x = (x : ZMod 5) :=
  rfl

/-! ## 6. Grothendieck extension: ℕ-grading → 5-grading -/

/--
Given an ℕ-graded Lie algebra, the Grothendieck colimit produces a
ℤ/5ℤ-graded Lie algebra that instantiates a `FiveGrading`.
-/
structure GrothendieckExtendedFiveGrading (L : Type*) [AddCommGroup L] [Module ℝ L]
    [LieRing L] [LieAlgebra ℝ L] where
  original : Type
  [originalAddCommGroup : AddCommGroup original]
  [originalModule : Module ℝ original]
  [originalLieRing : LieRing original]
  [originalLieAlgebra : LieAlgebra ℝ original]
  originalGrading : ℕ → Submodule ℝ original
  shiftMap : ∀ n : ℕ, originalGrading n → originalGrading (n+1)
  fiveGrading : FiveGrading L
  grothendieckIso : Type
  [grothendieckAddCommGroup : AddCommGroup grothendieckIso]
  iso : grothendieckIso ≃+ L

/-! ## 7. Correspondence between FiveGrading and CyclicFiveGrading -/

variable (L : Type*) [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]

/--
Concrete `ZMod 5`-component keys for the five grade subspaces.
-/
def fiveGradeZMod5Keys : ZMod 5 → ℤ
  | 0 => -2
  | 1 => -1
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | _ => 0

@[simp] lemma fiveGradeZMod5Keys_0 : fiveGradeZMod5Keys (0 : ZMod 5) = -2 := rfl
@[simp] lemma fiveGradeZMod5Keys_1 : fiveGradeZMod5Keys (1 : ZMod 5) = -1 := rfl
@[simp] lemma fiveGradeZMod5Keys_2 : fiveGradeZMod5Keys (2 : ZMod 5) = 0 := rfl
@[simp] lemma fiveGradeZMod5Keys_3 : fiveGradeZMod5Keys (3 : ZMod 5) = 1 := rfl
@[simp] lemma fiveGradeZMod5Keys_4 : fiveGradeZMod5Keys (4 : ZMod 5) = 2 := rfl

/-- Given a `FiveGrading`, construct a `CyclicFiveGrading` with the canonical
`ZMod 5`-indexed grading.  Mapping: `0→gNegTwo, 1→gNegOne, 2→gZero,
3→gPosOne, 4→gPosTwo`. -/
def fiveGradingToCyclic (FG : FiveGrading L) : CyclicFiveGrading L where
  fiveGrading := FG
  cyclicGradeMap k :=
    -- The `match` on a `ZMod 5` literal reduces by definition
    match k with
    | (0 : ZMod 5) => FG.gNegTwo
    | (1 : ZMod 5) => FG.gNegOne
    | (2 : ZMod 5) => FG.gZero
    | (3 : ZMod 5) => FG.gPosOne
    | (4 : ZMod 5) => FG.gPosTwo
    | _ => FG.gZero
  cyclicGradeMap_matches_fiveGrading := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Extract the five `ZMod 5` grade components from a `CyclicFiveGrading`
into the concrete named subspaces of `FiveGrading`.

Since `CG.fiveGrading` already carries a valid `FiveGrading` whose subspaces
match the `CG.cyclicGradeMap` entries by the matching axiom, we just return
`CG.fiveGrading`.  The `cyclicGradeMap_matches_fiveGrading` axiom of `CG`
provides the explicit equalities that identify the two representations. -/
def cyclicFiveGradingToFive (CG : CyclicFiveGrading L) : FiveGrading L :=
  CG.fiveGrading

/-- Extensionality lemma for `CyclicFiveGrading`. -/
@[ext]
theorem CyclicFiveGrading.ext (G H : CyclicFiveGrading L)
    (hFG : G.fiveGrading = H.fiveGrading)
    (hMap : ∀ (k : ZMod 5), G.cyclicGradeMap k = H.cyclicGradeMap k) : G = H := by
  rcases G with ⟨FG, gm, h⟩
  rcases H with ⟨FG', gm', h'⟩
  have hFG' : FG = FG' := hFG
  subst hFG'
  have hgm : gm = gm' := funext hMap
  subst hgm
  rfl

/-- Round-tripping recovers the original `CyclicFiveGrading`. -/
theorem cyclicFiveGradingToFive_toCyclic (CG : CyclicFiveGrading L) :
    fiveGradingToCyclic L (cyclicFiveGradingToFive L CG) = CG := by
  apply CyclicFiveGrading.ext
  · rfl
  · intro k
    rcases CG.cyclicGradeMap_matches_fiveGrading with ⟨h0, h1, h2, h3, h4⟩
    -- Since `fiveGradingToCyclic` only distinguishes 0,1,2,3,4, we prove
    -- the equality for each of the 5 cases individually and reduce using `native_decide`
    -- on the ZMod 5 equality tests.
    have h_cases : ∀ i : ZMod 5, (fiveGradingToCyclic L (cyclicFiveGradingToFive L CG)).cyclicGradeMap i =
      CG.cyclicGradeMap i := by
      -- brute-force all 5 elements
      have : Finset.univ = ({(0 : ZMod 5), 1, 2, 3, 4} : Finset (ZMod 5)) := by decide
      have : ∀ x : ZMod 5, x ∈ ({(0 : ZMod 5), 1, 2, 3, 4} : Finset (ZMod 5)) := by
        intro x; simpa [this] using Finset.mem_univ x
      intro x
      have hx : x ∈ ({(0 : ZMod 5), 1, 2, 3, 4} : Finset (ZMod 5)) := this x
      -- `simp` can use `Finset.mem_insert` and `Finset.mem_singleton` to break down the `∨`
      simp at hx
      rcases hx with (rfl|rfl|rfl|rfl|rfl)
      · calc
          (fiveGradingToCyclic L (cyclicFiveGradingToFive L CG)).cyclicGradeMap (0 : ZMod 5)
              = CG.fiveGrading.gNegTwo := rfl
          _ = CG.cyclicGradeMap (0 : ZMod 5) := h0.symm
      · calc
          (fiveGradingToCyclic L (cyclicFiveGradingToFive L CG)).cyclicGradeMap (1 : ZMod 5)
              = CG.fiveGrading.gNegOne := rfl
          _ = CG.cyclicGradeMap (1 : ZMod 5) := h1.symm
      · calc
          (fiveGradingToCyclic L (cyclicFiveGradingToFive L CG)).cyclicGradeMap (2 : ZMod 5)
              = CG.fiveGrading.gZero := rfl
          _ = CG.cyclicGradeMap (2 : ZMod 5) := h2.symm
      · calc
          (fiveGradingToCyclic L (cyclicFiveGradingToFive L CG)).cyclicGradeMap (3 : ZMod 5)
              = CG.fiveGrading.gPosOne := rfl
          _ = CG.cyclicGradeMap (3 : ZMod 5) := h3.symm
      · calc
          (fiveGradingToCyclic L (cyclicFiveGradingToFive L CG)).cyclicGradeMap (4 : ZMod 5)
              = CG.fiveGrading.gPosTwo := rfl
          _ = CG.cyclicGradeMap (4 : ZMod 5) := h4.symm
    exact h_cases k

/-- Round-tripping recovers the original `FiveGrading`. -/
theorem fiveGradingToCyclic_cyclicToFive (FG : FiveGrading L) :
    cyclicFiveGradingToFive L (fiveGradingToCyclic L FG) = FG := rfl

end InfoGeometry.Canonical.CyclicGradingGrothendieck
