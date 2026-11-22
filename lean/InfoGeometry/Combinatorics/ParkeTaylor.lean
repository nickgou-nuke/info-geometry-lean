/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Combinatorics.MHVTriplets
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Tactic

open MvPolynomial

/-!
# Parke-Taylor factors and ordered regions

Combinatorial core of arXiv:2512.25005, Sections 3.3 and 5.1.

For MHV diagrams (`k = 2`) on a finite set of external legs `α`, a cyclic ordering
`σ` of all legs determines a Parke-Taylor factor

    PT(σ) = 1 / (σ₁σ₂)(σ₂σ₃)...(σₙσ₁)

as a rational function in the unsigned Plücker variables `X_{ij}` (one variable per
unordered pair `{i,j}` : `Sym2 α`).  This file formalizes:

- `ptDenom σ` : the denominator polynomial of `PT(σ)` (a product of Plücker variables,
  including the cyclic wrap-around pair `(last, first)`)
- `PT σ` : the Parke-Taylor factor as an element of the fraction field
  `FractionRing (MvPolynomial (Sym2 α) ℚ)`
- `cyclicOrderBool σ a b c` : computes whether `a, b, c` appear in that
  cyclic order around `σ`
- `ptCompatibleBool o σ T` : computes finite ordering and triplet tests
  appearing in Eq. 3.21
- `allOrderings` / `compatibleOrderings` : the list of orderings (resp. compatible ones)
- `f_T` : the canonical function `Σ_{σ ∈ Sₙ(T)} PT(σ)` (Eq. 3.18 / 3.20)

The full Grassmannian geometry (oriented regions `R(εσ)`, Eq. 5.1) and the
sphere-move equivalence (Theorem 3) are layered on this substrate.

## BUCKET 1
`plucker_edge_product_ne_zero`, `ptDenom_ne_zero`, and
`PT_mul_denominator` are kernel-proved polynomial/fraction-field facts.

## BUCKET 2
The ordering and compatibility computations are definitions on finite labels;
no geometric realization is inferred from them here.

## BUCKET 3
The Grassmannian region interpretation, positive canonical form, and sphere-move
equivalence remain outside this file's theorem surface.
-/

namespace InfoGeometry.Combinatorics.ParkeTaylor

/-- A product of Plücker indeterminates is nonzero in the polynomial domain.
This ensures that Parke--Taylor denominators do not vanish as formal rational
functions, even though they can vanish after specialization. -/
theorem plucker_edge_product_ne_zero {α : Type*} (edges : List (α × α)) :
    (List.map (fun p => X (Sym2.mk p.1 p.2)) edges).prod ≠
      (0 : MvPolynomial (Sym2 α) ℚ) := by
  induction edges with
  | nil => simp
  | cons edge edges ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_ne_zero (MvPolynomial.X_ne_zero _) ih

variable {α : Type*}

/-- The Plücker variable `X_{ij}` as an element of the fraction field.
    Since `Sym2.mk i j = Sym2.mk j i`, this is the unsigned variable `{i,j}`. -/
noncomputable def pluckerVar [BEq α] (i j : α) : FractionRing (MvPolynomial (Sym2 α) ℚ) :=
  algebraMap (MvPolynomial (Sym2 α) ℚ) (FractionRing (MvPolynomial (Sym2 α) ℚ))
    (X (Sym2.mk i j))

/-- Test that a list has no repetitions and has the cardinality of `α`. -/
def isOrderingBool [Fintype α] [DecidableEq α] [BEq α] (σ : List α) : Bool :=
  (if List.Nodup σ then true else false) && (σ.length == Fintype.card α)

/-- Compute cyclic order by rotating the word to the first occurrence of `a`
and checking that the resulting index of `b` precedes that of `c`. -/
def cyclicOrderBool [BEq α] (σ : List α) (a b c : α) : Bool :=
  if List.idxOf b (List.drop (List.idxOf a σ) σ ++ List.take (List.idxOf a σ) σ) <
     List.idxOf c (List.drop (List.idxOf a σ) σ ++ List.take (List.idxOf a σ) σ)
  then true else false

/-- Compute the finite compatibility predicate: the list has the right length
and no repetitions, starts at `o`, and satisfies every oriented triplet. -/
noncomputable def ptCompatibleBool [Fintype α] [DecidableEq α] [BEq α] (o : α) (σ : List α)
    (T : Finset (α × α × α)) : Bool :=
  isOrderingBool σ && (List.headD σ o == o) &&
    T.toList.foldl (fun acc t => acc && cyclicOrderBool σ t.1 t.2.1 t.2.2) true

/-- The ordering test is true exactly for a duplicate-free list of the right
cardinality. `LawfulBEq` makes its Boolean length comparison agree with `=`. -/
theorem isOrderingBool_eq_true_iff [Fintype α] [DecidableEq α] [BEq α]
    [LawfulBEq α] (σ : List α) :
    isOrderingBool σ = true ↔ List.Nodup σ ∧ σ.length = Fintype.card α := by
  simp [isOrderingBool]

/-- The Boolean cyclic-order computation is exactly its index inequality. -/
theorem cyclicOrderBool_eq_true_iff [BEq α] (σ : List α) (a b c : α) :
    cyclicOrderBool σ a b c = true ↔
      List.idxOf b (List.drop (List.idxOf a σ) σ ++ List.take (List.idxOf a σ) σ) <
        List.idxOf c (List.drop (List.idxOf a σ) σ ++ List.take (List.idxOf a σ) σ) := by
  simp [cyclicOrderBool]

/-- The fold used for triplet filtering accepts exactly when every list member
passes its Boolean predicate. -/
private theorem foldl_and_eq_true_iff {β : Type*} (xs : List β) (p : β → Bool) :
    xs.foldl (fun acc x => acc && p x) true = true ↔ ∀ x ∈ xs, p x = true := by
  suffices haux : ∀ (acc : Bool),
      xs.foldl (fun acc x => acc && p x) acc = true ↔
        acc = true ∧ ∀ x ∈ xs, p x = true by
    simpa using haux true
  induction xs with
  | nil =>
      intro acc
      simp
  | cons x xs ih =>
      intro acc
      simp [List.foldl_cons, ih, Bool.and_eq_true, List.mem_cons, and_assoc]

/-- The compatibility computation agrees with its finite specification when
Boolean equality on labels is lawful. -/
theorem ptCompatibleBool_eq_true_iff [Fintype α] [DecidableEq α] [BEq α]
    [LawfulBEq α] (o : α) (σ : List α) (T : Finset (α × α × α)) :
    ptCompatibleBool o σ T = true ↔
      (List.Nodup σ ∧ σ.length = Fintype.card α) ∧
        List.headD σ o = o ∧
        ∀ t ∈ T, cyclicOrderBool σ t.1 t.2.1 t.2.2 = true := by
  simp only [ptCompatibleBool, Bool.and_eq_true, isOrderingBool_eq_true_iff,
    beq_iff_eq, foldl_and_eq_true_iff, Finset.mem_toList]
  simp only [and_assoc]

/-- The denominator polynomial of `PT(σ)`: `∏_i X_{σ_i σ_{i+1}}` (cyclic), built from
    adjacent pairs via `zipWith` plus the wrap-around pair `(last, first)`. -/
noncomputable def ptDenom [BEq α] (o : α) (σ : List α) : MvPolynomial (Sym2 α) ℚ :=
  (List.map (fun p => X (Sym2.mk p.1 p.2))
    (List.zipWith (fun a b => (a, b)) σ (List.tail σ) ++
     (if σ ≠ [] then List.singleton (σ.getLastD o, σ.headD o) else []))).prod

/-- `PT(σ) = 1 / ptDenom(σ)` as an element of the fraction field. -/
noncomputable def PT [BEq α] (o : α) (σ : List α) : FractionRing (MvPolynomial (Sym2 α) ℚ) :=
  (1 : FractionRing (MvPolynomial (Sym2 α) ℚ)) /
    (algebraMap (MvPolynomial (Sym2 α) ℚ) (FractionRing (MvPolynomial (Sym2 α) ℚ))
      ((ptDenom o σ : MvPolynomial (Sym2 α) ℚ)))

/-- The cyclic denominator polynomial is nonzero for every finite word of
external labels. This is a generic-polynomial statement, not a nonvanishing
claim after assigning numerical Plücker coordinates. -/
theorem ptDenom_ne_zero [BEq α] (o : α) (σ : List α) :
    ptDenom o σ ≠ 0 := by
  unfold ptDenom
  exact plucker_edge_product_ne_zero
    (List.zipWith (fun a b => (a, b)) σ (List.tail σ) ++
      (if σ ≠ [] then List.singleton (σ.getLastD o, σ.headD o) else []))

/-- The formal Parke--Taylor factor multiplied by its denominator is one in
the fraction field. The denominator nonzero fact is discharged from the
polynomial indeterminate construction above. -/
theorem PT_mul_denominator [BEq α] (o : α) (σ : List α) :
    PT o σ * algebraMap (MvPolynomial (Sym2 α) ℚ)
      (FractionRing (MvPolynomial (Sym2 α) ℚ)) (ptDenom o σ) = 1 := by
  have hden : algebraMap (MvPolynomial (Sym2 α) ℚ)
      (FractionRing (MvPolynomial (Sym2 α) ℚ)) (ptDenom o σ) ≠ 0 := by
    intro hzero
    apply ptDenom_ne_zero o σ
    apply (IsFractionRing.injective (MvPolynomial (Sym2 α) ℚ)
      (FractionRing (MvPolynomial (Sym2 α) ℚ)))
    simpa using hzero
  simp [PT, hden]

/- All orderings of the legs (each permutation of `α` appears exactly once). -/
/-- Enumerate permutations of the finite label type `α`. -/
noncomputable def allOrderings [Fintype α] [DecidableEq α] : List (List α) :=
  List.permutations (Finset.toList (Finset.univ : Finset α))

/-- The orderings compatible with `T` (the set `Sₙ(T)` from Eq. 3.21). -/
noncomputable def compatibleOrderings [Fintype α] [DecidableEq α] [BEq α]
    (o : α) (T : Finset (α × α × α)) : List (List α) :=
  List.filter (fun (σ : List α) => ptCompatibleBool o σ T) allOrderings

/-- The ordering enumeration contains exactly the permutations of the finite
label list. Combined with `allOrderings_nodup`, this shows that every ordering
occurs once rather than merely asserting the enumeration in the definition's
documentation. -/
theorem mem_allOrderings_iff [Fintype α] [DecidableEq α] {σ : List α} :
    σ ∈ allOrderings (α := α) ↔ σ.Perm (Finset.univ.toList) := by
  unfold allOrderings
  exact List.mem_permutations

/-- The finite ordering enumeration has no duplicate entries. -/
theorem allOrderings_nodup [Fintype α] [DecidableEq α] :
    (allOrderings (α := α)).Nodup := by
  unfold allOrderings
  exact List.nodup_permutations _ (Finset.nodup_toList _)

/-- Membership in the compatible-ordering list is equivalent to being a
permutation of all labels, starting at the chosen origin, and passing every
oriented triplet test. This is the exact finite specification of `Sₙ(T)`;
it makes no geometric realization claim. -/
theorem compatibleOrderings_mem_iff [Fintype α] [DecidableEq α] [BEq α]
    [LawfulBEq α] (o : α) (T : Finset (α × α × α)) (σ : List α) :
    σ ∈ compatibleOrderings o T ↔
      σ.Perm (Finset.univ.toList) ∧ List.headD σ o = o ∧
        ∀ t ∈ T, cyclicOrderBool σ t.1 t.2.1 t.2.2 = true := by
  constructor
  · intro h
    rcases List.mem_filter.mp h with ⟨hOrder, hCompatible⟩
    have hSpec := (ptCompatibleBool_eq_true_iff o σ T).mp hCompatible
    exact ⟨mem_allOrderings_iff.mp hOrder, hSpec.2.1, hSpec.2.2⟩
  · rintro ⟨hPerm, hHead, hTriplets⟩
    apply List.mem_filter.mpr
    refine ⟨mem_allOrderings_iff.mpr hPerm, ?_⟩
    apply (ptCompatibleBool_eq_true_iff o σ T).mpr
    refine ⟨?_, hHead, hTriplets⟩
    constructor
    · exact hPerm.nodup_iff.mpr (Finset.nodup_toList _)
    · have hLength := hPerm.length_eq
      simpa using hLength

/- The canonical function `f_T = Σ_{σ ∈ Sₙ(T)} PT(σ)` (Eq. 3.18 / 3.20). -/
/-- Sum formal Parke--Taylor factors over the computed compatible orderings. -/
noncomputable def f_T [Fintype α] [DecidableEq α] [BEq α]
    (o : α) (T : Finset (α × α × α)) : FractionRing (MvPolynomial (Sym2 α) ℚ) :=
  (List.map (PT o) (compatibleOrderings o T)).sum
