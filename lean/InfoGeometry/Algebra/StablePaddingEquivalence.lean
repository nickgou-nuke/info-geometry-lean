/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.StablePresentationEquivalence

/-!
# One-shot stable equivalence of finite matrix presentations

This module treats the existential common-padding formulation of Definitions
13–14 and Proposition 1 of arXiv:2608.09913v2. A padding first adjoins an
identity block, then zero columns, then zero rows. Its matrix is precisely
the canonical block matrix `M ⊕ I_α ⊕ 0_{β,η}`; the intermediate order of
zero-column and zero-row operations is certified by a block-matrix identity.

The two padded matrices are related by one basis change. Only native Sigma
equality is used to identify their dimensions: there are no arbitrary
existential row reindexings. The elementary version restricts only the left
unit, retaining arbitrary units on the right.

The balanced Whitehead matrix acts on appended zero rows just as it acts on
the original rows, while its inverse block leaves the new zero rows zero.
Thus any ordinary padded basis change becomes elementary after adding the
same number of zero rows to each side. Associativity of zero-row padding is
proved using the canonical `Fin.cast` of natural-number associativity.

This directly proves the one-shot ordinary/elementary coincidence. It does
not assert a general normal-form equivalence with the separate `EqvGen`
relations, and does not construct a physical circuit or classify CSS phases.
-/

namespace InfoGeometry.Algebra.StablePaddingEquivalence

open Matrix ElementaryMatrixOperators StablePresentationEquivalence

/-- Equality of packed matrices using only the canonical cast of equal row dimensions. -/
theorem ofMatrix_eq_ofMatrix_of_row_cast {A : Type*} {m m' n : ℕ}
    (h : m = m') (M : Matrix (Fin m) (Fin n) A)
    (N : Matrix (Fin m') (Fin n) A)
    (hMN : ∀ i j, M i j = N (Fin.cast h i) j) :
    ofMatrix M = ofMatrix N := by
  subst m'
  have hmatrix : M = N := by
    ext i j
    exact hMN i j
  cases hmatrix
  rfl

section Ring

variable {A : Type*} [Ring A]

@[simp]
theorem appendZeroRows_castAdd {m n : ℕ} (M : Matrix (Fin m) (Fin n) A)
    (r : ℕ) (i : Fin m) (j : Fin n) :
    appendZeroRows M r (Fin.castAdd r i) j = M i j := by
  simp [appendZeroRows]

@[simp]
theorem appendZeroRows_natAdd {m n : ℕ} (M : Matrix (Fin m) (Fin n) A)
    (r : ℕ) (i : Fin r) (j : Fin n) :
    appendZeroRows M r (Fin.natAdd m i) j = 0 := by
  simp [appendZeroRows]

/-- Two successive zero-row paddings are their sum, with canonical index casts. -/
theorem appendZeroRows_assoc {m n : ℕ} (M : Matrix (Fin m) (Fin n) A)
    (r s : ℕ) :
    ofMatrix (appendZeroRows (appendZeroRows M r) s) =
      ofMatrix (appendZeroRows M (r + s)) := by
  apply ofMatrix_eq_ofMatrix_of_row_cast (Nat.add_assoc m r s)
  intro i j
  refine Fin.addCases (fun i => ?_) (fun k => ?_) i
  · refine Fin.addCases (fun i => ?_) (fun k => ?_) i
    · have hcast :
          Fin.cast (Nat.add_assoc m r s) (Fin.castAdd s (Fin.castAdd r i)) =
            Fin.castAdd (r + s) i := by
        apply Fin.ext
        rfl
      rw [hcast]
      simp
    · have hcast :
          Fin.cast (Nat.add_assoc m r s) (Fin.castAdd s (Fin.natAdd m k)) =
            Fin.natAdd m (Fin.castAdd s k) := by
        apply Fin.ext
        rfl
      rw [hcast]
      simp
  · have hcast :
        Fin.cast (Nat.add_assoc m r s) (Fin.natAdd (m + r) k) =
          Fin.natAdd m (Fin.natAdd r k) := by
      apply Fin.ext
      exact Nat.add_assoc m r k.val
    rw [hcast]
    simp

/-- Zero-column then zero-row padding is the canonical rectangular zero block. -/
theorem zeroPadding_eq_fromBlocks {m n : ℕ} (M : Matrix (Fin m) (Fin n) A)
    (β η : ℕ) :
    appendZeroRows (appendZeroCols M η) β =
      Matrix.reindex
        (finSumFinEquiv : Fin m ⊕ Fin β ≃ Fin (m + β))
        (finSumFinEquiv : Fin n ⊕ Fin η ≃ Fin (n + η))
        (Matrix.fromBlocks M 0 0 (0 : Matrix (Fin β) (Fin η) A)) := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  all_goals refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  all_goals simp [appendZeroRows, appendZeroCols]

/-- Append zero rows while retaining dimensions in the native Sigma carrier. -/
def padRows (P : Presentation A) (r : ℕ) : Presentation A :=
  ofMatrix (appendZeroRows P.2.2 r)

/-- The fixed-order padding `M ⊕ I_α ⊕ 0_{β,η}`. -/
def padding (P : Presentation A) (α β η : ℕ) : Presentation A :=
  ofMatrix (appendZeroRows (appendZeroCols (appendIdentity P.2.2 α) η) β)

/-- The padding definition is the iterated canonical identity/zero block sum. -/
theorem padding_eq_fromBlocks {m n : ℕ} (M : Matrix (Fin m) (Fin n) A)
    (α β η : ℕ) :
    padding (ofMatrix M) α β η =
      ofMatrix (Matrix.reindex
        (finSumFinEquiv : Fin (m + α) ⊕ Fin β ≃ Fin ((m + α) + β))
        (finSumFinEquiv : Fin (n + α) ⊕ Fin η ≃ Fin ((n + α) + η))
        (Matrix.fromBlocks (appendIdentity M α) 0 0
          (0 : Matrix (Fin β) (Fin η) A))) := by
  exact congrArg ofMatrix (zeroPadding_eq_fromBlocks (appendIdentity M α) β η)

/-- Appending zero rows changes only the zero-row padding size. -/
theorem padRows_padding (P : Presentation A) (α β η r : ℕ) :
    padRows (padding P α β η) r = padding P α (β + r) η := by
  rcases P with ⟨m, n, M⟩
  exact appendZeroRows_assoc (appendZeroCols (appendIdentity M α) η) β r

/-- One basis change; native Sigma equality supplies only equal-dimension transport. -/
def BasisEquivalent (G : RowSubgroups A) (P Q : Presentation A) : Prop :=
  ∃ (U : (Matrix (Fin P.1) (Fin P.1) A)ˣ)
    (V : (Matrix (Fin P.2.1) (Fin P.2.1) A)ˣ),
    U ∈ G P.1 ∧
      ofMatrix ((U : Matrix (Fin P.1) (Fin P.1) A) * P.2.2 *
        (V : Matrix (Fin P.2.1) (Fin P.2.1) A)) = Q

/-- Enlarging the allowed row subgroup preserves a single basis change. -/
theorem basisEquivalent_mono {G H : RowSubgroups A} (hGH : ∀ m, G m ≤ H m)
    {P Q : Presentation A} (h : BasisEquivalent G P Q) : BasisEquivalent H P Q := by
  rcases h with ⟨U, V, hU, hQ⟩
  exact ⟨U, V, hGH P.1 hU, hQ⟩

/-- A single unrestricted basis change becomes elementary after common zero-row padding. -/
theorem basisEquivalent_zeroRows {P Q : Presentation A}
    (h : BasisEquivalent (fullRowFamily A) P Q) :
    BasisEquivalent (elementaryRowFamily A) (padRows P P.1) (padRows Q P.1) := by
  rcases P with ⟨m, n, M⟩
  rcases h with ⟨U, V, _hU, hQ⟩
  subst Q
  refine ⟨stabilizedLeft U, V, stabilizedLeft_mem_elementary U, ?_⟩
  exact congrArg ofMatrix (stabilized_zeroRows_basis_change M U V)

/-- One common identity/zero padding followed by one permitted basis change. -/
def PaddedStable (G : RowSubgroups A) (P Q : Presentation A) : Prop :=
  ∃ α β η α' β' η' : ℕ,
    BasisEquivalent G (padding P α β η) (padding Q α' β' η')

/-- One-shot free stable equivalence with unrestricted left and right units. -/
def AlgebraicPaddedStable : Presentation A → Presentation A → Prop :=
  PaddedStable (fullRowFamily A)

/-- One-shot free stable equivalence with elementary left units and arbitrary right units. -/
def ElementaryPaddedStable : Presentation A → Presentation A → Prop :=
  PaddedStable (elementaryRowFamily A)

/-- Adding common zero rows converts an ordinary one-shot padding witness to an elementary one. -/
theorem algebraicPaddedStable_implies_elementaryPaddedStable {P Q : Presentation A}
    (h : AlgebraicPaddedStable P Q) : ElementaryPaddedStable P Q := by
  rcases h with ⟨α, β, η, α', β', η', hPQ⟩
  let q := (padding P α β η).1
  refine ⟨α, β + q, η, α', β' + q, η', ?_⟩
  simpa only [padRows_padding] using basisEquivalent_zeroRows hPQ

/-- An elementary one-shot padded basis change is already an ordinary one. -/
theorem elementaryPaddedStable_implies_algebraicPaddedStable {P Q : Presentation A}
    (h : ElementaryPaddedStable P Q) : AlgebraicPaddedStable P Q := by
  rcases h with ⟨α, β, η, α', β', η', hPQ⟩
  refine ⟨α, β, η, α', β', η', ?_⟩
  exact basisEquivalent_mono (fun _ => le_top) hPQ

/-- The one-shot ordinary and elementary stable relations coincide over every ring. -/
theorem algebraicPaddedStable_iff_elementaryPaddedStable (P Q : Presentation A) :
    AlgebraicPaddedStable P Q ↔ ElementaryPaddedStable P Q :=
  ⟨algebraicPaddedStable_implies_elementaryPaddedStable,
    elementaryPaddedStable_implies_algebraicPaddedStable⟩

/-- Equality of the two one-shot stable relations on finite presentations. -/
theorem paddedStable_relations_eq :
    (AlgebraicPaddedStable : Presentation A → Presentation A → Prop) =
      ElementaryPaddedStable := by
  funext P Q
  exact propext (algebraicPaddedStable_iff_elementaryPaddedStable P Q)

end Ring

end InfoGeometry.Algebra.StablePaddingEquivalence
