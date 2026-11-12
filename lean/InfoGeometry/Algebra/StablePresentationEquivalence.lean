/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.WhiteheadStabilization
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Relation

/-!
# Stable equivalence of finite matrix presentations

A presentation is a native rectangular matrix together with its two finite
dimensions. The elementary moves are left and right changes of basis,
adjoining an identity block, adjoining zero rows, and adjoining zero columns.
A family of native subgroups controls the permitted left changes of basis;
the right change of basis is any native matrix unit.

Stable equivalence is the native `Relation.EqvGen` of these moves. Its
definition therefore includes inverse moves and finite chains, including
chains through different matrix dimensions.

The Whitehead stabilization identity replaces each unrestricted left change
of basis by an elementary one after adjoining a single identity block of
size equal to the original row dimension. This proves equality of the
unrestricted and elementary stable relations over every unital ring,
including noncommutative rings.

## Scope

This is the algebraic stable-matrix bridge used in the proof of Proposition 1
of arXiv:2608.09913v2, section VII.1. It does not construct a CSS code, a local
circuit, a Hamiltonian, or a classification of physical phases.

The paper's Definitions 13 and 14 use existential common padding followed by
one basis change. The relation defined here is the generated relation of the
listed moves. A common-padding normal-form theorem identifying those two
definitions is a separate result and is not asserted in this file.
-/

namespace InfoGeometry.Algebra.StablePresentationEquivalence

open Matrix ElementaryMatrixOperators WhiteheadStabilization

/-- A finite rectangular matrix with its two dimensions retained in the carrier. -/
abbrev Presentation (A : Type*) :=
  Σ m : ℕ, Σ n : ℕ, Matrix (Fin m) (Fin n) A

/-- Regard a native rectangular matrix as a finite presentation. -/
def ofMatrix {A : Type*} {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) A) : Presentation A :=
  ⟨m, n, M⟩

/-- A choice, in every row dimension, of permitted left basis transformations. -/
abbrev RowSubgroups (A : Type*) [Ring A] :=
  (m : ℕ) → Subgroup (Matrix (Fin m) (Fin m) A)ˣ

section Ring

variable {A : Type*} [Ring A]

/-- Adjoin an identity block and use the canonical sum-to-`Fin` equivalences. -/
def appendIdentity {m n : ℕ} (M : Matrix (Fin m) (Fin n) A) (r : ℕ) :
    Matrix (Fin (m + r)) (Fin (n + r)) A :=
  Matrix.reindex
    (finSumFinEquiv : Fin m ⊕ Fin r ≃ Fin (m + r))
    (finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n + r))
    (Matrix.fromBlocks M 0 0 (1 : Matrix (Fin r) (Fin r) A))

/-- Adjoin zero rows without changing the column dimension. -/
def appendZeroRows {m n : ℕ} (M : Matrix (Fin m) (Fin n) A) (r : ℕ) :
    Matrix (Fin (m + r)) (Fin n) A :=
  Matrix.reindex
    (finSumFinEquiv : Fin m ⊕ Fin r ≃ Fin (m + r))
    (Equiv.refl (Fin n))
    (Matrix.fromRows M (0 : Matrix (Fin r) (Fin n) A))

/-- Adjoin zero columns without changing the row dimension. -/
def appendZeroCols {m n : ℕ} (M : Matrix (Fin m) (Fin n) A) (r : ℕ) :
    Matrix (Fin m) (Fin (n + r)) A :=
  Matrix.reindex
    (Equiv.refl (Fin m))
    (finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n + r))
    (Matrix.fromCols M (0 : Matrix (Fin m) (Fin r) A))

/-- The generating moves for stable matrix equivalence with restricted left units. -/
inductive Move (G : RowSubgroups A) : Presentation A → Presentation A → Prop
  | basis (m n : ℕ) (M : Matrix (Fin m) (Fin n) A)
      (U : (Matrix (Fin m) (Fin m) A)ˣ)
      (V : (Matrix (Fin n) (Fin n) A)ˣ) (hU : U ∈ G m) :
      Move G (ofMatrix M) (ofMatrix ((U : Matrix (Fin m) (Fin m) A) * M *
        (V : Matrix (Fin n) (Fin n) A)))
  | identityPadding (m n : ℕ) (M : Matrix (Fin m) (Fin n) A) (r : ℕ) :
      Move G (ofMatrix M) (ofMatrix (appendIdentity M r))
  | zeroRows (m n : ℕ) (M : Matrix (Fin m) (Fin n) A) (r : ℕ) :
      Move G (ofMatrix M) (ofMatrix (appendZeroRows M r))
  | zeroCols (m n : ℕ) (M : Matrix (Fin m) (Fin n) A) (r : ℕ) :
      Move G (ofMatrix M) (ofMatrix (appendZeroCols M r))

/-- Finite chains of generating moves and their inverses. -/
def Stable (G : RowSubgroups A) : Presentation A → Presentation A → Prop :=
  Relation.EqvGen (Move G)

/-- The native setoid defined by stable equivalence. -/
def stableSetoid (G : RowSubgroups A) : Setoid (Presentation A) :=
  Relation.EqvGen.setoid (Move G)

theorem stable_refl (G : RowSubgroups A) (P : Presentation A) : Stable G P P :=
  Relation.EqvGen.refl P

theorem stable_symm {G : RowSubgroups A} {P Q : Presentation A}
    (h : Stable G P Q) : Stable G Q P :=
  Relation.EqvGen.symm P Q h

theorem stable_trans {G : RowSubgroups A} {P Q R : Presentation A}
    (hPQ : Stable G P Q) (hQR : Stable G Q R) : Stable G P R :=
  Relation.EqvGen.trans P Q R hPQ hQR

/-- Every generating move gives a stable equivalence. -/
theorem stable_of_move {G : RowSubgroups A} {P Q : Presentation A}
    (h : Move G P Q) : Stable G P Q :=
  Relation.EqvGen.rel P Q h

/-- Enlarging the permitted row subgroups preserves every generating move. -/
theorem move_mono {G H : RowSubgroups A} (hGH : ∀ m, G m ≤ H m)
    {P Q : Presentation A} (h : Move G P Q) : Move H P Q := by
  cases h with
  | basis m n M U V hU => exact Move.basis m n M U V (hGH m hU)
  | identityPadding m n M r => exact Move.identityPadding m n M r
  | zeroRows m n M r => exact Move.zeroRows m n M r
  | zeroCols m n M r => exact Move.zeroCols m n M r

/-- A stable realization of each generating move extends to every finite chain. -/
theorem stable_lift {G H : RowSubgroups A}
    (hMove : ∀ {P Q : Presentation A}, Move G P Q → Stable H P Q)
    {P Q : Presentation A} (h : Stable G P Q) : Stable H P Q := by
  induction h with
  | rel P Q hPQ => exact hMove hPQ
  | refl P => exact stable_refl H P
  | symm P Q _ ih => exact stable_symm ih
  | trans P Q R _ _ hPQ hQR => exact stable_trans hPQ hQR

/-- Enlarging the permitted row subgroups preserves stable equivalence. -/
theorem stable_mono {G H : RowSubgroups A} (hGH : ∀ m, G m ≤ H m)
    {P Q : Presentation A} (h : Stable G P Q) : Stable H P Q := by
  apply stable_lift (G := G) (H := H) ?_ h
  intro P Q hMove
  exact stable_of_move (move_mono hGH hMove)

variable (A) in
/-- All invertible row transformations are allowed. -/
def fullRowFamily : RowSubgroups A := fun _ => ⊤

variable (A) in
/-- Only the subgroup generated by scalar-entry transvections is allowed on the left. -/
def elementaryRowFamily : RowSubgroups A :=
  fun m => elementarySubgroup (Fin m) A

/-- Stable equivalence using unrestricted left and right matrix units. -/
def AlgebraicStable : Presentation A → Presentation A → Prop :=
  Stable (fullRowFamily A)

/-- Stable equivalence using elementary left units and unrestricted right units. -/
def ElementaryStable : Presentation A → Presentation A → Prop :=
  Stable (elementaryRowFamily A)

/-- Reindex a rectangular matrix product using the native submatrix product theorem. -/
theorem reindex_mul {ι κ ν ι' κ' ν' : Type*} [Fintype κ] [Fintype κ']
    (eι : ι ≃ ι') (eκ : κ ≃ κ') (eν : ν ≃ ν')
    (M : Matrix ι κ A) (N : Matrix κ ν A) :
    Matrix.reindex eι eν (M * N) =
      Matrix.reindex eι eκ M * Matrix.reindex eκ eν N := by
  exact (Matrix.submatrix_mul_equiv M N eι.symm eκ.symm eν.symm).symm

/-- The balanced row unit after converting its sum indices to `Fin`. -/
def stabilizedLeft {m : ℕ} (U : (Matrix (Fin m) (Fin m) A)ˣ) :
    (Matrix (Fin (m + m)) (Fin (m + m)) A)ˣ :=
  reindexUnit (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (balancedUnit U)

/-- The right unit which compensates the balanced row stabilization. -/
def stabilizedRight {m n : ℕ} (U : (Matrix (Fin m) (Fin m) A)ˣ)
    (V : (Matrix (Fin n) (Fin n) A)ˣ) :
    (Matrix (Fin (n + m)) (Fin (n + m)) A)ˣ :=
  reindexUnit (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m))
    (blockDiagonalUnit V U)

/-- The balanced left unit remains elementary after canonical finite reindexing. -/
theorem stabilizedLeft_mem_elementary {m : ℕ}
    (U : (Matrix (Fin m) (Fin m) A)ˣ) :
    stabilizedLeft U ∈ elementarySubgroup (Fin (m + m)) A := by
  exact reindexUnit_mem_elementarySubgroup _ (balancedUnit_mem_elementarySubgroup U)

/-- One identity padding converts an arbitrary basis change to an elementary left one. -/
theorem stabilized_basis_change {m n : ℕ} (M : Matrix (Fin m) (Fin n) A)
    (U : (Matrix (Fin m) (Fin m) A)ˣ)
    (V : (Matrix (Fin n) (Fin n) A)ˣ) :
    (stabilizedLeft U : Matrix (Fin (m + m)) (Fin (m + m)) A) *
      appendIdentity M m *
      (stabilizedRight U V : Matrix (Fin (n + m)) (Fin (n + m)) A) =
    appendIdentity ((U : Matrix (Fin m) (Fin m) A) * M *
      (V : Matrix (Fin n) (Fin n) A)) m := by
  simp only [stabilizedLeft, stabilizedRight, appendIdentity, coe_reindexUnit,
    ← reindex_mul]
  exact congrArg
    (Matrix.reindex
      (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m))
      (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)))
    (WhiteheadStabilization.stabilization_identity M U V)

/-- The balanced elementary change also transports zero-row padding. -/
theorem stabilized_zeroRows_basis_change {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) A)
    (U : (Matrix (Fin m) (Fin m) A)ˣ)
    (V : (Matrix (Fin n) (Fin n) A)ˣ) :
    (stabilizedLeft U : Matrix (Fin (m + m)) (Fin (m + m)) A) *
        appendZeroRows M m * (V : Matrix (Fin n) (Fin n) A) =
      appendZeroRows ((U : Matrix (Fin m) (Fin m) A) * M *
        (V : Matrix (Fin n) (Fin n) A)) m := by
  change Matrix.reindex finSumFinEquiv finSumFinEquiv
      (balancedUnit U : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A) *
    Matrix.reindex finSumFinEquiv (Equiv.refl (Fin n))
      (Matrix.fromRows M (0 : Matrix (Fin m) (Fin n) A)) *
    Matrix.reindex (Equiv.refl (Fin n)) (Equiv.refl (Fin n))
      (V : Matrix (Fin n) (Fin n) A) = _
  rw [← reindex_mul, ← reindex_mul]
  exact congrArg
    (Matrix.reindex (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m))
      (Equiv.refl (Fin n)))
    (WhiteheadStabilization.zeroRow_stabilization_identity M U V)

/-- Every unrestricted basis change is realized by three elementary stable steps. -/
theorem basis_change_elementaryStable {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) A)
    (U : (Matrix (Fin m) (Fin m) A)ˣ)
    (V : (Matrix (Fin n) (Fin n) A)ˣ) :
    ElementaryStable (ofMatrix M)
      (ofMatrix ((U : Matrix (Fin m) (Fin m) A) * M *
        (V : Matrix (Fin n) (Fin n) A))) := by
  have h₁ : ElementaryStable (ofMatrix M) (ofMatrix (appendIdentity M m)) :=
    stable_of_move (Move.identityPadding m n M m)
  have h₂ : ElementaryStable (ofMatrix (appendIdentity M m))
      (ofMatrix (appendIdentity ((U : Matrix (Fin m) (Fin m) A) * M *
        (V : Matrix (Fin n) (Fin n) A)) m)) := by
    rw [← stabilized_basis_change M U V]
    exact stable_of_move (Move.basis (m + m) (n + m) (appendIdentity M m)
      (stabilizedLeft U) (stabilizedRight U V) (stabilizedLeft_mem_elementary U))
  have h₃ : ElementaryStable
      (ofMatrix ((U : Matrix (Fin m) (Fin m) A) * M *
        (V : Matrix (Fin n) (Fin n) A)))
      (ofMatrix (appendIdentity ((U : Matrix (Fin m) (Fin m) A) * M *
        (V : Matrix (Fin n) (Fin n) A)) m)) :=
    stable_of_move (Move.identityPadding m n
      ((U : Matrix (Fin m) (Fin m) A) * M * (V : Matrix (Fin n) (Fin n) A)) m)
  exact stable_trans h₁ (stable_trans h₂ (stable_symm h₃))

/-- Each unrestricted generating move admits an elementary stable realization. -/
theorem algebraic_move_elementaryStable {P Q : Presentation A}
    (h : Move (fullRowFamily A) P Q) : ElementaryStable P Q := by
  cases h with
  | basis m n M U V _ => exact basis_change_elementaryStable M U V
  | identityPadding m n M r =>
      exact stable_of_move (Move.identityPadding m n M r)
  | zeroRows m n M r => exact stable_of_move (Move.zeroRows m n M r)
  | zeroCols m n M r => exact stable_of_move (Move.zeroCols m n M r)

/-- Whitehead stabilization converts every unrestricted stable chain to an elementary one. -/
theorem algebraicStable_implies_elementaryStable {P Q : Presentation A}
    (h : AlgebraicStable P Q) : ElementaryStable P Q := by
  apply stable_lift (G := fullRowFamily A) (H := elementaryRowFamily A) ?_ h
  intro P Q hMove
  exact algebraic_move_elementaryStable hMove

/-- Every elementary stable chain is already an unrestricted stable chain. -/
theorem elementaryStable_implies_algebraicStable {P Q : Presentation A}
    (h : ElementaryStable P Q) : AlgebraicStable P Q := by
  apply stable_mono (G := elementaryRowFamily A) (H := fullRowFamily A) ?_ h
  intro m
  exact le_top

/-- Unrestricted and elementary stable matrix equivalence coincide over every ring. -/
theorem algebraicStable_iff_elementaryStable (P Q : Presentation A) :
    AlgebraicStable P Q ↔ ElementaryStable P Q :=
  ⟨algebraicStable_implies_elementaryStable, elementaryStable_implies_algebraicStable⟩

/-- The two equivalence relations agree as relations on the native sigma carrier. -/
theorem stable_relations_eq :
    (AlgebraicStable : Presentation A → Presentation A → Prop) = ElementaryStable := by
  funext P Q
  exact propext (algebraicStable_iff_elementaryStable P Q)

end Ring

end InfoGeometry.Algebra.StablePresentationEquivalence
