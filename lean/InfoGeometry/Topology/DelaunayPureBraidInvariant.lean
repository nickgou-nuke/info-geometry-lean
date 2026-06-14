import Mathlib.Data.Matrix.Basic
import InfoGeometry.Topology.RohozhkinPentagonMatrix

/-!
# Delaunay pure-braid invariant presentation layer

#### BUCKET 1: CLOSED FINITE THEOREMS
- `rohozhkinMatrix_nil`: the empty flip word evaluates to the identity matrix.
- `rohozhkinMatrix_cons`: consing a flip multiplies its matrix on the left.
- `rohozhkin_invariant_under_inverse_move`,
  `rohozhkin_invariant_under_far_commute_move`, and
  `rohozhkin_invariant_under_pentagon_move`: `rohozhkinMatrix` is invariant
  under the three explicitly witnessed replacement moves.
- `rohozhkin_invariant_under_witnessed_move`: `rohozhkinMatrix` is invariant
  under the generated one-step move relation.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
- A concrete pure braid group presentation for the Rohozhkin flip-word quotient.
- A group homomorphism `PB_n → GL_{2n+1}(ℚ)`.
- Markov-move invariance and any knot invariant.

This is intentionally a presentation-level socket.  It does not identify the
rational Delaunay transport matrices with any anyon or Yang--Baxter
representation.
-/

namespace InfoGeometry.Topology.Delaunay

/-- Matrix dimension used by Rohozhkin's construction from `n` moving points. -/
abbrev rohozhkinDim (n : ℕ) : ℕ := 2 * n + 1

/--
One witnessed Delaunay flip in the presentation layer.

The `matrix` field is the already-inserted global transport matrix.  The
geometric admissibility and triangle-basis insertion map are deliberately not
claimed here.
-/
structure DelaunayFlipContext (n : ℕ) where
  matrix : Matrix (Fin (rohozhkinDim n)) (Fin (rohozhkinDim n)) ℚ

/-- The three local codimension-two move types used in Rohozhkin's invariant proof. -/
inductive DelaunayMoveKind where
  | inverse
  | farCommute
  | pentagon
  deriving DecidableEq, Repr

/-- A sequence of abstract Delaunay flips. -/
structure DelaunayFlipWord (n : ℕ) where
  flips : List (DelaunayFlipContext n)
  admissible : Prop

/-- Product matrix attached to a witnessed flip list. -/
def rohozhkinMatrixList {n : ℕ}
    (flips : List (DelaunayFlipContext n)) :
    Matrix (Fin (rohozhkinDim n)) (Fin (rohozhkinDim n)) ℚ :=
  flips.foldr (fun F M => F.matrix * M) 1

@[simp]
lemma rohozhkinMatrixList_nil {n : ℕ} : rohozhkinMatrixList ([] : List (DelaunayFlipContext n)) = 1 := rfl

@[simp]
lemma rohozhkinMatrixList_cons {n : ℕ} (A : DelaunayFlipContext n) (w : List (DelaunayFlipContext n)) :
    rohozhkinMatrixList (A :: w) = A.matrix * rohozhkinMatrixList w := rfl

@[simp]
lemma rohozhkinMatrixList_append {n : ℕ} (w₁ w₂ : List (DelaunayFlipContext n)) :
    rohozhkinMatrixList (w₁ ++ w₂) = rohozhkinMatrixList w₁ * rohozhkinMatrixList w₂ := by
  induction w₁ with
  | nil => simp
  | cons A w₁' ih => simp [ih, Matrix.mul_assoc]

/-- Product matrix attached to a witnessed flip word. -/
def rohozhkinMatrix {n : ℕ}
    (W : DelaunayFlipWord n) :
    Matrix (Fin (rohozhkinDim n)) (Fin (rohozhkinDim n)) ℚ :=
  rohozhkinMatrixList W.flips

@[simp]
theorem rohozhkinMatrix_nil {n : ℕ} (h : Prop) :
    rohozhkinMatrix ({ flips := [], admissible := h } : DelaunayFlipWord n) = 1 := by
  rfl

@[simp]
theorem rohozhkinMatrix_cons {n : ℕ}
    (F : DelaunayFlipContext n) (tail : List (DelaunayFlipContext n)) (h : Prop) :
    rohozhkinMatrix ({ flips := F :: tail, admissible := h } : DelaunayFlipWord n) =
      F.matrix *
        rohozhkinMatrix ({ flips := tail, admissible := h } : DelaunayFlipWord n) := by
  rfl

/-- Concrete presentation-level move relation for Delaunay flip sequences. -/
inductive DelaunayMoveList {n : ℕ} : DelaunayMoveKind → List (DelaunayFlipContext n) → List (DelaunayFlipContext n) → Prop
  | inverse (w₁ w₂ : List (DelaunayFlipContext n)) (A B : DelaunayFlipContext n)
      (h : A.matrix * B.matrix = 1) :
      DelaunayMoveList .inverse (w₁ ++ [A, B] ++ w₂) (w₁ ++ w₂)
  | farCommute (w₁ w₂ : List (DelaunayFlipContext n)) (A B : DelaunayFlipContext n)
      (h : A.matrix * B.matrix = B.matrix * A.matrix) :
      DelaunayMoveList .farCommute (w₁ ++ [A, B] ++ w₂) (w₁ ++ [B, A] ++ w₂)
  | pentagon (w₁ w₂ : List (DelaunayFlipContext n)) (A B C D E : DelaunayFlipContext n)
      (h : A.matrix * B.matrix * C.matrix * D.matrix * E.matrix = 1) :
      DelaunayMoveList .pentagon (w₁ ++ [A, B, C, D, E] ++ w₂) (w₁ ++ w₂)

/-- Matrix invariance under a witnessed presentation move on lists. -/
lemma rohozhkinMatrixList_invariant_under_move {n : ℕ} {kind : DelaunayMoveKind}
    {before after : List (DelaunayFlipContext n)} (h : DelaunayMoveList kind before after) :
    rohozhkinMatrixList before = rohozhkinMatrixList after := by
  cases h with
  | inverse w₁ w₂ A B eq =>
    simp
    have h1 : A.matrix * (B.matrix * rohozhkinMatrixList w₂) = (A.matrix * B.matrix) * rohozhkinMatrixList w₂ := by rw [Matrix.mul_assoc]
    rw [h1, eq, Matrix.one_mul]
  | farCommute w₁ w₂ A B eq =>
    simp
    have h1 : A.matrix * (B.matrix * rohozhkinMatrixList w₂) = (A.matrix * B.matrix) * rohozhkinMatrixList w₂ := by rw [Matrix.mul_assoc]
    have h2 : B.matrix * (A.matrix * rohozhkinMatrixList w₂) = (B.matrix * A.matrix) * rohozhkinMatrixList w₂ := by rw [Matrix.mul_assoc]
    rw [h1, h2, eq]
  | pentagon w₁ w₂ A B C D E eq =>
    simp
    have h1 : A.matrix * (B.matrix * (C.matrix * (D.matrix * (E.matrix * rohozhkinMatrixList w₂)))) =
      (A.matrix * B.matrix * C.matrix * D.matrix * E.matrix) * rohozhkinMatrixList w₂ := by
      simp only [Matrix.mul_assoc]
    rw [h1, eq, Matrix.one_mul]

/-- Matrix invariance for deleting adjacent inverse flips inside a word. -/
theorem rohozhkin_invariant_under_inverse_move {n : ℕ}
    (w₁ w₂ : List (DelaunayFlipContext n)) (A B : DelaunayFlipContext n)
    (h : A.matrix * B.matrix = 1)
    (hbefore hafter : Prop) :
    rohozhkinMatrix
        ({ flips := w₁ ++ [A, B] ++ w₂, admissible := hbefore } :
          DelaunayFlipWord n) =
      rohozhkinMatrix
        ({ flips := w₁ ++ w₂, admissible := hafter } :
          DelaunayFlipWord n) :=
  rohozhkinMatrixList_invariant_under_move
    (DelaunayMoveList.inverse w₁ w₂ A B h)

/-- Matrix invariance for swapping adjacent far-commuting flips inside a word. -/
theorem rohozhkin_invariant_under_far_commute_move {n : ℕ}
    (w₁ w₂ : List (DelaunayFlipContext n)) (A B : DelaunayFlipContext n)
    (h : A.matrix * B.matrix = B.matrix * A.matrix)
    (hbefore hafter : Prop) :
    rohozhkinMatrix
        ({ flips := w₁ ++ [A, B] ++ w₂, admissible := hbefore } :
          DelaunayFlipWord n) =
      rohozhkinMatrix
        ({ flips := w₁ ++ [B, A] ++ w₂, admissible := hafter } :
          DelaunayFlipWord n) :=
  rohozhkinMatrixList_invariant_under_move
    (DelaunayMoveList.farCommute w₁ w₂ A B h)

/-- Matrix invariance for deleting a witnessed five-flip pentagon block. -/
theorem rohozhkin_invariant_under_pentagon_move {n : ℕ}
    (w₁ w₂ : List (DelaunayFlipContext n))
    (A B C D E : DelaunayFlipContext n)
    (h : A.matrix * B.matrix * C.matrix * D.matrix * E.matrix = 1)
    (hbefore hafter : Prop) :
    rohozhkinMatrix
        ({ flips := w₁ ++ [A, B, C, D, E] ++ w₂, admissible := hbefore } :
          DelaunayFlipWord n) =
      rohozhkinMatrix
        ({ flips := w₁ ++ w₂, admissible := hafter } :
          DelaunayFlipWord n) :=
  rohozhkinMatrixList_invariant_under_move
    (DelaunayMoveList.pentagon w₁ w₂ A B C D E h)

/-- Presentation-level move relation for DelaunayFlipWord. -/
def DelaunayMove {n : ℕ} (kind : DelaunayMoveKind)
    (before after : DelaunayFlipWord n) : Prop :=
  DelaunayMoveList kind before.flips after.flips ∧ before.admissible = after.admissible

/-- Matrix invariance under a witnessed presentation move. -/
theorem rohozhkin_invariant_under_witnessed_move {n : ℕ}
    {kind : DelaunayMoveKind} {before after : DelaunayFlipWord n}
    (h : DelaunayMove kind before after) :
    rohozhkinMatrix before = rohozhkinMatrix after :=
  rohozhkinMatrixList_invariant_under_move h.1

/--
The equivalence relation generated by valid Delaunay moves.
This forms the presentation quotient for the pure braid mapping.
-/
inductive DelaunayEquiv {n : ℕ} : DelaunayFlipWord n → DelaunayFlipWord n → Prop
  | refl (W : DelaunayFlipWord n) : DelaunayEquiv W W
  | symm (W₁ W₂ : DelaunayFlipWord n) : DelaunayEquiv W₁ W₂ → DelaunayEquiv W₂ W₁
  | trans (W₁ W₂ W₃ : DelaunayFlipWord n) : DelaunayEquiv W₁ W₂ → DelaunayEquiv W₂ W₃ → DelaunayEquiv W₁ W₃
  | step (kind : DelaunayMoveKind) (W₁ W₂ : DelaunayFlipWord n) : DelaunayMove kind W₁ W₂ → DelaunayEquiv W₁ W₂

/-- Matrix invariance lifts to the full equivalence quotient. -/
theorem rohozhkin_invariant_under_equiv {n : ℕ} {W₁ W₂ : DelaunayFlipWord n} (h : DelaunayEquiv W₁ W₂) :
    rohozhkinMatrix W₁ = rohozhkinMatrix W₂ := by
  induction h with
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  | step _ _ _ h_step => exact rohozhkin_invariant_under_witnessed_move h_step

/-- The presentation group socket is the quotient of words by the move equivalence. -/
def DelaunayQuotient (n : ℕ) := Quot (@DelaunayEquiv n)

/-- The Rohozhkin matrix descends to the quotient, providing the core representation. -/
def rohozhkinQuotientMatrix {n : ℕ} (q : DelaunayQuotient n) : Matrix (Fin (rohozhkinDim n)) (Fin (rohozhkinDim n)) ℚ :=
  Quot.lift rohozhkinMatrix (fun _ _ h => rohozhkin_invariant_under_equiv h) q

/--
Boundary socket for the pure-braid group homomorphism.
When the pure braid group `PB_n` is formalized, its presentation should map into
`DelaunayQuotient n`.  This file only provides the quotient matrix readout;
the group-homomorphism theorem remains open until the `PB_n` presentation and
invertibility target are formalized.
-/
structure PureBraidRepresentationBoundary (n : ℕ) (PB : Type) [Group PB] where
  braidToQuotient : PB → DelaunayQuotient n
  -- The representation properties (respecting multiplication, etc.) will be stated here.

end InfoGeometry.Topology.Delaunay
