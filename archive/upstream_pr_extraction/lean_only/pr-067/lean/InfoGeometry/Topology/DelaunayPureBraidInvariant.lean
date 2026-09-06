import Mathlib.Data.Matrix.Basic
import InfoGeometry.Topology.PureBraidGroup

/-!
# Delaunay pure-braid invariant presentation layer

This file proves matrix invariance under witnessed local word moves.
It does not prove geometric admissibility of a Delaunay motion.

Product-order convention: a flip list is stored in matrix-product order.  Thus
`[A₁, A₂, ..., Aₗ]` evaluates to `A₁ * A₂ * ... * Aₗ`.  To match Rohozhkin's
chronological convention `γₗ ... γ₁(f) = f Aₗ ... A₁`, a chronological path
`γ₁, ..., γₗ` is represented here by the list `[Aₗ, ..., A₁]`.

#### BUCKET 1: CLOSED FINITE THEOREMS
- `rohozhkinMatrix_nil`: the empty flip word evaluates to the identity matrix.
- `rohozhkinMatrix_cons`: consing a flip multiplies its matrix on the left.
- `rohozhkin_invariant_under_inverse_move`,
  `rohozhkin_invariant_under_far_commute_move`, and
  `rohozhkin_invariant_under_pentagon_move`: `rohozhkinMatrix` is invariant
  under the three explicitly witnessed replacement moves.
- `rohozhkin_invariant_under_propertyed_move`: `rohozhkinMatrix` is invariant
  under the generated one-step move relation.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
- Proving the Rohozhkin generator assignment satisfies every relator in
  `PureBraid.pureBraidRelations`.
- Descending that assignment through the presented source group to a closed
  group homomorphism `PB_{moving+3} → GL_{2*moving+1}(ℚ)`.
- Markov-move invariance and any knot invariant.

This is intentionally a presentation-level datum.  It does not identify the
rational Delaunay transport matrices with any anyon or Yang--Baxter
representation.
-/

namespace InfoGeometry.Topology.Delaunay

/--
Matrix dimension used by Rohozhkin's construction from `n` moving points.

The paper has `n` moving points plus three fixed boundary points; this quotient
layer keeps only the moving-point parameter visible and uses the resulting
`2 * n + 1` internal-triangle dimension.
-/
abbrev rohozhkinDim (moving : ℕ) : ℕ := 2 * moving + 1

/-- Rohozhkin's total point count: `moving` points plus three fixed boundary points. -/
abbrev rohozhkinTotalPoints (moving : ℕ) : ℕ :=
  moving + 3

/-- Unit group of square rational matrices of dimension `d`. -/
abbrev MatrixUnits (d : ℕ) :=
  Units (Matrix (Fin d) (Fin d) ℚ)

/-- Source pure braid group when all moving plus fixed boundary points are strands. -/
abbrev RohozhkinSourcePB (moving : ℕ) :=
  InfoGeometry.Topology.PureBraid.PB (rohozhkinTotalPoints moving)

/--
One witnessed Delaunay flip in the presentation layer.

The `matrix` field is the already-inserted global transport matrix.  The
geometric admissibility and triangle-basis insertion map are deliberately not
claimed here.
-/
abbrev DelaunayFlipContext (n : ℕ) :=
  Matrix (Fin (rohozhkinDim n)) (Fin (rohozhkinDim n)) ℚ

namespace DelaunayFlipContext

/-- Compatibility accessor for the native flip transport matrix. -/
abbrev matrix (F : DelaunayFlipContext n) :
    Matrix (Fin (rohozhkinDim n)) (Fin (rohozhkinDim n)) ℚ := F

end DelaunayFlipContext

/-- The three local codimension-two move types used in Rohozhkin's invariant proof. -/
inductive DelaunayMoveKind where
  | inverse
  | farCommute
  | pentagon
  deriving DecidableEq, Repr

/-- A sequence of abstract Delaunay flips. -/
abbrev DelaunayFlipWord (n : ℕ) := List (DelaunayFlipContext n)

namespace DelaunayFlipWord

/-- Compatibility accessor for the native list carrier. -/
abbrev flips (W : DelaunayFlipWord n) : List (DelaunayFlipContext n) := W

end DelaunayFlipWord

/--
Presentation-level admissibility of a Delaunay flip word.

Every local transport matrix must be invertible. This is the algebraic
condition needed for a word to represent transport in a groupoid. It is
deliberately weaker than geometric Delaunay admissibility, which requires
separate point-configuration data.
-/
def DelaunayFlipWord.admissible {n : ℕ} (W : DelaunayFlipWord n) : Prop :=
  ∀ F ∈ W.flips, IsUnit F.matrix

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

/-- Product evaluation respects concatenation of witnessed flip words. -/
theorem rohozhkinMatrix_append {n : ℕ}
    (W₁ W₂ : DelaunayFlipWord n) :
    rohozhkinMatrix
        (W₁.flips ++ W₂.flips : DelaunayFlipWord n) =
      rohozhkinMatrix W₁ * rohozhkinMatrix W₂ := by
  exact rohozhkinMatrixList_append W₁.flips W₂.flips

@[simp]
theorem rohozhkinMatrix_nil {n : ℕ} :
    rohozhkinMatrix ([] : DelaunayFlipWord n) = 1 := by
  rfl

@[simp]
theorem rohozhkinMatrix_cons {n : ℕ}
    (F : DelaunayFlipContext n) (tail : List (DelaunayFlipContext n)) :
    rohozhkinMatrix (F :: tail : DelaunayFlipWord n) =
      F.matrix *
        rohozhkinMatrix (tail : DelaunayFlipWord n) := by
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
    (h : A.matrix * B.matrix = 1) :
    rohozhkinMatrix
        (w₁ ++ [A, B] ++ w₂ : DelaunayFlipWord n) =
      rohozhkinMatrix
        (w₁ ++ w₂ : DelaunayFlipWord n) :=
  rohozhkinMatrixList_invariant_under_move
    (DelaunayMoveList.inverse w₁ w₂ A B h)

/-- Matrix invariance for swapping adjacent far-commuting flips inside a word. -/
theorem rohozhkin_invariant_under_far_commute_move {n : ℕ}
    (w₁ w₂ : List (DelaunayFlipContext n)) (A B : DelaunayFlipContext n)
    (h : A.matrix * B.matrix = B.matrix * A.matrix) :
    rohozhkinMatrix
        (w₁ ++ [A, B] ++ w₂ : DelaunayFlipWord n) =
      rohozhkinMatrix
        (w₁ ++ [B, A] ++ w₂ : DelaunayFlipWord n) :=
  rohozhkinMatrixList_invariant_under_move
    (DelaunayMoveList.farCommute w₁ w₂ A B h)

/--
Matrix invariance for deleting a witnessed five-flip pentagon block.

The order is the local matrix-product order.  For the Appendix A pentagon in
`RohozhkinPentagonMatrix`, instantiate `(A, B, C, D, E)` with
`(Γ₅, Γ₄, Γ₃, Γ₂, Γ₁)`.
-/
theorem rohozhkin_invariant_under_pentagon_move {n : ℕ}
    (w₁ w₂ : List (DelaunayFlipContext n))
    (A B C D E : DelaunayFlipContext n)
    (h : A.matrix * B.matrix * C.matrix * D.matrix * E.matrix = 1) :
    rohozhkinMatrix
        (w₁ ++ [A, B, C, D, E] ++ w₂ : DelaunayFlipWord n) =
      rohozhkinMatrix
        (w₁ ++ w₂ : DelaunayFlipWord n) :=
  rohozhkinMatrixList_invariant_under_move
    (DelaunayMoveList.pentagon w₁ w₂ A B C D E h)

/--
Presentation-level move relation for `DelaunayFlipWord`.

The quotient layer proves matrix-word invariance under witnessed local
replacements. Geometric admissibility of a Delaunay motion remains a separate
point-configuration theorem.
-/
def DelaunayMove {n : ℕ} (kind : DelaunayMoveKind)
    (before after : DelaunayFlipWord n) : Prop :=
  DelaunayMoveList kind before.flips after.flips

/-- Matrix invariance under a witnessed presentation move. -/
theorem rohozhkin_invariant_under_propertyed_move {n : ℕ}
    {kind : DelaunayMoveKind} {before after : DelaunayFlipWord n}
    (h : DelaunayMove kind before after) :
    rohozhkinMatrix before = rohozhkinMatrix after :=
  rohozhkinMatrixList_invariant_under_move h

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
  | step _ _ _ h_step => exact rohozhkin_invariant_under_propertyed_move h_step

/-- The presentation group is the quotient of words by the move equivalence. -/
def DelaunayQuotient (n : ℕ) := Quot (@DelaunayEquiv n)

/-- The Rohozhkin matrix descends to the quotient, providing the core representation. -/
def rohozhkinQuotientMatrix {n : ℕ} (q : DelaunayQuotient n) : Matrix (Fin (rohozhkinDim n)) (Fin (rohozhkinDim n)) ℚ :=
  Quot.lift rohozhkinMatrix (fun _ _ h => rohozhkin_invariant_under_equiv h) q

/--
Boundary datum for a source pure-braid group map into the Delaunay flip-word
quotient.  This is still the quotient/factorization boundary, not yet the final
matrix-unit representation theorem.
-/
abbrev PureBraidQuotientBoundary (moving : ℕ) :=
  RohozhkinSourcePB moving → DelaunayQuotient moving

namespace PureBraidQuotientBoundary

abbrev braidToQuotient {moving : ℕ} (B : PureBraidQuotientBoundary moving) :
    RohozhkinSourcePB moving → DelaunayQuotient moving := B

end PureBraidQuotientBoundary

/--
Presented-group representation boundary with the paper's target shape:
`PB_{moving+3} → GL_{2*moving+1}(ℚ)`, represented as units of the rational
matrix monoid.

A closed construction of this homomorphism still requires proving that the
chosen generator matrices are units and satisfy every relator in
`PureBraid.pureBraidRelations`.
-/
def PureBraidRepresentationBoundary (moving : ℕ) :=
  RohozhkinSourcePB moving →* MatrixUnits (rohozhkinDim moving)

end InfoGeometry.Topology.Delaunay
