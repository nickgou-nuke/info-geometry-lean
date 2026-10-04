import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.BraidPermutationQuotient

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
- `rohozhkin_invariant_under_witnessed_move`: `rohozhkinMatrix` is invariant
  under the generated one-step move relation.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
- Defining a genuine generating family and presentation for the canonical pure
  braid kernel used below.
- Constructing the geometric Delaunay generator assignment and proving it
  extends to a homomorphism from that kernel to the matrix-unit group.
- Markov-move invariance and any knot invariant.

The witnessed matrix-word quotient is not identified with the canonical pure
braid kernel. The rational Delaunay transport matrices are not identified with
any anyon or Yang--Baxter representation.
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

/-- The pure braid subgroup on `moving + 3` strands, using the canonical
permutation kernel. The corresponding braid-generator count is `moving + 2`. -/
abbrev RohozhkinSourcePB (moving : ℕ) :=
  InfoGeometry.Categorical.BraidPermutationQuotient.pureBraidSubgroup (moving + 2)

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
        ({ flips := W₁.flips ++ W₂.flips } :
          DelaunayFlipWord n) =
      rohozhkinMatrix W₁ * rohozhkinMatrix W₂ := by
  exact rohozhkinMatrixList_append W₁.flips W₂.flips

@[simp]
theorem rohozhkinMatrix_nil {n : ℕ} :
    rohozhkinMatrix ({ flips := [] } : DelaunayFlipWord n) = 1 := by
  rfl

@[simp]
theorem rohozhkinMatrix_cons {n : ℕ}
    (F : DelaunayFlipContext n) (tail : List (DelaunayFlipContext n)) :
    rohozhkinMatrix ({ flips := F :: tail } : DelaunayFlipWord n) =
      F.matrix *
        rohozhkinMatrix ({ flips := tail } : DelaunayFlipWord n) := by
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
        ({ flips := w₁ ++ [A, B] ++ w₂ } :
          DelaunayFlipWord n) =
      rohozhkinMatrix
        ({ flips := w₁ ++ w₂ } :
          DelaunayFlipWord n) :=
  rohozhkinMatrixList_invariant_under_move
    (DelaunayMoveList.inverse w₁ w₂ A B h)

/-- Matrix invariance for swapping adjacent far-commuting flips inside a word. -/
theorem rohozhkin_invariant_under_far_commute_move {n : ℕ}
    (w₁ w₂ : List (DelaunayFlipContext n)) (A B : DelaunayFlipContext n)
    (h : A.matrix * B.matrix = B.matrix * A.matrix) :
    rohozhkinMatrix
        ({ flips := w₁ ++ [A, B] ++ w₂ } :
          DelaunayFlipWord n) =
      rohozhkinMatrix
        ({ flips := w₁ ++ [B, A] ++ w₂ } :
          DelaunayFlipWord n) :=
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
        ({ flips := w₁ ++ [A, B, C, D, E] ++ w₂ } :
          DelaunayFlipWord n) =
      rohozhkinMatrix
        ({ flips := w₁ ++ w₂ } :
          DelaunayFlipWord n) :=
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
theorem rohozhkin_invariant_under_witnessed_move {n : ℕ}
    {kind : DelaunayMoveKind} {before after : DelaunayFlipWord n}
    (h : DelaunayMove kind before after) :
    rohozhkinMatrix before = rohozhkinMatrix after :=
  rohozhkinMatrixList_invariant_under_move h

/-- The equivalence relation generated by explicitly witnessed matrix-word
replacement moves. This is not identified with a Delaunay flip groupoid or the
pure braid kernel. -/
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

/-- The set quotient of flip words by the witnessed matrix-word equivalence. -/
def DelaunayQuotient (n : ℕ) := Quot (@DelaunayEquiv n)

/-- The matrix-valued word function descends to this set quotient. This is not
a group representation: no group structure on the quotient is established. -/
def rohozhkinQuotientMatrix {n : ℕ} (q : DelaunayQuotient n) : Matrix (Fin (rohozhkinDim n)) (Fin (rohozhkinDim n)) ℚ :=
  Quot.lift rohozhkinMatrix (fun _ _ h => rohozhkin_invariant_under_equiv h) q

/-- Target type for a future homomorphism from the canonical pure braid kernel
to rational matrix units. This alias does not supply such a homomorphism. -/
def PureBraidRepresentationBoundary (moving : ℕ) :=
  RohozhkinSourcePB moving →* MatrixUnits (rohozhkinDim moving)

end InfoGeometry.Topology.Delaunay
