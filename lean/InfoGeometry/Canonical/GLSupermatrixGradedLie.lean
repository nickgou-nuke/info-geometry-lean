import Mathlib
import InfoGeometry.Algebra.SuperLieRing
import InfoGeometry.NCG.BerezinianSuperdeterminant

/-!
# Native finite `gl(m|n)` graded matrix Lie spine

This owner realizes the finite associative supermatrix carrier directly as the
native Mathlib matrix algebra on `Fin m ⊕ Fin n`.  The four familiar blocks are
recovered by restriction to the even/odd summands, while homogeneous even and
odd matrices are characterized by block-diagonal and block-off-diagonal
presentations.

The file proves:

* the Koszul parity arithmetic and sign;
* graded cyclicity of the supertrace on homogeneous matrices;
* vanishing supertrace of every homogeneous supercommutator;
* preservation of parity by the superbracket;
* graded skew symmetry;
* the universal graded super-Jacobi identity in any associative ring;
* its direct specialization to the native `gl(m|n)` matrix carrier.

This is finite superlinear algebra.  It does not construct a Grassmann-valued
matrix algebra, a matrix logarithm, BCH convergence, or the general identity
`Ber(exp X) = exp(str X)`.
-/

noncomputable section

open Matrix
open BigOperators

namespace InfoGeometry.Canonical.GLSupermatrixGradedLie

/-- Two-element grading parity. -/
inductive Parity where
  | even
  | odd
  deriving DecidableEq, Repr

namespace Parity

/-- Addition in `Z/2Z`. -/
def add : Parity → Parity → Parity
  | .even, p => p
  | .odd, .even => .odd
  | .odd, .odd => .even

instance : Add Parity := ⟨add⟩

@[simp] theorem even_add (p : Parity) : Parity.even + p = p := rfl
@[simp] theorem odd_add_even : Parity.odd + Parity.even = Parity.odd := rfl
@[simp] theorem odd_add_odd : Parity.odd + Parity.odd = Parity.even := rfl

/-- Koszul sign `(-1)^(|X||Y|)`. -/
def sign (R : Type*) [Ring R] : Parity → Parity → R
  | .odd, .odd => -1
  | _, _ => 1

end Parity

/-- Native associative carrier for `(m|n)` supermatrices. -/
abbrev SuperMatrix (m n : ℕ) (R : Type*) :=
  Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) R

section Blocks

variable {m n : ℕ} {R : Type*}

/-- Even-even block. -/
def blockA (M : SuperMatrix m n R) : Matrix (Fin m) (Fin m) R :=
  fun i j => M (Sum.inl i) (Sum.inl j)

/-- Even-odd block. -/
def blockB (M : SuperMatrix m n R) : Matrix (Fin m) (Fin n) R :=
  fun i j => M (Sum.inl i) (Sum.inr j)

/-- Odd-even block. -/
def blockC (M : SuperMatrix m n R) : Matrix (Fin n) (Fin m) R :=
  fun i j => M (Sum.inr i) (Sum.inl j)

/-- Odd-odd block. -/
def blockD (M : SuperMatrix m n R) : Matrix (Fin n) (Fin n) R :=
  fun i j => M (Sum.inr i) (Sum.inr j)

variable [Zero R]

/-- Block-diagonal homogeneous even matrix. -/
def evenMatrix (A : Matrix (Fin m) (Fin m) R)
    (D : Matrix (Fin n) (Fin n) R) : SuperMatrix m n R :=
  Matrix.fromBlocks A 0 0 D

/-- Block-off-diagonal homogeneous odd matrix. -/
def oddMatrix (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin n) (Fin m) R) : SuperMatrix m n R :=
  Matrix.fromBlocks 0 B C 0

@[simp] theorem blockA_evenMatrix (A : Matrix (Fin m) (Fin m) R)
    (D : Matrix (Fin n) (Fin n) R) : blockA (evenMatrix A D) = A := by
  ext i j
  rfl

@[simp] theorem blockD_evenMatrix (A : Matrix (Fin m) (Fin m) R)
    (D : Matrix (Fin n) (Fin n) R) : blockD (evenMatrix A D) = D := by
  ext i j
  rfl

@[simp] theorem blockA_oddMatrix (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin n) (Fin m) R) : blockA (oddMatrix B C) = 0 := by
  ext i j
  rfl

@[simp] theorem blockD_oddMatrix (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin n) (Fin m) R) : blockD (oddMatrix B C) = 0 := by
  ext i j
  rfl

end Blocks

section Grading

variable {m n : ℕ} {R : Type*} [CommRing R]

/-- Homogeneous matrices are exactly block diagonal (even) or block off-diagonal (odd). -/
def IsHomogeneous (p : Parity) (M : SuperMatrix m n R) : Prop :=
  match p with
  | .even => ∃ A D, M = evenMatrix A D
  | .odd => ∃ B C, M = oddMatrix B C

/-- Supertrace `str M = Tr A - Tr D`. -/
def supertrace (M : SuperMatrix m n R) : R :=
  Matrix.trace (blockA M) - Matrix.trace (blockD M)

@[simp] theorem supertrace_evenMatrix
    (A : Matrix (Fin m) (Fin m) R) (D : Matrix (Fin n) (Fin n) R) :
    supertrace (evenMatrix A D) = Matrix.trace A - Matrix.trace D := by
  simp [supertrace]

@[simp] theorem supertrace_oddMatrix
    (B : Matrix (Fin m) (Fin n) R) (C : Matrix (Fin n) (Fin m) R) :
    supertrace (oddMatrix B C) = 0 := by
  simp [supertrace]

/-- Graded supercommutator on the native associative matrix ring. -/
def superbracket (p q : Parity)
    (X Y : SuperMatrix m n R) : SuperMatrix m n R :=
  match p, q with
  | .odd, .odd => X * Y + Y * X
  | _, _ => X * Y - Y * X

/-- Even-even products remain block diagonal. -/
theorem even_mul_even
    (A E : Matrix (Fin m) (Fin m) R)
    (D H : Matrix (Fin n) (Fin n) R) :
    evenMatrix A D * evenMatrix E H = evenMatrix (A * E) (D * H) := by
  rw [evenMatrix, evenMatrix, Matrix.fromBlocks_multiply]
  simp [evenMatrix]

/-- Even-odd products are block off diagonal. -/
theorem even_mul_odd
    (A : Matrix (Fin m) (Fin m) R) (D : Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin m) (Fin n) R) (C : Matrix (Fin n) (Fin m) R) :
    evenMatrix A D * oddMatrix B C = oddMatrix (A * B) (D * C) := by
  rw [evenMatrix, oddMatrix, Matrix.fromBlocks_multiply]
  simp [oddMatrix]

/-- Odd-even products are block off diagonal. -/
theorem odd_mul_even
    (B : Matrix (Fin m) (Fin n) R) (C : Matrix (Fin n) (Fin m) R)
    (A : Matrix (Fin m) (Fin m) R) (D : Matrix (Fin n) (Fin n) R) :
    oddMatrix B C * evenMatrix A D = oddMatrix (B * D) (C * A) := by
  rw [oddMatrix, evenMatrix, Matrix.fromBlocks_multiply]
  simp [oddMatrix]

/-- Odd-odd products return to the diagonal sector. -/
theorem odd_mul_odd
    (B F : Matrix (Fin m) (Fin n) R)
    (C G : Matrix (Fin n) (Fin m) R) :
    oddMatrix B C * oddMatrix F G = evenMatrix (B * G) (C * F) := by
  rw [oddMatrix, oddMatrix, Matrix.fromBlocks_multiply]
  simp [evenMatrix]

/-- Even-even cyclicity of the supertrace. -/
theorem supertrace_mul_even_even
    (X Y : SuperMatrix m n R)
    (hX : IsHomogeneous .even X) (hY : IsHomogeneous .even Y) :
    supertrace (X * Y) = supertrace (Y * X) := by
  rcases hX with ⟨A, D, rfl⟩
  rcases hY with ⟨E, H, rfl⟩
  rw [even_mul_even, even_mul_even]
  simp only [supertrace_evenMatrix]
  rw [Matrix.trace_mul_comm A E, Matrix.trace_mul_comm D H]

/-- Mixed homogeneous products have zero supertrace. -/
theorem supertrace_mul_even_odd
    (X Y : SuperMatrix m n R)
    (hX : IsHomogeneous .even X) (hY : IsHomogeneous .odd Y) :
    supertrace (X * Y) = 0 := by
  rcases hX with ⟨A, D, rfl⟩
  rcases hY with ⟨B, C, rfl⟩
  rw [even_mul_odd]
  exact supertrace_oddMatrix _ _

/-- Mixed homogeneous products have zero supertrace in the reverse order. -/
theorem supertrace_mul_odd_even
    (X Y : SuperMatrix m n R)
    (hX : IsHomogeneous .odd X) (hY : IsHomogeneous .even Y) :
    supertrace (X * Y) = 0 := by
  rcases hX with ⟨B, C, rfl⟩
  rcases hY with ⟨A, D, rfl⟩
  rw [odd_mul_even]
  exact supertrace_oddMatrix _ _

/-- Odd-odd graded cyclicity.  Rectangular trace cyclicity supplies the sign. -/
theorem supertrace_mul_odd_odd
    (X Y : SuperMatrix m n R)
    (hX : IsHomogeneous .odd X) (hY : IsHomogeneous .odd Y) :
    supertrace (X * Y) = -supertrace (Y * X) := by
  rcases hX with ⟨B, C, rfl⟩
  rcases hY with ⟨F, G, rfl⟩
  rw [odd_mul_odd, odd_mul_odd]
  simp only [supertrace_evenMatrix]
  have hBG : Matrix.trace (B * G) = Matrix.trace (G * B) :=
    Matrix.trace_mul_comm B G
  have hCF : Matrix.trace (C * F) = Matrix.trace (F * C) :=
    Matrix.trace_mul_comm C F
  rw [hBG, hCF]
  ring

/-- Graded cyclicity `str(XY)=(-1)^(|X||Y|) str(YX)`. -/
theorem supertrace_mul_graded
    (p q : Parity) (X Y : SuperMatrix m n R)
    (hX : IsHomogeneous p X) (hY : IsHomogeneous q Y) :
    supertrace (X * Y) = Parity.sign R p q * supertrace (Y * X) := by
  cases p <;> cases q
  · simpa [Parity.sign] using supertrace_mul_even_even X Y hX hY
  · rw [supertrace_mul_even_odd X Y hX hY,
      supertrace_mul_odd_even Y X hY hX]
    simp [Parity.sign]
  · rw [supertrace_mul_odd_even X Y hX hY,
      supertrace_mul_even_odd Y X hY hX]
    simp [Parity.sign]
  · simpa [Parity.sign] using supertrace_mul_odd_odd X Y hX hY

/-- The superbracket preserves the `Z/2Z` degree. -/
theorem superbracket_preserves_grading
    (p q : Parity) (X Y : SuperMatrix m n R)
    (hX : IsHomogeneous p X) (hY : IsHomogeneous q Y) :
    IsHomogeneous (p + q) (superbracket p q X Y) := by
  cases p <;> cases q
  · rcases hX with ⟨A, D, rfl⟩
    rcases hY with ⟨E, H, rfl⟩
    refine ⟨A * E - E * A, D * H - H * D, ?_⟩
    simp [superbracket, even_mul_even, evenMatrix, Matrix.fromBlocks_sub]
  · rcases hX with ⟨A, D, rfl⟩
    rcases hY with ⟨B, C, rfl⟩
    refine ⟨A * B - B * D, D * C - C * A, ?_⟩
    simp [superbracket, even_mul_odd, odd_mul_even, oddMatrix, Matrix.fromBlocks_sub]
  · rcases hX with ⟨B, C, rfl⟩
    rcases hY with ⟨A, D, rfl⟩
    refine ⟨B * D - A * B, C * A - D * C, ?_⟩
    simp [superbracket, odd_mul_even, even_mul_odd, oddMatrix, Matrix.fromBlocks_sub]
  · rcases hX with ⟨B, C, rfl⟩
    rcases hY with ⟨F, G, rfl⟩
    refine ⟨B * G + F * C, C * F + G * B, ?_⟩
    simp [superbracket, odd_mul_odd, evenMatrix, Matrix.fromBlocks_add]

/-- Graded skew symmetry of the superbracket. -/
theorem superbracket_graded_skew
    (p q : Parity) (X Y : SuperMatrix m n R) :
    superbracket p q X Y =
      -(Parity.sign R p q) • superbracket q p Y X := by
  cases p <;> cases q <;>
    ext i j <;>
    simp [superbracket, Parity.sign] <;>
    ring

/-- The supertrace annihilates every homogeneous supercommutator. -/
theorem supertrace_superbracket_eq_zero
    (p q : Parity) (X Y : SuperMatrix m n R)
    (hX : IsHomogeneous p X) (hY : IsHomogeneous q Y) :
    supertrace (superbracket p q X Y) = 0 := by
  cases p <;> cases q
  · simp only [superbracket]
    have h := supertrace_mul_even_even X Y hX hY
    simp [supertrace, blockA, blockD] at *
    exact sub_eq_zero.mpr h
  · have h1 := supertrace_mul_even_odd X Y hX hY
    have h2 := supertrace_mul_odd_even Y X hY hX
    simp [superbracket, supertrace, blockA, blockD, h1, h2]
  · have h1 := supertrace_mul_odd_even X Y hX hY
    have h2 := supertrace_mul_even_odd Y X hY hX
    simp [superbracket, supertrace, blockA, blockD, h1, h2]
  · have h := supertrace_mul_odd_odd X Y hX hY
    rw [show superbracket Parity.odd Parity.odd X Y = X * Y + Y * X by rfl]
    unfold supertrace blockA blockD
    rw [Matrix.trace_add, Matrix.trace_add]
    have hxy := h
    unfold supertrace blockA blockD at hxy
    linarith

end Grading

/-! ## Universal associative-ring super-Jacobi law -/

section Universal

variable {S : Type*} [Ring S]

/-- The same parity superbracket on any associative ring. -/
def ringSuperbracket (p q : Parity) (X Y : S) : S :=
  match p, q with
  | .odd, .odd => X * Y + Y * X
  | _, _ => X * Y - Y * X

/-- Universal graded skew symmetry in an associative ring. -/
theorem ringSuperbracket_graded_skew
    (p q : Parity) (X Y : S) :
    ringSuperbracket p q X Y =
      -(Parity.sign S p q * ringSuperbracket q p Y X) := by
  cases p <;> cases q <;>
    simp [ringSuperbracket, Parity.sign] <;>
    noncomm_ring

/-- Graded super-Jacobi identity in every associative ring. -/
theorem graded_super_jacobi
    (pX pY pZ : Parity) (X Y Z : S) :
    Parity.sign S pX pZ *
        ringSuperbracket pX (pY + pZ) X (ringSuperbracket pY pZ Y Z) +
    Parity.sign S pY pX *
        ringSuperbracket pY (pZ + pX) Y (ringSuperbracket pZ pX Z X) +
    Parity.sign S pZ pY *
        ringSuperbracket pZ (pX + pY) Z (ringSuperbracket pX pY X Y) = 0 := by
  cases pX <;> cases pY <;> cases pZ <;>
    simp [ringSuperbracket, Parity.add, Parity.sign] <;>
    noncomm_ring

/-- Adjoint action is a graded derivation of the superbracket. -/
theorem super_adjoint_derivation
    (pX pY pZ : Parity) (X Y Z : S) :
    ringSuperbracket pX (pY + pZ) X (ringSuperbracket pY pZ Y Z) =
      ringSuperbracket (pX + pY) pZ (ringSuperbracket pX pY X Y) Z +
      Parity.sign S pX pY *
        ringSuperbracket pY (pX + pZ) Y (ringSuperbracket pX pZ X Z) := by
  cases pX <;> cases pY <;> cases pZ <;>
    simp [ringSuperbracket, Parity.add, Parity.sign] <;>
    noncomm_ring

end Universal

section GLJacobi

variable {m n : ℕ} {R : Type*} [CommRing R]

/-- The universal graded Jacobi identity specialized to the native matrix ring
`gl(m|n)`. -/
theorem gl_graded_super_jacobi
    (pX pY pZ : Parity)
    (X Y Z : SuperMatrix m n R) :
    Parity.sign (SuperMatrix m n R) pX pZ *
        ringSuperbracket pX (pY + pZ) X (ringSuperbracket pY pZ Y Z) +
    Parity.sign (SuperMatrix m n R) pY pX *
        ringSuperbracket pY (pZ + pX) Y (ringSuperbracket pZ pX Z X) +
    Parity.sign (SuperMatrix m n R) pZ pY *
        ringSuperbracket pZ (pX + pY) Z (ringSuperbracket pX pY X Y) = 0 :=
  graded_super_jacobi pX pY pZ X Y Z

/-- On the matrix carrier, the homogeneous bracket used by the grading owner is
definitionally the universal associative-ring bracket. -/
theorem superbracket_eq_ringSuperbracket
    (p q : Parity) (X Y : SuperMatrix m n R) :
    superbracket p q X Y = ringSuperbracket p q X Y := by
  cases p <;> cases q <;> rfl

end GLJacobi

end InfoGeometry.Canonical.GLSupermatrixGradedLie
