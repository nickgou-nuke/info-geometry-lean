import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.SuperLieRing
import InfoGeometry.NCG.BerezinianSuperdeterminant

/-!
# Native finite `gl(m|n)` graded matrix Lie spine

This owner realizes the finite associative supermatrix carrier directly as the
native Mathlib matrix algebra on `Fin m ⊕ Fin n`. The four standard blocks are
recovered by restriction to the even/odd summands. Homogeneous even matrices
are block diagonal and homogeneous odd matrices are block off diagonal.

Proved here:
* Koszul parity arithmetic and sign;
* exact block multiplication in all four parity sectors;
* parity preservation by the supercommutator;
* graded cyclicity of the supertrace;
* vanishing supertrace of homogeneous supercommutators;
* universal graded skew symmetry, super-Jacobi, and adjoint-derivation laws in
  every associative ring;
* direct specialization of super-Jacobi to the native `gl(m|n)` matrix ring.

This file deliberately does not claim a Grassmann-valued coefficient algebra,
matrix logarithm/BCH convergence, or `Ber(exp X) = exp(str X)`.
-/

noncomputable section

open Matrix
open BigOperators

namespace InfoGeometry.Canonical.GLSupermatrixGradedLie

inductive Parity where
  | even
  | odd
  deriving DecidableEq, Repr

namespace Parity

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

/-- Native associative `(m|n)` supermatrix carrier. -/
abbrev SuperMatrix (m n : ℕ) (R : Type*) :=
  Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) R

section Blocks
variable {m n : ℕ} {R : Type*}

def blockA (M : SuperMatrix m n R) : Matrix (Fin m) (Fin m) R :=
  fun i j => M (Sum.inl i) (Sum.inl j)

def blockB (M : SuperMatrix m n R) : Matrix (Fin m) (Fin n) R :=
  fun i j => M (Sum.inl i) (Sum.inr j)

def blockC (M : SuperMatrix m n R) : Matrix (Fin n) (Fin m) R :=
  fun i j => M (Sum.inr i) (Sum.inl j)

def blockD (M : SuperMatrix m n R) : Matrix (Fin n) (Fin n) R :=
  fun i j => M (Sum.inr i) (Sum.inr j)

variable [Zero R]

def evenMatrix (A : Matrix (Fin m) (Fin m) R)
    (D : Matrix (Fin n) (Fin n) R) : SuperMatrix m n R :=
  Matrix.fromBlocks A 0 0 D

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

def IsHomogeneous (p : Parity) (M : SuperMatrix m n R) : Prop :=
  match p with
  | .even => ∃ A D, M = evenMatrix A D
  | .odd => ∃ B C, M = oddMatrix B C

/-- `str M = Tr(A) - Tr(D)`. -/
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

/-- Homogeneous supercommutator. -/
def superbracket (p q : Parity)
    (X Y : SuperMatrix m n R) : SuperMatrix m n R :=
  match p, q with
  | .odd, .odd => X * Y + Y * X
  | _, _ => X * Y - Y * X

theorem even_mul_even
    (A E : Matrix (Fin m) (Fin m) R)
    (D H : Matrix (Fin n) (Fin n) R) :
    evenMatrix A D * evenMatrix E H = evenMatrix (A * E) (D * H) := by
  rw [evenMatrix, evenMatrix, Matrix.fromBlocks_multiply]
  simp [evenMatrix]

theorem even_mul_odd
    (A : Matrix (Fin m) (Fin m) R) (D : Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin m) (Fin n) R) (C : Matrix (Fin n) (Fin m) R) :
    evenMatrix A D * oddMatrix B C = oddMatrix (A * B) (D * C) := by
  rw [evenMatrix, oddMatrix, Matrix.fromBlocks_multiply]
  simp [oddMatrix]

theorem odd_mul_even
    (B : Matrix (Fin m) (Fin n) R) (C : Matrix (Fin n) (Fin m) R)
    (A : Matrix (Fin m) (Fin m) R) (D : Matrix (Fin n) (Fin n) R) :
    oddMatrix B C * evenMatrix A D = oddMatrix (B * D) (C * A) := by
  rw [oddMatrix, evenMatrix, Matrix.fromBlocks_multiply]
  simp [oddMatrix]

theorem odd_mul_odd
    (B F : Matrix (Fin m) (Fin n) R)
    (C G : Matrix (Fin n) (Fin m) R) :
    oddMatrix B C * oddMatrix F G = evenMatrix (B * G) (C * F) := by
  rw [oddMatrix, oddMatrix, Matrix.fromBlocks_multiply]
  simp [evenMatrix]

/-- Exact bracket formula in the even-even sector. -/
theorem superbracket_even_even
    (A E : Matrix (Fin m) (Fin m) R)
    (D H : Matrix (Fin n) (Fin n) R) :
    superbracket .even .even (evenMatrix A D) (evenMatrix E H) =
      evenMatrix (A * E - E * A) (D * H - H * D) := by
  change evenMatrix A D * evenMatrix E H - evenMatrix E H * evenMatrix A D = _
  rw [even_mul_even, even_mul_even]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [evenMatrix]

/-- Exact bracket formula in the even-odd sector. -/
theorem superbracket_even_odd
    (A : Matrix (Fin m) (Fin m) R) (D : Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin m) (Fin n) R) (C : Matrix (Fin n) (Fin m) R) :
    superbracket .even .odd (evenMatrix A D) (oddMatrix B C) =
      oddMatrix (A * B - B * D) (D * C - C * A) := by
  change evenMatrix A D * oddMatrix B C - oddMatrix B C * evenMatrix A D = _
  rw [even_mul_odd, odd_mul_even]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [oddMatrix]

/-- Exact bracket formula in the odd-even sector. -/
theorem superbracket_odd_even
    (B : Matrix (Fin m) (Fin n) R) (C : Matrix (Fin n) (Fin m) R)
    (A : Matrix (Fin m) (Fin m) R) (D : Matrix (Fin n) (Fin n) R) :
    superbracket .odd .even (oddMatrix B C) (evenMatrix A D) =
      oddMatrix (B * D - A * B) (C * A - D * C) := by
  change oddMatrix B C * evenMatrix A D - evenMatrix A D * oddMatrix B C = _
  rw [odd_mul_even, even_mul_odd]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [oddMatrix]

/-- Exact bracket formula in the odd-odd sector. -/
theorem superbracket_odd_odd
    (B F : Matrix (Fin m) (Fin n) R)
    (C G : Matrix (Fin n) (Fin m) R) :
    superbracket .odd .odd (oddMatrix B C) (oddMatrix F G) =
      evenMatrix (B * G + F * C) (C * F + G * B) := by
  change oddMatrix B C * oddMatrix F G + oddMatrix F G * oddMatrix B C = _
  rw [odd_mul_odd, odd_mul_odd]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [evenMatrix]

/-- The bracket preserves the `Z/2Z` degree. -/
theorem superbracket_preserves_grading
    (p q : Parity) (X Y : SuperMatrix m n R)
    (hX : IsHomogeneous p X) (hY : IsHomogeneous q Y) :
    IsHomogeneous (p + q) (superbracket p q X Y) := by
  cases p <;> cases q
  · rcases hX with ⟨A, D, rfl⟩
    rcases hY with ⟨E, H, rfl⟩
    exact ⟨A * E - E * A, D * H - H * D, superbracket_even_even A E D H⟩
  · rcases hX with ⟨A, D, rfl⟩
    rcases hY with ⟨B, C, rfl⟩
    exact ⟨A * B - B * D, D * C - C * A, superbracket_even_odd A D B C⟩
  · rcases hX with ⟨B, C, rfl⟩
    rcases hY with ⟨A, D, rfl⟩
    exact ⟨B * D - A * B, C * A - D * C, superbracket_odd_even B C A D⟩
  · rcases hX with ⟨B, C, rfl⟩
    rcases hY with ⟨F, G, rfl⟩
    exact ⟨B * G + F * C, C * F + G * B, superbracket_odd_odd B F C G⟩

/-- Even-even cyclicity of supertrace. -/
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

theorem supertrace_mul_odd_even
    (X Y : SuperMatrix m n R)
    (hX : IsHomogeneous .odd X) (hY : IsHomogeneous .even Y) :
    supertrace (X * Y) = 0 := by
  rcases hX with ⟨B, C, rfl⟩
  rcases hY with ⟨A, D, rfl⟩
  rw [odd_mul_even]
  exact supertrace_oddMatrix _ _

/-- Odd-odd cyclicity acquires the Koszul minus sign. -/
theorem supertrace_mul_odd_odd
    (X Y : SuperMatrix m n R)
    (hX : IsHomogeneous .odd X) (hY : IsHomogeneous .odd Y) :
    supertrace (X * Y) = -supertrace (Y * X) := by
  rcases hX with ⟨B, C, rfl⟩
  rcases hY with ⟨F, G, rfl⟩
  rw [odd_mul_odd, odd_mul_odd]
  simp only [supertrace_evenMatrix]
  have hBG : Matrix.trace (B * G) = Matrix.trace (G * B) := Matrix.trace_mul_comm B G
  have hCF : Matrix.trace (C * F) = Matrix.trace (F * C) := Matrix.trace_mul_comm C F
  rw [hBG, hCF]
  ring

/-- Graded cyclicity `str(XY)=(-1)^(|X||Y|) str(YX)`. -/
theorem supertrace_mul_graded
    (p q : Parity) (X Y : SuperMatrix m n R)
    (hX : IsHomogeneous p X) (hY : IsHomogeneous q Y) :
    supertrace (X * Y) = Parity.sign R p q * supertrace (Y * X) := by
  cases p <;> cases q
  · simpa [Parity.sign] using supertrace_mul_even_even X Y hX hY
  · rw [supertrace_mul_even_odd X Y hX hY, supertrace_mul_odd_even Y X hY hX]
    simp [Parity.sign]
  · rw [supertrace_mul_odd_even X Y hX hY, supertrace_mul_even_odd Y X hY hX]
    simp [Parity.sign]
  · simpa [Parity.sign] using supertrace_mul_odd_odd X Y hX hY

/-- Graded skew symmetry. -/
theorem superbracket_graded_skew
    (p q : Parity) (X Y : SuperMatrix m n R) :
    superbracket p q X Y = -(Parity.sign R p q) • superbracket q p Y X := by
  cases p <;> cases q <;>
    ext i j <;> simp [superbracket, Parity.sign] <;> ring

/-- Supertrace kills all homogeneous supercommutators. -/
theorem supertrace_superbracket_eq_zero
    (p q : Parity) (X Y : SuperMatrix m n R)
    (hX : IsHomogeneous p X) (hY : IsHomogeneous q Y) :
    supertrace (superbracket p q X Y) = 0 := by
  cases p <;> cases q
  · rcases hX with ⟨A, D, rfl⟩
    rcases hY with ⟨E, H, rfl⟩
    rw [superbracket_even_even]
    simp only [supertrace_evenMatrix, Matrix.trace_sub]
    rw [Matrix.trace_mul_comm A E, Matrix.trace_mul_comm D H]
    ring
  · rcases hX with ⟨A, D, rfl⟩
    rcases hY with ⟨B, C, rfl⟩
    rw [superbracket_even_odd]
    exact supertrace_oddMatrix _ _
  · rcases hX with ⟨B, C, rfl⟩
    rcases hY with ⟨A, D, rfl⟩
    rw [superbracket_odd_even]
    exact supertrace_oddMatrix _ _
  · rcases hX with ⟨B, C, rfl⟩
    rcases hY with ⟨F, G, rfl⟩
    rw [superbracket_odd_odd]
    simp only [supertrace_evenMatrix, Matrix.trace_add]
    have hBG : Matrix.trace (B * G) = Matrix.trace (G * B) := Matrix.trace_mul_comm B G
    have hCF : Matrix.trace (C * F) = Matrix.trace (F * C) := Matrix.trace_mul_comm C F
    rw [hBG, hCF]
    ring

end Grading

section Universal
variable {S : Type*} [Ring S]

/-- Parity superbracket in any associative ring. -/
def ringSuperbracket (p q : Parity) (X Y : S) : S :=
  match p, q with
  | .odd, .odd => X * Y + Y * X
  | _, _ => X * Y - Y * X

theorem ringSuperbracket_graded_skew
    (p q : Parity) (X Y : S) :
    ringSuperbracket p q X Y =
      -(Parity.sign S p q * ringSuperbracket q p Y X) := by
  cases p <;> cases q <;> simp [ringSuperbracket, Parity.sign] <;> abel

/-- Universal graded super-Jacobi identity. -/
theorem graded_super_jacobi
    (pX pY pZ : Parity) (X Y Z : S) :
    Parity.sign S pX pZ *
        ringSuperbracket pX (pY + pZ) X (ringSuperbracket pY pZ Y Z) +
    Parity.sign S pY pX *
        ringSuperbracket pY (pZ + pX) Y (ringSuperbracket pZ pX Z X) +
    Parity.sign S pZ pY *
        ringSuperbracket pZ (pX + pY) Z (ringSuperbracket pX pY X Y) = 0 := by
  cases pX <;> cases pY <;> cases pZ <;>
    simp [ringSuperbracket, Parity.add, Parity.sign] <;> noncomm_ring

/-- `ad_X` is a graded derivation of the bracket. -/
theorem super_adjoint_derivation
    (pX pY pZ : Parity) (X Y Z : S) :
    ringSuperbracket pX (pY + pZ) X (ringSuperbracket pY pZ Y Z) =
      ringSuperbracket (pX + pY) pZ (ringSuperbracket pX pY X Y) Z +
      Parity.sign S pX pY *
        ringSuperbracket pY (pX + pZ) Y (ringSuperbracket pX pZ X Z) := by
  cases pX <;> cases pY <;> cases pZ <;>
    simp [ringSuperbracket, Parity.add, Parity.sign] <;> noncomm_ring
end Universal

section GLJacobi
variable {m n : ℕ} {R : Type*} [CommRing R]

/-- Universal super-Jacobi specialized to `gl(m|n)`. -/
theorem gl_graded_super_jacobi
    (pX pY pZ : Parity) (X Y Z : SuperMatrix m n R) :
    Parity.sign (SuperMatrix m n R) pX pZ *
        ringSuperbracket pX (pY + pZ) X (ringSuperbracket pY pZ Y Z) +
    Parity.sign (SuperMatrix m n R) pY pX *
        ringSuperbracket pY (pZ + pX) Y (ringSuperbracket pZ pX Z X) +
    Parity.sign (SuperMatrix m n R) pZ pY *
        ringSuperbracket pZ (pX + pY) Z (ringSuperbracket pX pY X Y) = 0 :=
  graded_super_jacobi pX pY pZ X Y Z

@[simp] theorem superbracket_eq_ringSuperbracket
    (p q : Parity) (X Y : SuperMatrix m n R) :
    superbracket p q X Y = ringSuperbracket p q X Y := by
  cases p <;> cases q <;> rfl
end GLJacobi

end InfoGeometry.Canonical.GLSupermatrixGradedLie
