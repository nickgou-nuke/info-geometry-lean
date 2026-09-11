import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Permutation
import InfoGeometry.Canonical.SplitOctonionThreeColorModularCl11

/-!
# A finite three-colour polynomial braid operator

This owner is deliberately an external associative operator layer.  The
colour carrier is a finite tensor index set; no associativity of Zorn or
split-octonion multiplication is used here.
-/

namespace InfoGeometry.Canonical

abbrev ColourPair := SplitOctonionColour × SplitOctonionColour
abbrev ColourTriple := SplitOctonionColour × SplitOctonionColour × SplitOctonionColour
abbrev ColourRMatrix (K : Type*) := Matrix ColourPair ColourPair K
abbrev ColourTripleOperator (K : Type*) := Matrix ColourTriple ColourTriple K

def pairSwap : Equiv.Perm ColourPair where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  left_inv := by intro p; rcases p with ⟨a, b⟩; rfl
  right_inv := by intro p; rcases p with ⟨a, b⟩; rfl

def tripleSwap12 : Equiv.Perm ColourTriple where
  toFun p := (p.2.1, p.1, p.2.2)
  invFun p := (p.2.1, p.1, p.2.2)
  left_inv := by intro p; rcases p with ⟨a, b, c⟩; rfl
  right_inv := by intro p; rcases p with ⟨a, b, c⟩; rfl

def tripleSwap23 : Equiv.Perm ColourTriple where
  toFun p := (p.1, p.2.2, p.2.1)
  invFun p := (p.1, p.2.2, p.2.1)
  left_inv := by intro p; rcases p with ⟨a, b, c⟩; rfl
  right_inv := by intro p; rcases p with ⟨a, b, c⟩; rfl

def R12 {K : Type*} [Semiring K]
    (R : ColourRMatrix K) : ColourTripleOperator K :=
  fun (a, b, c) (a', b', c') =>
    R (a, b) (a', b') * if c = c' then 1 else 0

def R23 {K : Type*} [Semiring K]
    (R : ColourRMatrix K) : ColourTripleOperator K :=
  fun (a, b, c) (a', b', c') =>
    (if a = a' then 1 else 0) * R (b, c) (b', c')

/-- The external colour swap, represented as a non-diagonal permutation matrix. -/
def colourSwapR {K : Type*} [Semiring K] : ColourRMatrix K :=
  Equiv.Perm.permMatrix K pairSwap

noncomputable def matrixPolynomialEval {K : Type*} [CommRing K]
    (p : Polynomial K) (R : ColourRMatrix K) : ColourRMatrix K :=
  Polynomial.eval₂ (algebraMap K (ColourRMatrix K)) R p

structure ThreeColorPolynomialRData (K : Type*) [CommRing K] where
  R : ColourRMatrix K
  polynomial : Polynomial K
  polynomial_ne_zero : polynomial ≠ 0
  annihilates : matrixPolynomialEval polynomial R = 0

noncomputable def colourSwapPolynomial (K : Type*) [CommRing K] : Polynomial K :=
  Polynomial.X ^ 2 - 1

theorem pairSwap_sq : pairSwap * pairSwap = 1 := by
  ext p <;> rcases p with ⟨a, b⟩ <;> rfl

theorem colourSwapR_sq {K : Type*} [Semiring K] :
    colourSwapR (K := K) * colourSwapR (K := K) = 1 := by
  have h := congrArg (fun σ : Equiv.Perm ColourPair => Equiv.Perm.permMatrix K σ) pairSwap_sq
  simpa [colourSwapR, Matrix.permMatrix_mul, mul_assoc] using h

theorem tripleSwap_artin_relation :
    tripleSwap12 * tripleSwap23 * tripleSwap12 =
      tripleSwap23 * tripleSwap12 * tripleSwap23 := by
  ext p <;> rcases p with ⟨a, b, c⟩ <;> rfl

def colourR12 {K : Type*} [Semiring K] : ColourTripleOperator K :=
  Equiv.Perm.permMatrix K tripleSwap12.symm

def colourR23 {K : Type*} [Semiring K] : ColourTripleOperator K :=
  Equiv.Perm.permMatrix K tripleSwap23.symm

theorem colourR12_artin_relation {K : Type*} [Semiring K] :
    colourR12 (K := K) * colourR23 (K := K) * colourR12 (K := K) =
      colourR23 (K := K) * colourR12 (K := K) * colourR23 (K := K) := by
  have h := congrArg (fun σ : Equiv.Perm ColourTriple => Equiv.Perm.permMatrix K σ)
    tripleSwap_artin_relation
  simpa [colourR12, colourR23, Matrix.permMatrix_mul, mul_assoc] using h

theorem colourSwapR_polynomial_property {K : Type*} [CommRing K] :
    matrixPolynomialEval (colourSwapPolynomial K) (colourSwapR (K := K)) = 0 := by
  calc
    matrixPolynomialEval (colourSwapPolynomial K) (colourSwapR (K := K))
        = colourSwapR (K := K) * colourSwapR (K := K) - 1 := by
            simp [matrixPolynomialEval, colourSwapPolynomial, pow_two]
    _ = 0 := by simpa [colourSwapR_sq]

noncomputable def colourSwapRDataQ : ThreeColorPolynomialRData ℚ where
  R := colourSwapR
  polynomial := colourSwapPolynomial ℚ
  polynomial_ne_zero := by
    intro h
    have h0 := congrArg (fun p : Polynomial ℚ => p.eval 0) h
    simpa [colourSwapPolynomial] using h0
  annihilates := colourSwapR_polynomial_property

theorem colourSwapR_artin_relation {K : Type*} [Semiring K] :
    colourR12 (K := K) * colourR23 (K := K) * colourR12 (K := K) =
      colourR23 (K := K) * colourR12 (K := K) * colourR23 (K := K) :=
  colourR12_artin_relation

theorem colourSwapRDataQ_artin_relation :
    colourR12 (K := ℚ) * colourR23 (K := ℚ) * colourR12 (K := ℚ) =
      colourR23 (K := ℚ) * colourR12 (K := ℚ) * colourR23 (K := ℚ) :=
  colourSwapR_artin_relation

def diagonalColourAction (g : Equiv.Perm SplitOctonionColour) : Equiv.Perm ColourPair where
  toFun p := (g p.1, g p.2)
  invFun p := (g.symm p.1, g.symm p.2)
  left_inv := by intro p; rcases p with ⟨a, b⟩; simp
  right_inv := by intro p; rcases p with ⟨a, b⟩; simp

theorem diagonalColourAction_comm_pairSwap (g : Equiv.Perm SplitOctonionColour) :
    diagonalColourAction g * pairSwap = pairSwap * diagonalColourAction g := by
  ext p <;> rcases p with ⟨a, b⟩ <;> rfl

def diagonalColourMatrix (g : Equiv.Perm SplitOctonionColour) : ColourRMatrix ℚ :=
  Equiv.Perm.permMatrix ℚ (diagonalColourAction g)

theorem colourSwapR_equivariant (g : Equiv.Perm SplitOctonionColour) :
    colourSwapR (K := ℚ) * diagonalColourMatrix g =
      diagonalColourMatrix g * colourSwapR (K := ℚ) := by
  simpa [colourSwapR, diagonalColourMatrix, Matrix.permMatrix_mul, mul_assoc] using
    congrArg (fun σ : Equiv.Perm ColourPair => Equiv.Perm.permMatrix ℚ σ)
      (diagonalColourAction_comm_pairSwap g)

end InfoGeometry.Canonical
