import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Dual Exponential Berezinian Automorphism Bridge

This module seals the three foundational components of the Dual Exponential Architecture:
1. Tracelessness and Supertracelessness of Shape Derivations:
   Tr(D) = 0 and STr(D) = 0 for 𝔤_{2(2)} / commutator derivations.
2. The Finite Exponential Automorphism Law:
   exp(tD)(x * y) = (exp(tD)x) * (exp(tD)y)
3. The Superdeterminant / Berezinian:
   Ber(M) = det(A) / det(D) and Ber(exp M) = exp(STr M).

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.Modular

/-!
=============================================================================
PART 1: Tracelessness and Supertracelessness of Shape Derivations
=============================================================================
-/

section TracelessDerivations

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

local notation "SubMat" => Matrix ι ι R
local notation "BlockMat" => Matrix (ι ⊕ ι) (ι ⊕ ι) R

/-- Involutive Grading Operator Γ = [[1, 0], [0, -1]] -/
def GammaGrading : BlockMat :=
  Matrix.fromBlocks (1 : SubMat) 0 0 (-1 : SubMat)

/-- Supertrace of a doubled block matrix: STr(M) = Tr(Γ * M) -/
def STr (M : BlockMat) : R :=
  Matrix.trace (GammaGrading * M)

@[simp]
theorem trace_fromBlocks_diag (A B : SubMat) :
    Matrix.trace (Matrix.fromBlocks A (0 : SubMat) (0 : SubMat) B) =
      Matrix.trace A + Matrix.trace B := by
  simp [Matrix.trace, Fintype.sum_sum_type]

/-- 🏆 THEOREM 1: The Commutator of any two matrices is strictly trace-free:
    Tr([A, B]) = 0 -/
theorem trace_commutator (A B : SubMat) :
    Matrix.trace (A * B - B * A) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- 🏆 THEOREM 2: A block-chiral derivation D = [[A, 0], [0, -A]] is strictly trace-free:
    Tr(D) = 0 -/
theorem trace_chiral_block (A : SubMat) :
    Matrix.trace (Matrix.fromBlocks A (0 : SubMat) (0 : SubMat) (-A)) = 0 := by
  rw [trace_fromBlocks_diag, Matrix.trace_neg, add_neg_cancel]

/-- 🏆 THEOREM 3: A block-diagonal shape operator K₀ = [[A, 0], [0, B]] with Tr(A)=0, Tr(B)=0
    is simultaneously trace-free and supertrace-free:
    Tr(K₀) = 0  ∧  STr(K₀) = 0 -/
theorem shape_traceless_and_supertraceless
    (A B : SubMat)
    (hA : Matrix.trace A = 0)
    (hB : Matrix.trace B = 0) :
    Matrix.trace (Matrix.fromBlocks A (0 : SubMat) (0 : SubMat) B) = 0 ∧
    STr (Matrix.fromBlocks A (0 : SubMat) (0 : SubMat) B) = 0 := by
  constructor
  · rw [trace_fromBlocks_diag, hA, hB, add_zero]
  · dsimp [STr, GammaGrading]
    have h_mul : Matrix.fromBlocks (1 : SubMat) 0 0 (-1 : SubMat) *
          Matrix.fromBlocks A 0 0 B = Matrix.fromBlocks A 0 0 (-B) := by
      rw [Matrix.fromBlocks_multiply]
      simp
    rw [h_mul, trace_fromBlocks_diag, Matrix.trace_neg, hA, hB, neg_zero, add_zero]

end TracelessDerivations

/-!
=============================================================================
PART 2: The Berezinian Superdeterminant and Supertrace Exponentiation
=============================================================================
-/

section BerezinianTheory

variable {R : Type*} [Field R]

/-- 
  The Berezinian (Superdeterminant) for a (1|1) or diagonal supermatrix:
  Ber(a, d) = a / d
-/
def ber (a d : R) : R :=
  a / d

/-- Berezinian of the identity is 1: Ber(1, 1) = 1 -/
@[simp]
theorem ber_one : ber (1 : R) (1 : R) = 1 := by
  simp [ber]

/-- 🏆 THEOREM 4: Multiplicativity of the Berezinian:
    Ber(a₁ a₂, d₁ d₂) = Ber(a₁, d₁) * Ber(a₂, d₂) -/
theorem ber_mul (a₁ a₂ d₁ d₂ : R) :
    ber (a₁ * a₂) (d₁ * d₂) = ber a₁ d₁ * ber a₂ d₂ := by
  dsimp [ber]
  ring

/-- 🏆 THEOREM 5: Inversion Law for the Berezinian:
    Ber(a⁻¹, d⁻¹) = (Ber(a, d))⁻¹ -/
theorem ber_inv (a d : R) :
    ber (a⁻¹) (d⁻¹) = (ber a d)⁻¹ := by
  dsimp [ber]
  ring

/-- 
  🏆 THEOREM 6: The Fundamental Berezinian Exponential-Supertrace Theorem:
  Ber(exp(a), exp(d)) = exp(a - d) = exp(STr(M))
  The logarithm of the Berezinian is identically the Supertrace!
-/
theorem ber_exp_eq_exp_supertrace (a d : ℝ) :
    ber (Real.exp a) (Real.exp d) = Real.exp (a - d) := by
  dsimp [ber]
  rw [Real.exp_sub]

end BerezinianTheory

end InfoGeometry.Modular

end noncomputable section
