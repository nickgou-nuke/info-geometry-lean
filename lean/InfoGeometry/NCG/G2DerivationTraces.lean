import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Matrix
open BigOperators

namespace InfoGeometry.NCG

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

local notation "BlockMat" => Matrix (ι ⊕ ι) (ι ⊕ ι) R
local notation "SubMat" => Matrix ι ι R

/-!
=============================================================================
SECTION 1: Trace-Free and Supertrace-Free Properties of Geometric Derivations
=============================================================================
-/

/-- The Grading Operator Γ = diag(I, -I) -/
def g2Gamma : BlockMat :=
  fromBlocks (1 : SubMat) 0 0 (-1 : SubMat)

@[simp]
theorem trace_fromBlocks_gen (A B C D : SubMat) :
    Matrix.trace (fromBlocks A B C D : BlockMat) =
      Matrix.trace A + Matrix.trace D := by
  simp [Matrix.trace, Fintype.sum_sum_type]

/-- Supertrace functional: STr(M) = Tr(M₁₁) - Tr(M₂₂) -/
def g2SuperTrace (M : BlockMat) : R :=
  Matrix.trace (fromBlocks (1 : SubMat) 0 0 (-1 : SubMat) * M)

/-- An infinitesimally symplectic / so(n, n) block derivation:
    D = [[A, B], [C, -Aᵀ]] where Bᵀ = -B, Cᵀ = -C -/
def soBlockDerivation (A B C : SubMat) : BlockMat :=
  fromBlocks A B C (-Aᵀ)

/-- 🏆 THEOREM 1: Every so(n,n) / g_{2(2)} block derivation is strictly Trace-Free:
    Tr(D) = 0 -/
theorem trace_soBlockDerivation (A B C : SubMat) :
    Matrix.trace (soBlockDerivation A B C : BlockMat) = 0 := by
  dsimp [soBlockDerivation]
  rw [trace_fromBlocks_gen, Matrix.trace_neg, Matrix.trace_transpose]
  ring

/-- 🏆 THEOREM 2: Off-diagonal Bogoliubov / Pairing derivations are Supertrace-Free:
    STr(D_pair) = 0 -/
theorem superTrace_pairingDerivation (B C : SubMat) :
    g2SuperTrace (fromBlocks (0 : SubMat) B C (0 : SubMat)) = 0 := by
  dsimp [g2SuperTrace]
  have h_mul : fromBlocks (1 : SubMat) 0 0 (-1) * fromBlocks 0 B C 0 =
      fromBlocks 0 B (-C) 0 := by
    rw [fromBlocks_multiply]
    simp
  rw [h_mul, trace_fromBlocks_gen]
  simp

/-- 🏆 THEOREM 3: Pure Shape Operator has both vanishing Trace and vanishing Supertrace:
    Tr(D_shape) = 0  and  STr(D_shape) = 0 -/
theorem shape_operator_traces (A : SubMat) (hA_trace : Matrix.trace A = 0) (B C : SubMat) :
    Matrix.trace (soBlockDerivation A B C) = 0 ∧
    g2SuperTrace (fromBlocks A B C (-Aᵀ)) = 0 := by
  constructor
  · exact trace_soBlockDerivation A B C
  · dsimp [g2SuperTrace]
    have h_mul : fromBlocks (1 : SubMat) 0 0 (-1) * fromBlocks A B C (-Aᵀ) =
        fromBlocks A B (-C) (Aᵀ) := by
      rw [fromBlocks_multiply]
      simp
    rw [h_mul, trace_fromBlocks_gen, Matrix.trace_transpose, hA_trace]
    ring

end InfoGeometry.NCG
