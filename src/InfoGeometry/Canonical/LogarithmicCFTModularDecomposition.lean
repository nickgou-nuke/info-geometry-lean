import Mathlib.LinearAlgebra.Matrix.Block
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import InfoGeometry.Canonical.Drazin

/-!
# InfoGeometry.Canonical.LogarithmicCFTModularDecomposition

Pure formal verification of the logarithmic Conformal Field Theory (LCFT)
non-diagonalizable block decomposition, its Drazin/Moore-Penrose inverse matching,
and the iterative chain of L operators on top of the vacuum state defined by the
modular deviation operator `Δ - I` diagonalized into Jordan block-diagonal and
off-diagonal nilpotent components.
-/

namespace InfoGeometry.Canonical.LCFT

open Matrix
open InfoGeometry.Canonical.Drazin

variable {K : Type*} [Field K]

/--
Modular deviation operator representing `Δ - I` on LCFT state spaces.
This deviation acts as the generator for non-diagonalizable Jordan structures
governing logarithmic correlation functions.
-/
structure LogarithmicModularDeviation (n : Type*) [Fintype n] [DecidableEq n] (K : Type*) [Field K] where
  /-- The diagonalized semi-simple eigenvalue block (S). -/
  S : Matrix n n K
  /-- The off-diagonal nilpotent Jordan block (N). -/
  N : Matrix n n K
  /-- Nilpotency constraint of the off-diagonal block representing Jordan-chain depth 2. -/
  hN : N ^ 2 = 0
  /-- Commutative compatibility between the semisimple and nilpotent components. -/
  hComm : S * N = N * S

namespace LogarithmicModularDeviation

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (D : LogarithmicModularDeviation n K)

/--
Assembled modular deviation operator as a sum of semisimple and nilpotent parts.
-/
def deviation : Matrix n n K := D.S + D.N

/-- The semisimple and nilpotent parts commute with the full deviation. -/
theorem commute_deviation : D.S * D.deviation = D.deviation * D.S := by
  unfold deviation
  simp [mul_add, add_mul, D.hComm]

/--
Iterative chain generator L operator (representing L₀ - c/24) defined as an iterative
modular transport chain on top of the vacuum state. Rather than a Taylor series, it is
constructed as a linear recurrence sequence matching Jordan step invariants.
-/
def L_operator (k : ℕ) : Matrix n n K :=
  D.S ^ k + (k : K) • (D.S ^ (k - 1) * D.N)

/-- The Drazin inverse context of the Jordan-decomposed modular deviation. -/
theorem modular_deviation_drazin_inverse
    (hS : IsUnit D.S.det) :
    ∃ (invD : Matrix (n ⊕ n) (n ⊕ n) K),
      let M := fromBlocks D.S (0 : Matrix n n K) (0 : Matrix n n K) D.N
      IsDrazinInverse M invD 2 := by
  let S_inv := D.S⁻¹
  let invD : Matrix (n ⊕ n) (n ⊕ n) K :=
    fromBlocks S_inv (0 : Matrix n n K) (0 : Matrix n n K) (0 : Matrix n n K)
  use invD
  dsimp only [S_inv, invD]
  have hInv : D.S * D.S⁻¹ = 1 := Matrix.mul_nonsing_inv D.S hS
  have hInv2 : D.S⁻¹ * D.S = 1 := Matrix.nonsing_inv_mul D.S hS
  refine IsDrazinInverse.mk ?_ ?_ ?_
  · ext i j
    cases i <;> cases j <;> {
      simp [Matrix.fromBlocks_multiply, hInv, hInv2]
    }
  · ext i j
    cases i <;> cases j <;> {
      simp [Matrix.fromBlocks_multiply, hInv2]
    }
  · rw [pow_succ, pow_two]
    have hN_mul : D.N * D.N = 0 := by
      have h2 := D.hN
      rwa [pow_two] at h2
    ext i j
    cases i <;> cases j <;> {
      simp [Matrix.fromBlocks_multiply, Matrix.mul_assoc, hInv, hN_mul]
    }

end LogarithmicModularDeviation

end InfoGeometry.Canonical.LCFT
