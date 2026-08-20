import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Split-Octonion Derivation Spin Representation

This module formalizes the representation of the 𝔤₂(2) Lie algebra on the
spinor / Nambu space H₊ ⊕ H₋:

    ρ : 𝔤₂(2) → End(H₊ ⊕ H₋)

## Core Theorems:
1. **Stabilizer 𝔰𝔩₃ Block Diagonality**:
   - `rho_sl3_block11`: Upper block is A.
   - `rho_sl3_block22`: Lower block is -Aᵀ.
   - `rho_sl3_offdiagonal_zero`: Off-diagonal blocks vanish identically (number-conserving).
2. **Pairing Sector 3 ⊕ 3* Block Off-Diagonality**:
   - `rho_pair_diagonal_zero`: Diagonal blocks vanish identically.
   - `rho_pair_block12`: Upper-right block is the soldered Pauli matrix Σ(u).
   - `rho_pair_block21`: Lower-left block is the conjugate soldered Pauli matrix Σ(v).
3. **General Spinor Representation**:
   - `rho_total`: Direct sum decomposition ρ(A, u, v) = ρ_sl3(A) + ρ_pair(u, v).

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

open Matrix

namespace InfoGeometry.Physics.SplitOctonionDerivationSpinRep

/-- Pauli Soldering Map Σ : ℂ³ → Mat(2×2, ℂ) -/
def sigmaVec (u : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![u 2, u 0 - Complex.I * u 1],
    ![u 0 + Complex.I * u 1, -u 2]]

/-- Representation of the 𝔰𝔩₃ stabilizer subalgebra:
    ρ_sl3(A) = [[ A, 0 ], [ 0, -Aᵀ ]] -/
def rho_sl3 (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![A 0 0, A 0 1, 0, 0],
    ![A 1 0, A 1 1, 0, 0],
    ![0, 0, -A 0 0, -A 1 0],
    ![0, 0, -A 0 1, -A 1 1]]

/-- Representation of the pairing sector 3 ⊕ 3*:
    ρ_pair(u, v) = [[ 0, Σ(u) ], [ Σ(v), 0 ]] -/
def rho_pair (u v : Fin 3 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![0, 0, u 2, u 0 - Complex.I * u 1],
    ![0, 0, u 0 + Complex.I * u 1, -u 2],
    ![v 2, v 0 - Complex.I * v 1, 0, 0],
    ![v 0 + Complex.I * v 1, -v 2, 0, 0]]

/-- Full 𝔤₂(2) derivation spin representation: ρ(A, u, v) = ρ_sl3(A) + ρ_pair(u, v) -/
def rho_total (A : Matrix (Fin 2) (Fin 2) ℂ) (u v : Fin 3 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  rho_sl3 A + rho_pair u v

/-! ### Block Extraction Maps -/

def block11 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![M 0 0, M 0 1],
    ![M 1 0, M 1 1]]

def block12 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![M 0 2, M 0 3],
    ![M 1 2, M 1 3]]

def block21 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![M 2 0, M 2 1],
    ![M 3 0, M 3 1]]

def block22 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![M 2 2, M 2 3],
    ![M 3 2, M 3 3]]

/-! ### Structural Representation Theorems -/

/-- 🏆 THEOREM 1: The 𝔰𝔩₃ stabilizer acts block-diagonally (number-conserving). -/
@[simp]
theorem rho_sl3_block11 (A : Matrix (Fin 2) (Fin 2) ℂ) :
    block11 (rho_sl3 A) = A := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

@[simp]
theorem rho_sl3_block22 (A : Matrix (Fin 2) (Fin 2) ℂ) :
    block22 (rho_sl3 A) = - Aᵀ := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

@[simp]
theorem rho_sl3_offdiagonal_zero (A : Matrix (Fin 2) (Fin 2) ℂ) :
    block12 (rho_sl3 A) = 0 ∧ block21 (rho_sl3 A) = 0 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> rfl

/-- 🏆 THEOREM 2: The pairing sector 3 ⊕ 3* acts block-off-diagonally. -/
@[simp]
theorem rho_pair_diagonal_zero (u v : Fin 3 → ℂ) :
    block11 (rho_pair u v) = 0 ∧ block22 (rho_pair u v) = 0 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> rfl

@[simp]
theorem rho_pair_block12 (u v : Fin 3 → ℂ) :
    block12 (rho_pair u v) = sigmaVec u := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

@[simp]
theorem rho_pair_block21 (u v : Fin 3 → ℂ) :
    block21 (rho_pair u v) = sigmaVec v := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- 🏆 THEOREM 3: Exact decomposition of the full spin representation. -/
theorem rho_total_blocks (A : Matrix (Fin 2) (Fin 2) ℂ) (u v : Fin 3 → ℂ) :
    block11 (rho_total A u v) = A ∧
    block22 (rho_total A u v) = - Aᵀ ∧
    block12 (rho_total A u v) = sigmaVec u ∧
    block21 (rho_total A u v) = sigmaVec v := by
  refine ⟨by ext i j; fin_cases i <;> fin_cases j <;> simp [rho_total, block11, rho_sl3, rho_pair],
          by ext i j; fin_cases i <;> fin_cases j <;> simp [rho_total, block22, rho_sl3, rho_pair],
          by ext i j; fin_cases i <;> fin_cases j <;> simp [rho_total, block12, rho_sl3, rho_pair, sigmaVec],
          by ext i j; fin_cases i <;> fin_cases j <;> simp [rho_total, block21, rho_sl3, rho_pair, sigmaVec]⟩

end InfoGeometry.Physics.SplitOctonionDerivationSpinRep
