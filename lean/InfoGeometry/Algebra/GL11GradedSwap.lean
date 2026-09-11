import Mathlib.LinearAlgebra.Matrix.Kronecker
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.Algebra.SupermatrixKoszul

/-!
# The finite `ℂ^(1|1)` graded swap

This file fixes the standard two-site tensor basis

`(00, 01, 10, 11)`.

The local parity is `Γ = diag(1,-1)`.  The graded swap acts by

`τ̂ (eᵢ ⊗ eⱼ) = (-1)^(|i||j|) eⱼ ⊗ eᵢ`.

Consequently it agrees with the ordinary swap on `00`, `01`, and `10`, and
negates the odd--odd vector `11`.  All results are direct finite matrix
theorems; no integrability or continuum-limit claim is made here.
-/

namespace InfoGeometry.Algebra.GL11GradedSwap

open Matrix
open scoped Kronecker Matrix

/-- The local `1|1` parity matrix `diag(1,-1)`. -/
def localParity : Matrix (Fin 2) (Fin 2) ℂ :=
  InfoGeometry.Algebra.SupermatrixKoszul.parityBlock

/-- Total parity `Γ ⊗ Γ` in the standard basis `(00,01,10,11)`. -/
def totalParity : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, -1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, 1]

/-- Ordinary two-site swap in the standard tensor basis. -/
def ordinarySwap : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 0, 1, 0;
     0, 1, 0, 0;
     0, 0, 0, 1]

/-- Koszul graded swap on `ℂ^(1|1) ⊗ ℂ^(1|1)`. -/
def gradedSwap : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 0, 1, 0;
     0, 1, 0, 0;
     0, 0, 0, -1]

/-- The local parity is involutive. -/
theorem localParity_sq :
    localParity * localParity = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [localParity, InfoGeometry.Algebra.SupermatrixKoszul.parityBlock,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Tensor-basis index `0` decodes as the even-even pair `(0,0)`. -/
@[simp]
theorem finProdFinEquiv_symm_zero :
    (finProdFinEquiv.symm (0 : Fin 4) : Fin 2 × Fin 2) = (0, 0) := by
  decide

/-- Tensor-basis index `1` decodes as the even-odd pair `(0,1)`. -/
@[simp]
theorem finProdFinEquiv_symm_one :
    (finProdFinEquiv.symm (1 : Fin 4) : Fin 2 × Fin 2) = (0, 1) := by
  decide

/-- Tensor-basis index `2` decodes as the odd-even pair `(1,0)`. -/
@[simp]
theorem finProdFinEquiv_symm_two :
    (finProdFinEquiv.symm (2 : Fin 4) : Fin 2 × Fin 2) = (1, 0) := by
  decide

/-- Tensor-basis index `3` decodes as the odd-odd pair `(1,1)`. -/
@[simp]
theorem finProdFinEquiv_symm_three :
    (finProdFinEquiv.symm (3 : Fin 4) : Fin 2 × Fin 2) = (1, 1) := by
  decide

/-- The displayed total parity is exactly the Kronecker product `Γ ⊗ Γ`. -/
theorem totalParity_eq_kronecker :
    totalParity =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (localParity ⊗ₖ localParity) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [totalParity, localParity,
      InfoGeometry.Algebra.SupermatrixKoszul.parityBlock, finProdFinEquiv,
      Fin.divNat, Fin.modNat]

/-- The graded swap fixes the even--even basis vector `|00⟩`. -/
theorem gradedSwap_mulVec_00 :
    gradedSwap.mulVec ![(1 : ℂ), 0, 0, 0] = ![(1 : ℂ), 0, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [gradedSwap, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The graded swap sends `|01⟩` to `|10⟩`. -/
theorem gradedSwap_mulVec_01 :
    gradedSwap.mulVec ![(0 : ℂ), 1, 0, 0] = ![(0 : ℂ), 0, 1, 0] := by
  funext i
  fin_cases i <;>
    simp [gradedSwap, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The graded swap sends `|10⟩` to `|01⟩`. -/
theorem gradedSwap_mulVec_10 :
    gradedSwap.mulVec ![(0 : ℂ), 0, 1, 0] = ![(0 : ℂ), 1, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [gradedSwap, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The odd--odd basis vector acquires the Koszul sign. -/
theorem gradedSwap_mulVec_11 :
    gradedSwap.mulVec ![(0 : ℂ), 0, 0, 1] = ![(0 : ℂ), 0, 0, -1] := by
  funext i
  fin_cases i <;>
    simp [gradedSwap, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The graded swap is an involution. -/
theorem gradedSwap_sq :
    gradedSwap * gradedSwap = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gradedSwap, Matrix.mul_apply, Fin.sum_univ_four]

/-- The graded swap preserves total parity. -/
theorem gradedSwap_commutes_totalParity :
    gradedSwap * totalParity = totalParity * gradedSwap := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gradedSwap, totalParity, Matrix.mul_apply, Fin.sum_univ_four]

/-- The Koszul swap is genuinely different from the ordinary swap. -/
theorem gradedSwap_ne_ordinarySwap :
    gradedSwap ≠ ordinarySwap := by
  intro h
  have h33 := congrFun (congrFun h (3 : Fin 4)) (3 : Fin 4)
  change (-1 : ℂ) = 1 at h33
  norm_num at h33

end InfoGeometry.Algebra.GL11GradedSwap
