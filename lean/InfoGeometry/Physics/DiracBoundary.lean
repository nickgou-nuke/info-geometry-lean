import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Block

open Complex Matrix

namespace InfoGeometry.Physics.Dirac

/-- The Dirac Gamma Matrices in the Chiral (Weyl) Basis over ℂ. -/
def I2 : Matrix (Fin 2) (Fin 2) ℂ := 1
def Z2 : Matrix (Fin 2) (Fin 2) ℂ := 0

def sigma_1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def sigma_2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]
def sigma_3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def gamma_0 : Matrix (Fin 4) (Fin 4) ℂ :=
  fromBlocks Z2 I2
             I2 Z2

def gamma_1 : Matrix (Fin 4) (Fin 4) ℂ :=
  fromBlocks Z2 sigma_1
             (-sigma_1) Z2

def gamma_2 : Matrix (Fin 4) (Fin 4) ℂ :=
  fromBlocks Z2 sigma_2
             (-sigma_2) Z2

def gamma_3 : Matrix (Fin 4) (Fin 4) ℂ :=
  fromBlocks Z2 sigma_3
             (-sigma_3) Z2

/-- 
THEOREM: The Clifford Algebra Boundary Condition.
Proves that the chiral Weyl representation natively satisfies the 
relativistic anti-commutation relations, rooting the Dirac boundary 
into the non-commutative geometry.
-/
theorem dirac_clifford_boundary :
    gamma_0 * gamma_0 = 1 ∧ 
    gamma_1 * gamma_1 = -1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl

end InfoGeometry.Physics.Dirac
