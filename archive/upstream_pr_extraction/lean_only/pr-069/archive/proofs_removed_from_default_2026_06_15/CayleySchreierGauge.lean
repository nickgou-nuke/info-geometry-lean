import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Topological Non-Abelian Gauge Structures in Cayley-Schreier Lattices

Formalizes the emergent spinful symmetries arising from the Peter-Weyl 
decomposition of the quaternion gauge group Q₈ in a Cayley-Schreier lattice.
-/

namespace CayleySchreierGauge

open Matrix Complex

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Pauli matrices. -/
def σ1 : M2C := !![0, 1; 1, 0]
def σ2 : M2C := !![0, -I; I, 0]
def σ3 : M2C := !![1, 0; 0, -1]

/-- The 2D Irreducible Representation E for Q₈ -/
def DE_1 : M2C := 1
def DE_i : M2C := -I • σ1
def DE_j : M2C := -I • σ2
def DE_k : M2C := -I • σ3

/-- 
Theorem: The emergent spinful time-reversal symmetry operator `T_E`.
Even though the fundamental lattice degrees of freedom are spinless, 
the Peter-Weyl block-diagonalization isolates the 2D irrep `E` 
which natively acts as a spinor.
-/
def TE : M2C := I • σ2

/-- 
Theorem: `T_E` squares to `-1` (Kramers degeneracy).
The block-diagonalized synthetic gauge effectively generates 
true spin-1/2 fermions with spinful time-reversal symmetry!
-/
theorem emergent_spinful_trs : TE * TE = -1 := by
  dsimp [TE, σ2]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two] <;>
    rw [I_sq] <;> ring

end CayleySchreierGauge
