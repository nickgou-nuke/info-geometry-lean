import Mathlib.Data.Int.ModEq
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# The integral `D₄` root lattice

This owner is deliberately independent of the older finite triality packets.
It records the standard integral lattice, its four simple roots, the Cartan
Gram matrix, and the corresponding integral reflections.  No assertion about
the discriminant group or `E₈` gluing is made here.
-/

namespace InfoGeometry.RootSystem.D4

def Ambient := Fin 4 → ℤ

def coordinateSum (x : Ambient) : ℤ := ∑ i, x i

def IsD4 (x : Ambient) : Prop := coordinateSum x % 2 = 0

abbrev Lattice := {x : Ambient // IsD4 x}

def basisVector (i : Fin 4) : Ambient := fun j => if i = j then 1 else 0

def dot (x y : Ambient) : ℤ := ∑ i, x i * y i

def simpleRoot (i : Fin 4) : Ambient :=
  match i with
  | 0 => ![1, -1, 0, 0]
  | 1 => ![0, 1, -1, 0]
  | 2 => ![0, 0, 1, -1]
  | 3 => ![0, 0, 1, 1]

theorem coordinateSum_simpleRoot (i : Fin 4) :
    coordinateSum (simpleRoot i) = if i = 3 then 2 else 0 := by
  fin_cases i <;> simp [simpleRoot, coordinateSum, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]

theorem simpleRoot_mem (i : Fin 4) : IsD4 (simpleRoot i) := by
  change coordinateSum (simpleRoot i) % 2 = 0
  fin_cases i <;>
    norm_num [coordinateSum, simpleRoot, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]

def simpleRootLattice (i : Fin 4) : Lattice :=
  ⟨simpleRoot i, simpleRoot_mem i⟩

theorem simpleRoot_norm (i : Fin 4) : dot (simpleRoot i) (simpleRoot i) = 2 := by
  fin_cases i <;>
    norm_num [dot, simpleRoot, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]

def cartanMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  fun i j => dot (simpleRoot i) (simpleRoot j)

theorem cartanMatrix_diagonal (i : Fin 4) : cartanMatrix i i = 2 :=
  simpleRoot_norm i

theorem cartanMatrix_adjacent :
    cartanMatrix 0 1 = -1 ∧ cartanMatrix 1 2 = -1 ∧
      cartanMatrix 1 3 = -1 := by
  norm_num [cartanMatrix, dot, simpleRoot, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]

theorem cartanMatrix_symmetric :
    Matrix.transpose cartanMatrix = cartanMatrix := by
  ext i j
  simp [cartanMatrix, dot, mul_comm]

theorem cartanMatrix_off_diagonal (i j : Fin 4) (h : i ≠ j) :
    cartanMatrix i j = if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
      (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
      (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then -1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [cartanMatrix, dot, simpleRoot, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]

def reflect (i : Fin 4) (x : Ambient) : Ambient :=
  x - (dot x (simpleRoot i)) • simpleRoot i

theorem coordinateSum_reflect_mod (i : Fin 4) (x : Ambient) :
    coordinateSum (reflect i x) % 2 = coordinateSum x % 2 := by
  fin_cases i <;>
    simp [reflect, coordinateSum, dot, simpleRoot, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] <;> omega

theorem reflect_mem (i : Fin 4) (x : Lattice) :
    IsD4 (reflect i x.1) := by
  change coordinateSum (reflect i x.1) % 2 = 0
  rw [coordinateSum_reflect_mod]
  exact x.2

def reflect_lattice (i : Fin 4) : Lattice → Lattice := fun x =>
  ⟨reflect i x.1, reflect_mem i x⟩

theorem reflect_simpleRoot (i : Fin 4) :
    reflect i (simpleRoot i) = -simpleRoot i := by
  funext j
  fin_cases i <;> fin_cases j <;>
    norm_num [reflect, dot, simpleRoot, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]

end InfoGeometry.RootSystem.D4
