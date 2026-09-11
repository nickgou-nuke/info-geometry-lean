import Mathlib.Data.Int.ModEq
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

instance : DecidableEq Ambient := inferInstanceAs (DecidableEq (Fin 4 → ℤ))

instance : AddCommGroup Ambient := inferInstanceAs (AddCommGroup (Fin 4 → ℤ))

instance : SMul ℤ Ambient := inferInstanceAs (SMul ℤ (Fin 4 → ℤ))

def coordinateSum (x : Ambient) : ℤ := ∑ i, x i

def IsD4 (x : Ambient) : Prop := coordinateSum x % 2 = 0

instance (x : Ambient) : Decidable (IsD4 x) := by
  unfold IsD4 coordinateSum
  infer_instance

theorem zero_mem_D4 : IsD4 (0 : Ambient) := by
  native_decide

theorem add_mem_D4 {x y : Ambient} (hx : IsD4 x) (hy : IsD4 y) :
    IsD4 (x + y) := by
  change coordinateSum (x + y) % 2 = 0
  rw [show coordinateSum (x + y) = coordinateSum x + coordinateSum y by
    simp only [coordinateSum, Fin.sum_univ_four]
    change (x 0 + y 0) + (x 1 + y 1) + (x 2 + y 2) + (x 3 + y 3) =
      (x 0 + x 1 + x 2 + x 3) + (y 0 + y 1 + y 2 + y 3)
    abel]
  rw [Int.add_emod, hx, hy]
  norm_num

theorem neg_mem_D4 {x : Ambient} (hx : IsD4 x) : IsD4 (-x) := by
  change coordinateSum (-x) % 2 = 0
  rw [show coordinateSum (-x) = -coordinateSum x by
    simp only [coordinateSum, Fin.sum_univ_four]
    change (-x 0) + (-x 1) + (-x 2) + (-x 3) =
      -(x 0 + x 1 + x 2 + x 3)
    abel]
  apply Int.emod_eq_zero_of_dvd
  exact (dvd_neg).2 (Int.dvd_of_emod_eq_zero hx)

def latticeSubgroup : AddSubgroup Ambient where
  carrier := IsD4
  zero_mem' := zero_mem_D4
  add_mem' := add_mem_D4
  neg_mem' := neg_mem_D4

abbrev Lattice := {x : Ambient // IsD4 x}

def basisVector (i : Fin 4) : Ambient := fun j => if i = j then 1 else 0

def dot (x y : Ambient) : ℤ := ∑ i, x i * y i

theorem dot_sub_left (x y z : Ambient) :
    dot (x - y) z = dot x z - dot y z := by
  unfold dot
  change (∑ i, (x i - y i) * z i) = _
  rw [show (fun i => (x i - y i) * z i) =
      (fun i => x i * z i - y i * z i) by
    funext i
    ring]
  rw [Finset.sum_sub_distrib]

theorem dot_sub_right (x y z : Ambient) :
    dot x (y - z) = dot x y - dot x z := by
  unfold dot
  change (∑ i, x i * (y i - z i)) = _
  rw [show (fun i => x i * (y i - z i)) =
      (fun i => x i * y i - x i * z i) by
    funext i
    ring]
  rw [Finset.sum_sub_distrib]

theorem dot_smul_left (a : ℤ) (x y : Ambient) :
    dot (a • x) y = a * dot x y := by
  unfold dot
  change (∑ i, (a * x i) * y i) = _
  rw [show (fun i => (a * x i) * y i) =
      (fun i => a * (x i * y i)) by
    funext i
    ring]
  rw [Finset.mul_sum]

theorem dot_smul_right (a : ℤ) (x y : Ambient) :
    dot x (a • y) = a * dot x y := by
  unfold dot
  change (∑ i, x i * (a * y i)) = _
  rw [show (fun i => x i * (a * y i)) =
      (fun i => a * (x i * y i)) by
    funext i
    ring]
  rw [Finset.mul_sum]

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

def ternaryCoordinate (a : Fin 3) : ℤ := a.1 - 1

def ternaryVector (a : Fin 4 → Fin 3) : Ambient :=
  fun i => ternaryCoordinate (a i)

def rootFinset : Finset Ambient :=
  (Finset.univ.image ternaryVector).filter (fun x => dot x x = 2 ∧ IsD4 x)

theorem rootFinset_card : rootFinset.card = 24 := by
  native_decide

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
  have hsum : coordinateSum (reflect i x) =
      coordinateSum x - dot x (simpleRoot i) * coordinateSum (simpleRoot i) := by
    unfold coordinateSum reflect
    change (∑ k, (x k - dot x (simpleRoot i) * simpleRoot i k)) = _
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsum, Int.sub_emod]
  have hroot : coordinateSum (simpleRoot i) % 2 = 0 := simpleRoot_mem i
  rw [Int.mul_emod, hroot]
  simp

theorem reflect_mem (i : Fin 4) (x : Lattice) :
    IsD4 (reflect i x.1) := by
  change coordinateSum (reflect i x.1) % 2 = 0
  rw [coordinateSum_reflect_mod]
  exact x.2

def reflect_lattice (i : Fin 4) : Lattice → Lattice := fun x =>
  ⟨reflect i x.1, reflect_mem i x⟩

theorem reflect_simpleRoot (i : Fin 4) :
    reflect i (simpleRoot i) = fun j => -simpleRoot i j := by
  unfold reflect
  rw [show dot (simpleRoot i) (simpleRoot i) = 2 by exact simpleRoot_norm i]
  funext j
  change simpleRoot i j - 2 * simpleRoot i j = -simpleRoot i j
  ring

theorem reflect_square (i : Fin 4) (x : Ambient) :
    reflect i (reflect i x) = x := by
  unfold reflect
  have hi : dot (simpleRoot i) (simpleRoot i) = 2 := simpleRoot_norm i
  rw [dot_sub_left, dot_smul_left, hi]
  funext j
  change x j - (dot x (simpleRoot i) * simpleRoot i j) -
      ((dot x (simpleRoot i) -
        dot x (simpleRoot i) * 2) * simpleRoot i j) = x j
  ring

theorem reflect_commute_of_cartan_zero
    (i j : Fin 4) (hij : cartanMatrix i j = 0) (x : Ambient) :
    reflect i (reflect j x) = reflect j (reflect i x) := by
  have hji : cartanMatrix j i = 0 := by
    simpa [cartanMatrix, dot, mul_comm] using hij
  have hij' : dot (simpleRoot i) (simpleRoot j) = 0 := hij
  have hji' : dot (simpleRoot j) (simpleRoot i) = 0 := hji
  unfold reflect
  rw [dot_sub_left, dot_smul_left, dot_sub_left, dot_smul_left,
    hji', hij']
  simp only [mul_zero, sub_zero]
  funext k
  change x k - dot x (simpleRoot j) * simpleRoot j k -
      dot x (simpleRoot i) * simpleRoot i k =
    x k - dot x (simpleRoot i) * simpleRoot i k -
      dot x (simpleRoot j) * simpleRoot j k
  ring

theorem reflect_braid_of_cartan_neg_one
    (i j : Fin 4) (hij : cartanMatrix i j = -1) (x : Ambient) :
    reflect i (reflect j (reflect i x)) =
      reflect j (reflect i (reflect j x)) := by
  have hji : cartanMatrix j i = -1 := by
    simpa [cartanMatrix, dot, mul_comm] using hij
  have hii : dot (simpleRoot i) (simpleRoot i) = 2 := simpleRoot_norm i
  have hjj : dot (simpleRoot j) (simpleRoot j) = 2 := simpleRoot_norm j
  have hij' : dot (simpleRoot i) (simpleRoot j) = -1 := hij
  have hji' : dot (simpleRoot j) (simpleRoot i) = -1 := hji
  unfold reflect
  repeat rw [dot_sub_left, dot_smul_left]
  rw [hii, hjj, hij', hji']
  module

theorem reflect_lattice_square (i : Fin 4) (x : Lattice) :
    reflect_lattice i (reflect_lattice i x) = x := by
  apply Subtype.ext
  exact reflect_square i x.1

theorem reflect_lattice_commute_of_cartan_zero
    (i j : Fin 4) (hij : cartanMatrix i j = 0) (x : Lattice) :
    reflect_lattice i (reflect_lattice j x) =
      reflect_lattice j (reflect_lattice i x) := by
  apply Subtype.ext
  exact reflect_commute_of_cartan_zero i j hij x.1

theorem reflect_lattice_braid_of_cartan_neg_one
    (i j : Fin 4) (hij : cartanMatrix i j = -1) (x : Lattice) :
    reflect_lattice i (reflect_lattice j (reflect_lattice i x)) =
      reflect_lattice j (reflect_lattice i (reflect_lattice j x)) := by
  apply Subtype.ext
  exact reflect_braid_of_cartan_neg_one i j hij x.1

end InfoGeometry.RootSystem.D4
