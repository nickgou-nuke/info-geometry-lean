import Mathlib

namespace InfoGeometry.Physics

/-- Zorn split norm (determinant). -/
@[ext]
structure ZornMatrix where
  a : ℚ
  x : Fin 3 → ℚ
  y : Fin 3 → ℚ
  b : ℚ

def ZornMatrix.det (Z : ZornMatrix) : ℚ :=
  Z.a * Z.b - ∑ i : Fin 3, Z.x i * Z.y i

def ZornMatrix.vacuumPos : ZornMatrix := { a := 1, b := 0, x := fun _ => 0, y := fun _ => 0 }
def ZornMatrix.vacuumNeg : ZornMatrix := { a := 0, b := 1, x := fun _ => 0, y := fun _ => 0 }

def ZornMatrix.quarkState (i : Fin 3) : ZornMatrix :=
  { a := 0, b := 0, x := fun j => if i = j then 1 else 0, y := fun _ => 0 }

def ZornMatrix.antiquarkState (i : Fin 3) : ZornMatrix :=
  { a := 0, b := 0, x := fun _ => 0, y := fun j => if i = j then 1 else 0 }

instance : Add ZornMatrix where
  add Z1 Z2 := { a := Z1.a + Z2.a, b := Z1.b + Z2.b, x := fun i => Z1.x i + Z2.x i, y := fun i => Z1.y i + Z2.y i }

@[simp] lemma add_a (Z1 Z2 : ZornMatrix) : (Z1 + Z2).a = Z1.a + Z2.a := rfl
@[simp] lemma add_b (Z1 Z2 : ZornMatrix) : (Z1 + Z2).b = Z1.b + Z2.b := rfl
@[simp] lemma add_x (Z1 Z2 : ZornMatrix) (i : Fin 3) : (Z1 + Z2).x i = Z1.x i + Z2.x i := rfl
@[simp] lemma add_y (Z1 Z2 : ZornMatrix) (i : Fin 3) : (Z1 + Z2).y i = Z1.y i + Z2.y i := rfl

lemma det_vacuum_1 : (ZornMatrix.vacuumPos).det = 0 := by simp [ZornMatrix.det, ZornMatrix.vacuumPos]
lemma det_vacuum_2 : (ZornMatrix.vacuumNeg).det = 0 := by simp [ZornMatrix.det, ZornMatrix.vacuumNeg]

lemma det_quark (i : Fin 3) : (ZornMatrix.quarkState i).det = 0 := by
  simp [ZornMatrix.det, ZornMatrix.quarkState]

lemma det_antiquark (i : Fin 3) : (ZornMatrix.antiquarkState i).det = 0 := by
  simp [ZornMatrix.det, ZornMatrix.antiquarkState]

lemma det_vacuum_combo (c₁ c₂ : ℚ) : 
  ({ a := c₁, b := c₂, x := fun _ => 0, y := fun _ => 0 } : ZornMatrix).det = c₁ * c₂ := by
  simp [ZornMatrix.det]

lemma sum_ite_eq {α : Type} [AddCommMonoid α] (i : Fin 3) (f : Fin 3 → α) :
  (∑ j : Fin 3, if i = j then f j else 0) = f i := by
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

lemma det_quark_add_antiquark (i : Fin 3) : 
  (ZornMatrix.quarkState i + ZornMatrix.antiquarkState i).det = -1 := by
  have H_add : ZornMatrix.quarkState i + ZornMatrix.antiquarkState i = 
    { a := 0, b := 0, x := fun j => if i = j then (1 : ℚ) else 0, y := fun j => if i = j then (1 : ℚ) else 0 } := by
    ext
    · simp [ZornMatrix.quarkState, ZornMatrix.antiquarkState]
    · simp [ZornMatrix.quarkState, ZornMatrix.antiquarkState]
    · simp [ZornMatrix.quarkState, ZornMatrix.antiquarkState]
    · simp [ZornMatrix.quarkState, ZornMatrix.antiquarkState]
  rw [H_add]
  dsimp [ZornMatrix.det]
  have h : (∑ j : Fin 3, (if i = j then (1 : ℚ) else 0) * (if i = j then 1 else 0)) = 1 := by
    calc (∑ j : Fin 3, (if i = j then (1 : ℚ) else 0) * (if i = j then 1 else 0))
      _ = ∑ j : Fin 3, if i = j then (1 : ℚ) * 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> simp
      _ = ∑ j : Fin 3, if i = j then (1 : ℚ) else 0 := by simp
      _ = 1 := by rw [sum_ite_eq]
  rw [h]
  norm_num

end InfoGeometry.Physics