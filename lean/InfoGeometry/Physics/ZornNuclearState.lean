import Mathlib.Tactic

namespace InfoGeometry.Physics

/-- Rational Zorn split norm (determinant). -/
@[ext]
structure RationalZornMatrix where
  a : ℚ
  x : Fin 3 → ℚ
  y : Fin 3 → ℚ
  b : ℚ

def RationalZornMatrix.det (Z : RationalZornMatrix) : ℚ :=
  Z.a * Z.b - ∑ i : Fin 3, Z.x i * Z.y i

def RationalZornMatrix.vacuumPos : RationalZornMatrix := { a := 1, b := 0, x := fun _ => 0, y := fun _ => 0 }
def RationalZornMatrix.vacuumNeg : RationalZornMatrix := { a := 0, b := 1, x := fun _ => 0, y := fun _ => 0 }

def RationalZornMatrix.quarkState (i : Fin 3) : RationalZornMatrix :=
  { a := 0, b := 0, x := fun j => if i = j then 1 else 0, y := fun _ => 0 }

def RationalZornMatrix.antiquarkState (i : Fin 3) : RationalZornMatrix :=
  { a := 0, b := 0, x := fun _ => 0, y := fun j => if i = j then 1 else 0 }

instance : Add RationalZornMatrix where
  add Z1 Z2 := { a := Z1.a + Z2.a, b := Z1.b + Z2.b, x := fun i => Z1.x i + Z2.x i, y := fun i => Z1.y i + Z2.y i }

@[simp] lemma add_a (Z1 Z2 : RationalZornMatrix) : (Z1 + Z2).a = Z1.a + Z2.a := rfl
@[simp] lemma add_b (Z1 Z2 : RationalZornMatrix) : (Z1 + Z2).b = Z1.b + Z2.b := rfl
@[simp] lemma add_x (Z1 Z2 : RationalZornMatrix) (i : Fin 3) : (Z1 + Z2).x i = Z1.x i + Z2.x i := rfl
@[simp] lemma add_y (Z1 Z2 : RationalZornMatrix) (i : Fin 3) : (Z1 + Z2).y i = Z1.y i + Z2.y i := rfl

lemma det_vacuum_1 : (RationalZornMatrix.vacuumPos).det = 0 := by simp [RationalZornMatrix.det, RationalZornMatrix.vacuumPos]
lemma det_vacuum_2 : (RationalZornMatrix.vacuumNeg).det = 0 := by simp [RationalZornMatrix.det, RationalZornMatrix.vacuumNeg]

lemma det_quark (i : Fin 3) : (RationalZornMatrix.quarkState i).det = 0 := by
  simp [RationalZornMatrix.det, RationalZornMatrix.quarkState]

lemma det_antiquark (i : Fin 3) : (RationalZornMatrix.antiquarkState i).det = 0 := by
  simp [RationalZornMatrix.det, RationalZornMatrix.antiquarkState]

lemma det_vacuum_combo (c₁ c₂ : ℚ) :
  ({ a := c₁, b := c₂, x := fun _ => 0, y := fun _ => 0 } : RationalZornMatrix).det = c₁ * c₂ := by
  simp [RationalZornMatrix.det]

lemma sum_ite_eq {α : Type} [AddCommMonoid α] (i : Fin 3) (f : Fin 3 → α) :
  (∑ j : Fin 3, if i = j then f j else 0) = f i := by
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

lemma det_quark_add_antiquark (i : Fin 3) :
  (RationalZornMatrix.quarkState i + RationalZornMatrix.antiquarkState i).det = -1 := by
  have H_add : RationalZornMatrix.quarkState i + RationalZornMatrix.antiquarkState i =
    { a := 0, b := 0, x := fun j => if i = j then (1 : ℚ) else 0, y := fun j => if i = j then (1 : ℚ) else 0 } := by
    ext
    · simp [RationalZornMatrix.quarkState, RationalZornMatrix.antiquarkState]
    · simp [RationalZornMatrix.quarkState, RationalZornMatrix.antiquarkState]
    · simp [RationalZornMatrix.quarkState, RationalZornMatrix.antiquarkState]
    · simp [RationalZornMatrix.quarkState, RationalZornMatrix.antiquarkState]
  rw [H_add]
  dsimp [RationalZornMatrix.det]
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
