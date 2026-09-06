import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Module.End
import Mathlib.Tactic

/-! Operator skeleton of a Freudenthal--Kantor triple system. -/

noncomputable section
namespace InfoGeometry.Algebra.KantorTripleFiveGrading

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

structure KantorTripleSystem where
  triple : V → V → V → V
  triple_add_left : ∀ x₁ x₂ y z, triple (x₁ + x₂) y z = triple x₁ y z + triple x₂ y z
  triple_smul_left : ∀ (a : R) x y z, triple (a • x) y z = a • triple x y z
  triple_add_middle : ∀ x y₁ y₂ z, triple x (y₁ + y₂) z = triple x y₁ z + triple x y₂ z
  triple_smul_middle : ∀ (a : R) x y z, triple x (a • y) z = a • triple x y z
  triple_add_right : ∀ x y z₁ z₂, triple x y (z₁ + z₂) = triple x y z₁ + triple x y z₂
  triple_smul_right : ∀ (a : R) x y z, triple x y (a • z) = a • triple x y z
  first_identity : ∀ u v x y z,
    triple u v (triple x y z) - triple x y (triple u v z) =
      triple (triple u v x) y z - triple x (triple v u y) z
  second_identity : ∀ u v x y z,
    triple (triple u x v - triple v x u) z y -
        triple y z (triple u x v - triple v x u) =
      triple y x (triple u z v - triple v z u) +
        (triple u (triple x y z) v - triple v (triple x y z) u)

namespace KantorTripleSystem
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable (T : KantorTripleSystem R V)

def D (x y : V) : Module.End R V where
  toFun z := T.triple x y z
  map_add' z₁ z₂ := T.triple_add_right x y z₁ z₂
  map_smul' a z := T.triple_smul_right a x y z

@[simp] theorem D_apply (x y z : V) : T.D x y z = T.triple x y z := rfl

def K (x y : V) : Module.End R V where
  toFun z := T.triple x z y - T.triple y z x
  map_add' z₁ z₂ := by
    rw [T.triple_add_middle, T.triple_add_middle]
    abel
  map_smul' a z := by
    rw [T.triple_smul_middle, T.triple_smul_middle, smul_sub]
    rfl

@[simp] theorem K_apply (x y z : V) :
    T.K x y z = T.triple x z y - T.triple y z x := rfl

theorem K_skew (x y : V) : T.K x y = -T.K y x := by
  ext z
  simp [K_apply]

@[simp] theorem K_self (x : V) : T.K x x = 0 := by
  ext z
  simp [K_apply]

def endCommutator (A B : Module.End R V) : Module.End R V := A * B - B * A

@[simp] theorem endCommutator_apply (A B : Module.End R V) (z : V) :
    endCommutator A B z = A (B z) - B (A z) := rfl

theorem D_comm_D (u v x y : V) :
    endCommutator (T.D u v) (T.D x y) =
      T.D (T.D u v x) y - T.D x (T.D v u y) := by
  ext z
  change T.triple u v (T.triple x y z) - T.triple x y (T.triple u v z) =
    T.triple (T.triple u v x) y z - T.triple x (T.triple v u y) z
  exact T.first_identity u v x y z

theorem D_comm_D_apply (u v x y z : V) :
    endCommutator (T.D u v) (T.D x y) z =
      T.D (T.D u v x) y z - T.D x (T.D v u y) z :=
  LinearMap.congr_fun (T.D_comm_D u v x y) z

theorem K_K_eq_DK_add_KD (u v x y : V) :
    T.K (T.K u v x) y = T.D y x * T.K u v + T.K u v * T.D x y := by
  ext z
  change T.triple (T.triple u x v - T.triple v x u) z y -
      T.triple y z (T.triple u x v - T.triple v x u) =
    T.triple y x (T.triple u z v - T.triple v z u) +
      (T.triple u (T.triple x y z) v - T.triple v (T.triple x y z) u)
  exact T.second_identity u v x y z

theorem K_K_eq_DK_add_KD_apply (u v x y z : V) :
    T.K (T.K u v x) y z = T.D y x (T.K u v z) + T.K u v (T.D x y z) :=
  LinearMap.congr_fun (T.K_K_eq_DK_add_KD u v x y) z

def IsJordan : Prop := ∀ x y : V, T.K x y = 0

theorem isJordan_of_outerSymm (houter : ∀ x z y : V, T.triple x z y = T.triple y z x) :
    T.IsJordan := by
  intro x y
  ext z
  simp [K_apply, houter]

theorem not_isJordan_of_K_ne_zero {x y : V} (hK : T.K x y ≠ 0) : ¬ T.IsJordan := by
  intro hJ
  exact hK (hJ x y)

end KantorTripleSystem
end InfoGeometry.Algebra.KantorTripleFiveGrading
