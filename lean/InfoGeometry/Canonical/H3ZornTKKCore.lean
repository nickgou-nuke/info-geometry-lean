import Mathlib

noncomputable section
namespace InfoGeometry.Canonical.H3ZornTKKCore

class JordanTriple (V : Type*) [AddCommGroup V] [Module ℝ V] where
  triple : V → V → V → V
  triple_add_left : ∀ x₁ x₂ y z, triple (x₁ + x₂) y z = triple x₁ y z + triple x₂ y z
  triple_smul_left : ∀ (r : ℝ) x y z, triple (r • x) y z = r • triple x y z
  triple_add_mid : ∀ x y₁ y₂ z, triple x (y₁ + y₂) z = triple x y₁ z + triple x y₂ z
  triple_smul_mid : ∀ (r : ℝ) x y z, triple x (r • y) z = r • triple x y z
  triple_add_right : ∀ x y z₁ z₂, triple x y (z₁ + z₂) = triple x y z₁ + triple x y z₂
  triple_smul_right : ∀ (r : ℝ) x y z, triple x y (r • z) = r • triple x y z
  outer_symm : ∀ x y z, triple x y z = triple z y x
  fundamental_id : ∀ x y u v z, triple x y (triple u v z) - triple u v (triple x y z) = triple (triple x y u) v z - triple u (triple y x v) z

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [JordanTriple V]
open JordanTriple

def tripleLeft (x y : V) : Module.End ℝ V where
  toFun z := triple x y z
  map_add' := triple_add_right x y
  map_smul' := fun r z => triple_smul_right r x y z

@[simp] theorem tripleLeft_apply (x y z : V) : tripleLeft x y z = triple x y z := rfl

def innerDeriv (x y : V) : Module.End ℝ V := tripleLeft x y - tripleLeft y x

@[simp] theorem innerDeriv_apply (x y z : V) : innerDeriv x y z = triple x y z - triple y x z := rfl

theorem innerDeriv_skew (x y : V) : innerDeriv y x = - innerDeriv x y := by
  ext z
  simp only [innerDeriv_apply, LinearMap.neg_apply]
  abel

theorem innerDeriv_self (x : V) : innerDeriv x x = 0 := by
  ext z
  simp only [innerDeriv_apply, LinearMap.zero_apply, sub_self]

def kantorOperator (x y : V) : Module.End ℝ V where
  toFun z := triple x z y - triple y z x
  map_add' z₁ z₂ := by rw [triple_add_mid, triple_add_mid]; abel
  map_smul' r z := by rw [triple_smul_mid, triple_smul_mid, smul_sub]; rfl

theorem kantorOperator_zero (x y : V) (h_outer : ∀ a b c : V, triple a b c = triple c b a) :
    kantorOperator x y = 0 := by
  ext z
  change triple x z y - triple y z x = 0
  rw [h_outer x z y, h_outer y z x]
  simp

def commEnd (A B : Module.End ℝ V) : Module.End ℝ V := A * B - B * A

@[simp] theorem commEnd_apply (A B : Module.End ℝ V) (z : V) : commEnd A B z = A (B z) - B (A z) := rfl

theorem fundamental_operator_identity (x y u v : V) :
    commEnd (tripleLeft x y) (tripleLeft u v) = tripleLeft (triple x y u) v - tripleLeft u (triple y x v) := by
  ext z
  simp only [commEnd_apply, tripleLeft_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  exact fundamental_id x y u v z

end InfoGeometry.Canonical.H3ZornTKKCore
