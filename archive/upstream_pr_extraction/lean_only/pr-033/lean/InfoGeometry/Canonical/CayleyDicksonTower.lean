#exit
import InfoGeometry.Canonical.CayleyDicksonEmbedding

namespace InfoGeometry.Canonical

open AlbertCayleyDickson
open AlbertStep

variable {F A : Type*} [CommRing F] [NonAssocRing A] [Module F A] [SMulCommClass F A A] [IsScalarTower F A A] [StarRing A] {γ : F}

instance : AddCommGroup (AlbertStep F A γ) where
  add := (· + ·)
  add_assoc := by intros a b c; ext <;> simp [add_assoc]
  zero := 0
  zero_add := by intros a; ext <;> simp
  add_zero := by intros a; ext <;> simp
  add_comm := by intros a b; ext <;> simp [add_comm]
  neg := (-·)
  sub x y := x + -y
  sub_eq_add_neg := by intros a b; rfl
  zsmul n x := ⟨n • x.p, n • x.q⟩
  zsmul_zero' := by intros a; ext <;> simp
  zsmul_succ' := by intros n a; ext <;> simp [add_smul, add_comm]
  zsmul_neg' := by intros n a; ext <;> simp [add_smul]
  nsmul n x := ⟨n • x.p, n • x.q⟩
  nsmul_zero := by intros a; ext <;> simp
  nsmul_succ := by intros n a; ext <;> simp [add_smul, add_comm]

instance : Module F (AlbertStep F A γ) where
  smul := (· • ·)
  one_smul := by intros a; ext <;> simp
  mul_smul := by intros x y a; ext <;> simp [mul_smul]
  smul_zero := by intros x; ext <;> simp
  smul_add := by intros x a b; ext <;> simp [smul_add]
  add_smul := by intros x y a; ext <;> simp [add_smul]
  zero_smul := by intros a; ext <;> simp

end InfoGeometry.Canonical
