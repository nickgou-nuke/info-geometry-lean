import InfoGeometry.Algebra.Zorn.G2WeylGroupEquiv
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The abstract dihedral and concrete finite Weyl carriers

The parameter type is only a normal-form carrier.  This file identifies it
with `DihedralGroup 6` and then with the concrete Weyl subgroup, without
overloading the inherited operations on the parameter alias.
-/

namespace InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2

open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open DihedralGroup

def dihedralParameterMap : DihedralGroup 6 → WeylG2
  | .r k => (k, false)
  | .sr k => (k, true)

noncomputable def dihedralParameterEquiv : DihedralGroup 6 ≃ WeylG2 where
  toFun := dihedralParameterMap
  invFun := fun p => if p.2 then .sr p.1 else .r p.1
  left_inv := by
    intro g
    cases g <;> rfl
  right_inv := by
    intro p
    cases p with
    | mk k b => cases b <;> rfl

@[simp] theorem dihedralParameterEquiv_apply (g : DihedralGroup 6) :
    dihedralParameterEquiv g = dihedralParameterMap g :=
  rfl

noncomputable def dihedralWeylSubgroupEquiv :
    DihedralGroup 6 ≃ weylG2Subgroup :=
  dihedralParameterEquiv.trans weylG2ParameterEquiv

@[simp] theorem dihedralWeylSubgroupEquiv_apply (g : DihedralGroup 6) :
    (dihedralWeylSubgroupEquiv g).val =
      weylNF (dihedralParameterMap g).1 (dihedralParameterMap g).2 :=
  rfl

theorem dihedralWeylSubgroupEquiv_card :
    Fintype.card (DihedralGroup 6) = Fintype.card weylG2Subgroup := by
  exact Fintype.card_congr dihedralWeylSubgroupEquiv

theorem weylNF_mul_rot_refl_canonical (k l : ZMod 6) :
    ∃ n : Fin 6, weylNF k false * weylNF l true = weylNF n.val true := by
  let i : Fin 6 := ⟨k.val, k.isLt⟩
  let j : Fin 6 := ⟨l.val, l.isLt⟩
  let n : Fin 6 := ⟨((6 - (i : ℕ)) % 6 + (j : ℕ)) % 6,
    Nat.mod_lt _ (by norm_num)⟩
  refine ⟨n, ?_⟩
  simp [weylNF, ZMod.val_natCast]
  simpa [n, i, j] using c_pow_mul_s_mul_c_pow i j

theorem weylNF_mul_refl_refl_canonical (k l : ZMod 6) :
    ∃ n : Fin 6, weylNF k true * weylNF l true = weylNF n.val false := by
  let i : Fin 6 := ⟨k.val, k.isLt⟩
  let j : Fin 6 := ⟨l.val, l.isLt⟩
  let n : Fin 6 := ⟨((6 - (i : ℕ)) % 6 + (j : ℕ)) % 6,
    Nat.mod_lt _ (by norm_num)⟩
  refine ⟨n, ?_⟩
  simp [weylNF, ZMod.val_natCast]
  simpa [n, i, j] using s_mul_c_pow_mul_s_mul_c_pow i j

end InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
