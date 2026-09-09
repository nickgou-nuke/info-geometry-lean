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

theorem zmod6_val_natCast_of_val (k : ZMod 6) :
    ((k.val : ZMod 6).val) = k.val := by
  exact ZMod.val_natCast_of_lt k.isLt

theorem zmod6_canonical_subtraction (k l : ZMod 6) :
    (((((6 - k.val) % 6 + l.val) % 6 : ℕ) : ZMod 6)) = l - k := by
  rw [ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_mod]
  have hk : k.val ≤ 6 := Nat.le_of_lt k.isLt
  rw [Nat.cast_sub hk]
  rw [ZMod.natCast_zmod_val]
  simp only [ZMod.natCast_self, zero_sub]
  norm_num
  ring_nf

def mixedIndex (k l : ZMod 6) : Fin 6 :=
  ⟨((6 - k.val) % 6 + l.val) % 6, Nat.mod_lt _ (by norm_num)⟩

theorem mixedIndex_val_sub (k l : ZMod 6) :
    (mixedIndex k l).val = (l - k).val := by
  simpa [mixedIndex, ZMod.val_add, ZMod.val_natCast] using congrArg ZMod.val
    (zmod6_canonical_subtraction k l)

theorem weylNF_val (p : ZMod 6) (b : Bool) :
    weylNF p.val b = weylNF p b := by
  simp [weylNF]

theorem weylNF_mul_rot_refl_canonical (k l : ZMod 6) :
    weylNF k false * weylNF l true = weylNF (mixedIndex k l).val true := by
  let i : Fin 6 := ⟨k.val, k.isLt⟩
  let j : Fin 6 := ⟨l.val, l.isLt⟩
  let n : Fin 6 := ⟨((6 - (i : ℕ)) % 6 + (j : ℕ)) % 6,
    Nat.mod_lt _ (by norm_num)⟩
  change weylNF k false * weylNF l true = weylNF (mixedIndex k l).val true
  simp [weylNF, ZMod.val_natCast]
  simpa [mixedIndex, n, i, j] using c_pow_mul_s_mul_c_pow i j

theorem weylNF_mul_refl_refl_canonical (k l : ZMod 6) :
    weylNF k true * weylNF l true = weylNF (mixedIndex k l).val false := by
  let i : Fin 6 := ⟨k.val, k.isLt⟩
  let j : Fin 6 := ⟨l.val, l.isLt⟩
  let n : Fin 6 := ⟨((6 - (i : ℕ)) % 6 + (j : ℕ)) % 6,
    Nat.mod_lt _ (by norm_num)⟩
  change weylNF k true * weylNF l true = weylNF (mixedIndex k l).val false
  simp [weylNF, ZMod.val_natCast]
  simpa [mixedIndex, n, i, j] using s_mul_c_pow_mul_s_mul_c_pow i j

theorem weylNF_mul_rot_refl_exact (k l : ZMod 6) :
    weylNF k false * weylNF l true = weylNF (l - k) true := by
  rw [weylNF_mul_rot_refl_canonical, mixedIndex_val_sub, weylNF_val]

theorem weylNF_mul_refl_refl_exact (k l : ZMod 6) :
    weylNF k true * weylNF l true = weylNF (l - k) false := by
  rw [weylNF_mul_refl_refl_canonical, mixedIndex_val_sub, weylNF_val]

/-! The transported normal-form product is the inversion semidirect law on
    `ZMod 6 × Bool`.  We keep this as an explicit operation rather than
    installing a conflicting global group instance on the product alias. -/

def weylSemidirectMul : WeylG2 → WeylG2 → WeylG2
  | (k, false), (l, false) => (k + l, false)
  | (k, false), (l, true) => (l - k, true)
  | (k, true), (l, false) => (k + l, true)
  | (k, true), (l, true) => (l - k, false)

theorem dihedralParameterMap_mul (g h : DihedralGroup 6) :
    dihedralParameterMap (g * h) =
      weylSemidirectMul (dihedralParameterMap g) (dihedralParameterMap h) := by
  cases g <;> cases h <;> rfl

theorem weylMul_eq_weylSemidirectMul (p q : WeylG2) :
    weylMul p q = weylSemidirectMul p q := by
  rcases p with ⟨k, b⟩
  rcases q with ⟨l, d⟩
  cases b <;> cases d
  · apply weylNF_injective
    simpa [weylSemidirectMul] using
      (weylNF_weylMul (k, false) (l, false)).trans
        (weylNF_mul_rot_rot k l)
  · apply weylNF_injective
    simpa [weylSemidirectMul] using
      (weylNF_weylMul (k, false) (l, true)).trans
        (weylNF_mul_rot_refl_exact k l)
  · apply weylNF_injective
    simpa [weylSemidirectMul] using
      (weylNF_weylMul (k, true) (l, false)).trans
        (weylNF_mul_refl_rot k l)
  · apply weylNF_injective
    simpa [weylSemidirectMul] using
        (weylNF_weylMul (k, true) (l, true)).trans
        (weylNF_mul_refl_refl_exact k l)

theorem dihedralParameterMap_mul_weylMul (g h : DihedralGroup 6) :
    dihedralParameterMap (g * h) =
      weylMul (dihedralParameterMap g) (dihedralParameterMap h) := by
  rw [dihedralParameterMap_mul, weylMul_eq_weylSemidirectMul]

theorem weylSemidirectMul_assoc (p q r : WeylG2) :
    weylSemidirectMul (weylSemidirectMul p q) r =
      weylSemidirectMul p (weylSemidirectMul q r) := by
  rw [← weylMul_eq_weylSemidirectMul, ← weylMul_eq_weylSemidirectMul,
    ← weylMul_eq_weylSemidirectMul, ← weylMul_eq_weylSemidirectMul]
  exact weylMul_assoc p q r

theorem weylSemidirectMul_one_left (p : WeylG2) :
    weylSemidirectMul (0, false) p = p := by
  rw [← weylMul_eq_weylSemidirectMul]
  exact weyl_one_mul p

theorem weylSemidirectMul_one_right (p : WeylG2) :
    weylSemidirectMul p (0, false) = p := by
  rw [← weylMul_eq_weylSemidirectMul]
  exact weyl_mul_one p

theorem weylSemidirectMul_inv_left (p : WeylG2) :
    weylSemidirectMul (weylInv p) p = (0, false) := by
  rw [← weylMul_eq_weylSemidirectMul]
  exact weylInv_mul_self p

theorem weylSemidirectMul_inv_right (p : WeylG2) :
    weylSemidirectMul p (weylInv p) = (0, false) := by
  rw [← weylMul_eq_weylSemidirectMul]
  exact weyl_mul_inv_self p

noncomputable def dihedralWeylHom : DihedralGroup 6 →* weylG2Subgroup where
  toFun := dihedralWeylSubgroupEquiv
  map_one' := by
    rw [DihedralGroup.one_def]
    rfl
  map_mul' := by
    intro a b
    cases a <;> cases b
    · rw [DihedralGroup.r_mul_r]
      apply Subtype.ext
      dsimp [dihedralWeylSubgroupEquiv, dihedralParameterEquiv,
        dihedralParameterMap, weylG2ParameterEquiv, weylG2ParameterMap]
      exact (weylNF_mul_rot_rot _ _).symm
    · rw [DihedralGroup.r_mul_sr]
      apply Subtype.ext
      dsimp [dihedralWeylSubgroupEquiv, dihedralParameterEquiv,
        dihedralParameterMap, weylG2ParameterEquiv, weylG2ParameterMap]
      exact (weylNF_mul_rot_refl_exact _ _).symm
    · rw [DihedralGroup.sr_mul_r]
      apply Subtype.ext
      dsimp [dihedralWeylSubgroupEquiv, dihedralParameterEquiv,
        dihedralParameterMap, weylG2ParameterEquiv, weylG2ParameterMap]
      exact (weylNF_mul_refl_rot _ _).symm
    · rw [DihedralGroup.sr_mul_sr]
      apply Subtype.ext
      dsimp [dihedralWeylSubgroupEquiv, dihedralParameterEquiv,
        dihedralParameterMap, weylG2ParameterEquiv, weylG2ParameterMap]
      exact (weylNF_mul_refl_refl_exact _ _).symm

theorem dihedralWeylHom_injective : Function.Injective dihedralWeylHom := by
  intro a b h
  exact dihedralWeylSubgroupEquiv.injective h

noncomputable def dihedralWeylMulEquiv : DihedralGroup 6 ≃* weylG2Subgroup :=
  MulEquiv.ofBijective dihedralWeylHom
    ⟨dihedralWeylHom_injective, dihedralWeylSubgroupEquiv.surjective⟩

end InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
