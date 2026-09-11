/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Algebra.Group.TransferInstance
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.TransferInstance
import InfoGeometry.External.Virasoro.LieCohomologySmallDegree

namespace VirasoroProject

universe u
variable (𝕜 : Type*) [CommRing 𝕜]
variable (𝓰 𝓪 : Type u) [LieRing 𝓰] [AddCommGroup 𝓪] [LieAlgebra 𝕜 𝓰] [Module 𝕜 𝓪]

variable {𝕜 𝓰 𝓪}

section LieTwoCocycle.CentralExtension

namespace LieTwoCocycle

set_option linter.unusedVariables false in
@[ext]
structure CentralExtension (γ : LieTwoCocycle 𝕜 𝓰 𝓪) where
  fst : 𝓰
  snd : 𝓪

variable {γ : LieTwoCocycle 𝕜 𝓰 𝓪}

namespace CentralExtension

def coeProd (Z : γ.CentralExtension) : 𝓰 × 𝓪 :=
  (Z.fst, Z.snd)

def equivProd : γ.CentralExtension ≃ 𝓰 × 𝓪 where
  toFun := coeProd
  invFun := fun Z ↦ ⟨Z.1, Z.2⟩
  left_inv := by
    intro Z
    ext <;> rfl
  right_inv := by
    intro Z
    cases Z
    rfl

instance : AddCommGroup (γ.CentralExtension) :=
  (equivProd (γ := γ)).addCommGroup

instance : Module 𝕜 (γ.CentralExtension) :=
  (equivProd (γ := γ)).module 𝕜

@[simp] lemma coeProd_apply (Z : γ.CentralExtension) :
    coeProd Z = (Z.fst, Z.snd) :=
  rfl

lemma add_def (Z₁ Z₂ : γ.CentralExtension) :
    Z₁ + Z₂ = ⟨Z₁.fst + Z₂.fst, Z₁.snd + Z₂.snd⟩ := by
  change (equivProd (γ := γ)).symm (equivProd Z₁ + equivProd Z₂) = _
  rfl

lemma smul_def (c : 𝕜) (Z : γ.CentralExtension) :
    c • Z = ⟨c • Z.fst, c • Z.snd⟩ := by
  change (equivProd (γ := γ)).symm (c • equivProd Z) = _
  rfl

@[simp] lemma zero_fst :
    (0 : γ.CentralExtension).fst = 0 :=
  rfl

@[simp] lemma zero_snd :
    (0 : γ.CentralExtension).snd = 0 :=
  rfl

@[simp] lemma add_fst (Z W : γ.CentralExtension) :
    (Z + W).fst = Z.fst + W.fst := by
  rw [add_def]

@[simp] lemma add_snd (Z W : γ.CentralExtension) :
    (Z + W).snd = Z.snd + W.snd := by
  rw [add_def]

@[simp] lemma smul_fst (c : 𝕜) (Z : γ.CentralExtension) :
    (c • Z).fst = c • Z.fst := by
  rw [smul_def]

@[simp] lemma smul_snd (c : 𝕜) (Z : γ.CentralExtension) :
    (c • Z).snd = c • Z.snd := by
  rw [smul_def]

end CentralExtension

variable (γ)

open LinearMapClass RingHom in
/-- The Lie bracket in a central extension defined by a Lie algebra 2-cocycle. -/
def bracket : γ.CentralExtension
      →ₗ[𝕜] γ.CentralExtension →ₗ[𝕜] γ.CentralExtension where
  toFun := fun Z ↦ {
    toFun := fun W ↦ ⟨⁅Z.fst, W.fst⁆, γ Z.fst W.fst⟩
    map_add' := by
      intros
      ext <;> simp [lie_add, map_add]
    map_smul' := by
      intros
      ext <;> simp [lie_smul, map_smul] }
  map_add' := by
    intros
    ext <;> simp [add_lie, map_add, LinearMap.add_apply]
  map_smul' := by
    intros
    ext <;> simp [smul_lie, map_smul, LinearMap.smul_apply, id_apply]


@[simp] lemma bracket_apply (Z W : γ.CentralExtension) :
    γ.bracket Z W = ⟨⁅Z.fst, W.fst⁆, γ Z.fst W.fst⟩ :=
  rfl

lemma bracket_self (Z : γ.CentralExtension) :
    γ.bracket Z Z = 0 := by
  ext <;> simp [bracket_apply]

lemma bracket_smul (c : 𝕜) (Z W : γ.CentralExtension) :
    γ.bracket Z (c • W) = c • γ.bracket Z W := by
  simp only [LinearMapClass.map_smul, LieTwoCocycle.bracket_apply]

lemma bracket_leibniz (Z W₁ W₂ : γ.CentralExtension) :
    γ.bracket Z (γ.bracket W₁ W₂)
      = γ.bracket (γ.bracket Z W₁) W₂ + γ.bracket W₁ (γ.bracket Z W₂) := by
  simp only [γ.bracket_apply]
  ext
  · exact leibniz_lie Z.fst W₁.fst W₂.fst
  · apply γ.leibniz

namespace CentralExtension

instance : LieRing γ.CentralExtension where
  bracket Z W := γ.bracket Z W
  add_lie Z₁ Z₂ W := by
    ext <;> simp [LieTwoCocycle.bracket_apply]
  lie_add Z W₁ W₂ := by
    ext <;> simp [LieTwoCocycle.bracket_apply]
  lie_self := γ.bracket_self
  leibniz_lie Z₁ Z₂ W := γ.bracket_leibniz Z₁ Z₂ W

instance : LieAlgebra 𝕜 γ.CentralExtension where
  lie_smul := γ.bracket_smul

lemma lie_def (Z W : γ.CentralExtension) :
    ⁅Z, W⁆ = ⟨⁅Z.fst, W.fst⁆, γ Z.fst W.fst⟩ :=
  rfl

@[simp] lemma lie_fst (Z W : γ.CentralExtension) :
    ⁅Z, W⁆.fst = ⁅Z.fst, W.fst⁆ :=
  rfl

@[simp] lemma lie_snd (Z W : γ.CentralExtension) :
    ⁅Z, W⁆.snd = γ Z.fst W.fst :=
  rfl

end CentralExtension

end LieTwoCocycle

variable (β : LieOneCochain 𝕜 𝓰 𝓪)
variable (γ)

def LieOneCochain.bdryHom :
    γ.CentralExtension →ₗ⁅𝕜⁆ (γ + β.bdry).CentralExtension where
  toFun := fun Z ↦ ⟨Z.fst, Z.snd + β Z.fst⟩
  map_add' Z W := by
    ext
    · rfl
    · calc
        Z.snd + W.snd + β (Z.fst + W.fst)
            = Z.snd + β Z.fst + (W.snd + β W.fst) := by
                simp only [map_add]
                ac_rfl
        _   = (⟨Z.fst, Z.snd + β Z.fst⟩
                + ⟨W.fst, W.snd + β W.fst⟩ :
                (γ + β.bdry).CentralExtension).snd := by
                rfl
  map_smul' c Z := by
    ext
    · rfl
    · calc
        (c • Z).snd + β (c • Z).fst
            = c • Z.snd + β (c • Z.fst) := by
                rfl
        _   = c • (Z.snd + β Z.fst) := by
                simp only [LinearMapClass.map_smul, smul_add]
        _   = (c • (⟨Z.fst, Z.snd + β Z.fst⟩ :
                (γ + β.bdry).CentralExtension)).snd := by
                rfl
  map_lie' := by
    intro Z W
    ext <;> rfl

namespace LieTwoCocycle.CentralExtension

def congr {γ₁ γ₂ : LieTwoCocycle 𝕜 𝓰 𝓪} (h : γ₁ = γ₂) :
    γ₁.CentralExtension ≃ₗ⁅𝕜⁆ γ₂.CentralExtension where
  toFun := fun Z ↦ ⟨Z.fst, Z.snd⟩
  map_add' Z₁ Z₂ := rfl
  map_smul' c Z := rfl
  map_lie' := by
    intro Z₁ Z₂
    ext <;> simp only [lie_def, h]
  invFun := fun Z ↦ ⟨Z.fst, Z.snd⟩
  left_inv := by
    intro Z
    ext <;> rfl
  right_inv := by
    intro Z
    ext <;> rfl

lemma congr_apply {γ₁ γ₂ : LieTwoCocycle 𝕜 𝓰 𝓪} (h : γ₁ = γ₂)
    (Z : γ₁.CentralExtension) :
    congr h Z = ⟨Z.fst, Z.snd⟩ :=
  rfl

@[simp] lemma congr_trans {γ₁ γ₂ γ₃ : LieTwoCocycle 𝕜 𝓰 𝓪}
    (h₁₂ : γ₁ = γ₂) (h₂₃ : γ₂ = γ₃) :
    (congr h₁₂).trans (congr h₂₃) = congr (h₁₂.trans h₂₃) := by
  ext Z <;> rfl

lemma congr_congr_symm {γ₁ γ₂ : LieTwoCocycle 𝕜 𝓰 𝓪} (h : γ₁ = γ₂) :
    (congr h).trans (congr h.symm) = LieEquiv.refl := by
  ext Z <;> rfl

lemma hom_of_coboundary_refl (γ : LieTwoCocycle 𝕜 𝓰 𝓪) :
    congr (Eq.refl γ) = LieEquiv.refl (R := 𝕜) (L₁ := γ.CentralExtension) := by
  ext Z <;> rfl

lemma hom_of_coboundary_add (γ₁ γ₂ γ₃ : LieTwoCocycle 𝕜 𝓰 𝓪)
    (β₁ β₂ : LieOneCochain 𝕜 𝓰 𝓪)
    (h₂ : γ₁ + β₁.bdry = γ₂) (h₃ : γ₂ + β₂.bdry = γ₃) :
    ((congr h₃).toLieHom.comp (β₂.bdryHom γ₂)).comp
        ((congr h₂).toLieHom.comp (β₁.bdryHom γ₁))
      = (congr (show γ₁ + (β₁ + β₂).bdry = γ₃ by
            rw [← h₃, ← h₂]
            ac_rfl)).toLieHom.comp
          ((β₁ + β₂).bdryHom γ₁) := by
  ext Z
  · rfl
  · simp only [LieTwoCocycle.CentralExtension.congr, LieOneCochain.bdryHom,
      LieHom.comp_apply, LieHom.coe_mk]
    change Z.snd + β₁ Z.fst + β₂ Z.fst = Z.snd + (β₁ + β₂).toLinearMap Z.fst
    simp only [LieOneCochain.toLinearMap_add, LinearMap.add_apply]
    abel

noncomputable def equiv_of_lieTwoCoboundary {γ' : LieTwoCocycle 𝕜 𝓰 𝓪}
    (h : γ' - γ ∈ LieTwoCoboundary 𝕜 𝓰 𝓪) :
    γ.CentralExtension ≃ₗ⁅𝕜⁆ γ'.CentralExtension :=
  let β := h.choose
  have obs : γ + β.bdry = γ' := by
    change γ + LieOneCochain_bdryHom _ _ _ h.choose = γ'
    simp [h.choose_spec]
  have obs' : γ' + -β.bdry = γ := by
    change γ' - LieOneCochain_bdryHom _ _ _ h.choose = γ
    simp [h.choose_spec]
  LieEquiv.mk_of_comp_eq_id
      (f := (LieTwoCocycle.CentralExtension.congr obs).toLieHom.comp <| β.bdryHom γ)
      (g := (LieTwoCocycle.CentralExtension.congr obs').toLieHom.comp <| (-β).bdryHom γ')
      (by
        convert LieTwoCocycle.CentralExtension.hom_of_coboundary_add
          γ γ' γ β (-β) obs obs'
        ext1 Z
        simp only [LieHom.coe_id, id_eq, LieTwoCocycle.CentralExtension.congr,
          LieOneCochain.bdryHom, add_neg_cancel, LieHom.comp_apply, LieHom.coe_mk]
        ext
        · rfl
        · simp only [left_eq_add]
          rfl)
      (by
        convert LieTwoCocycle.CentralExtension.hom_of_coboundary_add
          γ' γ γ' (-β) β obs' obs
        ext1 Z
        simp only [LieHom.coe_id, id_eq, LieTwoCocycle.CentralExtension.congr,
          LieOneCochain.bdryHom, LieHom.comp_apply, LieHom.coe_mk]
        ext
        · rfl
        · simp only [neg_add_cancel, left_eq_add]
          rfl)






end CentralExtension
end LieTwoCocycle
end LieTwoCocycle.CentralExtension
end VirasoroProject
