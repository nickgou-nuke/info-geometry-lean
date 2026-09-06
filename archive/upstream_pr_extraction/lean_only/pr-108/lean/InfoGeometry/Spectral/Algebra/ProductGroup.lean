import Mathlib

/-!
# Products of groups

The old Spectral reference rebuilt the direct product group structure.  In
Lean 4 this structure is native, so this file ports the useful homomorphism
and equivalence interface directly onto `G × H`.
-/

namespace InfoGeometry.Spectral.Algebra.ProductGroup

universe u v w z

variable {G : Type u} {H : Type v} {K : Type w} {L : Type z}
variable [Group G] [Group H] [Group K] [Group L]

def inl : G →* G × H where
  toFun x := (x, 1)
  map_one' := by simp
  map_mul' x y := by simp

def inr : H →* G × H where
  toFun y := (1, y)
  map_one' := by simp
  map_mul' x y := by simp

def fst : G × H →* G where
  toFun := Prod.fst
  map_one' := rfl
  map_mul' := by intros; rfl

def snd : G × H →* H where
  toFun := Prod.snd
  map_one' := rfl
  map_mul' := by intros; rfl

@[simp] theorem fst_inl (x : G) : fst (inl (G := G) (H := H) x) = x := rfl
@[simp] theorem snd_inr (y : H) : snd (G := G) (H := H) (inr y) = y := rfl
@[simp] theorem snd_inl (x : G) : snd (G := G) (H := H) (inl x) = 1 := rfl
@[simp] theorem fst_inr (y : H) : fst (G := G) (H := H) (inr y) = 1 := rfl

def map (f : G →* K) (g : H →* L) : G × H →* K × L where
  toFun x := (f x.1, g x.2)
  map_one' := by simp
  map_mul' x y := by simp

@[simp] theorem map_apply (f : G →* K) (g : H →* L) (x : G × H) :
    map f g x = (f x.1, g x.2) := rfl

@[simp] theorem map_inl (f : G →* K) (g : H →* L) (x : G) :
    map f g (inl (G := G) (H := H) x) = (f x, 1) := by simp [map, inl]

@[simp] theorem map_inr (f : G →* K) (g : H →* L) (y : H) :
    map f g (inr (G := G) (H := H) y) = (1, g y) := by simp [map, inr]

@[simp] theorem map_id (x : G × H) :
    map (MonoidHom.id G) (MonoidHom.id H) x = x := by
  rfl

theorem map_comp
    (f₁ : G →* K) (f₂ : K →* L)
    (g₁ : H →* H) (g₂ : H →* H) (x : G × H) :
    map (f₂.comp f₁) (g₂.comp g₁) x =
      map f₂ g₂ (map f₁ g₁ x) := by
  rfl

def equiv (eG : G ≃* K) (eH : H ≃* L) : G × H ≃* K × L where
  toFun x := (eG x.1, eH x.2)
  invFun x := (eG.symm x.1, eH.symm x.2)
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by simp

@[simp] theorem equiv_apply (eG : G ≃* K) (eH : H ≃* L) (x : G × H) :
    equiv eG eH x = (eG x.1, eH x.2) := rfl

def trivialRight (h : Subsingleton H) : G × H ≃* G where
  toFun x := x.1
  invFun x := (x, 1)
  left_inv x := by
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _
  right_inv x := rfl
  map_mul' x y := rfl

def trivialLeft (h : Subsingleton G) : G × H ≃* H where
  toFun x := x.2
  invFun x := (1, x)
  left_inv x := by
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  right_inv x := rfl
  map_mul' x y := rfl

end InfoGeometry.Spectral.Algebra.ProductGroup
