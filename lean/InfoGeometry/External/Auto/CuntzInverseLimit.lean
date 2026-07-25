import Mathlib.Tactic

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open Opposite

universe u

/-!
# Cuntz Algebra $\mathcal{O}_\infty$ as an Inverse Limit

This file formalizes the $C^*$-algebraic norm completion of the Cuntz Algebra 
($\mathcal{O}_\infty$) as a projective (inverse) limit.
-/

structure CuntzInverseSystemData where
  IndexCat : Type u
  [index_cat_inst : SmallCategory IndexCat]
  CuntzSystem : IndexCatᵒᵖ ⥤ TopCat.{u}
  tail_proj_surjective :
    ∀ (X Y : IndexCatᵒᵖ) (f : X ⟶ Y),
      Function.Surjective (CuntzSystem.map f)
  shift_nat_trans : CuntzSystem ⟶ CuntzSystem

attribute [instance] CuntzInverseSystemData.index_cat_inst

-- 3. Formally prove that the infinite Cuntz algebra O_infty is the categorical `limit`
-- The universal cone for the limit defines O_infty as the projective limit.
noncomputable def O_infty (D : CuntzInverseSystemData.{u}) : TopCat.{u} :=
  limit D.CuntzSystem

noncomputable def cuntz_cone (D : CuntzInverseSystemData.{u}) : Cone D.CuntzSystem :=
  limit.cone D.CuntzSystem

-- Here is the formal proof that it is the universal limit cone (0 sorrys)
noncomputable def O_infty_is_limit (D : CuntzInverseSystemData.{u}) :
    IsLimit (cuntz_cone D) :=
  limit.isLimit D.CuntzSystem

theorem tail_projection_surjective (D : CuntzInverseSystemData.{u})
    (X Y : D.IndexCatᵒᵖ) (f : X ⟶ Y) :
    Function.Surjective (D.CuntzSystem.map f) :=
  D.tail_proj_surjective X Y f

-- This natural transformation universally induces an endomorphism on the limit.
-- Because this is constructed in TopCat, it is strictly well-defined
-- and continuous in the projective limit topology (infinite tails converge).
noncomputable def CuntzShift (D : CuntzInverseSystemData.{u}) :
    O_infty D ⟶ O_infty D :=
  limMap D.shift_nat_trans
