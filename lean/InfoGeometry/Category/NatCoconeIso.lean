import Mathlib.CategoryTheory.Limits.HasLimits
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Colimits of iso-legged sequential cocones

For the natural-number preorder, a cocone whose legs are all isomorphisms is
already a colimit.  The proof uses the initial index `0` and the unique arrow
from `0` to each stage.
-/

namespace InfoGeometry.Category

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type*} [Category C]
variable {F : ℕ ⥤ C} (s : Cocone F)

lemma isIso_map_of_iso_legs [∀ n, IsIso (s.ι.app n)]
    (m n : ℕ) (h : m ≤ n) :
    IsIso (F.map (homOfLE h)) := by
  have h_eq : F.map (homOfLE h) = s.ι.app m ≫ inv (s.ι.app n) := by
    rw [← Category.comp_id (F.map _)]
    rw [← IsIso.hom_inv_id (s.ι.app n)]
    rw [← Category.assoc, s.w (homOfLE h)]
  rw [h_eq]
  infer_instance

noncomputable def natCoconeIsColimitOfIsoLegs [∀ n, IsIso (s.ι.app n)] : IsColimit s where
  desc t := inv (s.ι.app 0) ≫ t.ι.app 0
  fac t n := by
    have h0n : 0 ≤ n := Nat.zero_le n
    have hmap : IsIso (F.map (homOfLE h0n)) :=
      isIso_map_of_iso_legs s 0 n h0n
    letI := hmap
    have h_sn : s.ι.app n = inv (F.map (homOfLE h0n)) ≫ s.ι.app 0 := by
      rw [IsIso.eq_inv_comp, s.w (homOfLE h0n)]
    rw [h_sn, Category.assoc]
    rw [IsIso.hom_inv_id_assoc]
    rw [← t.w (homOfLE h0n), IsIso.inv_hom_id_assoc]
  uniq t m hm := by
    have h0 := hm 0
    calc
      m = 𝟙 _ ≫ m := by simp
      _ = inv (s.ι.app 0) ≫ s.ι.app 0 ≫ m := by
        simp
      _ = inv (s.ι.app 0) ≫ t.ι.app 0 := by rw [h0]

end InfoGeometry.Category
