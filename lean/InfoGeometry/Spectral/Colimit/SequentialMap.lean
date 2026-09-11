import InfoGeometry.Spectral.Colimit.SequentialModule
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Maps induced on sequential colimits

This is the categorical, Lean 4 form of the reference `seq_colim_functor`:
a natural transformation of sequential diagrams induces a unique map between
their colimits.  The construction uses the existing `Cocone` and `IsColimit`
API rather than a second quotient construction.
-/

namespace InfoGeometry.Spectral.Colimit.SequentialModule

open CategoryTheory CategoryTheory.Limits

universe u

variable {R : Type u} [Ring R]
variable {F G : Diagram R}

def targetCocone (α : F ⟶ G) (t : Cocone R G) : Cocone R F where
  pt := t.pt
  ι :=
    { app := fun n => α.app n ≫ t.ι.app n
      naturality := by
        intro i j hij
        rw [Category.assoc, α.naturality_assoc]
        simp }

@[simp] theorem targetCocone_ι (α : F ⟶ G) (t : Cocone R G) (n : ℕ) :
    (targetCocone α t).ι.app n = α.app n ≫ t.ι.app n :=
  rfl

noncomputable def induced
    (α : F ⟶ G) (s : Cocone R F) (hs : IsColimit s)
    (t : Cocone R G) : s.pt ⟶ t.pt :=
  hs.desc (targetCocone α t)

@[simp] theorem induced_fac
    (α : F ⟶ G) (s : Cocone R F) (hs : IsColimit s)
    (t : Cocone R G) (n : ℕ) :
    s.ι.app n ≫ induced α s hs t = α.app n ≫ t.ι.app n := by
  exact hs.fac (targetCocone α t) n

theorem induced_unique
    (α : F ⟶ G) (s : Cocone R F) (hs : IsColimit s)
    (t : Cocone R G) (f : s.pt ⟶ t.pt)
    (h : ∀ n, s.ι.app n ≫ f = α.app n ≫ t.ι.app n) :
    f = induced α s hs t := by
  apply hs.hom_ext
  intro n
  exact (h n).trans (induced_fac α s hs t n).symm

@[simp] theorem induced_id
    (s : Cocone R F) (hs : IsColimit s) :
    induced (𝟙 F) s hs s = 𝟙 s.pt := by
  apply hs.hom_ext
  intro n
  rw [induced_fac]
  simp

theorem induced_comp
    {H : Diagram R}
    (α : F ⟶ G) (β : G ⟶ H)
    (s : Cocone R F) (hs : IsColimit s)
    (t : Cocone R G) (ht : IsColimit t)
    (u : Cocone R H) :
    induced (α ≫ β) s hs u =
      induced α s hs t ≫ induced β t ht u := by
  apply hs.hom_ext
  intro n
  rw [induced_fac (α ≫ β) s hs u n]
  change α.app n ≫ β.app n ≫ u.ι.app n = _
  rw [← induced_fac β t ht u n]
  rw [← Category.assoc]
  rw [← induced_fac α s hs t n]
  simp only [Category.assoc]

end InfoGeometry.Spectral.Colimit.SequentialModule
