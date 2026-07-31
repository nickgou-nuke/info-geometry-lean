import InfoGeometry.Canonical.ContinuousLeftActionTopCat
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit

/-!
# Colimit descent of continuous left translations

For a continuous left action, every translation acts on the constant `TopCat`
diagram and therefore descends through its categorical direct colimit.  The
composition law records the right-action order forced by `TopCat` composition.
-/

noncomputable section

namespace InfoGeometry.Canonical.ContinuousLeftActionTopCatColimit

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Canonical.ContinuousLeftActionTopCat
open FilteredColimit.Native.Topological

universe u v

variable {J : Type u} [Category.{u} J]
variable {M : Type v} {X : Type u} [Monoid M] [TopologicalSpace X]

variable (A : ContinuousLeftAction M X)

def constantTopDiagram : J ⥤ TopCat.{u} :=
  (Functor.const J).obj (TopCat.of X)

/-- The constant-diagram natural transformation induced by one translation. -/
def translationNaturalTransformation (a : M) :
    constantTopDiagram (J := J) (X := X) ⟶
      constantTopDiagram (J := J) (X := X) where
  app := fun _ => translation A a
  naturality := by
    intro j k f
    rfl

/-- The continuous translation descended through the categorical direct colimit. -/
noncomputable def translationColimit (a : M) :
    topologicalDirectColimit (constantTopDiagram (J := J) (X := X)) ⟶
      topologicalDirectColimit (constantTopDiagram (J := J) (X := X)) :=
  topologicalDirectMapBetween (translationNaturalTransformation A a)

@[reassoc]
theorem translationColimit_stage (a : M) (j : J) :
    topologicalDirectInjection (constantTopDiagram (J := J) (X := X)) j ≫
        translationColimit A a =
      translation A a ≫
        topologicalDirectInjection (constantTopDiagram (J := J) (X := X)) j := by
  exact topologicalDirectMapBetween_injection
    (translationNaturalTransformation A a) j

theorem translationColimit_apply_stage (a : M) (j : J) (x : X) :
    translationColimit A a
        (topologicalDirectInjection
          (constantTopDiagram (J := J) (X := X)) j x) =
      topologicalDirectInjection
        (constantTopDiagram (J := J) (X := X)) j (A.smul a x) := by
  exact congrArg (fun f => f x) (translationColimit_stage A a j)

theorem translationColimit_one :
    translationColimit A 1 =
      𝟙 (topologicalDirectColimit
        (constantTopDiagram (J := J) (X := X))) := by
  apply colimit.hom_ext
  intro j
  change topologicalDirectInjection
      (constantTopDiagram (J := J) (X := X)) j ≫ translationColimit A 1 =
    topologicalDirectInjection
      (constantTopDiagram (J := J) (X := X)) j ≫ 𝟙 _
  rw [translationColimit_stage A 1 j, translation_one A]
  simp

theorem translationColimit_comp (a b : M) :
    translationColimit (J := J) (X := X) A a ≫
        translationColimit (J := J) (X := X) A b =
      translationColimit (J := J) (X := X) A (b * a) := by
  apply colimit.hom_ext
  intro j
  change topologicalDirectInjection
      (constantTopDiagram (J := J) (X := X)) j ≫
      translationColimit A a ≫ translationColimit A b =
    topologicalDirectInjection
        (constantTopDiagram (J := J) (X := X)) j ≫
      translationColimit A (b * a)
  calc
    topologicalDirectInjection
        (constantTopDiagram (J := J) (X := X)) j ≫
        translationColimit A a ≫ translationColimit A b =
      (translation A a ≫
        topologicalDirectInjection
          (constantTopDiagram (J := J) (X := X)) j) ≫
        translationColimit A b := by
          simpa only [Category.assoc] using
            congrArg
              (fun k => k ≫ translationColimit (J := J) (X := X) A b)
              (translationColimit_stage (J := J) (X := X) A a j)
    _ = translation A a ≫
        (topologicalDirectInjection
          (constantTopDiagram (J := J) (X := X)) j ≫
          translationColimit A b) := by
          simp only [Category.assoc]
    _ = translation A a ≫
        (translation A b ≫
          topologicalDirectInjection
            (constantTopDiagram (J := J) (X := X)) j) := by
          rw [translationColimit_stage (J := J) (X := X) A b j]
    _ = translation A (b * a) ≫
        topologicalDirectInjection
          (constantTopDiagram (J := J) (X := X)) j := by
          rw [← translation_comp A a b]
          exact (Category.assoc (translation A a) (translation A b)
            (topologicalDirectInjection
              (constantTopDiagram (J := J) (X := X)) j)).symm
    _ = topologicalDirectInjection
        (constantTopDiagram (J := J) (X := X)) j ≫
        translationColimit A (b * a) := by
          rw [translationColimit_stage (J := J) (X := X) A (b * a) j]

end InfoGeometry.Canonical.ContinuousLeftActionTopCatColimit
