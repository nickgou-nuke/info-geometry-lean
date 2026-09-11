import InfoGeometry.Canonical.ContinuousLeftActionTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit

/-!
# Colimit descent of continuous left translations

Translations of a continuous left action descend through the categorical direct
colimit of the constant `TopCat` diagram.  The descended maps assemble into a
continuous left action on that colimit.
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

/-- The carrier of the topological colimit of the constant diagram. -/
abbrev constantTopDiagramColimitSpace : Type u :=
  (colimit (constantTopDiagram (J := J) (X := X))).carrier

instance : TopologicalSpace (constantTopDiagramColimitSpace (J := J) (X := X)) :=
  (colimit (constantTopDiagram (J := J) (X := X))).str

def translationNaturalTransformation (a : M) :
    constantTopDiagram (J := J) (X := X) ⟶
      constantTopDiagram (J := J) (X := X) where
  app := fun _ => translation A a
  naturality := by
    intro j k f
    rfl

noncomputable def translationColimit (a : M) :
    colimit (constantTopDiagram (J := J) (X := X)) ⟶
      colimit (constantTopDiagram (J := J) (X := X)) :=
  colim.map (translationNaturalTransformation A a)

@[reassoc]
theorem translationColimit_stage (a : M) (j : J) :
    colimit.ι (constantTopDiagram (J := J) (X := X)) j ≫
        translationColimit A a =
      translation A a ≫
        colimit.ι (constantTopDiagram (J := J) (X := X)) j := by
  exact colimit.ι_map (translationNaturalTransformation A a) j

theorem translationColimit_apply_stage (a : M) (j : J) (x : X) :
    translationColimit A a
        (colimit.ι
          (constantTopDiagram (J := J) (X := X)) j x) =
      colimit.ι
        (constantTopDiagram (J := J) (X := X)) j (A.smul a x) := by
  exact congrArg (fun f => f x) (translationColimit_stage A a j)

theorem translationColimit_one :
    translationColimit A 1 =
      𝟙 (colimit
        (constantTopDiagram (J := J) (X := X))) := by
  apply colimit.hom_ext
  intro j
  change colimit.ι
      (constantTopDiagram (J := J) (X := X)) j ≫ translationColimit A 1 =
    colimit.ι
      (constantTopDiagram (J := J) (X := X)) j ≫ 𝟙 _
  rw [translationColimit_stage A 1 j, translation_one A]
  simp

theorem translationColimit_comp (a b : M) :
    translationColimit (J := J) (X := X) A a ≫
        translationColimit (J := J) (X := X) A b =
      translationColimit (J := J) (X := X) A (b * a) := by
  apply colimit.hom_ext
  intro j
  change colimit.ι
      (constantTopDiagram (J := J) (X := X)) j ≫
      translationColimit A a ≫ translationColimit A b =
    colimit.ι
        (constantTopDiagram (J := J) (X := X)) j ≫
      translationColimit A (b * a)
  calc
    colimit.ι
        (constantTopDiagram (J := J) (X := X)) j ≫
        translationColimit A a ≫ translationColimit A b =
      (translation A a ≫
        colimit.ι
          (constantTopDiagram (J := J) (X := X)) j) ≫
        translationColimit A b := by
          simpa only [Category.assoc] using
            congrArg
              (fun k => k ≫ translationColimit (J := J) (X := X) A b)
              (translationColimit_stage (J := J) (X := X) A a j)
    _ = translation A a ≫
        (colimit.ι
          (constantTopDiagram (J := J) (X := X)) j ≫
          translationColimit A b) := by
          simp only [Category.assoc]
    _ = translation A a ≫
        (translation A b ≫
          colimit.ι
            (constantTopDiagram (J := J) (X := X)) j) := by
          rw [translationColimit_stage (J := J) (X := X) A b j]
    _ = translation A (b * a) ≫
        colimit.ι
          (constantTopDiagram (J := J) (X := X)) j := by
          rw [← translation_comp A a b]
          exact (Category.assoc (translation A a) (translation A b)
            (colimit.ι
              (constantTopDiagram (J := J) (X := X)) j)).symm
    _ = colimit.ι
        (constantTopDiagram (J := J) (X := X)) j ≫
        translationColimit A (b * a) := by
          rw [translationColimit_stage (J := J) (X := X) A (b * a) j]

def colimitAction :
    ContinuousLeftAction M
      (constantTopDiagramColimitSpace (J := J) (X := X)) where
  smul a x := translationColimit (J := J) (X := X) A a x
  one_smul := by
    intro x
    exact congrArg (fun f => f x) (translationColimit_one A)
  mul_smul := by
    intro a b x
    simpa only [CategoryTheory.comp_apply] using
      (congrArg (fun f => f x)
        (translationColimit_comp (J := J) (X := X) A b a)).symm
  continuous_smul := by
    intro a
    exact (translationColimit (J := J) (X := X) A a).hom.continuous

theorem colimitAction_apply_stage (a : M) (j : J) (x : X) :
    (colimitAction (J := J) (X := X) A).smul a
        (colimit.ι
          (constantTopDiagram (J := J) (X := X)) j x) =
      colimit.ι
        (constantTopDiagram (J := J) (X := X)) j (A.smul a x) := by
  exact translationColimit_apply_stage (J := J) (X := X) A a j x

end InfoGeometry.Canonical.ContinuousLeftActionTopCatColimit
