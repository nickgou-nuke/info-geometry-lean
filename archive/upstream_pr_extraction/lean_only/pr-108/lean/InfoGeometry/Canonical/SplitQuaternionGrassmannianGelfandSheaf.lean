import InfoGeometry.Canonical.SplitQuaternionGrassmannianSpinorBridge
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit
import Mathlib.CategoryTheory.Sites.Sheaf

namespace InfoGeometry.Canonical

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological

noncomputable section

universe u

/-!
# Colimit spectrum and sheaf owners for the split-quaternion Grassmannian

The repository's continuum construction is categorical.  Accordingly, a
Gelfand spectrum here is the `TopCat` colimit of its finite character stages;
it is not replaced by a scalar diagonal model or by a smooth/analytic
completion.  A Grassmannian identification is obtained from an actual
`IsColimit` cocone, rather than stored as a `Homeomorph` field.
-/

variable {J : Type u} [Category.{u, u} J]

/-- The categorical spectrum presented by a diagram of finite character stages. -/
abbrev GelfandSpectrum (F : J ⥤ TopCat.{u}) : TopCat.{u} :=
  CategoryTheory.Limits.colimit F

/-- The spectrum-to-target map obtained by the colimit universal property. -/
noncomputable def gelfandSpectrumDescend
    (F : J ⥤ TopCat.{u}) (P : Cocone F) :
    GelfandSpectrum F ⟶ P.pt :=
  colimit.desc F P

/-- The categorical Gelfand-spectrum identification. -/
noncomputable def gelfandSpectrumIsoTarget
  (F : J ⥤ TopCat.{u}) (P : Cocone F) (hP : IsColimit P) :
    GelfandSpectrum F ≅ P.pt :=
  (Cocones.forget F).mapIso ((colimit.isColimit F).uniqueUpToIso hP)

@[reassoc (attr := simp)]
theorem gelfandSpectrum_stage
    (F : J ⥤ TopCat.{u}) (P : Cocone F) (j : J) :
    colimit.ι F j ≫ gelfandSpectrumDescend F P =
      P.ι.app j :=
  colimit.ι_desc P j

theorem gelfandSpectrum_descend_unique
    (F : J ⥤ TopCat.{u}) (P : Cocone F)
    (f : GelfandSpectrum F ⟶ P.pt)
    (h : ∀ j : J, colimit.ι F j ≫ f = P.ι.app j) :
    f = gelfandSpectrumDescend F P :=
by
  apply colimit.hom_ext
  intro j
  change colimit.ι F j ≫ f =
    colimit.ι F j ≫ gelfandSpectrumDescend F P
  rw [h j]
  exact (colimit.ι_desc P j).symm

/-! ## Native sheaf layer -/

/-- A presheaf of monogenic sections with an actual Mathlib sheaf cover. -/
structure MonogenicSheafData
    (Gr : Type*) [TopologicalSpace Gr]
    (Open : Type*) [Category Open] where
  openCarrier : Open → Set Gr
  sections : Openᵒᵖ ⥤ Type*
  monogenicSections : ∀ U : Open, Set (sections.obj (Opposite.op U))
  coverObject : Open
  cover : Presieve coverObject
  isSheafFor : Presieve.IsSheafFor sections cover

theorem monogenicSheaf_isSheafFor
    {Gr Open : Type*} [TopologicalSpace Gr] [Category Open]
    (S : MonogenicSheafData Gr Open) :
    Presieve.IsSheafFor S.sections S.cover :=
  S.isSheafFor

theorem monogenicSection_mem
    {Gr Open : Type*} [TopologicalSpace Gr] [Category Open]
    (S : MonogenicSheafData Gr Open) (U : Open)
    (s : S.monogenicSections U) :
    (s : S.sections.obj (Opposite.op U)) ∈ S.monogenicSections U :=
  s.property

end

end InfoGeometry.Canonical
