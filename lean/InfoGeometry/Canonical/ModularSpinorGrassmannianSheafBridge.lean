import InfoGeometry.Canonical.ModularSpinorGrassmannianBoundaryBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitQuaternionGrassmannianGelfandSheaf

namespace InfoGeometry.Canonical

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological

noncomputable section

universe u

/-!
# Modular-spinor / Grassmannian sheaf bridge

This file adds the next honest node after
`ModularSpinorGrassmannianBoundaryBridge`. The current repository already owns:

* modular-spinor transport plus Grassmannian Dirichlet-to-Neumann boundary data;
* categorical Gelfand-spectrum presentations;
* native sheaf-cover data for monogenic sections.

What it does not own is an analytic theorem identifying the modular-spinor
boundary problem with a specific spectrum or sheaf construction. Accordingly,
this file only packages the three owner surfaces together and re-exports the
native categorical and sheaf laws already proved elsewhere.
-/

variable {E Sections BoundarySections Gr Open : Type*}
variable [AddCommGroup Sections] [Module ℝ Sections]
variable [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
variable [TopologicalSpace Gr] [Category Open]
variable {J : Type u} [Category.{u, u} J]

/-- Joint owner for the modular-spinor boundary bridge and a native sheaf layer. -/
structure ModularSpinorGrassmannianSheafBridge where
  boundaryBridge : ModularSpinorGrassmannianBoundaryBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
  sheafData : MonogenicSheafData Gr Open

/-/ The spectrum presentation reuses the sheaf bridge; `F` is supplied by the
    surrounding categorical readout and is not additional carrier data. -/
abbrev ModularSpinorGrassmannianSpectrumBridge (F : J ⥤ TopCat.{u}) : Type _ :=
  ModularSpinorGrassmannianSheafBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open)

/-- The sheaf cover condition remains available on the sheaf side of the bridge. -/
theorem modularSpinor_monogenicSheaf_isSheafFor
    (B : ModularSpinorGrassmannianSheafBridge
      (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
      (Gr := Gr) (Open := Open)) :
    Presieve.IsSheafFor B.sheafData.sections B.sheafData.cover :=
  monogenicSheaf_isSheafFor B.sheafData

/-- The monogenic section membership theorem remains available on the sheaf side. -/
theorem modularSpinor_monogenicSection_mem
    (B : ModularSpinorGrassmannianSheafBridge
      (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
      (Gr := Gr) (Open := Open))
    (U : Open) (s : B.sheafData.monogenicSections U) :
    (s : B.sheafData.sections.obj (Opposite.op U)) ∈ B.sheafData.monogenicSections U :=
  monogenicSection_mem B.sheafData U s

/-- The boundary DN kernel theorem remains available inside the sheaf bridge. -/
theorem modularSpinor_boundary_kernel_eq_traceMonogenic
    (B : ModularSpinorGrassmannianSheafBridge
      (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
      (Gr := Gr) (Open := Open)) :
    LinearMap.ker B.boundaryBridge.boundaryData.dirichletToNeumann =
      traceMonogenic B.boundaryBridge.boundaryData :=
  boundary_kernel_eq_traceMonogenic B.boundaryBridge

/-- The categorical spectrum descent map remains available on the spectrum side. -/
noncomputable def modularSpinor_gelfandSpectrumDescend
    (F : J ⥤ TopCat.{u})
    (B : ModularSpinorGrassmannianSpectrumBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ⟶ GelfandSpectrum F :=
  𝟙 _
@[reassoc (attr := simp)]
theorem modularSpinor_gelfandSpectrum_stage
    (F : J ⥤ TopCat.{u})
    (B : ModularSpinorGrassmannianSpectrumBridge
      (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
    (j : J) :
    colimit.ι F j ≫ modularSpinor_gelfandSpectrumDescend F B =
      colimit.ι F j := by
  simp only [modularSpinor_gelfandSpectrumDescend, Category.comp_id]

/-- Modular-spinor transport still preserves the canonical three-form inside the full bridge. -/
theorem modularSpinor_sheafBridge_transport_preserves_threeForm
    (B : ModularSpinorGrassmannianSheafBridge
      (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
      (Gr := Gr) (Open := Open))
    (path : List E) (x y z : ModularSpinorCarrier) :
    canonicalSplitG2ThreeFormValue
        (modularSpinorTransport B.boundaryBridge.connection path x)
        (modularSpinorTransport B.boundaryBridge.connection path y)
        (modularSpinorTransport B.boundaryBridge.connection path z) =
      canonicalSplitG2ThreeFormValue x y z := by
  exact bridge_transport_preserves_threeForm B.boundaryBridge path x y z

end

end InfoGeometry.Canonical
