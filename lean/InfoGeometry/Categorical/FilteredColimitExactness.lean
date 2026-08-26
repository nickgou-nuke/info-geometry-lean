import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Exactness of filtered colimits of abelian groups

For a filtered small category `J`, Mathlib proves that the colimit functor from
`J`-diagrams of abelian groups preserves finite limits and homology.  The
canonical kernel and cokernel comparison isomorphisms below expose the exact
finite-limit/finite-colimit facts needed by spectral and chain-complex towers.
-/

noncomputable section

namespace InfoGeometry.Categorical

open CategoryTheory
open CategoryTheory.Limits

variable {J : Type} [SmallCategory J] [IsFiltered J]

/-- A filtered colimit of abelian groups commutes with the kernel of a natural
transformation. -/
noncomputable def filteredColimitKernelIso
    {X Y : J ⥤ AddCommGrpCat} (f : X ⟶ Y) :
    colim.obj (kernel f) ≅ kernel (colim.map f) :=
  PreservesKernel.iso colim f

/-- A filtered colimit of abelian groups commutes with the cokernel of a
natural transformation. -/
noncomputable def filteredColimitCokernelIso
    {X Y : J ⥤ AddCommGrpCat} (f : X ⟶ Y) :
    colim.obj (cokernel f) ≅ cokernel (colim.map f) :=
  PreservesCokernel.iso colim f

/-- The homology object of a filtered colimit of short complexes is canonically
the filtered colimit of their homology objects. -/
noncomputable def filteredColimitHomologyIso
    (S : ShortComplex (J ⥤ AddCommGrpCat))
    [S.HasHomology] [(S.map colim).HasHomology] :
    colim.obj S.homology ≅ (S.map colim).homology :=
  (S.mapHomologyIso colim).symm

@[simp]
theorem filteredColimitKernelIso_hom_inv_id
    {X Y : J ⥤ AddCommGrpCat} (f : X ⟶ Y) :
    (filteredColimitKernelIso f).hom ≫
        (filteredColimitKernelIso f).inv = 𝟙 _ := by
  exact (filteredColimitKernelIso f).hom_inv_id

@[simp]
theorem filteredColimitKernelIso_inv_hom_id
    {X Y : J ⥤ AddCommGrpCat} (f : X ⟶ Y) :
    (filteredColimitKernelIso f).inv ≫
        (filteredColimitKernelIso f).hom = 𝟙 _ := by
  exact (filteredColimitKernelIso f).inv_hom_id

@[simp]
theorem filteredColimitCokernelIso_hom_inv_id
    {X Y : J ⥤ AddCommGrpCat} (f : X ⟶ Y) :
    (filteredColimitCokernelIso f).hom ≫
        (filteredColimitCokernelIso f).inv = 𝟙 _ := by
  exact (filteredColimitCokernelIso f).hom_inv_id

@[simp]
theorem filteredColimitCokernelIso_inv_hom_id
    {X Y : J ⥤ AddCommGrpCat} (f : X ⟶ Y) :
    (filteredColimitCokernelIso f).inv ≫
        (filteredColimitCokernelIso f).hom = 𝟙 _ := by
  exact (filteredColimitCokernelIso f).inv_hom_id

@[simp]
theorem filteredColimitHomologyIso_hom_inv_id
    (S : ShortComplex (J ⥤ AddCommGrpCat))
    [S.HasHomology] [(S.map colim).HasHomology] :
    (filteredColimitHomologyIso S).hom ≫
        (filteredColimitHomologyIso S).inv = 𝟙 _ := by
  exact (filteredColimitHomologyIso S).hom_inv_id

@[simp]
theorem filteredColimitHomologyIso_inv_hom_id
    (S : ShortComplex (J ⥤ AddCommGrpCat))
    [S.HasHomology] [(S.map colim).HasHomology] :
    (filteredColimitHomologyIso S).inv ≫
        (filteredColimitHomologyIso S).hom = 𝟙 _ := by
  exact (filteredColimitHomologyIso S).inv_hom_id

end InfoGeometry.Categorical
