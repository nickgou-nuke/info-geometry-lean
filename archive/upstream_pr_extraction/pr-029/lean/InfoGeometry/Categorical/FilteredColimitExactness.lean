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

end InfoGeometry.Categorical
