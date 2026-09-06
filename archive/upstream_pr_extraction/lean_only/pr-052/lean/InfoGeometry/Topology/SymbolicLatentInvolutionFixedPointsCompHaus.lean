import InfoGeometry.Topology.SymbolicLatentInvolutionTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff packaging of symbolic-latent involution fixed points

The fixed-point set is the existing closed subtype from the TopCat owner.
This file adds only its native `CompHaus` packaging and the corresponding
underlying inclusion; no new fixed-point or equalizer object is introduced.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]

noncomputable def SymbolicLatentInvolution.toCompHausHom
    (J : SymbolicLatentInvolution X) :
    CompHaus.of X ⟶ CompHaus.of X := by
  exact ⟨J.toTopCatHom⟩

theorem SymbolicLatentInvolution.toCompHausHom_square
    (J : SymbolicLatentInvolution X) :
    J.toCompHausHom ≫ J.toCompHausHom = 𝟙 (CompHaus.of X) := by
  apply ConcreteCategory.hom_ext
  intro x
  exact J.involutive x

theorem SymbolicLatentInvolution.toCompHausHom_isIso
    (J : SymbolicLatentInvolution X) :
    IsIso J.toCompHausHom := by
  refine IsIso.mk ⟨J.toCompHausHom, ?_, ?_⟩
  · exact J.toCompHausHom_square
  · exact J.toCompHausHom_square

noncomputable def symbolicLatentInvolutionFixedPointCompHaus
    (J : SymbolicLatentInvolution X) : CompHaus := by
  let hclosed : IsClosed (symbolicLatentInvolutionFixedPointSet J) :=
    isClosed_symbolicLatentInvolutionFixedPointSet J
  let hcompact : IsCompact (symbolicLatentInvolutionFixedPointSet J) :=
    IsCompact.of_isClosed_subset isCompact_univ hclosed (Set.subset_univ _)
  letI : CompactSpace (symbolicLatentInvolutionFixedPointSet J) :=
    isCompact_iff_compactSpace.mp hcompact
  exact CompHaus.of (symbolicLatentInvolutionFixedPointSet J)

noncomputable def SymbolicLatentInvolution.fixedPointInclusionCompHausTopCatHom
    (J : SymbolicLatentInvolution X) :
    compHausToTop.obj (symbolicLatentInvolutionFixedPointCompHaus J) ⟶
      TopCat.of X := by
  change TopCat.of (symbolicLatentInvolutionFixedPointSet J) ⟶ TopCat.of X
  exact J.fixedPointInclusion

noncomputable def SymbolicLatentInvolution.fixedPointInclusionCompHausHom
    (J : SymbolicLatentInvolution X) :
    symbolicLatentInvolutionFixedPointCompHaus J ⟶ CompHaus.of X := by
  exact ⟨J.fixedPointInclusionCompHausTopCatHom⟩

theorem SymbolicLatentInvolution.fixedPointInclusionCompHausHom_forget
    (J : SymbolicLatentInvolution X) :
    compHausToTop.map J.fixedPointInclusionCompHausHom =
      J.fixedPointInclusionCompHausTopCatHom := by
  rfl

theorem SymbolicLatentInvolution.fixedPointInclusionCompHausTopCatHom_apply
    (J : SymbolicLatentInvolution X)
    (x : symbolicLatentInvolutionFixedPointSet J) :
    J.fixedPointInclusionCompHausTopCatHom x = x.1 :=
  rfl

theorem SymbolicLatentInvolution.fixedPointInclusionCompHausTopCatHom_invariant
    (J : SymbolicLatentInvolution X) :
    J.fixedPointInclusionCompHausTopCatHom ≫ J.toTopCatHom =
      J.fixedPointInclusionCompHausTopCatHom := by
  ext x
  exact x.2

theorem SymbolicLatentInvolution.fixedPointInclusionCompHausHom_invariant
    (J : SymbolicLatentInvolution X) :
    J.fixedPointInclusionCompHausHom ≫ J.toCompHausHom =
      J.fixedPointInclusionCompHausHom := by
  apply ConcreteCategory.hom_ext
  intro x
  exact x.2

end InfoGeometry.Topology

end
