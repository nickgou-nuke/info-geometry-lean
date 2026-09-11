import InfoGeometry.Topology.SymbolicLatentBoundaryCylinderColimitTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Conditional quotient-map property for the boundary-cylinder readout

The carrier colimit is not compact in complete generality, so the readout
cannot be promoted to a quotient map without an explicit compactness and
surjectivity property.  Under those hypotheses, this owner delegates
directly to Mathlib's compact-to-Hausdorff quotient-map theorem.
-/

noncomputable section

namespace InfoGeometry.Topology.SymbolicLatentBoundaryCylinderQuotientTopCat

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology.SymbolicLatentBoundaryAddress
open InfoGeometry.Topology.SymbolicLatentBoundaryCylinderColimit

variable {ι : Type} {A : Type}
  [Fintype ι] [TopologicalSpace A]
  [T2Space A]
variable {D : SymbolicLatentSequence ι}

theorem boundaryReadout_isQuotientMap_of_compactSpace
    (S : System A D)
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    (h_surj : Function.Surjective (boundaryReadout D S).hom) :
    Topology.IsQuotientMap (boundaryReadout D S).hom := by
  exact IsQuotientMap.of_surjective_continuous h_surj
    (boundaryReadout D S).hom.continuous

noncomputable def boundaryReadout_homeomorph_of_bijective
    (S : System A D)
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    (h_inj : Function.Injective (boundaryReadout D S).hom)
    (h_surj : Function.Surjective (boundaryReadout D S).hom) :
    ((colimit (carrierDiagram D) : TopCat) : Type) ≃ₜ (ℕ → A) := by
  let e : ((colimit (carrierDiagram D) : TopCat) : Type) ≃ (ℕ → A) :=
    Equiv.ofBijective (boundaryReadout D S).hom ⟨h_inj, h_surj⟩
  refine
    { toEquiv := e
      continuous_toFun := (boundaryReadout D S).hom.continuous
      continuous_invFun := ?_ }
  apply (boundaryReadout_isQuotientMap_of_compactSpace S h_surj).continuous_iff.mpr
  change Continuous (e.symm ∘ (boundaryReadout D S).hom)
  have hcomp : e.symm ∘ (boundaryReadout D S).hom = id := by
    funext x
    exact e.left_inv x
  rw [hcomp]
  exact continuous_id

noncomputable def boundaryReadout_inverseTopCatHom_of_bijective
    (S : System A D)
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    (h_inj : Function.Injective (boundaryReadout D S).hom)
    (h_surj : Function.Surjective (boundaryReadout D S).hom) :
    TopCat.of (ℕ → A) ⟶ colimit (carrierDiagram D) := by
  let e := boundaryReadout_homeomorph_of_bijective S h_inj h_surj
  exact TopCat.ofHom
    { toFun := e.symm
      continuous_toFun := e.symm.continuous_toFun }

theorem boundaryReadout_isIso_of_bijective
    (S : System A D)
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    (h_inj : Function.Injective (boundaryReadout D S).hom)
    (h_surj : Function.Surjective (boundaryReadout D S).hom) :
    IsIso (boundaryReadout D S) := by
  let e := boundaryReadout_homeomorph_of_bijective S h_inj h_surj
  refine IsIso.mk ⟨TopCat.ofHom
    { toFun := e.symm
      continuous_toFun := e.symm.continuous_toFun }, ?_, ?_⟩
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change e.symm ((boundaryReadout D S).hom x) = x
    exact e.left_inv x
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change (boundaryReadout D S).hom (e.symm x) = x
    exact e.right_inv x

end InfoGeometry.Topology.SymbolicLatentBoundaryCylinderQuotientTopCat
