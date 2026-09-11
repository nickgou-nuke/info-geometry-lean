import InfoGeometry.Topology.SymbolicLatentBoundaryAddressTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentBoundaryCylinderQuotientTopCat

/-!
# Symbolic-latent readouts into the native prefix inverse limit

The varying-carrier readout first lands in the sequence-space model of the
boundary.  The inverse-limit owner identifies that model with the actual
`TopCat` limit of finite-prefix spaces.  This file records that comparison
without introducing a second limit or a surrogate universal-property API.
-/

noncomputable section

namespace InfoGeometry.Topology.SymbolicLatentBoundaryReadoutInverseLimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology.SymbolicLatentBoundaryAddress
open InfoGeometry.Topology.SymbolicLatentBoundaryCylinderQuotientTopCat
open InfoGeometry.Topology.NaryTreeBoundaryInverseLimit

variable {ι : Type} {A : Type}
  [Fintype ι] [TopologicalSpace A]
variable {D : SymbolicLatentSequence ι}

/-- The compatible symbolic-latent readout viewed in the native prefix limit. -/
noncomputable def boundaryReadoutToPrefixLimit
    (D : SymbolicLatentSequence ι)
    (S : System A D) :
    colimit (carrierDiagram D) ⟶
      limit (prefixDiagram (A := A)) :=
  boundaryReadout D S ≫ prefixBoundaryLimitIso (A := A).hom

/-- Each finite-prefix projection of the transported readout is the
stage-address cocone followed by the corresponding prefix projection. -/
theorem boundaryReadoutToPrefixLimit_stage
    (D : SymbolicLatentSequence ι)
    (S : System A D) (n : ℕ) :
    colimit.ι (carrierDiagram D) n ≫
        boundaryReadoutToPrefixLimit D S ≫
          limit.π (prefixDiagram (A := A)) (Opposite.op n) =
      (boundaryAddressCocone D S).ι.app n ≫
        (prefixCone (A := A)).π.app (Opposite.op n) := by
  rw [boundaryReadoutToPrefixLimit]
  rw [Category.assoc, prefixBoundaryLimitIso_hom_comp]
  rw [← Category.assoc, boundaryReadout_stage]

theorem boundaryReadoutToPrefixLimit_stage_apply
    (D : SymbolicLatentSequence ι)
    (S : System A D) (n : ℕ) (x : (D.obj n).carrier) (i : Fin n) :
    (limit.π (prefixDiagram (A := A)) (Opposite.op n)).hom
        ((boundaryReadoutToPrefixLimit D S).hom
          ((colimit.ι (carrierDiagram D) n).hom x)) i =
      S.address n x i.1 := by
  have h := congrArg (fun f => f.hom x)
    (boundaryReadoutToPrefixLimit_stage D S n)
  have h' :
      (limit.π (prefixDiagram (A := A)) (Opposite.op n)).hom
          ((boundaryReadoutToPrefixLimit D S).hom
            ((colimit.ι (carrierDiagram D) n).hom x)) =
        (fun j : Fin n => S.address n x j.1) := by
    simpa [Category.assoc, prefixCone, boundaryAddressCocone] using h
  exact congrFun h' i

theorem prefixBoundaryLimit_ext
    {A : Type} [TopologicalSpace A]
    {x y : ((limit (prefixDiagram (A := A)) : TopCat) : Type)}
    (h : ∀ n : ℕ,
      (limit.π (prefixDiagram (A := A)) (Opposite.op n)).hom x =
        (limit.π (prefixDiagram (A := A)) (Opposite.op n)).hom y) :
    x = y := by
  let f : TopCat.of PUnit ⟶ limit (prefixDiagram (A := A)) :=
    TopCat.ofHom
      { toFun := fun _ => x
        continuous_toFun := continuous_const }
  let g : TopCat.of PUnit ⟶ limit (prefixDiagram (A := A)) :=
    TopCat.ofHom
      { toFun := fun _ => y
        continuous_toFun := continuous_const }
  have hfg : f = g := by
    apply limit.hom_ext
    intro j
    rcases j with ⟨n⟩
    apply TopCat.hom_ext
    ext p
    exact h n
  exact congrArg (fun q => q PUnit.unit) hfg

/-- The inverse-limit comparison is uniquely determined by all finite-prefix
projections. -/
theorem boundaryReadoutToPrefixLimit_unique
    (D : SymbolicLatentSequence ι)
    {u v : colimit (carrierDiagram D) ⟶
      limit (prefixDiagram (A := A))}
    (h : ∀ n : ℕ,
      u ≫ limit.π (prefixDiagram (A := A)) (Opposite.op n) =
        v ≫ limit.π (prefixDiagram (A := A)) (Opposite.op n)) :
    u = v := by
  apply limit.hom_ext
  intro j
  rcases j with ⟨n⟩
  exact h n

theorem boundaryReadoutToPrefixLimit_isIso_of_bijective
    (D : SymbolicLatentSequence ι)
    (S : System A D)
    [T2Space A]
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    (h_inj : Function.Injective (boundaryReadout D S).hom)
    (h_surj : Function.Surjective (boundaryReadout D S).hom) :
    IsIso (boundaryReadoutToPrefixLimit D S) := by
  letI :=
    InfoGeometry.Topology.SymbolicLatentBoundaryCylinderQuotientTopCat.boundaryReadout_isIso_of_bijective
      S h_inj h_surj
  change IsIso
    (boundaryReadout D S ≫ prefixBoundaryLimitIso (A := A).hom)
  infer_instance

theorem boundaryReadoutToPrefixLimit_isQuotientMap_of_surjective
    (D : SymbolicLatentSequence ι)
    (S : System A D)
    [T2Space A]
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    (h_surj : Function.Surjective (boundaryReadout D S).hom) :
    Topology.IsQuotientMap (boundaryReadoutToPrefixLimit D S).hom := by
  have hreadout :=
    InfoGeometry.Topology.SymbolicLatentBoundaryCylinderQuotientTopCat.boundaryReadout_isQuotientMap_of_compactSpace
      S h_surj
  have hlimit :=
    (TopCat.homeoOfIso (prefixBoundaryLimitIso (A := A))).isQuotientMap
  have hcomp := hlimit.comp hreadout
  simpa [boundaryReadoutToPrefixLimit, Category.assoc] using hcomp

end InfoGeometry.Topology.SymbolicLatentBoundaryReadoutInverseLimit
