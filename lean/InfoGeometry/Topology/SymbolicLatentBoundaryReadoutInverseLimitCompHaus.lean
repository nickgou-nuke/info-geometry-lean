import InfoGeometry.Topology.SymbolicLatentBoundaryInverseLimitCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentBoundaryReadoutInverseLimitTopCat
import Mathlib.Topology.Category.CompHaus.Basic

namespace InfoGeometry.Topology

open CategoryTheory CategoryTheory.Limits
open SymbolicLatentBoundaryAddress
open SymbolicLatentBoundaryReadoutInverseLimit
open NaryTreeBoundaryInverseLimit

noncomputable section

variable {ι A : Type} [Fintype ι] [TopologicalSpace A]
variable {D : SymbolicLatentSequence ι}

/-- The native symbolic-latent boundary readout, transported to the compact
prefix inverse-limit object when compactness and Hausdorffness of the source
carrier colimit are supplied explicitly. -/
noncomputable def boundaryReadoutToPrefixLimitCompHausHom
    (D : SymbolicLatentSequence ι)
    (S : SymbolicLatentBoundaryAddress.System A D)
    [CompactSpace A] [T2Space A]
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)] :
    CompHaus.of ((colimit (carrierDiagram D) : TopCat) : Type) ⟶
      symbolicBoundaryPrefixLimitCompHaus (A := A) := by
  change CompHaus.of ((colimit (carrierDiagram D) : TopCat) : Type) ⟶
    CompHaus.of ((limit (prefixDiagram (A := A)) : TopCat) : Type)
  exact ⟨boundaryReadoutToPrefixLimit D S⟩

theorem boundaryReadoutToPrefixLimitCompHausHom_forget
    (D : SymbolicLatentSequence ι)
    (S : SymbolicLatentBoundaryAddress.System A D)
    [CompactSpace A] [T2Space A]
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)] :
    compHausToTop.map (boundaryReadoutToPrefixLimitCompHausHom D S) =
      boundaryReadoutToPrefixLimit D S := by
  rfl

@[simp] theorem boundaryReadoutToPrefixLimitCompHausHom_compHaus_apply
    (D : SymbolicLatentSequence ι)
    (S : SymbolicLatentBoundaryAddress.System A D)
    [CompactSpace A] [T2Space A]
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (n : ℕ) (x : (D.obj n).carrier) (i : Fin n) :
    (limit.π (prefixDiagram (A := A)) (Opposite.op n)).hom
        ((boundaryReadoutToPrefixLimitCompHausHom D S)
          ((colimit.ι (carrierDiagram D) n).hom x)) i =
      S.address n x i.1 := by
  exact boundaryReadoutToPrefixLimit_stage_apply D S n x i

theorem boundaryReadoutToPrefixLimitCompHausHom_isQuotientMap_of_surjective
    (D : SymbolicLatentSequence ι)
    (S : SymbolicLatentBoundaryAddress.System A D)
    [CompactSpace A] [T2Space A]
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (h_surj : Function.Surjective (boundaryReadout D S).hom) :
    Topology.IsQuotientMap
      (compHausToTop.map (boundaryReadoutToPrefixLimitCompHausHom D S)).hom := by
  rw [boundaryReadoutToPrefixLimitCompHausHom_forget]
  exact boundaryReadoutToPrefixLimit_isQuotientMap_of_surjective
    (D := D) (S := S) h_surj

/-- The transported boundary readout is an isomorphism in `CompHaus` whenever
the native symbolic-latent readout is bijective. -/
theorem boundaryReadoutToPrefixLimitCompHausHom_isIso_of_bijective
    (D : SymbolicLatentSequence ι)
    (S : SymbolicLatentBoundaryAddress.System A D)
    [CompactSpace A] [T2Space A]
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (h_inj : Function.Injective (boundaryReadout D S).hom)
    (h_surj : Function.Surjective (boundaryReadout D S).hom) :
    IsIso (boundaryReadoutToPrefixLimitCompHausHom D S) := by
  have hIso :
      IsIso (compHausToTop.map (boundaryReadoutToPrefixLimitCompHausHom D S)) := by
    simpa [boundaryReadoutToPrefixLimitCompHausHom_forget] using
      (boundaryReadoutToPrefixLimit_isIso_of_bijective (D := D) (S := S)
        h_inj h_surj)
  have hFF : (compHausToTop).FullyFaithful := by
    simpa using (CompHausLike.fullyFaithfulCompHausLikeToTop (fun _ => True))
  exact hFF.isIso_of_isIso_map (boundaryReadoutToPrefixLimitCompHausHom D S)

/-- The transported boundary readout is a canonical isomorphism in `CompHaus`
whenever the native symbolic-latent readout is bijective. -/
noncomputable def boundaryReadoutToPrefixLimitCompHausIso
    (D : SymbolicLatentSequence ι)
    (S : SymbolicLatentBoundaryAddress.System A D)
    [CompactSpace A] [T2Space A]
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (h_inj : Function.Injective (boundaryReadout D S).hom)
    (h_surj : Function.Surjective (boundaryReadout D S).hom) :
    CompHaus.of ((colimit (carrierDiagram D) : TopCat) : Type) ≅
      symbolicBoundaryPrefixLimitCompHaus (A := A) := by
  letI : IsIso (boundaryReadoutToPrefixLimitCompHausHom D S) :=
    boundaryReadoutToPrefixLimitCompHausHom_isIso_of_bijective
      (D := D) (S := S) h_inj h_surj
  exact asIso (boundaryReadoutToPrefixLimitCompHausHom D S)

@[simp] theorem boundaryReadoutToPrefixLimitCompHausIso_hom_forget
    (D : SymbolicLatentSequence ι)
    (S : SymbolicLatentBoundaryAddress.System A D)
    [CompactSpace A] [T2Space A]
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (h_inj : Function.Injective (boundaryReadout D S).hom)
    (h_surj : Function.Surjective (boundaryReadout D S).hom) :
    compHausToTop.map ((boundaryReadoutToPrefixLimitCompHausIso
        (D := D) (S := S) h_inj h_surj).hom) =
      boundaryReadoutToPrefixLimit D S := by
  rfl

theorem boundaryReadoutToPrefixLimitCompHausIso_hom_inv_id
    (D : SymbolicLatentSequence ι)
    (S : SymbolicLatentBoundaryAddress.System A D)
    [CompactSpace A] [T2Space A]
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (h_inj : Function.Injective (boundaryReadout D S).hom)
    (h_surj : Function.Surjective (boundaryReadout D S).hom) :
  (boundaryReadoutToPrefixLimitCompHausIso (D := D) (S := S)
        h_inj h_surj).hom ≫
      (boundaryReadoutToPrefixLimitCompHausIso (D := D) (S := S)
        h_inj h_surj).inv =
        𝟙 _ := by
  exact (boundaryReadoutToPrefixLimitCompHausIso (D := D) (S := S)
    h_inj h_surj).hom_inv_id

@[simp] theorem boundaryReadoutToPrefixLimitCompHausIso_hom_inv_apply
    (D : SymbolicLatentSequence ι)
    (S : SymbolicLatentBoundaryAddress.System A D)
    [CompactSpace A] [T2Space A]
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (h_inj : Function.Injective (boundaryReadout D S).hom)
    (h_surj : Function.Surjective (boundaryReadout D S).hom)
    (x : ((colimit (carrierDiagram D) : TopCat) : Type)) :
    ((boundaryReadoutToPrefixLimitCompHausIso (D := D) (S := S)
        h_inj h_surj).hom ≫
      (boundaryReadoutToPrefixLimitCompHausIso (D := D) (S := S)
        h_inj h_surj).inv) x =
      x := by
  exact congrArg (fun f => f x)
    ((boundaryReadoutToPrefixLimitCompHausIso (D := D) (S := S)
      h_inj h_surj).hom_inv_id)

@[simp] theorem boundaryReadoutToPrefixLimitCompHausIso_hom_apply
    (D : SymbolicLatentSequence ι)
    (S : SymbolicLatentBoundaryAddress.System A D)
    [CompactSpace A] [T2Space A]
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (h_inj : Function.Injective (boundaryReadout D S).hom)
    (h_surj : Function.Surjective (boundaryReadout D S).hom)
    (x : ((colimit (carrierDiagram D) : TopCat) : Type)) :
    (boundaryReadoutToPrefixLimitCompHausIso (D := D) (S := S)
        h_inj h_surj).hom x =
      (boundaryReadoutToPrefixLimit D S).hom x := by
  rfl

theorem boundaryReadoutToPrefixLimitCompHausIso_inv_hom_id
    (D : SymbolicLatentSequence ι)
    (S : SymbolicLatentBoundaryAddress.System A D)
    [CompactSpace A] [T2Space A]
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (h_inj : Function.Injective (boundaryReadout D S).hom)
    (h_surj : Function.Surjective (boundaryReadout D S).hom) :
  (boundaryReadoutToPrefixLimitCompHausIso (D := D) (S := S)
        h_inj h_surj).inv ≫
      (boundaryReadoutToPrefixLimitCompHausIso (D := D) (S := S)
        h_inj h_surj).hom =
        𝟙 _ := by
  exact (boundaryReadoutToPrefixLimitCompHausIso (D := D) (S := S)
    h_inj h_surj).inv_hom_id

@[simp] theorem boundaryReadoutToPrefixLimitCompHausIso_inv_hom_apply
    (D : SymbolicLatentSequence ι)
    (S : SymbolicLatentBoundaryAddress.System A D)
    [CompactSpace A] [T2Space A]
    [CompactSpace ((colimit (carrierDiagram D) : TopCat) : Type)]
    [T2Space ((colimit (carrierDiagram D) : TopCat) : Type)]
    (h_inj : Function.Injective (boundaryReadout D S).hom)
    (h_surj : Function.Surjective (boundaryReadout D S).hom)
    (x : symbolicBoundaryPrefixLimitCompHaus (A := A)) :
    ((boundaryReadoutToPrefixLimitCompHausIso (D := D) (S := S)
        h_inj h_surj).inv ≫
      (boundaryReadoutToPrefixLimitCompHausIso (D := D) (S := S)
        h_inj h_surj).hom) x =
      x := by
  exact congrArg (fun f => f x)
    ((boundaryReadoutToPrefixLimitCompHausIso (D := D) (S := S)
      h_inj h_surj).inv_hom_id)

end

end InfoGeometry.Topology
