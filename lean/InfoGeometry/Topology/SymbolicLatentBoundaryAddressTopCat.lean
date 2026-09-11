import InfoGeometry.Topology.SymbolicLatentVaryingCarrierCategory
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.NaryTreeBoundaryInverseLimit

namespace InfoGeometry.Topology

open CategoryTheory CategoryTheory.Limits

/-!
# Boundary-address readouts for varying symbolic-latent carriers

This bridge keeps two categorical constructions distinct.  The latent carrier
sequence has a genuine `TopCat` colimit, while the target `ℕ → A` is the
prefix-boundary space owned by `NaryTreeBoundaryInverseLimit`.  An explicit
compatible address family therefore descends through the carrier colimit;
no claim identifies that colimit with the inverse limit boundary.
-/

variable {ι : Type} {A : Type} [Fintype ι] [TopologicalSpace A]

namespace SymbolicLatentBoundaryAddress

structure System (A : Type) (D : SymbolicLatentSequence ι)
    [TopologicalSpace A] where
  address : ∀ n, (D.obj n).carrier →
    ℕ → A
  continuous_address : ∀ n, Continuous (address n)
  compatible : ∀ {n m : ℕ} (h : n ≤ m) (x : (D.obj n).carrier),
    address m ((D.diagram.map (homOfLE h)).toFun x) = address n x

noncomputable def carrierDiagram (D : SymbolicLatentSequence ι) : ℕ ⥤ TopCat where
  obj n := (D.obj n).carrier
  map f := TopCat.ofHom
    (ContinuousMap.mk
      (D.diagram.map f).toFun
      (D.diagram.map f).continuous_toFun)
  map_id := by
    intro n
    apply TopCat.hom_ext
    ext x
    change (D.diagram.map (𝟙 n)).toFun x = x
    rw [D.diagram.map_id]
    rfl
  map_comp := by
    intro n m k f g
    apply TopCat.hom_ext
    ext x
    change (D.diagram.map (f ≫ g)).toFun x =
      (D.diagram.map g).toFun ((D.diagram.map f).toFun x)
    rw [D.diagram.map_comp]
    rfl

noncomputable def boundaryAddressCocone
    (D : SymbolicLatentSequence ι)
    (S : System A D) : Cocone (carrierDiagram D) where
  pt := TopCat.of (ℕ → A)
  ι :=
    { app := fun n =>
        TopCat.ofHom
          (ContinuousMap.mk (S.address n) (S.continuous_address n))
      naturality := by
        intro n m f
        apply TopCat.hom_ext
        ext x
        exact S.compatible (leOfHom f) x }

noncomputable def boundaryReadout
    (D : SymbolicLatentSequence ι)
    (S : System A D) :
    colimit (carrierDiagram D) ⟶
      TopCat.of (ℕ → A) :=
  colimit.desc (carrierDiagram D) (boundaryAddressCocone D S)

theorem boundaryReadout_stage
    (D : SymbolicLatentSequence ι)
    (S : System A D) (n : ℕ) :
    colimit.ι (carrierDiagram D) n ≫ boundaryReadout D S =
      (boundaryAddressCocone D S).ι.app n :=
  colimit.ι_desc (boundaryAddressCocone D S) n

theorem boundaryReadout_unique
    (D : SymbolicLatentSequence ι)
    (S : System A D)
    {u v : colimit (carrierDiagram D) ⟶
      TopCat.of (ℕ → A)}
    (hu : ∀ n, colimit.ι (carrierDiagram D) n ≫ u =
      (boundaryAddressCocone D S).ι.app n)
    (hv : ∀ n, colimit.ι (carrierDiagram D) n ≫ v =
      (boundaryAddressCocone D S).ι.app n) :
    u = v := by
  apply colimit.hom_ext
  intro n
  rw [hu n, hv n]

end SymbolicLatentBoundaryAddress
end InfoGeometry.Topology
