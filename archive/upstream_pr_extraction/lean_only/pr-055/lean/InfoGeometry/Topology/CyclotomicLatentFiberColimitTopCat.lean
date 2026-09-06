import Mathlib
import InfoGeometry.Topology.CyclotomicLatentFiberPacketTopCat

/-!
# Genuine `TopCat` coproduct of cyclotomic latent fibers

The parameter-indexed finite latent fibers are assembled by a diagram on the
discrete parameter category.  Its cocone point is the dependent packet from
the preceding owner; the induced colimit map is then proved stagewise and
surjectively.  No analytic completion is asserted.
-/

namespace InfoGeometry.Topology.CyclotomicLatentFiberColimitTopCat

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology.CyclotomicLatentFiberPacketTopCat
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological

noncomputable section

def latentFiberDiagram : Discrete SixthRootParameter ⥤ TopCat where
  obj q := TopCat.of (LatentFiberRange q.as)
  map f := eqToHom (congrArg (fun q => TopCat.of (LatentFiberRange q))
    (Discrete.eq_of_hom f))
  map_id q := by simp
  map_comp f g := by simp

def latentFiberInclusion (q : SixthRootParameter) :
    TopCat.of (LatentFiberRange q) ⟶ TopCat.of LatentFiberPacket :=
  TopCat.ofHom <| ContinuousMap.mk
    (fun z => ⟨q, z⟩) continuous_of_discreteTopology

def latentFiberPacketCocone : Cocone latentFiberDiagram where
  pt := TopCat.of LatentFiberPacket
  ι := { app := fun q => latentFiberInclusion q.as
         naturality := by
           intro q r f
           apply TopCat.hom_ext
           have hqr := Discrete.eq_of_hom f
           cases q with
           | mk q =>
             cases r with
             | mk r =>
               dsimp at hqr ⊢
               cases hqr
               rfl }

noncomputable def latentFiberColimitReadout :
    colimit latentFiberDiagram ⟶ TopCat.of LatentFiberPacket :=
  colimit.desc latentFiberDiagram latentFiberPacketCocone

theorem latentFiberColimitReadout_stage (q : SixthRootParameter) :
    colimit.ι latentFiberDiagram (Discrete.mk q) ≫
        latentFiberColimitReadout =
      (latentFiberPacketCocone.ι.app (Discrete.mk q)) := by
  exact colimit.ι_desc latentFiberPacketCocone (Discrete.mk q)

theorem latentFiberColimitReadout_surjective :
    Function.Surjective latentFiberColimitReadout := by
  intro z
  rcases z with ⟨q, z⟩
  refine ⟨colimit.ι latentFiberDiagram (Discrete.mk q) z, ?_⟩
  have hstage := latentFiberColimitReadout_stage q
  have hstage' := congrArg (fun f => f z) hstage
  exact hstage'

theorem latentFiberColimitReadout_unique
    {u v : colimit latentFiberDiagram ⟶ TopCat.of LatentFiberPacket}
    (hu : ∀ q, colimit.ι latentFiberDiagram (Discrete.mk q) ≫ u =
      latentFiberPacketCocone.ι.app (Discrete.mk q))
    (hv : ∀ q, colimit.ι latentFiberDiagram (Discrete.mk q) ≫ v =
      latentFiberPacketCocone.ι.app (Discrete.mk q)) :
    u = v := by
  apply colimit.hom_ext
  intro q
  rw [hu q.as, hv q.as]

end
end InfoGeometry.Topology.CyclotomicLatentFiberColimitTopCat
