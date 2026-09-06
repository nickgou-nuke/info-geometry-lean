import Mathlib
import InfoGeometry.Topology.CyclotomicLatentQuotientTopological

/-!
# Topological range quotient for the cyclotomic latent chart

The finite latent chart is first replaced by its actual image subtype.  The
canonical map onto that subtype is a quotient map because both the source and
the range carry their native discrete topologies.  This records the honest
universal property of the observable range, without claiming that it is the
whole ambient latent quotient.
-/

namespace InfoGeometry.Topology.CyclotomicLatentQuotientRangeTopCat

open CategoryTheory
open InfoGeometry.Topology.CyclotomicHeisenbergZornLocalSystemTopological
open InfoGeometry.Topology.CyclotomicLatentQuotientTopological
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological

noncomputable section

abbrev LatentParameter := SixthRootParameter × (ℕ × ℕ)
abbrev LatentReadoutRange := Set.range cyclotomicLatentQuotientReadout

def latentReadoutRangeMap (p : LatentParameter) : LatentReadoutRange :=
  ⟨cyclotomicLatentQuotientReadout p, ⟨p, rfl⟩⟩

@[simp] theorem latentReadoutRangeMap_value (p : LatentParameter) :
    (latentReadoutRangeMap p : LatentQuotient) =
      cyclotomicLatentQuotientReadout p := by
  rfl

theorem continuous_latentReadoutRangeMap :
    Continuous latentReadoutRangeMap := by
  exact continuous_of_discreteTopology

theorem isLocallyConstant_latentReadoutRangeMap :
    IsLocallyConstant latentReadoutRangeMap := by
  exact IsLocallyConstant.of_discrete (f := latentReadoutRangeMap)

theorem latentReadoutRangeMap_surjective :
    Function.Surjective latentReadoutRangeMap := by
  intro z
  exact ⟨z.2.choose, Subtype.ext z.2.choose_spec⟩

theorem isOpenMap_latentReadoutRangeMap :
    IsOpenMap latentReadoutRangeMap := by
  intro s hs
  exact isOpen_discrete _

theorem isQuotientMap_latentReadoutRangeMap :
    Topology.IsQuotientMap latentReadoutRangeMap := by
  exact IsOpenMap.isQuotientMap isOpenMap_latentReadoutRangeMap
    continuous_latentReadoutRangeMap latentReadoutRangeMap_surjective

/-- The range subtype is the canonical factor of the full latent readout. -/
def latentReadoutRangeTopCatMap :
    TopCat.of LatentParameter ⟶ TopCat.of LatentReadoutRange :=
  TopCat.ofHom ⟨latentReadoutRangeMap, continuous_latentReadoutRangeMap⟩

@[simp] theorem latentReadoutRangeTopCatMap_apply (p : LatentParameter) :
    latentReadoutRangeTopCatMap p = latentReadoutRangeMap p := by
  rfl

theorem continuous_latentReadoutRange_iff
    {Y : Type*} [TopologicalSpace Y] {f : LatentReadoutRange → Y} :
    Continuous f ↔ Continuous (f ∘ latentReadoutRangeMap) := by
  exact isQuotientMap_latentReadoutRangeMap.continuous_iff

def latentObservableRange (z : LatentReadoutRange) :
    ℂ × CyclotomicLatentQuotientTopological.WeylWord :=
  latentObservable z.1

theorem continuous_latentObservableRange :
    Continuous latentObservableRange := by
  exact continuous_latentObservable.comp continuous_subtype_val

theorem latentObservableRange_factorization (p : LatentParameter) :
    latentObservableRange (latentReadoutRangeMap p) =
      cyclotomicLocalSystemReadout p := by
  exact cyclotomicLocalSystemReadout_factorization p

end
end InfoGeometry.Topology.CyclotomicLatentQuotientRangeTopCat
