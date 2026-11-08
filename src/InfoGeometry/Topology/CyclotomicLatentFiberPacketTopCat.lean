import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.CyclotomicLatentQuotientTopological

/-!
# Parameter-indexed cyclotomic latent fibers

For each sixth-root parameter this owner forms the finite latent range of the
mode lattice and then packages all such ranges in a dependent topological
packet.  The packet is a concrete dependent sum, not an asserted categorical
colimit; its universal quotient property is recorded only for the explicit
surjective readout.
-/

namespace InfoGeometry.Topology.CyclotomicLatentFiberPacketTopCat

open CategoryTheory
open InfoGeometry.Topology.CyclotomicHeisenbergZornLocalSystemTopological
open InfoGeometry.Topology.CyclotomicLatentQuotientTopological
open InfoGeometry.Topology.HeisenbergCyclotomicAtlasTopological

noncomputable section

abbrev LatentMode := ℕ × ℕ

abbrev LatentFiberRange (q : SixthRootParameter) :=
  Set.range (fun m : LatentMode =>
    cyclotomicLatentQuotientReadout (q, m))

abbrev LatentFiberPacket :=
  Σ q : SixthRootParameter, LatentFiberRange q

instance latentFiberPacketTopologicalSpace :
    TopologicalSpace LatentFiberPacket := ⊥

instance latentFiberPacketDiscreteTopology :
    DiscreteTopology LatentFiberPacket := ⟨rfl⟩

def latentFiberPacketReadout
    (p : SixthRootParameter × LatentMode) : LatentFiberPacket :=
  ⟨p.1, ⟨cyclotomicLatentQuotientReadout (p.1, p.2),
    ⟨p.2, rfl⟩⟩⟩

@[simp] theorem latentFiberPacketReadout_parameter
    (p : SixthRootParameter × LatentMode) :
    (latentFiberPacketReadout p).1 = p.1 := by
  rfl

@[simp] theorem latentFiberPacketReadout_value
    (p : SixthRootParameter × LatentMode) :
    (latentFiberPacketReadout p).2.1 =
      cyclotomicLatentQuotientReadout (p.1, p.2) := by
  rfl

theorem continuous_latentFiberPacketReadout :
    Continuous latentFiberPacketReadout := by
  exact continuous_of_discreteTopology

theorem isLocallyConstant_latentFiberPacketReadout :
    IsLocallyConstant latentFiberPacketReadout := by
  exact IsLocallyConstant.of_discrete (f := latentFiberPacketReadout)

theorem latentFiberPacketReadout_surjective :
    Function.Surjective latentFiberPacketReadout := by
  intro z
  rcases z with ⟨q, z⟩
  rcases z.2 with ⟨m, hm⟩
  refine ⟨(q, m), ?_⟩
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply Subtype.ext
  change cyclotomicLatentQuotientReadout (q, m) = (z : LatentQuotient)
  exact hm

theorem isOpenMap_latentFiberPacketReadout :
    IsOpenMap latentFiberPacketReadout := by
  intro s hs
  exact isOpen_discrete _

theorem isQuotientMap_latentFiberPacketReadout :
    Topology.IsQuotientMap latentFiberPacketReadout := by
  exact IsOpenMap.isQuotientMap isOpenMap_latentFiberPacketReadout
    continuous_latentFiberPacketReadout latentFiberPacketReadout_surjective

def latentFiberPacketTopCatMap :
    TopCat.of (SixthRootParameter × LatentMode) ⟶
      TopCat.of LatentFiberPacket :=
  TopCat.ofHom ⟨latentFiberPacketReadout,
    continuous_latentFiberPacketReadout⟩

@[simp] theorem latentFiberPacketTopCatMap_apply
    (p : SixthRootParameter × LatentMode) :
    latentFiberPacketTopCatMap p = latentFiberPacketReadout p := by
  rfl

def latentFiberPacketObservable
    (z : LatentFiberPacket) : ℂ ×
      CyclotomicLatentQuotientTopological.WeylWord :=
  latentObservable z.2.1

theorem continuous_latentFiberPacketObservable :
    Continuous latentFiberPacketObservable := by
  exact continuous_of_discreteTopology

theorem latentFiberPacketObservable_factorization
    (p : SixthRootParameter × LatentMode) :
    latentFiberPacketObservable (latentFiberPacketReadout p) =
      cyclotomicLocalSystemReadout p := by
  exact cyclotomicLocalSystemReadout_factorization p

end
end InfoGeometry.Topology.CyclotomicLatentFiberPacketTopCat
