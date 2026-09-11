import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.GaloisZornTrialityBridge

/-!
# Topological readout of the cyclotomic Galois action on Zorn triality

This file packages the already verified canonical order-three action on
`ZornCore.Zorn` together with a discrete product readout. It does not add a
new algebraic identification between the charge label and the Zorn carrier.
-/

namespace InfoGeometry.Topology.GaloisZornTrialityTopological

open InfoGeometry.Canonical
open InfoGeometry.Canonical.GaloisZornTrialityBridge

noncomputable section

/-- The native Zorn carrier is treated with the discrete topology here. -/
instance zornCoreTopologicalSpace : TopologicalSpace ZornCore.Zorn := ⊥

instance zornCoreDiscreteTopology : DiscreteTopology ZornCore.Zorn := ⟨rfl⟩

/-- The cyclotomic label space is discrete. -/
instance zmod3TopologicalSpace : TopologicalSpace (ZMod 3) := ⊥

instance zmod3DiscreteTopology : DiscreteTopology (ZMod 3) := ⟨rfl⟩

/-- The combined Zorn / cyclotomic packet is discrete. -/
instance galoisTrialityPacketTopologicalSpace :
    TopologicalSpace (ZornCore.Zorn × ZMod 3) := ⊥

instance galoisTrialityPacketDiscreteTopology :
    DiscreteTopology (ZornCore.Zorn × ZMod 3) := ⟨rfl⟩

/-- Read out the triality action together with the unchanged cyclotomic label. -/
def galoisTrialityReadout (p : ZornCore.Zorn × ZMod 3) :
    ZornCore.Zorn × ZMod 3 :=
  (galoisActionOnTriality p.1 p.2, p.2)

@[simp] theorem galoisTrialityReadout_fst (p : ZornCore.Zorn × ZMod 3) :
    (galoisTrialityReadout p).1 = galoisActionOnTriality p.1 p.2 := by
  rfl

@[simp] theorem galoisTrialityReadout_snd (p : ZornCore.Zorn × ZMod 3) :
    (galoisTrialityReadout p).2 = p.2 := by
  rfl

/-- The combined Galois/triality packet is continuous. -/
theorem continuous_galoisTrialityReadout :
    Continuous galoisTrialityReadout := by
  exact continuous_of_discreteTopology

/-- The combined Galois/triality packet is locally constant. -/
theorem isLocallyConstant_galoisTrialityReadout :
    IsLocallyConstant galoisTrialityReadout := by
  exact IsLocallyConstant.of_discrete (f := galoisTrialityReadout)

/-- The Zorn determinant is preserved on the Zorn component of the packet. -/
theorem galoisTrialityReadout_det (p : ZornCore.Zorn × ZMod 3) :
    ZornCore.det (galoisTrialityReadout p).1 = ZornCore.det p.1 := by
  simpa [galoisTrialityReadout] using
    (galoisActionOnTriality_preserves_det p.1 p.2)
