import Mathlib
import InfoGeometry.Topology.MobiusFiniteTripleNormalization

/-!
# Topological `0,1,∞` normalization packet for finite Möbius triples

This file packages the already proved finite normalization theorem into a
discrete topological readout. It does not introduce a new analytic or
continuous Möbius action; the topology is the honest discrete one.
-/

namespace InfoGeometry.Topology.MobiusFiniteTripleNormalizationTopological

open InfoGeometry

noncomputable section

/-- Finite distinct triples of complex points. -/
abbrev FiniteTriple :=
  {p : ℂ × ℂ × ℂ // p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2 ∧ p.1 ≠ p.2.2}

instance finiteTripleTopologicalSpace : TopologicalSpace FiniteTriple := ⊥

instance finiteTripleDiscreteTopology : DiscreteTopology FiniteTriple := ⟨rfl⟩

instance mobiusTransformTopologicalSpace : TopologicalSpace MobiusTransform := ⊥

instance mobiusTransformDiscreteTopology : DiscreteTopology MobiusTransform := ⟨rfl⟩

instance riemannSphereTopologicalSpace : TopologicalSpace RiemannSphere := ⊥

instance riemannSphereDiscreteTopology : DiscreteTopology RiemannSphere := ⟨rfl⟩

/-- A canonical normalization property selected from the finite `0,1,∞` theorem. -/
noncomputable def finiteTripleNormalizationMap (p : FiniteTriple) :
    MobiusTransform :=
  Classical.choose
    (MobiusFiniteTripleNormalization.maps_to_01inf_finite
      p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2.1 p.2.2.2)

/-- The normalized `0,1,∞` packet for a finite triple. -/
def finiteTripleNormalizationPacket (p : FiniteTriple) :
    MobiusTransform × RiemannSphere × RiemannSphere × RiemannSphere :=
  (finiteTripleNormalizationMap p, some 0, some 1, none)

@[simp] theorem finiteTripleNormalizationPacket_fst (p : FiniteTriple) :
    (finiteTripleNormalizationPacket p).1 = finiteTripleNormalizationMap p := by
  rfl

@[simp] theorem finiteTripleNormalizationPacket_snd_fst (p : FiniteTriple) :
    (finiteTripleNormalizationPacket p).2.1 = (some 0 : RiemannSphere) := by
  rfl

@[simp] theorem finiteTripleNormalizationPacket_snd_snd_fst (p : FiniteTriple) :
    (finiteTripleNormalizationPacket p).2.2.1 = (some 1 : RiemannSphere) := by
  rfl

@[simp] theorem finiteTripleNormalizationPacket_snd_snd_snd (p : FiniteTriple) :
    (finiteTripleNormalizationPacket p).2.2.2 = (none : RiemannSphere) := by
  rfl

/-- The selected property satisfies the concrete `0,1,∞` normalization. -/
theorem finiteTripleNormalizationMap_spec (p : FiniteTriple) :
    (finiteTripleNormalizationMap p).eval (some p.1.1) = some 0 ∧
    (finiteTripleNormalizationMap p).eval (some p.1.2.1) = some 1 ∧
    (finiteTripleNormalizationMap p).eval (some p.1.2.2) = none := by
  simpa [finiteTripleNormalizationMap] using
    (Classical.choose_spec
      (MobiusFiniteTripleNormalization.maps_to_01inf_finite
        p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2.1 p.2.2.2))

/-- The normalization packet is continuous on the discrete finite triple space. -/
theorem continuous_finiteTripleNormalizationPacket :
    Continuous finiteTripleNormalizationPacket := by
  exact continuous_of_discreteTopology

/-- The normalization packet is locally constant on the discrete finite triple space. -/
theorem isLocallyConstant_finiteTripleNormalizationPacket :
    IsLocallyConstant finiteTripleNormalizationPacket := by
  exact IsLocallyConstant.of_discrete (f := finiteTripleNormalizationPacket)

end
