import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.MassSpectrometry.FiniteFragmentationModel

/-!
# Verified inference architecture for mass spectrometry

This module formalizes the theorem-safe part of a physics-informed inverse
pipeline.  It deliberately separates structural guarantees from empirical
performance claims.

A reconstructor is *certified by construction* when its codomain is
`FiniteValuedFragmentationModel n`.  Consequently every output carries:

* a rank-certified acyclic fragmentation DAG;
* an explicit positive mass valuation decreasing on cleavage edges;
* a Mathlib doubly-stochastic peak/fragment assignment;
* an energy-conditioned grammar whose nonzero transitions have positive
  neutral mass loss.

Forward simulation and inverse reconstruction are related only through explicit
cycle-consistency hypotheses.  No learning accuracy, identifiability,
regulatory acceptance, or molecular-graph uniqueness theorem is asserted.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

/-! ## Multi-condition observations -/

/-- A family of spectra measured under collision conditions.  The type itself
makes no assumption that all conditions uniquely identify one molecule. -/
structure MultiEnergyObservation (n : ℕ) where
  spectrumAt : CollisionCondition → Spectrum n

namespace MultiEnergyObservation

variable {n : ℕ}

@[simp] theorem spectrumAt_apply (O : MultiEnergyObservation n)
    (cond : CollisionCondition) : O.spectrumAt cond = O.spectrumAt cond := rfl

end MultiEnergyObservation

/-! ## Structural admissibility -/

/-- The exact structural guarantees currently formalized for a physical finite
fragmentation model. -/
def IsStructurallyAdmissible {n : ℕ}
    (M : FiniteValuedFragmentationModel n) : Prop :=
  M.valuedDag.toDAG.IsDAG ∧
  IsSoftAssignment M.assignment ∧
  ∀ (cond : CollisionCondition) (u v : Fin n),
    (M.grammarAt cond).weight u v ≠ 0 →
      M.valuedDag.massOf v < M.valuedDag.massOf u

/-- Every `FiniteValuedFragmentationModel` is structurally admissible by the
proof fields and inherited theorems of its component owners. -/
theorem finiteValuedFragmentationModel_structurallyAdmissible
    {n : ℕ} (M : FiniteValuedFragmentationModel n) :
    IsStructurallyAdmissible M := by
  refine ⟨M.dag_isDAG, M.assignment_soft, ?_⟩
  intro cond u v h
  exact M.grammarAt_mass_decreases cond h

/-- A reconstructor whose codomain is the certified physical model carrier. -/
abbrev CertifiedReconstructor (Obs : Type*) (n : ℕ) :=
  Obs → FiniteValuedFragmentationModel n

/-- Structural admissibility is preserved automatically by any certified
reconstructor, independently of how that reconstructor is implemented. -/
theorem CertifiedReconstructor.output_structurallyAdmissible
    {Obs : Type*} {n : ℕ} (R : CertifiedReconstructor Obs n) (obs : Obs) :
    IsStructurallyAdmissible (R obs) :=
  finiteValuedFragmentationModel_structurallyAdmissible (R obs)

/-- Multi-energy reconstruction uses one certified output carrier for the whole
condition-indexed observation family. -/
abbrev MultiEnergyReconstructor (n : ℕ) :=
  MultiEnergyObservation n → FiniteValuedFragmentationModel n

/-- Every output of a multi-energy reconstructor inherits the same structural
assurance theorem. -/
theorem MultiEnergyReconstructor.output_structurallyAdmissible
    {n : ℕ} (R : MultiEnergyReconstructor n) (obs : MultiEnergyObservation n) :
    IsStructurallyAdmissible (R obs) :=
  finiteValuedFragmentationModel_structurallyAdmissible (R obs)

/-! ## Forward/inverse systems and cycle consistency -/

/-- Generic forward/inverse pair.  `reconstruct` is the inverse-problem map and
`simulate` is the forward map. -/
structure ForwardInverseSystem (SpectrumLike StructureLike : Type*) where
  reconstruct : SpectrumLike → StructureLike
  simulate : StructureLike → SpectrumLike

namespace ForwardInverseSystem

variable {SpectrumLike StructureLike : Type*}

/-- Exact spectrum-side cycle consistency: simulate after reconstruct is the
identity on spectra. -/
def SpectrumCycleConsistent
    (F : ForwardInverseSystem SpectrumLike StructureLike) : Prop :=
  Function.LeftInverse F.simulate F.reconstruct

/-- Exact structure-side cycle consistency: reconstruct after simulate is the
identity on structures. -/
def StructureCycleConsistent
    (F : ForwardInverseSystem SpectrumLike StructureLike) : Prop :=
  Function.RightInverse F.simulate F.reconstruct

/-- Both cycle identities, packaged without claiming that either identity holds
for a learned model unless supplied as a hypothesis. -/
structure ExactCycleConsistent
    (F : ForwardInverseSystem SpectrumLike StructureLike) : Prop where
  spectrum : F.SpectrumCycleConsistent
  structureSide : F.StructureCycleConsistent

/-- Spectrum round-trip identity extracted from the native `Function.LeftInverse`
contract. -/
theorem spectrum_roundTrip
    (F : ForwardInverseSystem SpectrumLike StructureLike)
    (h : F.SpectrumCycleConsistent) (s : SpectrumLike) :
    F.simulate (F.reconstruct s) = s :=
  h s

/-- Structure round-trip identity extracted from the native
`Function.RightInverse` contract. -/
theorem structure_roundTrip
    (F : ForwardInverseSystem SpectrumLike StructureLike)
    (h : F.StructureCycleConsistent) (m : StructureLike) :
    F.reconstruct (F.simulate m) = m :=
  h m

section Residual

variable [NormedAddCommGroup SpectrumLike]

/-- Norm residual of the spectrum-side reconstruction/simulation cycle. -/
def spectrumCycleResidual
    (F : ForwardInverseSystem SpectrumLike StructureLike)
    (s : SpectrumLike) : ℝ :=
  ‖F.simulate (F.reconstruct s) - s‖

/-- Exact cycle consistency forces zero spectrum reconstruction residual. -/
theorem spectrumCycleResidual_eq_zero
    (F : ForwardInverseSystem SpectrumLike StructureLike)
    (h : F.SpectrumCycleConsistent) (s : SpectrumLike) :
    F.spectrumCycleResidual s = 0 := by
  rw [spectrumCycleResidual, h s]
  simp

end Residual

end ForwardInverseSystem

/-! ## Certified inverse pipeline -/

/-- A generic observation-to-model reconstruction paired with a forward
simulator back into the observation space.  Certification concerns the output
carrier; cycle consistency is a separate property. -/
structure CertifiedInversePipeline (Obs : Type*) (n : ℕ) where
  reconstruct : CertifiedReconstructor Obs n
  simulate : FiniteValuedFragmentationModel n → Obs

namespace CertifiedInversePipeline

variable {Obs : Type*} {n : ℕ}

/-- Underlying generic forward/inverse system. -/
def toForwardInverseSystem (P : CertifiedInversePipeline Obs n) :
    ForwardInverseSystem Obs (FiniteValuedFragmentationModel n) where
  reconstruct := P.reconstruct
  simulate := P.simulate

/-- Every reconstructed output is structurally admissible, without any cycle
consistency hypothesis. -/
theorem reconstructed_structurallyAdmissible
    (P : CertifiedInversePipeline Obs n) (obs : Obs) :
    IsStructurallyAdmissible (P.reconstruct obs) :=
  P.reconstruct.output_structurallyAdmissible obs

/-- If the pipeline is exactly spectrum-cycle-consistent, the observation
round-trip is exact. -/
theorem observation_roundTrip
    (P : CertifiedInversePipeline Obs n)
    (h : P.toForwardInverseSystem.SpectrumCycleConsistent) (obs : Obs) :
    P.simulate (P.reconstruct obs) = obs :=
  h obs

end CertifiedInversePipeline

end InfoGeometry.MassSpectrometry
