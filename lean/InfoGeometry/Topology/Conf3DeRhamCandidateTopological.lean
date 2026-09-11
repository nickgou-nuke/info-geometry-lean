import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.Conf3ArnoldNormalizationTopological
import InfoGeometry.External.Auto.NonIsoConf3DeRhamCooperad
import InfoGeometry.External.Auto.NonIsoConf3DeRhamCohomologyFormula

/-!
# Topological `Conf₃` de Rham candidate packet

This file packages the already-normalized finite triple data together with the
existing finite de Rham/cooperad branch data.  It stays on the candidate side:
it records the branch choice and its formal rank readout, but it does not claim
that the analytic de Rham computation of the configuration space has been
closed in Lean.
-/

namespace InfoGeometry.Topology.Conf3DeRhamCandidateTopological

noncomputable section

variable {D : ℕ}

/-- Finite triples normalized to `0,1,∞` on the topological candidate side. -/
abbrev Conf3FiniteTriple :=
  InfoGeometry.Topology.MobiusFiniteTripleNormalizationTopological.FiniteTriple

/-- The combined normalized-triple and de Rham-candidate packet. -/
abbrev Conf3DeRhamCandidatePacket (D : ℕ) :=
  Conf3FiniteTriple × NonIsoConf3DeRhamCooperad.ConcreteDeRhamCooperadData D

instance conf3DeRhamCandidatePacketTopologicalSpace (D : ℕ) :
    TopologicalSpace (Conf3DeRhamCandidatePacket D) := ⊥

instance conf3DeRhamCandidatePacketDiscreteTopology (D : ℕ) :
    DiscreteTopology (Conf3DeRhamCandidatePacket D) := ⟨rfl⟩

/-- The selected finite de Rham branch for the packet. -/
def conf3DeRhamBranchPoincare
    (D : ℕ) (p : Conf3DeRhamCandidatePacket D) : Polynomial ℤ :=
  NonIsoConf3DeRhamCohomologyFormula.deRhamBranchPoincare D p.2

/-- The packet rank readout at `t = 1`. -/
def conf3DeRhamBranchRank
    (D : ℕ) (p : Conf3DeRhamCandidatePacket D) : ℤ :=
  Polynomial.eval (1 : ℤ) (conf3DeRhamBranchPoincare D p)

/-- The packet is continuous because the topology is discrete. -/
theorem continuous_conf3DeRhamCandidatePacket
    (D : ℕ) :
    Continuous (fun p : Conf3DeRhamCandidatePacket D => p) := by
  exact continuous_of_discreteTopology

/-- The packet is locally constant because the topology is discrete. -/
theorem isLocallyConstant_conf3DeRhamCandidatePacket
    (D : ℕ) :
    IsLocallyConstant (fun p : Conf3DeRhamCandidatePacket D => p) := by
  exact IsLocallyConstant.of_discrete (f := fun p : Conf3DeRhamCandidatePacket D => p)

/-- Product/Leray branch readout at the normalized Conf3 packet. -/
theorem conf3DeRhamBranchRank_product
    (D : ℕ) (p : Conf3DeRhamCandidatePacket D)
    (hchoice : p.2.relationChoice =
      NonIsoConf3DeRhamCooperad.ModelChoice.productLeray) :
    conf3DeRhamBranchRank D p = 32 := by
  rw [conf3DeRhamBranchRank, conf3DeRhamBranchPoincare]
  rw [NonIsoConf3DeRhamCohomologyFormula.deRhamBranchPoincare_product_formula
    (D := D) p.2 hchoice]
  exact NonIsoConf3DeRhamCohomologyFormula.lightConeProduct_rank_at_one D

/-- OS-alpha branch readout at the normalized Conf3 packet. -/
theorem conf3DeRhamBranchRank_os
    (D : ℕ) (p : Conf3DeRhamCandidatePacket D)
    (hchoice : p.2.relationChoice =
      NonIsoConf3DeRhamCooperad.ModelChoice.osAlpha) :
    conf3DeRhamBranchRank D p = 24 := by
  rw [conf3DeRhamBranchRank, conf3DeRhamBranchPoincare]
  rw [NonIsoConf3DeRhamCohomologyFormula.deRhamBranchPoincare_os_formula
    (D := D) p.2 hchoice]
  exact NonIsoConf3DeRhamCohomologyFormula.lightConeOS_rank_at_one D

/-- The packet keeps the normalization and finite branch side-by-side. -/
def normalizedConf3DeRhamPacket
    (D : ℕ)
    (p : Conf3FiniteTriple)
    (data : NonIsoConf3DeRhamCooperad.ConcreteDeRhamCooperadData D) :
    Conf3DeRhamCandidatePacket D :=
  (p, data)

end

end InfoGeometry.Topology.Conf3DeRhamCandidateTopological
