import InfoGeometry.GromovWittenErlangen.GWCanonicalCountRayBridge
import InfoGeometry.GromovWittenErlangen.DrazinLocalization
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.GromovWittenErlangen.ProjectiveCountProbabilityDrazinBridge

Repo-native bridge from GW projective count rays through probability gauges and
operator surprisal/modular readouts to the existing Drazin localization lane.

This file does not introduce a new probability ontology.  It reuses the
existing corridor:

```text
RelativeCounts
  → countRay
  → gaugeSectionFinProb
  → density/surprisal and modular-potential operators
  → GWDrazinLocalizationPacket / DrazinGromovWittenLocalizationBridge
```

No virtual localization theorem, Moore-Penrose theorem, Frobenius theorem,
Drazin existence theorem, edge-Euler readout theorem, or residue/singularity
identification theorem is proved here.
-/

noncomputable section

namespace InfoGeometry.GromovWittenErlangen

open InfoGeometry.Canonical.RelativePotentialCountBridge
open InfoGeometry.Canonical.RelativeSurprisalOperatorLift
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.MaxEnt.JaynesInfoStatMech.ThermalDiagonal

/--
GW localization graph with a canonical finite projective-count/probability
readout.

This is the repo-native L0-L4 owner bridge.  It consumes
`GWCanonicalCountRayBridge`, whose derived objects are the existing count rays,
probability gauge sections, density matrices, surprisal operators, and
projective modular count profiles.
-/
@[rep_depth operator]
abbrev GWProjectiveCountProbabilityBridge
    (n : ℕ) [Nonempty (Fin n)]
    (G T Target Coeff : Type*) :=
  GWCanonicalCountRayBridge n G T Target Coeff

namespace GWProjectiveCountProbabilityBridge

variable {n : ℕ} [Nonempty (Fin n)]
variable {G T Target Coeff : Type*}
variable (B : GWProjectiveCountProbabilityBridge n G T Target Coeff)

/-- Probability gauge of the localized count ray. -/
def stateFinProb : InfoGeometry.FinProb (Fin n) :=
  GWCanonicalCountRayBridge.stateFinProb B

/-- Density matrix of the localized probability gauge. -/
def stateDensityMatrix : FinMat n :=
  GWCanonicalCountRayBridge.stateDensityMatrix B

/-- Surprisal operator of the localized probability gauge. -/
def stateSurprisalOperator : FinMat n :=
  GWCanonicalCountRayBridge.stateSurprisalOperator B

/-- Projective count Hamiltonian profile of the localized/reference count pair. -/
def projectiveHamiltonianProfile : Fin n → ℝ :=
  GWCanonicalCountRayBridge.projectiveHamiltonianProfile B

/-- Modular-potential operator attached to the raw count representative pair. -/
def relativeCountModularPotentialOperator : FinMat n :=
  InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeCountModularPotentialOperator
    B.counts B.ref

/-- Density diagonal entries are the normalized count masses. -/
theorem stateDensityMatrix_diag
    (i : Fin n) :
    stateDensityMatrix B i i =
      B.counts i /
        countMass B.counts B.counts_pos := by
  exact GWCanonicalCountRayBridge.stateDensityMatrix_diag B i

/-- Entropy of the probability gauge is expectation of the surprisal operator. -/
theorem entropy_eq_diagonalExpectation_stateSurprisalOperator :
    InfoGeometry.entropy (stateFinProb B) =
      diagonalExpectation (stateFinProb B) (stateSurprisalOperator B) := by
  exact GWCanonicalCountRayBridge.entropy_eq_diagonalExpectation_stateSurprisalOperator B

/--
The projective count Hamiltonian is the relative modular potential of the
canonical count rays.
-/
theorem projectiveHamiltonianProfile_eq_relativeModularPotential
    (i : Fin n) :
    projectiveHamiltonianProfile B i =
      relativeModularPotential
        (α := Fin n)
        (GWCanonicalCountRayBridge.stateRay (n := n) B)
        (GWCanonicalCountRayBridge.referenceRay (n := n) B) i := by
  exact GWCanonicalCountRayBridge.projectiveHamiltonianProfile_eq_relativeModularPotential B i

end GWProjectiveCountProbabilityBridge

/--
Drazin localization attached to the canonical GW projective-count/probability
readout.

This is the witness-gated L5 attachment: the existing Drazin localization edge
data is calibrated as a readout of the projective count/probability/operator
lane.
-/
@[rep_depth operator]
structure GWProjectiveCountDrazinBridge
    (n : ℕ) [Nonempty (Fin n)]
    (G T Target Coeff Algebra : Type*) [Ring Algebra] [StarRing Algebra] where
  /-- Count/probability/operator readout of the GW localization graph. -/
  projectiveProbability :
    GWProjectiveCountProbabilityBridge n G T Target Coeff

  /-- Existing Drazin/GW localization bridge. -/
  drazin :
    DrazinGromovWittenLocalizationBridge G T Target Coeff Algebra

  /--
  The Drazin localization packet and the projective-count packet refer to the
  same GW localization graph.
  -/
  localization_packet_eq :
    drazin.drazinLocalization.virtualLocalization =
      projectiveProbability.projectiveCounts.localization

namespace GWProjectiveCountDrazinBridge

variable {n : ℕ} [Nonempty (Fin n)]
variable {G T Target Coeff Algebra : Type*} [Ring Algebra] [StarRing Algebra]
variable (B : GWProjectiveCountDrazinBridge n G T Target Coeff Algebra)

/-- The Drazin and projective-count packets use the same localization graph. -/
theorem localization_packet_matches_projectiveCounts :
    B.drazin.drazinLocalization.virtualLocalization =
      B.projectiveProbability.projectiveCounts.localization :=
  B.localization_packet_eq

/-- Edge Drazin residues annihilate the corresponding regular inverse on the left. -/
theorem edgeResidue_mul_regularInverse
    (e : B.drazin.drazinLocalization.virtualLocalization.graph.Edge) :
    B.drazin.edgeLocalizedDrazinResidue e *
        B.drazin.edgeLocalizedRegularInverse e = 0 :=
  B.drazin.edgeResidue_mul_regularInverse e

/-- Entropy of the projective probability gauge is expectation of surprisal. -/
theorem entropy_eq_diagonalExpectation_stateSurprisalOperator :
    InfoGeometry.entropy
        (GWProjectiveCountProbabilityBridge.stateFinProb B.projectiveProbability) =
      diagonalExpectation
        (GWProjectiveCountProbabilityBridge.stateFinProb B.projectiveProbability)
        (GWProjectiveCountProbabilityBridge.stateSurprisalOperator
          B.projectiveProbability) :=
  GWProjectiveCountProbabilityBridge.entropy_eq_diagonalExpectation_stateSurprisalOperator
    B.projectiveProbability

end GWProjectiveCountDrazinBridge

end InfoGeometry.GromovWittenErlangen
