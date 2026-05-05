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

No virtual localization theorem, Moore-Penrose theorem, Frobenius theorem, or
Drazin existence theorem is proved here.  The connection to edge Euler weights
and residues is witness-gated.
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
structure GWProjectiveCountProbabilityBridge
    (n : ℕ) [Nonempty (Fin n)]
    (G T Target Coeff : Type*) where
  /-- Canonical finite count-ray bridge for the GW localization packet. -/
  canonical :
    GWCanonicalCountRayBridge n G T Target Coeff

  /--
  Law saying the probability gauge section is the intended normalized readout
  of the GW localization count shadow.
  -/
  probabilityGaugeLaw :
    Prop

  /-- Certificate for the probability gauge law. -/
  probabilityGauge_valid :
    probabilityGaugeLaw

namespace GWProjectiveCountProbabilityBridge

variable {n : ℕ} [Nonempty (Fin n)]
variable {G T Target Coeff : Type*}
variable (B : GWProjectiveCountProbabilityBridge n G T Target Coeff)

/-- The GW localization-to-count shadow law is available. -/
theorem countShadow_holds :
    B.canonical.projectiveCounts.countShadowLaw :=
  B.canonical.countShadow_holds

/-- The finite carrier realizes the GW count shadow. -/
theorem finiteCarrierShadow_holds :
    B.canonical.finiteCarrierShadowLaw :=
  B.canonical.finiteCarrierShadow_holds

/-- The supplied probability-gauge law is available. -/
theorem probabilityGauge_holds :
    B.probabilityGaugeLaw :=
  B.probabilityGauge_valid

/-- Probability gauge of the localized count ray. -/
def stateFinProb : InfoGeometry.FinProb (Fin n) :=
  B.canonical.stateFinProb

/-- Density matrix of the localized probability gauge. -/
def stateDensityMatrix : FinMat n :=
  B.canonical.stateDensityMatrix

/-- Surprisal operator of the localized probability gauge. -/
def stateSurprisalOperator : FinMat n :=
  B.canonical.stateSurprisalOperator

/-- Projective count Hamiltonian profile of the localized/reference count pair. -/
def projectiveHamiltonianProfile : Fin n → ℝ :=
  B.canonical.projectiveHamiltonianProfile

/-- Modular-potential operator attached to the raw count representative pair. -/
def relativeCountModularPotentialOperator : FinMat n :=
  InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeCountModularPotentialOperator
    B.canonical.counts B.canonical.ref

/-- Density diagonal entries are the normalized count masses. -/
theorem stateDensityMatrix_diag
    (i : Fin n) :
    B.stateDensityMatrix i i =
      B.canonical.counts i /
        countMass B.canonical.counts B.canonical.counts_pos := by
  exact B.canonical.stateDensityMatrix_diag i

/-- Entropy of the probability gauge is expectation of the surprisal operator. -/
theorem entropy_eq_diagonalExpectation_stateSurprisalOperator :
    InfoGeometry.entropy B.stateFinProb =
      diagonalExpectation B.stateFinProb B.stateSurprisalOperator := by
  exact B.canonical.entropy_eq_diagonalExpectation_stateSurprisalOperator

/--
The projective count Hamiltonian is the relative modular potential of the
canonical count rays.
-/
theorem projectiveHamiltonianProfile_eq_relativeModularPotential
    (i : Fin n) :
    B.projectiveHamiltonianProfile i =
      relativeModularPotential
        (α := Fin n)
        B.canonical.stateRay
        B.canonical.referenceRay i := by
  exact B.canonical.projectiveHamiltonianProfile_eq_relativeModularPotential i

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
    (G T Target Coeff Algebra : Type*) [Ring Algebra] where
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
      projectiveProbability.canonical.projectiveCounts.localization

  /--
  Witness that edge Euler weights are read from the projective count/probability
  lane.
  -/
  edgeEulerWeight_eq_projectiveCountReadout :
    Prop

  /-- Certificate for the edge Euler/projective-count readout law. -/
  edgeEulerWeight_eq_projectiveCountReadout_valid :
    edgeEulerWeight_eq_projectiveCountReadout

  /--
  Witness that Drazin residues are the operator-algebraic readout of singular
  or degenerate projective count strata.
  -/
  drazinResidue_eq_projectiveSingularityReadout :
    Prop

  /-- Certificate for the Drazin residue/projective-singularity law. -/
  drazinResidue_eq_projectiveSingularityReadout_valid :
    drazinResidue_eq_projectiveSingularityReadout

namespace GWProjectiveCountDrazinBridge

variable {n : ℕ} [Nonempty (Fin n)]
variable {G T Target Coeff Algebra : Type*} [Ring Algebra]
variable (B : GWProjectiveCountDrazinBridge n G T Target Coeff Algebra)

/-- The underlying GW count shadow law is available. -/
theorem countShadow_holds :
    B.projectiveProbability.canonical.projectiveCounts.countShadowLaw :=
  B.projectiveProbability.countShadow_holds

/-- The probability gauge law is available. -/
theorem probabilityGauge_holds :
    B.projectiveProbability.probabilityGaugeLaw :=
  B.projectiveProbability.probabilityGauge_holds

/-- The Drazin and projective-count packets use the same localization graph. -/
theorem localization_packet_matches_projectiveCounts :
    B.drazin.drazinLocalization.virtualLocalization =
      B.projectiveProbability.canonical.projectiveCounts.localization :=
  B.localization_packet_eq

/-- The supplied edge Euler/projective-count readout law is available. -/
theorem edgeEulerWeight_eq_projectiveCountReadout_holds :
    B.edgeEulerWeight_eq_projectiveCountReadout :=
  B.edgeEulerWeight_eq_projectiveCountReadout_valid

/-- The supplied Drazin residue/projective-singularity law is available. -/
theorem drazinResidue_eq_projectiveSingularityReadout_holds :
    B.drazinResidue_eq_projectiveSingularityReadout :=
  B.drazinResidue_eq_projectiveSingularityReadout_valid

/-- Edge Drazin residues annihilate the corresponding regular inverse on the left. -/
theorem edgeResidue_mul_regularInverse
    (e : B.drazin.drazinLocalization.virtualLocalization.graph.Edge) :
    B.drazin.edgeLocalizedDrazinResidue e *
        B.drazin.edgeLocalizedRegularInverse e = 0 :=
  B.drazin.edgeResidue_mul_regularInverse e

/-- Entropy of the projective probability gauge is expectation of surprisal. -/
theorem entropy_eq_diagonalExpectation_stateSurprisalOperator :
    InfoGeometry.entropy B.projectiveProbability.stateFinProb =
      diagonalExpectation
        B.projectiveProbability.stateFinProb
        B.projectiveProbability.stateSurprisalOperator :=
  B.projectiveProbability.entropy_eq_diagonalExpectation_stateSurprisalOperator

end GWProjectiveCountDrazinBridge

end InfoGeometry.GromovWittenErlangen
