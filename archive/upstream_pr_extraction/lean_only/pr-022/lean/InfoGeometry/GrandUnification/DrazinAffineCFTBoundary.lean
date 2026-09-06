import InfoGeometry.Singular.MoorePenrose
import InfoGeometry.Singular.Drazin
import InfoGeometry.Clifford.ClNN
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

/-!
# InfoGeometry.GrandUnification.DrazinAffineCFTBoundary

Witness-gated CFT boundary enhancement for the existing Drazin, Moore--Penrose,
split-Clifford, and affine-Virasoro lanes.

This file does not assert that singular generalized-inverse data automatically
produce a boundary CFT.  It records the theorem-safe bridge shape:

* Moore--Penrose data provide metric support;
* Drazin data provide spectral/core support;
* their mismatch may be read as chiral-anomaly data when supplied;
* a finite split-Clifford host may model the finite boundary residue;
* an affine-current/Virasoro bridge supplies the Sugawara readout;
* Cardy entropy is available only when explicit CFT/Cardy hypotheses are
  supplied.

The concrete central-charge arithmetic for the level-one `so(4,4)` / `D₄`
case lives in `OperatorAlgebra.AffineVirasoroBridge`.
-/

noncomputable section

namespace InfoGeometry.GrandUnification

/--
Drazin--Affine CFT boundary packet.

This packet connects:

* Moore--Penrose metric support data;
* Drazin spectral/core support data;
* finite split Clifford boundary residue data;
* affine-current promotion;
* Virasoro/Sugawara central-charge readout;
* optional Cardy entropy readout.

It does not assert that Drazin data automatically produce a CFT.  Every
physical interpretation is carried by explicit witnesses.
-/
structure DrazinAffineCFTBoundaryPacket where
  /-- Algebra or operator host for the singular problem. -/
  OperatorAlgebra : Type 0

  /-- Moore--Penrose inverse/support data. -/
  MoorePenroseData : Type 0

  /-- Drazin inverse/projector data. -/
  DrazinData : Type 0

  /-- Metric support projector, morally `P_MP`. -/
  MetricSupportProjector : Type 0

  /-- Spectral/core projector, morally `P_D`. -/
  DrazinCoreProjector : Type 0

  /-- Chiral anomaly / mismatch data, morally `[P_MP, P_D]`. -/
  ChiralAnomalyData : Type 0

  /--
  Witness that the Drazin projector isolates the intended stable/core sector.
  This is not automatic from the Drazin equations alone.
  -/
  drazinCoreSectorWitness : Type 0

  /--
  Witness that the complementary/singular sector is physically interpreted as a
  boundary or defect residue.
  -/
  boundaryResidueWitness : Type 0

  /-- Finite split Clifford host, e.g. `Cl(4,4)` or `Cl(n,n)`. -/
  SplitCliffordHost : Type 0

  /-- Witness for the finite split Clifford matrix realization. -/
  splitCliffordMatrixWitness : Type 0

  /--
  Optional full `O(4,4)` / `Pin(4,4)` finite symmetry datum.

  Do not interpret this as merely `SO(4,4)` / `Spin(4,4)` when
  CPT/reflection data are claimed: odd reflection components live in the full
  orthogonal/Pin lane.
  -/
  SplitOrthogonalSymmetry : Type 0

  /--
  Guard: CPT/reflection-sensitive claims require the full `O`/`Pin` lane, not
  only `SO`/`Spin` even-sector symmetry.
  -/
  noSOOnlyCPTWitness : Type 0

  /--
  Optional split-octonion/triality model witness.
  This prevents identifying split octonions with the Clifford algebra itself.
  -/
  splitOctonionTrialityWitness : Type 0

  /-- Finite current algebra, e.g. `so(4,4)`. -/
  FiniteCurrentAlgebra : Type 0

  /-- Affine current algebra / Kac--Moody extension. -/
  AffineCurrentAlgebra : Type 0

  /-- Virasoro algebra data. -/
  VirasoroData : Type 0

  /-- Sugawara central-charge readout. -/
  SugawaraCentralCharge : Type 0

  /--
  Witness that the affine-current/Virasoro bridge is supplied.
  This should correspond to `AffineVirasoroBridgeDatum` in concrete models.
  -/
  affineVirasoroBridgeWitness : Type 0

  /--
  Witness for the central-charge calibration, e.g.
  `c = k * dim(g) / (k + h∨)`.
  -/
  centralChargeCalibrationWitness : Type 0

  /--
  Optional Cardy entropy readout.
  Valid only after CFT/Cardy hypotheses are supplied.
  -/
  CardyEntropyReadout : Type 0

  /-- Witness that Cardy hypotheses hold for the readout. -/
  cardyHypothesesWitness : Type 0

  /--
  Guard: Cardy entropy is not automatic from Moore--Penrose, Drazin, or finite
  Clifford data alone.
  -/
  noAutomaticCardyWitness : Type 0

  /--
  Guard: Moore--Penrose generalized-inverse data are not, by themselves, a
  theorem about resolving singular spacetime metrics.
  -/
  noAutomaticSpacetimeSingularityResolutionWitness : Type 0

  /--
  Guard: Drazin projector data are not, by themselves, a theorem that a
  physical bulk sector has been filtered and a boundary sector isolated.
  -/
  noAutomaticBulkBoundaryIsolationWitness : Type 0

/-- Owner target for Drazin--Affine CFT boundary data. -/
def DrazinAffineCFTBoundaryTarget : Prop :=
  Nonempty DrazinAffineCFTBoundaryPacket

/-- A supplied packet constructs the owner target. -/
theorem constructDrazinAffineCFTBoundaryTarget
    (P : DrazinAffineCFTBoundaryPacket) :
    DrazinAffineCFTBoundaryTarget := by
  exact ⟨P⟩

namespace DrazinAffineCFTBoundaryPacket

/--
The packet explicitly carries the witness that Moore--Penrose support data are
not being promoted to an automatic spacetime-singularity-resolution theorem.
-/
def moorePenroseSpacetimeResolutionGuard
    (P : DrazinAffineCFTBoundaryPacket) : Type 0 :=
  P.noAutomaticSpacetimeSingularityResolutionWitness

@[simp] theorem moorePenroseSpacetimeResolutionGuard_eq
    (P : DrazinAffineCFTBoundaryPacket) :
    P.moorePenroseSpacetimeResolutionGuard =
      P.noAutomaticSpacetimeSingularityResolutionWitness :=
  rfl

/--
The packet explicitly carries the witness that Drazin core-projector data are
not being promoted to an automatic bulk/boundary separation theorem.
-/
def drazinBulkBoundaryIsolationGuard
    (P : DrazinAffineCFTBoundaryPacket) : Type 0 :=
  P.noAutomaticBulkBoundaryIsolationWitness

@[simp] theorem drazinBulkBoundaryIsolationGuard_eq
    (P : DrazinAffineCFTBoundaryPacket) :
    P.drazinBulkBoundaryIsolationGuard =
      P.noAutomaticBulkBoundaryIsolationWitness :=
  rfl

/--
The packet explicitly carries the witness that Cardy entropy is gated by
separate CFT/Cardy hypotheses.
-/
def cardyAutomaticityGuard
    (P : DrazinAffineCFTBoundaryPacket) : Type 0 :=
  P.noAutomaticCardyWitness

@[simp] theorem cardyAutomaticityGuard_eq
    (P : DrazinAffineCFTBoundaryPacket) :
    P.cardyAutomaticityGuard = P.noAutomaticCardyWitness :=
  rfl

/--
The packet explicitly carries the witness that CPT/reflection-sensitive claims
are not being routed through an `SO`/`Spin`-only even-sector symmetry.
-/
def soOnlyCPTGuard
    (P : DrazinAffineCFTBoundaryPacket) : Type 0 :=
  P.noSOOnlyCPTWitness

@[simp] theorem soOnlyCPTGuard_eq
    (P : DrazinAffineCFTBoundaryPacket) :
    P.soOnlyCPTGuard = P.noSOOnlyCPTWitness :=
  rfl

end DrazinAffineCFTBoundaryPacket

/--
Re-export the theorem-safe level-one `so(4,4)` / `D₄` Sugawara calibration
from the affine-Virasoro owner lane.
-/
theorem sugawaraCentralCharge_so44_levelOne :
    InfoGeometry.OperatorAlgebra.AffineVirasoroBridge.sugawaraCentralCharge
        1 28 6 = 4 :=
  InfoGeometry.OperatorAlgebra.AffineVirasoroBridge.sugawaraCentralCharge_so44_levelOne

end InfoGeometry.GrandUnification
