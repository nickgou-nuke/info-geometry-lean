/-
InfoGeometry/OperatorAlgebra/AnomalyTubuleStability.lean

Anomaly and topological readout sockets for stable defect/tubule sectors.

The local Clifford/Drazin/Krein algebra may expose defect directions, but a
stable global object requires an invariant readout: an index, residue, cyclic
cocycle, determinant-line charge, bordism/anomaly class, or equivalent
certificate.  This file records that distinction without asserting a concrete
analytic classification theorem.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.CliffordAtomsZ2n
import InfoGeometry.OperatorAlgebra.DrazinRepresentedSplit

noncomputable section

namespace InfoGeometry.OperatorAlgebra.AnomalyTubuleStability

/-! ## 1. Generic anomaly readouts -/

/--
A generic anomaly readout.

For a symmetry variation `delta` and a readout backend `tau`, the anomaly is
the readout of the variation:

`A_delta x = tau (delta x)`.
-/
structure AnomalyReadout
    (Op : Type*) [Ring Op] where
  /-- Symmetry variation or infinitesimal transformation. -/
  symmetryVariation : Op → Op

  /-- Regularized trace, index, residue, weight, determinant variation, etc. -/
  readout : Op → ℝ

  /-- Certificate that the readout has a nonzero anomaly in the intended model. -/
  nonvanishingCertificate : Prop

namespace AnomalyReadout

variable {Op : Type*} [Ring Op]
variable (A : AnomalyReadout Op)

/-- The anomaly functional attached to the readout. -/
def anomaly
    (x : Op) : ℝ :=
  A.readout (A.symmetryVariation x)

/-- Re-export the definitional anomaly law. -/
theorem anomaly_eq_readout_variation
    (x : Op) :
    A.anomaly x = A.readout (A.symmetryVariation x) :=
  rfl

end AnomalyReadout

/-! ## 2. Anomalous flow witnesses -/

/--
A driven anomalous flow witness.

This records the exact qualification that a local defect becomes stable only
after the chosen anomaly/index readout detects it and remains meaningful under
the admissible flow.
-/
structure AnomalousFlowWitness
    (Op Index : Type*) [Ring Op] where
  /-- Admissible driven flow, for example modular or Bogoliubov evolution. -/
  flow : ℝ → Op → Op

  /-- Local defect predicate. -/
  defect : Op → Prop

  /-- Anomaly, index, residue, or global obstruction readout. -/
  anomaly : Op → Index

  /-- Flat/inertial-frame predicate. -/
  flatFrame : Op → Prop

  /-- Flat frames carry the reference anomaly. -/
  flat_anomaly_zero :
    ∀ x : Op, flatFrame x → anomaly x = anomaly 0

  /-- Defect membership is invariant under the admissible flow. -/
  defect_flow_invariant :
    ∀ (t : ℝ) (x : Op), defect x → defect (flow t x)

  /-- Defects are detected by a non-reference anomaly. -/
  anomaly_detects_defect :
    ∀ x : Op, defect x → anomaly x ≠ anomaly 0

namespace AnomalousFlowWitness

variable {Op Index : Type*} [Ring Op]
variable (W : AnomalousFlowWitness Op Index)

/-- Re-export flow invariance of the defect predicate. -/
theorem defect_stays_defect
    (t : ℝ)
    {x : Op}
    (hx : W.defect x) :
    W.defect (W.flow t x) :=
  W.defect_flow_invariant t x hx

/-- Re-export anomaly detection of a defect. -/
theorem defect_has_nontrivial_anomaly
    {x : Op}
    (hx : W.defect x) :
    W.anomaly x ≠ W.anomaly 0 :=
  W.anomaly_detects_defect x hx

end AnomalousFlowWitness

/-! ## 3. Specialized anomaly sockets -/

/--
Chiral anomaly datum.

This records the objects usually feeding an index/supertrace/cyclic-cocycle
obstruction without forcing a specific heat-kernel or spectral-triple backend.
-/
structure ChiralAnomalyDatum
    (Op : Type*) [Ring Op] where
  /-- Chiral grading. -/
  chi : Op

  /-- Dirac/BdG/spectral generator. -/
  D : Op

  /-- Real-valued backend, for example a regularized supertrace. -/
  backend : Op → ℝ

  /-- Cyclic-cocycle style backend, arity left abstract as a list. -/
  cyclicCocycle : List Op → ℂ

  /-- Integer index readout. -/
  indexReadout : ℤ

  /-- Certificate that this data carries the intended chiral anomaly. -/
  anomalyCertificate : Prop

/--
Weyl/conformal anomaly datum.

This records the failure of a regularized determinant, zeta residue, heat
coefficient, or weight/trace backend to remain invariant under a conformal
variation.
-/
structure WeylAnomalyDatum
    (Op : Type*) [Ring Op] where
  /-- Dirac/spectral generator. -/
  D : Op

  /-- Conformal or Weyl variation. -/
  conformalVariation : Op → Op

  /-- Zeta/residue-style backend. -/
  zetaResidue : Op → ℂ

  /-- Determinant variation readout. -/
  determinantVariation : ℝ

  /-- Certificate that this data carries the intended Weyl anomaly. -/
  anomalyCertificate : Prop

/-! ## 4. DIII interacting invariant socket -/

/--
Free-to-interacting DIII invariant bridge.

The local `Z2^4` Clifford hypercube labels Cartan sectors.  The interacting
DIII stacking invariant is cyclic and is represented here by `ZMod 16`.
-/
structure DIIIInteractionInvariant where
  /-- Free-fermion winding/integer index. -/
  nuFree : ℤ

  /-- Interacting cyclic reduction. -/
  nuInteracting : ZMod 16

  /-- Reduction law from the free integer invariant to the cyclic class. -/
  reduction_law :
    nuInteracting = (nuFree : ZMod 16)

/--
Bridge from four local Clifford bits to a cyclic DIII interacting readout.

This is intentionally proof-carrying: it does not identify `Z2^4` with `Z16`.
-/
structure CliffordToDIIIInteractionBridge where
  /-- Local Cartan/Clifford sector label. -/
  localSector :
    InfoGeometry.OperatorAlgebra.CliffordAtomsZ2n.Z2FourCharge

  /-- Global cyclic interacting invariant. -/
  globalInvariant : DIIIInteractionInvariant

  /-- Certificate relating this local sector to the chosen global invariant. -/
  compatibility : Prop

/-! ## 5. Tubule stability as global obstruction -/

/--
A stable tubule/defect sector datum.

The point of this socket is the strict qualification: a local defect becomes a
stable global object only after a nonzero anomaly/topological readout certifies
that it cannot be removed by local gauge choices.
-/
structure TubuleStabilityDatum
    (Op : Type*) [Ring Op] where
  /-- Local defect locus: Drazin nil branch, isotropic cone shadow, tear, etc. -/
  defect : Set Op

  /-- Energy or action readout. -/
  energy : Op → ℝ

  /-- Anomaly/global obstruction readout. -/
  anomaly : AnomalyReadout Op

  /-- Model-specific topological sector type. -/
  topologicalSector : Type*

  /-- Sector readout for configurations/operators. -/
  sectorReadout : Op → topologicalSector

  /-- Chosen nontrivial sector predicate. -/
  isNontrivialSector : topologicalSector → Prop

  /--
  Stability certificate.

  Intended theorem target: nonzero anomaly/topological readout rules out a
  flat trivial representative and forces a stable nonlinear representative.
  -/
  stableNontrivialSector : Prop

namespace TubuleStabilityDatum

variable {Op : Type*} [Ring Op]
variable (T : TubuleStabilityDatum Op)

/-- A configuration lies in a nontrivial topological sector. -/
def InNontrivialSector
    (x : Op) : Prop :=
  T.isNontrivialSector (T.sectorReadout x)

/--
Re-export the stability certificate: this is where the tubule metaphor becomes
a theorem target in concrete models.
-/
theorem stable_of_nonzero_global_readout
    (h : T.stableNontrivialSector) :
    T.stableNontrivialSector :=
  h

end TubuleStabilityDatum

end InfoGeometry.OperatorAlgebra.AnomalyTubuleStability
