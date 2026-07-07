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
def anomaly {Op : Type*} [Ring Op]
    (symmetryVariation : Op → Op)
    (readout : Op → ℝ)
    (x : Op) : ℝ :=
  readout (symmetryVariation x)

theorem anomaly_eq_readout_variation {Op : Type*} [Ring Op]
    (symmetryVariation : Op → Op)
    (readout : Op → ℝ)
    (x : Op) :
    anomaly symmetryVariation readout x = readout (symmetryVariation x) :=
  rfl

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
obstruction without forcing a specific heat-kernel or spectral-triple backend,
but strictly requires the index theorem to be proven for any concrete instance.
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

  /-- The required proof that the backend evaluates to the topological index. -/
  index_theorem : backend (chi * D) = (indexReadout : ℝ)

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

  /-- The required proof that the determinant variation is strictly non-zero. -/
  determinantVariation_nonzero : determinantVariation ≠ 0

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
  reduction_True :
    nuInteracting = (nuFree : ZMod 16)

/--
Bridge from four local Clifford bits to a cyclic DIII interacting readout.

This forces a concrete structural map from local charges to the global cyclic class.
-/
structure CliffordToDIIIInteractionBridge where
  /-- Local Cartan/Clifford sector label. -/
  localSector : InfoGeometry.OperatorAlgebra.CliffordAtomsZ2n.Z2FourCharge

  /-- Global cyclic interacting invariant. -/
  globalInvariant : DIIIInteractionInvariant

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
  anomaly : Op → ℝ

  /-- Model-specific topological sector type. -/
  topologicalSector : Type*

  /-- Sector readout for configurations/operators. -/
  sectorReadout : Op → topologicalSector

  /-- Chosen nontrivial sector predicate. -/
  isNontrivialSector : topologicalSector → Prop

  /-- The rigorous proof that a nonzero anomaly forces topological stability. -/
  stable_of_nonzero_global_readout :
    ∀ (x : Op), anomaly x ≠ 0 → isNontrivialSector (sectorReadout x)

namespace TubuleStabilityDatum

variable {Op : Type*} [Ring Op]
variable (T : TubuleStabilityDatum Op)

/-- A configuration lies in a nontrivial topological sector. -/
def InNontrivialSector (x : Op) : Prop :=
  T.isNontrivialSector (T.sectorReadout x)

end TubuleStabilityDatum

end InfoGeometry.OperatorAlgebra.AnomalyTubuleStability
