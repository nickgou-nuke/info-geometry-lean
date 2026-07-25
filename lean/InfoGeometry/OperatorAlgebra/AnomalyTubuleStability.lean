/-
InfoGeometry/OperatorAlgebra/AnomalyTubuleStability.lean

Anomaly and topological readout sockets for stable defect/tubule sectors.

The local Clifford/Drazin/Krein algebra may expose defect directions, but a
stable global object requires an invariant readout: an index, residue, cyclic
cocycle, determinant-line charge, bordism/anomaly class, or equivalent
sector invariant.  This file records that distinction without asserting a concrete
analytic classification theorem.
-/

import Mathlib.Tactic
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

  /-- The readout has a nonzero anomaly in the intended model. -/
  nonvanishing :
    ∃ x : Op,
      readout (symmetryVariation x) ≠ readout (symmetryVariation 0)

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

/-- The stored nonvanishing hypothesis gives a nonzero anomaly. -/
theorem exists_nonzero_anomaly :
    ∃ x : Op, A.anomaly x ≠ A.anomaly 0 := by
  simpa [AnomalyReadout.anomaly] using A.nonvanishing

end AnomalyReadout

/-! ## 2. Anomalous flow data -/

/--
A driven anomalous flow package.

This records the exact qualification that a local defect becomes stable only
after the chosen anomaly/index readout detects it and remains meaningful under
the admissible flow.
-/
structure AnomalousFlowData
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

namespace AnomalousFlowData

variable {Op Index : Type*} [Ring Op]
variable (W : AnomalousFlowData Op Index)

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

/-- A detected defect cannot also be a flat reference-frame point. -/
theorem not_flatFrame_of_defect
    {x : Op}
    (hx : W.defect x) :
    ¬ W.flatFrame x := by
  intro hflat
  exact W.defect_has_nontrivial_anomaly hx (W.flat_anomaly_zero x hflat)

/-- A flat reference-frame point cannot be a detected defect. -/
theorem not_defect_of_flatFrame
    {x : Op}
    (hflat : W.flatFrame x) :
    ¬ W.defect x := by
  intro hx
  exact W.not_flatFrame_of_defect hx hflat

end AnomalousFlowData

/-! ## 3. Specialized anomaly sockets -/

/--
Chiral anomaly structure.

This records the objects usually feeding an index/supertrace/cyclic-cocycle
obstruction without forcing a specific heat-kernel or spectral-triple backend.
-/
structure ChiralAnomaly
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

  /-- Exact index readout for the chosen backend. -/
  backend_chi_mul_D_eq_indexReadout :
    backend (chi * D) = (indexReadout : ℝ)

/--
Weyl/conformal anomaly structure.

This records the failure of a regularized determinant, zeta residue, heat
coefficient, or weight/trace backend to remain invariant under a conformal
variation.
-/
structure WeylAnomaly
    (Op : Type*) [Ring Op] where
  /-- Dirac/spectral generator. -/
  D : Op

  /-- Conformal or Weyl variation. -/
  conformalVariation : Op → Op

  /-- Zeta/residue-style backend. -/
  zetaResidue : Op → ℂ

  /-- Determinant variation readout. -/
  determinantVariation : ℝ

  /-- Exact nonzero determinant-variation readout. -/
  determinantVariation_nonzero :
    determinantVariation ≠ 0

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

  /-- Model-dependent calibration from local four-bit sectors to `ZMod 16`. -/
  calibration :
    InfoGeometry.OperatorAlgebra.CliffordAtomsZ2n.DIIIInteractionCalibration

  /-- The calibrated local sector is the supplied interacting DIII index. -/
  compatibility :
    calibration.encode localSector = globalInvariant.nuInteracting

namespace CliffordToDIIIInteractionBridge

variable (B : CliffordToDIIIInteractionBridge)

/-- Read back the exact local-to-global DIII compatibility equation. -/
theorem calibrated_sector_eq_interacting_index :
    B.calibration.encode B.localSector = B.globalInvariant.nuInteracting :=
  B.compatibility

/--
The calibrated local sector also agrees with the mod-16 reduction of the free
integer invariant.
-/
theorem calibrated_sector_eq_free_reduction :
    B.calibration.encode B.localSector =
      (B.globalInvariant.nuFree : ZMod 16) := by
  rw [B.calibrated_sector_eq_interacting_index, B.globalInvariant.reduction_law]

end CliffordToDIIIInteractionBridge

/-! ## 5. Tubule stability as global obstruction -/

/--
A stable tubule/defect sector structure.

The point of this socket is the strict qualification: a local defect becomes a
stable global object only after a nonzero anomaly/topological readout proves
that it cannot be removed by local gauge choices.
-/
structure TubuleStability
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
  Nonzero anomaly/topological readout rules out a trivial sector for the
  selected model.
  -/
  stable_nontrivial_of_nonzero_anomaly :
    ∀ x : Op,
      anomaly.anomaly x ≠ anomaly.anomaly 0 →
        isNontrivialSector (sectorReadout x)

namespace TubuleStability

variable {Op : Type*} [Ring Op]
variable (T : TubuleStability Op)

/-- A configuration lies in a nontrivial topological sector. -/
def InNontrivialSector
    (x : Op) : Prop :=
  T.isNontrivialSector (T.sectorReadout x)

/--
Read back the stability implication supplied by the selected model.
-/
theorem stable_of_nonzero_global_readout
    {x : Op}
    (h : T.anomaly.anomaly x ≠ T.anomaly.anomaly 0) :
    T.InNontrivialSector x :=
  T.stable_nontrivial_of_nonzero_anomaly x h

end TubuleStability

end InfoGeometry.OperatorAlgebra.AnomalyTubuleStability
