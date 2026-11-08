import InfoGeometry.Canonical.ChiralHodgeDecomposition
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ChiralHodgeLichnerowiczBridge
import InfoGeometry.Canonical.TwistorOperatorialIncidence
import InfoGeometry.Canonical.PathIntegral
import InfoGeometry.Canonical.WeylTransport
import InfoGeometry.Canonical.LiteratureGrandCanonicalWeylTKK
import InfoGeometry.Twistor.Incidence
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.TwistorHodgePalatialBridge

Interface layer separating two nearby but distinct twistor/Hodge corridors.

This file deliberately does **not** assert a single unconditional
"Penrose-palatial Hodge integral".  The repo currently has:

- a Hodge/chiral-sector lane (`ChiralHodgeDecomposition`,
  `ChiralHodgeLichnerowiczBridge`);
- a classical twistor incidence lane (`Twistor.Incidence`);
- an operatorial/palatial-like incidence lane
  (`TwistorOperatorialIncidence`);
- path/holonomy abstractions (`PathIntegral`, `WeylTransport`);
- contour/holonomy residue data for singular ensembles
  (`LiteratureGrandCanonicalWeylTKK`).

The correct formal move is therefore to expose two proof-carrying interfaces
and connect them only under explicit compatibility hypotheses.
-/

namespace InfoGeometry.Canonical.TwistorHodgePalatialBridge

open InfoGeometry.Canonical.ChiralHodgeDecomposition
open InfoGeometry.Canonical.ChiralHodgeLichnerowiczBridge
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Twistor.Incidence

section AbstractInterfaces

variable {SD ASD TwistorObj IncidenceObj HolonomyObj OperatorObj : Type*}

/--
Hodge-star/self-dual split interface.

This represents the classical SD/ASD twistor-geometric side: Hodge star data,
self-dual and anti-self-dual sectors, and an incidence readout.  It is an
interface, not a claim that the repo already has a full smooth exterior-calculus
Hodge integral.
-/
@[rep_depth transport]
structure HodgeStarSelfDualSplit where
  selfDualSector : SD
  antiSelfDualSector : ASD
  twistorIncidence : IncidenceObj
  selfDualLocus : Set SD
  antiSelfDualLocus : Set ASD
  incidenceCompatibleLocus : Set (SD × ASD × IncidenceObj)
  selfDualCondition : selfDualSector ∈ selfDualLocus
  antiSelfDualCondition : antiSelfDualSector ∈ antiSelfDualLocus
  incidenceCompatible :
    (selfDualSector, antiSelfDualSector, twistorIncidence) ∈
      incidenceCompatibleLocus

/--
Palatial-twistor operator interface.

This represents the operator/noncommutative side: twistor operator algebra,
operatorial incidence, and holonomy/action readout.  It is intentionally
separate from the Hodge-star split.
-/
@[rep_depth krein]
structure PalatialTwistorOperatorAlgebra where
  twistorOperator : OperatorObj
  holonomyReadout : HolonomyObj
  operatorialIncidenceLocus : Set OperatorObj
  differentialOperatorCompatibleLocus : Set OperatorObj
  incidenceHolonomyCompatibleLocus : Set (OperatorObj × HolonomyObj)
  operatorialIncidence : twistorOperator ∈ operatorialIncidenceLocus
  differentialOperatorCompatible :
    twistorOperator ∈ differentialOperatorCompatibleLocus
  incidenceHolonomyCompatible :
    (twistorOperator, holonomyReadout) ∈ incidenceHolonomyCompatibleLocus

/--
Explicit bridge context between the Hodge SD/ASD side and the palatial operator
side.

The compatibility fields are the required hypotheses for any later theorem that
relates Hodge/twistor contour data to operatorial incidence or holonomy.  This
prevents graph or literature proximity from becoming an unconditional theorem.
-/
@[rep_depth transport]
structure TwistorHodgePalatialBridgeContext where
  hodgeSplit : HodgeStarSelfDualSplit
    (SD := SD) (ASD := ASD) (IncidenceObj := IncidenceObj)
  palatialOps : PalatialTwistorOperatorAlgebra
    (OperatorObj := OperatorObj) (HolonomyObj := HolonomyObj)
  incidenceTransportLocus : Set (HodgeStarSelfDualSplit ×
    PalatialTwistorOperatorAlgebra)
  hodgeHolonomyLocus : Set (HodgeStarSelfDualSplit ×
    PalatialTwistorOperatorAlgebra)
  operatorHodgeLocus : Set (HodgeStarSelfDualSplit ×
    PalatialTwistorOperatorAlgebra)
  incidenceTransportCompatible :
    (hodgeSplit, palatialOps) ∈ incidenceTransportLocus
  hodgeHolonomyCompatible :
    (hodgeSplit, palatialOps) ∈ hodgeHolonomyLocus
  operatorHodgeCompatible :
    (hodgeSplit, palatialOps) ∈ operatorHodgeLocus

@[rep_depth transport]
theorem TwistorHodgePalatialBridgeContext.has_hodge_split
    (C : TwistorHodgePalatialBridgeContext
      (SD := SD) (ASD := ASD) (IncidenceObj := IncidenceObj)
      (OperatorObj := OperatorObj) (HolonomyObj := HolonomyObj)) :
    C.hodgeSplit.selfDualSector ∈ C.hodgeSplit.selfDualLocus
      ∧ C.hodgeSplit.antiSelfDualSector ∈ C.hodgeSplit.antiSelfDualLocus
      ∧ (C.hodgeSplit.selfDualSector, C.hodgeSplit.antiSelfDualSector,
          C.hodgeSplit.twistorIncidence) ∈
        C.hodgeSplit.incidenceCompatibleLocus := by
  exact ⟨C.hodgeSplit.selfDualCondition,
    C.hodgeSplit.antiSelfDualCondition,
    C.hodgeSplit.incidenceCompatible⟩

@[rep_depth krein]
theorem TwistorHodgePalatialBridgeContext.has_palatial_operator_data
    (C : TwistorHodgePalatialBridgeContext
      (SD := SD) (ASD := ASD) (IncidenceObj := IncidenceObj)
      (OperatorObj := OperatorObj) (HolonomyObj := HolonomyObj)) :
    C.palatialOps.twistorOperator ∈ C.palatialOps.operatorialIncidenceLocus
      ∧ C.palatialOps.twistorOperator ∈
          C.palatialOps.differentialOperatorCompatibleLocus
      ∧ (C.palatialOps.twistorOperator, C.palatialOps.holonomyReadout) ∈
          C.palatialOps.incidenceHolonomyCompatibleLocus := by
  exact ⟨C.palatialOps.operatorialIncidence,
    C.palatialOps.differentialOperatorCompatible,
    C.palatialOps.incidenceHolonomyCompatible⟩

/--
Only an explicit bridge context licenses a combined Hodge/palatial conclusion.
This theorem is intentionally just the unpacking of the bridge hypotheses; later
owner theorems can replace these abstract propositions with concrete objects.
-/
@[rep_depth transport]
theorem TwistorHodgePalatialBridgeContext.combined_compatibility
    (C : TwistorHodgePalatialBridgeContext
      (SD := SD) (ASD := ASD) (IncidenceObj := IncidenceObj)
      (OperatorObj := OperatorObj) (HolonomyObj := HolonomyObj)) :
    (C.hodgeSplit, C.palatialOps) ∈ C.incidenceTransportLocus
      ∧ (C.hodgeSplit, C.palatialOps) ∈ C.hodgeHolonomyLocus
      ∧ (C.hodgeSplit, C.palatialOps) ∈ C.operatorHodgeLocus := by
  exact ⟨C.incidenceTransportCompatible,
    C.hodgeHolonomyCompatible, C.operatorHodgeCompatible⟩

end AbstractInterfaces

section RepoBridges

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Concrete palatial-operator interface induced by certified conformal inference.

The operatorial incidence field is exactly the existing projector-obstruction
incidence predicate; no new palatial theorem is asserted.
-/
@[rep_depth krein]
noncomputable def palatialOperatorAlgebraOfCertifiedConformalInference
    (CCI : CertifiedConformalInference E)
    (hCCI : CCI.operatorialIncidence) :
    PalatialTwistorOperatorAlgebra
      (OperatorObj := EndH) (HolonomyObj := E →L[ℝ] E) where
  twistorOperator := CCI.liftedProjectorObstructionOperator
  holonomyReadout := CCI.chiralAnomalyOperator
  operatorialIncidenceLocus := {T | T = 0}
  differentialOperatorCompatibleLocus := {T | T = 0}
  incidenceHolonomyCompatibleLocus := {p | p.1 = 0 ↔ p.2 = 0}
  operatorialIncidence :=
    by
      change CCI.liftedProjectorObstructionOperator = 0
      exact hCCI
  differentialOperatorCompatible :=
    by
      change CCI.liftedProjectorObstructionOperator = 0
      exact hCCI
  incidenceHolonomyCompatible := by
    change CCI.liftedProjectorObstructionOperator = 0 ↔
      CCI.chiralAnomalyOperator = 0
    exact
      (CertifiedConformalInference.operatorialIncidence_iff_chiralAnomalyOperator_zero
        (CCI := CCI))

@[rep_depth krein]
theorem palatialOperatorAlgebraOfCertifiedConformalInference_operatorialIncidence
    (CCI : CertifiedConformalInference E)
    (hCCI : CCI.operatorialIncidence) :
    (palatialOperatorAlgebraOfCertifiedConformalInference
      (E := E) CCI hCCI).twistorOperator ∈
        (palatialOperatorAlgebraOfCertifiedConformalInference
      (E := E) CCI hCCI).operatorialIncidenceLocus ↔
      CCI.operatorialIncidence := by
  change CCI.liftedProjectorObstructionOperator = 0 ↔
    CCI.operatorialIncidence
  rfl

@[rep_depth krein]
theorem palatialOperatorAlgebraOfCertifiedConformalInference_incidenceHolonomyCompatible
    (CCI : CertifiedConformalInference E)
    (hCCI : CCI.operatorialIncidence) :
    (palatialOperatorAlgebraOfCertifiedConformalInference
      (E := E) CCI hCCI).twistorOperator ∈
        (palatialOperatorAlgebraOfCertifiedConformalInference
          (E := E) CCI hCCI).operatorialIncidenceLocus ↔
      (palatialOperatorAlgebraOfCertifiedConformalInference
        (E := E) CCI hCCI).holonomyReadout ∈
        {T | T = 0} := by
  exact
    (CertifiedConformalInference.operatorialIncidence_iff_chiralAnomalyOperator_zero
      (CCI := CCI))

end RepoBridges

section ClassicalIncidence

/--
Classical twistor incidence supplies the SD/ASD-side incidence compatibility
only under its own nonzero-spinor hypothesis.  This is deliberately kept as a
separate interface from palatial operator algebra.
-/
@[rep_depth projective]
def hodgeStarSelfDualSplitOfIncidentNullSeparation
    (Z : Twistor) (X Y : InfoGeometry.Clifford.Soldering.Vec22)
    (hX : Incident Z X) (hY : Incident Z Y)
    (hNull : InfoGeometry.Clifford.Soldering.q22 (X - Y) = 0) :
    HodgeStarSelfDualSplit
      (SD := InfoGeometry.Clifford.Soldering.Vec22)
      (ASD := InfoGeometry.Clifford.Soldering.Vec22)
      (IncidenceObj := Prop) where
  selfDualSector := X
  antiSelfDualSector := Y
  twistorIncidence := Incident Z X ∧ Incident Z Y
  selfDualLocus := {V | Incident Z V}
  antiSelfDualLocus := {V | Incident Z V}
  incidenceCompatibleLocus :=
    {p | InfoGeometry.Clifford.Soldering.q22 (p.1 - p.2.1) = 0}
  selfDualCondition := hX
  antiSelfDualCondition := hY
  incidenceCompatible := hNull

@[rep_depth projective]
theorem hodgeStarSelfDualSplitOfIncidentNullSeparation_incidenceCompatible
    (Z : Twistor) (X Y : InfoGeometry.Clifford.Soldering.Vec22)
    (hX : Incident Z X) (hY : Incident Z Y) (hπ : Z.2 ≠ 0) :
    (X, Y, Incident Z X ∧ Incident Z Y) ∈
      (hodgeStarSelfDualSplitOfIncidentNullSeparation
        Z X Y hX hY (incident_points_null_separated Z X Y hX hY hπ)).incidenceCompatibleLocus := by
  exact incident_points_null_separated Z X Y hX hY hπ

end ClassicalIncidence

end InfoGeometry.Canonical.TwistorHodgePalatialBridge
