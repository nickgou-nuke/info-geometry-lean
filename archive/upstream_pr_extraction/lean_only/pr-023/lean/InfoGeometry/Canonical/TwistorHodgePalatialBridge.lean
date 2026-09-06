import InfoGeometry.Canonical.ChiralHodgeDecomposition
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
  selfDualCondition : Prop
  antiSelfDualCondition : Prop
  incidenceCompatible : Prop

/--
Palatial-twistor operator interface.

This represents the operator/noncommutative side: twistor operator algebra,
operatorial incidence, and holonomy/action readout.  It is intentionally
separate from the Hodge-star split.
-/
@[rep_depth krein]
structure PalatialTwistorOperatorAlgebra where
  twistorOperator : OperatorObj
  operatorialIncidence : Prop
  holonomyReadout : HolonomyObj
  differentialOperatorCompatible : Prop
  incidenceHolonomyCompatible : Prop

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
  incidenceTransportCompatible : Prop
  hodgeHolonomyCompatible : Prop
  operatorHodgeCompatible : Prop

@[rep_depth transport]
theorem TwistorHodgePalatialBridgeContext.has_hodge_split
    (C : TwistorHodgePalatialBridgeContext
      (SD := SD) (ASD := ASD) (IncidenceObj := IncidenceObj)
      (OperatorObj := OperatorObj) (HolonomyObj := HolonomyObj)) :
    C.hodgeSplit.selfDualCondition
      →
    C.hodgeSplit.antiSelfDualCondition
      →
    C.hodgeSplit.incidenceCompatible
      →
    C.hodgeSplit.selfDualCondition
        ∧ C.hodgeSplit.antiSelfDualCondition
        ∧ C.hodgeSplit.incidenceCompatible := by
  intro hSD hASD hInc
  exact ⟨hSD, hASD, hInc⟩

@[rep_depth krein]
theorem TwistorHodgePalatialBridgeContext.has_palatial_operator_data
    (C : TwistorHodgePalatialBridgeContext
      (SD := SD) (ASD := ASD) (IncidenceObj := IncidenceObj)
      (OperatorObj := OperatorObj) (HolonomyObj := HolonomyObj)) :
    C.palatialOps.operatorialIncidence
      →
    C.palatialOps.differentialOperatorCompatible
      →
    C.palatialOps.incidenceHolonomyCompatible
      →
    C.palatialOps.operatorialIncidence
        ∧ C.palatialOps.differentialOperatorCompatible
        ∧ C.palatialOps.incidenceHolonomyCompatible := by
  intro hInc hDiff hHol
  exact ⟨hInc, hDiff, hHol⟩

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
    C.incidenceTransportCompatible
      →
    C.hodgeHolonomyCompatible
      →
    C.operatorHodgeCompatible
      →
    C.incidenceTransportCompatible
        ∧ C.hodgeHolonomyCompatible
        ∧ C.operatorHodgeCompatible := by
  intro hTransport hHodge hOperator
  exact ⟨hTransport, hHodge, hOperator⟩

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
    (CCI : CertifiedConformalInference E) :
    PalatialTwistorOperatorAlgebra
      (OperatorObj := EndH) (HolonomyObj := ℝ) where
  twistorOperator := CCI.liftedProjectorObstructionOperator
  operatorialIncidence := CCI.operatorialIncidence
  holonomyReadout := CCI.toConformalInference.chiralScale
  differentialOperatorCompatible := CCI.operatorialIncidence
  incidenceHolonomyCompatible :=
    CCI.liftedProjectorObstructionOperator = 0
      ↔ CCI.chiralAnomalyOperator = 0

@[rep_depth krein]
theorem palatialOperatorAlgebraOfCertifiedConformalInference_operatorialIncidence
    (CCI : CertifiedConformalInference E) :
    (palatialOperatorAlgebraOfCertifiedConformalInference
      (E := E) CCI).operatorialIncidence
      =
    CCI.operatorialIncidence := by
  rfl

@[rep_depth krein]
theorem palatialOperatorAlgebraOfCertifiedConformalInference_incidenceHolonomyCompatible
    (CCI : CertifiedConformalInference E) :
    (palatialOperatorAlgebraOfCertifiedConformalInference
      (E := E) CCI).incidenceHolonomyCompatible := by
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
    (Z : Twistor) (X Y : InfoGeometry.Clifford.Soldering.Vec22) :
    HodgeStarSelfDualSplit
      (SD := InfoGeometry.Clifford.Soldering.Vec22)
      (ASD := InfoGeometry.Clifford.Soldering.Vec22)
      (IncidenceObj := Prop) where
  selfDualSector := X
  antiSelfDualSector := Y
  twistorIncidence := Incident Z X ∧ Incident Z Y
  selfDualCondition := Incident Z X
  antiSelfDualCondition := Incident Z Y
  incidenceCompatible := InfoGeometry.Clifford.Soldering.q22 (X - Y) = 0

@[rep_depth projective]
theorem hodgeStarSelfDualSplitOfIncidentNullSeparation_incidenceCompatible
    (Z : Twistor) (X Y : InfoGeometry.Clifford.Soldering.Vec22)
    (hX : Incident Z X) (hY : Incident Z Y) (hπ : Z.2 ≠ 0) :
    (hodgeStarSelfDualSplitOfIncidentNullSeparation
      Z X Y).incidenceCompatible := by
  exact incident_points_null_separated Z X Y hX hY hπ

end ClassicalIncidence

end InfoGeometry.Canonical.TwistorHodgePalatialBridge
