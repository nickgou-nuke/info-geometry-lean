import Lean
import InfoGeometry.Canonical.SpineAttributes
import InfoGeometry.Physics.QCDChiralStructuralBridge
import InfoGeometry.Physics.QCDZornColorSlotBridge
import InfoGeometry.Physics.QCDTrialityStructuralBridge
import InfoGeometry.Physics.QCDExceptionalArtinBridge

/-!
# Audited QCD-facing structural theorem DAG

This metadata layer records only theorem-supported structural statements.
Physical QCD interpretations remain explicit ownerless debt unless a genuine
representation/dynamics theorem exists in the Lean environment.
-/

open Lean Elab Command
open InfoGeometry.Canonical

namespace InfoGeometry.Physics.QCDStructuralLogosMap

inductive Status where
  | theorem
  | structuralBridge
  | openDebt
  deriving DecidableEq, Repr, Inhabited

inductive Concept where
  | chiralZ2Relation
  | zornThreeVectorSlots
  | zornSlotPreservation
  | artinChiralPreservation
  | finiteTrialityThreeCycle
  | physicalGamma5Identification
  | physicalSU3ColorIdentification
  | fullG2SplitOctonionAutomorphismGroup
  | physicalQuarkAntiquarkSlotIdentification
  | qcdConfinement
  | njlChiralCondensateDynamics
  | qcdThetaVacuumKleinTopology
  | albertThreeGenerationIdentification
  | ckmFromExceptionalGeometry
  deriving DecidableEq, Repr, Inhabited

structure Entry where
  concept : Concept
  phrase : String
  status : Status
  owner : Option Name
  boundary : String
  deriving Repr, Inhabited

inductive Edge where
  | chiral_to_artin
  | zornSlots_to_slotPreservation
  | zornSlots_to_triality
  deriving DecidableEq, Repr, Inhabited

def edgeEndpoints : Edge → Concept × Concept
  | .chiral_to_artin => (.chiralZ2Relation, .artinChiralPreservation)
  | .zornSlots_to_slotPreservation => (.zornThreeVectorSlots, .zornSlotPreservation)
  | .zornSlots_to_triality => (.zornThreeVectorSlots, .finiteTrialityThreeCycle)


def allConcepts : List Concept :=
  [ .chiralZ2Relation
  , .zornThreeVectorSlots
  , .zornSlotPreservation
  , .artinChiralPreservation
  , .finiteTrialityThreeCycle
  , .physicalGamma5Identification
  , .physicalSU3ColorIdentification
  , .fullG2SplitOctonionAutomorphismGroup
  , .physicalQuarkAntiquarkSlotIdentification
  , .qcdConfinement
  , .njlChiralCondensateDynamics
  , .qcdThetaVacuumKleinTopology
  , .albertThreeGenerationIdentification
  , .ckmFromExceptionalGeometry
  ]


def allEdges : List Edge :=
  [ .chiral_to_artin
  , .zornSlots_to_slotPreservation
  , .zornSlots_to_triality
  ]


def entry : Concept → Entry
  | .chiralZ2Relation =>
      ⟨.chiralZ2Relation, "shared Z2 chiral operator relation", .structuralBridge,
        some ``InfoGeometry.Physics.QCDChiralStructuralBridge.nuclear_massspec_chiral_packet,
        "Nuclear and doubled-spectroscopy carriers satisfy the same grading sign law; no physical gamma5 identification is asserted."⟩
  | .zornThreeVectorSlots =>
      ⟨.zornThreeVectorSlots, "Zorn upper/lower three-vector slot extraction", .theorem,
        some ``InfoGeometry.Physics.QCDZornColorSlotBridge.zorn_three_vector_slot_packet,
        "Projector sandwiches extract the two three-vector slots exactly; the slots are not identified with physical color triplets."⟩
  | .zornSlotPreservation =>
      ⟨.zornSlotPreservation, "OP-stabilizer preserves Zorn three-vector slots", .theorem,
        some ``InfoGeometry.Physics.QCDZornColorSlotBridge.op_stabilizer_preserves_three_vector_slots,
        "Preservation requires an explicitly multiplication-preserving OP-stabilizing map; this is not yet an SU(3) group theorem."⟩
  | .artinChiralPreservation =>
      ⟨.artinChiralPreservation, "G2/Artin spin closure and chiral nilpotent preservation", .structuralBridge,
        some ``InfoGeometry.Physics.QCDExceptionalArtinBridge.artin_chiral_packet,
        "The Artin representation lives on its own operator carrier; no QCD gauge-group identification is inferred."⟩
  | .finiteTrialityThreeCycle =>
      ⟨.finiteTrialityThreeCycle, "finite three-state/triality cycle", .structuralBridge,
        some ``InfoGeometry.Physics.QCDTrialityStructuralBridge.finite_triality_cycle_packet,
        "The finite order-three cycles are theorem-owned; they are not identified with the three physical generations."⟩
  | .physicalGamma5Identification =>
      ⟨.physicalGamma5Identification, "repository grading equals physical Dirac gamma5", .openDebt, none,
        "Requires an explicit Dirac-spinor representation intertwining the repository grading with gamma5."⟩
  | .physicalSU3ColorIdentification =>
      ⟨.physicalSU3ColorIdentification, "Zorn/G2 stabilizer equals physical SU(3)_C", .openDebt, none,
        "The finite Zorn owner explicitly does not prove the stabilizer is the Lie group SU(3), much less the QCD gauge group."⟩
  | .fullG2SplitOctonionAutomorphismGroup =>
      ⟨.fullG2SplitOctonionAutomorphismGroup, "full Aut(split octonions) = split G2 theorem", .openDebt, none,
        "Finite G2-labelled root and stabilizer structures exist, but this QCD lane has no full automorphism-group classification owner."⟩
  | .physicalQuarkAntiquarkSlotIdentification =>
      ⟨.physicalQuarkAntiquarkSlotIdentification, "Zorn three-vector slots are quark and antiquark color representations", .openDebt, none,
        "No physical representation theorem identifies these algebraic slots with quark fields."⟩
  | .qcdConfinement =>
      ⟨.qcdConfinement, "Zorn nonassociativity proves QCD confinement", .openDebt, none,
        "The associator defect is formalized algebraically; no Yang-Mills mass-gap or confinement theorem follows from it."⟩
  | .njlChiralCondensateDynamics =>
      ⟨.njlChiralCondensateDynamics, "Soloviev block is the physical NJL/QCD chiral condensate", .openDebt, none,
        "Only operator relation-shape compatibility is available; no NJL Lagrangian, gap equation, or condensate dynamics is formalized here."⟩
  | .qcdThetaVacuumKleinTopology =>
      ⟨.qcdThetaVacuumKleinTopology, "QCD theta-vacuum has the repository Klein topology", .openDebt, none,
        "No theta term, CP action, instanton sector, or physical QCD vacuum quotient theorem is owned."⟩
  | .albertThreeGenerationIdentification =>
      ⟨.albertThreeGenerationIdentification, "three Albert/triality slots are the three fermion generations", .openDebt, none,
        "The repository has exact three-cycles, but no Standard Model generation representation theorem."⟩
  | .ckmFromExceptionalGeometry =>
      ⟨.ckmFromExceptionalGeometry, "CKM mixing derived from exceptional Jordan geometry", .openDebt, none,
        "No CKM matrix, mixing-angle, or phenomenological identification theorem is owned by this lane."⟩


def Concept.isFormalized (c : Concept) : Bool :=
  match (entry c).status, (entry c).owner with
  | .openDebt, _ => false
  | _, some _ => true
  | _, none => false


def auditQCDStructuralLogos : CoreM Unit := do
  let env ← getEnv
  let mut failures : Array String := #[]
  for c in allConcepts do
    let e := entry c
    match e.status, e.owner with
    | .openDebt, none => pure ()
    | .openDebt, some n =>
        failures := failures.push s!"open-debt entry unexpectedly names owner {n}"
    | _, none =>
        failures := failures.push s!"formal entry has no owner: {repr c}"
    | _, some n =>
        unless env.contains n do
          failures := failures.push s!"missing owner declaration: {n} ({repr c})"
  for edge in allEdges do
    let ep := edgeEndpoints edge
    unless ep.1.isFormalized && ep.2.isFormalized do
      failures := failures.push s!"QCD structural DAG edge touches open debt: {repr edge}"
  if failures.isEmpty then
    logInfo m!"QCD structural Logos audit PASS: {allConcepts.length} concepts and {allEdges.length} formal edges."
  else
    for failure in failures do
      logError m!"QCD STRUCTURAL LOGOS FAILURE: {failure}"
    throwError "QCD structural Logos audit failed"

elab "#audit_qcd_structural_logos" : command =>
  Command.liftCoreM auditQCDStructuralLogos

attribute [spine_object] Concept Entry

end InfoGeometry.Physics.QCDStructuralLogosMap
