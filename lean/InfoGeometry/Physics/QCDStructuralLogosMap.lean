import Lean
import InfoGeometry.Canonical.SpineAttributes
import InfoGeometry.Physics.QCDChiralStructuralBridge
import InfoGeometry.Physics.QCDZornColorSlotBridge
import InfoGeometry.Physics.QCDTrialityStructuralBridge
import InfoGeometry.Physics.QCDExceptionalArtinBridge
import InfoGeometry.Physics.QCDColorCARAnyonBridge

/-!
# Audited QCD-facing structural theorem DAG

This metadata layer records theorem-supported algebraic structures already
present in the native `InfoGeometry` library.  In particular, the repository
already owns a concrete Gell-Mann `su(3)` corridor, split-octonion Cartan
weights, three-colour `Cl(5,5)` CAR data, finite colour/parafermion braid
relations, Zorn null-boundary colour pairings, and generic anyon monodromy.

Those facts are distinct from the stronger physical claim that these carriers
are the QCD colour gauge representation or that they prove confinement.
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
  | gellMannSU3Algebra
  | splitOctonionGellMannWeights
  | threeColorCAR
  | colorParafermionBraid
  | zornMajoranaBraid
  | zornNullColorGaugeInvariant
  | anyonDoubleBraid
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
  | zornSlots_to_threeColorCAR
  | gellMann_to_splitOctonionWeights
  | threeColorCAR_to_colorBraid
  | zornSlots_to_zornMajoranaBraid
  | zornSlots_to_nullGaugeInvariant
  | colorBraid_to_anyonDoubleBraid
  | zornSlots_to_triality
  deriving DecidableEq, Repr, Inhabited

def edgeEndpoints : Edge → Concept × Concept
  | .chiral_to_artin => (.chiralZ2Relation, .artinChiralPreservation)
  | .zornSlots_to_slotPreservation => (.zornThreeVectorSlots, .zornSlotPreservation)
  | .zornSlots_to_threeColorCAR => (.zornThreeVectorSlots, .threeColorCAR)
  | .gellMann_to_splitOctonionWeights => (.gellMannSU3Algebra, .splitOctonionGellMannWeights)
  | .threeColorCAR_to_colorBraid => (.threeColorCAR, .colorParafermionBraid)
  | .zornSlots_to_zornMajoranaBraid => (.zornThreeVectorSlots, .zornMajoranaBraid)
  | .zornSlots_to_nullGaugeInvariant => (.zornThreeVectorSlots, .zornNullColorGaugeInvariant)
  | .colorBraid_to_anyonDoubleBraid => (.colorParafermionBraid, .anyonDoubleBraid)
  | .zornSlots_to_triality => (.zornThreeVectorSlots, .finiteTrialityThreeCycle)


def allConcepts : List Concept :=
  [ .chiralZ2Relation
  , .zornThreeVectorSlots
  , .zornSlotPreservation
  , .gellMannSU3Algebra
  , .splitOctonionGellMannWeights
  , .threeColorCAR
  , .colorParafermionBraid
  , .zornMajoranaBraid
  , .zornNullColorGaugeInvariant
  , .anyonDoubleBraid
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
  , .zornSlots_to_threeColorCAR
  , .gellMann_to_splitOctonionWeights
  , .threeColorCAR_to_colorBraid
  , .zornSlots_to_zornMajoranaBraid
  , .zornSlots_to_nullGaugeInvariant
  , .colorBraid_to_anyonDoubleBraid
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
        "Projector sandwiches extract the two three-vector slots exactly."⟩
  | .zornSlotPreservation =>
      ⟨.zornSlotPreservation, "OP-stabilizer preserves Zorn three-vector slots", .theorem,
        some ``InfoGeometry.Physics.QCDZornColorSlotBridge.op_stabilizer_preserves_three_vector_slots,
        "Preservation requires an explicitly multiplication-preserving OP-stabilizing map."⟩
  | .gellMannSU3Algebra =>
      ⟨.gellMannSU3Algebra, "native Gell-Mann su(3) algebra packet", .theorem,
        some ``InfoGeometry.Physics.QCDColorCARAnyonBridge.gellMann_su3_packet,
        "Concrete 3x3 Gell-Mann commutators and the bridge to the anti-Hermitian `su (Fin 3)` basis are formalized."⟩
  | .splitOctonionGellMannWeights =>
      ⟨.splitOctonionGellMannWeights, "Gell-Mann Cartan weights on split-octonion circular roots", .structuralBridge,
        some ``InfoGeometry.Physics.QCDColorCARAnyonBridge.split_octonion_gellMann_weight_packet,
        "The three circular root channels carry exact opposite Cartan weights; this is an algebraic representation statement."⟩
  | .threeColorCAR =>
      ⟨.threeColorCAR, "native three-colour Clifford/Zorn CAR packet", .structuralBridge,
        some ``InfoGeometry.Physics.QCDColorCARAnyonBridge.circular_and_cl55_color_car_packet,
        "The main library owns three colour-indexed Cl(5,5) CAR channels and matching circular Zorn CAR relations."⟩
  | .colorParafermionBraid =>
      ⟨.colorParafermionBraid, "finite A2 colour and parafermion Artin braiding", .structuralBridge,
        some ``InfoGeometry.Physics.QCDColorCARAnyonBridge.color_weyl_and_parafermion_braid_packet,
        "Both the finite colour Weyl model and explicit parafermion-style matrices satisfy the Artin relation."⟩
  | .zornMajoranaBraid =>
      ⟨.zornMajoranaBraid, "Zorn Majorana-shaped generators and braid inverses", .structuralBridge,
        some ``InfoGeometry.Physics.QCDColorCARAnyonBridge.zorn_majorana_braid_packet,
        "The Zorn Q_k generators square to the identity and their unnormalised braid elements have explicit two-sided inverses."⟩
  | .zornNullColorGaugeInvariant =>
      ⟨.zornNullColorGaugeInvariant, "Zorn null-boundary colour-pairing gauge invariant", .theorem,
        some ``InfoGeometry.Physics.QCDColorCARAnyonBridge.zorn_null_color_gauge_packet,
        "The colour tensor trace equals the dot pairing, vanishes on the supplied null boundary, and is invariant under matrix conjugation."⟩
  | .anyonDoubleBraid =>
      ⟨.anyonDoubleBraid, "unitary anyon double-braid monodromy", .theorem,
        some ``InfoGeometry.Physics.QCDColorCARAnyonBridge.anyon_double_braid_packet,
        "Generic unitary braid data gives a unitary double-braiding monodromy with normalized trace."⟩
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
      ⟨.physicalSU3ColorIdentification, "native algebraic su(3)/colour carriers are the physical QCD SU(3)_C representation", .openDebt, none,
        "The algebraic Gell-Mann, colour-CAR, Weyl and Zorn invariants are formalized; identifying them with quark fields and the QCD gauge action requires a physical representation theorem."⟩
  | .fullG2SplitOctonionAutomorphismGroup =>
      ⟨.fullG2SplitOctonionAutomorphismGroup, "full Aut(split octonions) = split G2 theorem", .openDebt, none,
        "Substantial G2 derivation/root infrastructure exists, but this QCD lane does not claim a completed global automorphism-group classification."⟩
  | .physicalQuarkAntiquarkSlotIdentification =>
      ⟨.physicalQuarkAntiquarkSlotIdentification, "Zorn three-vector slots are physical quark and antiquark color representations", .openDebt, none,
        "The algebraic three-vector and three-colour carriers are exact; their physical field interpretation is not yet theorem-owned."⟩
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
