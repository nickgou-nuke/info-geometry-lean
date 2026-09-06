import Lean
import InfoGeometry.Canonical.SpineAttributes
import InfoGeometry.Physics.NuclearChargeSpinSymmetry
import InfoGeometry.Physics.NuclearExceptionalArtinGaloisBridge

/-!
# Audited symmetry DAG for the nuclear exceptional/Artin/Galois lane

Formal nodes name exact theorem owners.  Stronger claims about a physical
exceptional or Galois symmetry of nuclear quantum numbers remain ownerless.
-/

open Lean Elab Command
open InfoGeometry.Canonical

namespace InfoGeometry.Physics.NuclearExceptionalSymmetryLogosMap

inductive Status where
  | definition | theorem | structuralBridge | openDebt
  deriving DecidableEq, Repr, Inhabited

inductive Concept where
  | nuclearQuantumNumberSymmetry
  | nuclearFiveGradeRelation
  | g2ArtinSpinClosure
  | braidNilpotentPreservation
  | g2CyclotomicSectorPreservation
  | arithmeticGaloisChargeSpinPreservation
  | exceptionalGroupActsOnNuclearPacket
  | nontrivialGaloisActsOnNuclearPacket
  | artinBraidingPreservesTwoJTwoT3
  | f4e6e7e8NuclearSymmetry
  deriving DecidableEq, Repr, Inhabited

structure Entry where
  concept : Concept
  phrase : String
  status : Status
  owner : Option Name
  boundary : String
  deriving Repr, Inhabited

inductive Edge where
  | quantumNumbers_to_fiveGrade
  | fiveGrade_to_g2Artin
  | g2Artin_to_nilpotentPreservation
  | g2Artin_to_cyclotomicSector
  | quantumNumbers_to_arithmeticGalois
  deriving DecidableEq, Repr, Inhabited

def edgeEndpoints : Edge → Concept × Concept
  | .quantumNumbers_to_fiveGrade => (.nuclearQuantumNumberSymmetry, .nuclearFiveGradeRelation)
  | .fiveGrade_to_g2Artin => (.nuclearFiveGradeRelation, .g2ArtinSpinClosure)
  | .g2Artin_to_nilpotentPreservation => (.g2ArtinSpinClosure, .braidNilpotentPreservation)
  | .g2Artin_to_cyclotomicSector => (.g2ArtinSpinClosure, .g2CyclotomicSectorPreservation)
  | .quantumNumbers_to_arithmeticGalois =>
      (.nuclearQuantumNumberSymmetry, .arithmeticGaloisChargeSpinPreservation)


def allConcepts : List Concept :=
  [ .nuclearQuantumNumberSymmetry, .nuclearFiveGradeRelation,
    .g2ArtinSpinClosure, .braidNilpotentPreservation,
    .g2CyclotomicSectorPreservation, .arithmeticGaloisChargeSpinPreservation,
    .exceptionalGroupActsOnNuclearPacket, .nontrivialGaloisActsOnNuclearPacket,
    .artinBraidingPreservesTwoJTwoT3, .f4e6e7e8NuclearSymmetry ]


def allEdges : List Edge :=
  [ .quantumNumbers_to_fiveGrade, .fiveGrade_to_g2Artin,
    .g2Artin_to_nilpotentPreservation, .g2Artin_to_cyclotomicSector,
    .quantumNumbers_to_arithmeticGalois ]


def entry : Concept → Entry
  | .nuclearQuantumNumberSymmetry =>
      ⟨.nuclearQuantumNumberSymmetry, "charge/spin preserving nuclear symmetry", .definition,
        some ``InfoGeometry.Physics.NuclearChargeSpinSymmetry.QuantumNumberSymmetry,
        "Preserves only the currently owned readouts: 2J, occupation, 2T3 and derived quasiparticle parity."⟩
  | .nuclearFiveGradeRelation =>
      ⟨.nuclearFiveGradeRelation, "nuclear balanced Cartan / five-grade relation shape", .structuralBridge,
        some ``InfoGeometry.Physics.NuclearExceptionalArtinGaloisBridge.nuclear_five_grade_relation_packet,
        "Exact ±1 relation-shape agreement; no Lie-algebra isomorphism is asserted."⟩
  | .g2ArtinSpinClosure =>
      ⟨.g2ArtinSpinClosure, "G2 Artin spin/projective closure", .theorem,
        some ``InfoGeometry.Physics.NuclearExceptionalArtinGaloisBridge.g2_artin_spin_packet,
        "The supplied G2 spin lift satisfies the Artin relation, C^6=-I and C^12=I."⟩
  | .braidNilpotentPreservation =>
      ⟨.braidNilpotentPreservation, "braid conjugation preserves square-zero chiral channels", .theorem,
        some ``InfoGeometry.Physics.NuclearExceptionalArtinGaloisBridge.artin_conjugation_preserves_nuclear_nilpotent_shape,
        "Preserves nilpotence under conjugation; it does not by itself preserve nuclear spin or isospin labels."⟩
  | .g2CyclotomicSectorPreservation =>
      ⟨.g2CyclotomicSectorPreservation, "G2 cyclotomic short/long sector preservation", .theorem,
        some ``InfoGeometry.Physics.NuclearExceptionalArtinGaloisBridge.g2_cyclotomic_sector_packet,
        "Preserves the G2 doubled-root sector coordinate, not automatically a nuclear charge label."⟩
  | .arithmeticGaloisChargeSpinPreservation =>
      ⟨.arithmeticGaloisChargeSpinPreservation, "arithmetic Galois extension preserves nuclear charge/spin", .theorem,
        some ``InfoGeometry.Physics.NuclearExceptionalArtinGaloisBridge.galois_preserves_nuclear_charge_spin,
        "The supplied Galois action moves only the arithmetic coordinate; nuclear quantum numbers are fixed."⟩
  | .exceptionalGroupActsOnNuclearPacket =>
      ⟨.exceptionalGroupActsOnNuclearPacket, "nontrivial exceptional-group action on nuclear quantum numbers", .openDebt, none,
        "Requires an explicit representation on QuantumNumbers or a richer nuclear state carrier with preservation proofs."⟩
  | .nontrivialGaloisActsOnNuclearPacket =>
      ⟨.nontrivialGaloisActsOnNuclearPacket, "nontrivial Galois action on nuclear 2J and 2T3", .openDebt, none,
        "Current Galois preservation is an inert product extension, not a nontrivial action on the nuclear packet."⟩
  | .artinBraidingPreservesTwoJTwoT3 =>
      ⟨.artinBraidingPreservesTwoJTwoT3, "Artin braiding preserves nuclear spin/isospin", .openDebt, none,
        "The Artin owner preserves nilpotent operator shape; no action on QuantumNumbers is yet supplied."⟩
  | .f4e6e7e8NuclearSymmetry =>
      ⟨.f4e6e7e8NuclearSymmetry, "F4/E6/E7/E8 nuclear symmetry action", .openDebt, none,
        "Exceptional towers exist elsewhere, but no theorem identifies their action with the present nuclear quantum-number carrier."⟩


def Concept.isFormalized (c : Concept) : Bool :=
  match (entry c).status, (entry c).owner with
  | .openDebt, _ => false
  | _, some _ => true
  | _, none => false


def auditNuclearExceptionalSymmetryLogos : CoreM Unit := do
  let env ← getEnv
  let mut failures : Array String := #[]
  for c in allConcepts do
    let e := entry c
    match e.status, e.owner with
    | .openDebt, none => pure ()
    | .openDebt, some n => failures := failures.push s!"open debt unexpectedly has owner {n}"
    | _, none => failures := failures.push s!"formal node has no owner: {repr c}"
    | _, some n => unless env.contains n do failures := failures.push s!"missing owner {n} ({repr c})"
  for edge in allEdges do
    let ep := edgeEndpoints edge
    unless ep.1.isFormalized && ep.2.isFormalized do
      failures := failures.push s!"formal edge touches open debt: {repr edge}"
  if failures.isEmpty then
    logInfo m!"NuclearExceptionalSymmetry Logos audit PASS: {allConcepts.length} concepts and {allEdges.length} edges."
  else
    for failure in failures do logError m!"NUCLEAR EXCEPTIONAL SYMMETRY FAILURE: {failure}"
    throwError "NuclearExceptionalSymmetry Logos audit failed"

elab "#audit_nuclear_exceptional_symmetry_logos" : command =>
  Command.liftCoreM auditNuclearExceptionalSymmetryLogos

end InfoGeometry.Physics.NuclearExceptionalSymmetryLogosMap
