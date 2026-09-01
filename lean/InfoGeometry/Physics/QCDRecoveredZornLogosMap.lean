import Lean
import InfoGeometry.Canonical.SpineAttributes
import InfoGeometry.Physics.QCDFureyZornProjectorBridge
import InfoGeometry.Physics.QCDZornChargeConjugationBridge

/-!
# Audited recovered-Zorn structural ledger

This ledger records finite Zorn theorems recovered from the downstream proof
workspace and re-established on native main-library carriers.

The canonical `G2TrifactorSU3` carrier and the complex
`SplitOctonionBraidSU3.Zorn` carrier remain distinct. No equivalence between
them is asserted by this ledger.
-/

open Lean Elab Command
open InfoGeometry.Canonical

namespace InfoGeometry.Physics.QCDRecoveredZornLogosMap

inductive Status where
  | theorem
  | structuralBridge
  | openDebt
  deriving DecidableEq, Repr, Inhabited

inductive Concept where
  | canonicalZornProjectorRouting
  | complexZornConjugateExchange
  | canonicalComplexZornEquivalence
  | zornCliffordFureyIntertwiner
  | nativeFaithfulZornColorRepresentation
  deriving DecidableEq, Repr, Inhabited

structure Entry where
  concept : Concept
  phrase : String
  status : Status
  owner : Option Name
  boundary : String
  deriving Repr, Inhabited

def allConcepts : List Concept :=
  [ .canonicalZornProjectorRouting
  , .complexZornConjugateExchange
  , .canonicalComplexZornEquivalence
  , .zornCliffordFureyIntertwiner
  , .nativeFaithfulZornColorRepresentation
  ]


def entry : Concept → Entry
  | .canonicalZornProjectorRouting =>
      ⟨.canonicalZornProjectorRouting,
        "canonical Zorn projector routing for upper/lower color lanes",
        .theorem,
        some ``InfoGeometry.Physics.QCDFureyZornProjectorBridge.furey_zorn_projector_packet,
        "The canonical projectors select complementary square-zero three-vector lanes by right multiplication."⟩
  | .complexZornConjugateExchange =>
      ⟨.complexZornConjugateExchange,
        "complex Zorn conjugate-linear scalar/color exchange",
        .theorem,
        some ``InfoGeometry.Physics.QCDZornChargeConjugationBridge.zorn_charge_conjugation_packet,
        "Coefficient conjugation exchanges scalar and upper/lower color slots and is involutive."⟩
  | .canonicalComplexZornEquivalence =>
      ⟨.canonicalComplexZornEquivalence,
        "equivalence between canonical and complex Zorn carriers",
        .openDebt, none,
        "Both finite carriers are theorem-owned, but no native equivalence intertwining their products/projectors is supplied here."⟩
  | .zornCliffordFureyIntertwiner =>
      ⟨.zornCliffordFureyIntertwiner,
        "Zorn color lanes intertwined with the Cl(5,5) Furey spans",
        .openDebt, none,
        "The repository owns parallel Zorn and Clifford/Furey lanes; an explicit carrier intertwiner remains to be constructed."⟩
  | .nativeFaithfulZornColorRepresentation =>
      ⟨.nativeFaithfulZornColorRepresentation,
        "faithful gl3 color representation on a native Zorn-spinor carrier",
        .openDebt, none,
        "A faithful theorem exists downstream in proofs/ZornColorLieRepresentation.lean but still depends on proof-workspace carriers and has not been migrated to the main library."⟩


def auditRecoveredZornLogos : CoreM Unit := do
  let env ← getEnv
  let mut failures : Array String := #[]
  for c in allConcepts do
    let e := entry c
    match e.status, e.owner with
    | .openDebt, none => pure ()
    | .openDebt, some n =>
        failures := failures.push s!"open-debt entry unexpectedly names owner {n}"
    | _, none =>
        failures := failures.push s!"formal recovered-Zorn entry has no owner: {repr c}"
    | _, some n =>
        unless env.contains n do
          failures := failures.push s!"missing recovered-Zorn owner declaration: {n} ({repr c})"
  if failures.isEmpty then
    logInfo m!"Recovered-Zorn Logos audit PASS: {allConcepts.length} concepts."
  else
    for failure in failures do
      logError m!"RECOVERED-ZORN LOGOS FAILURE: {failure}"
    throwError "Recovered-Zorn Logos audit failed"

elab "#audit_recovered_zorn_logos" : command =>
  Command.liftCoreM auditRecoveredZornLogos

attribute [spine_object] Concept Entry

end InfoGeometry.Physics.QCDRecoveredZornLogosMap
