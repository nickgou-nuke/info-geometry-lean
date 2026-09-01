import Lean
import InfoGeometry.Canonical.SpineAttributes
import InfoGeometry.Physics.QCDFureyZornProjectorBridge
import InfoGeometry.Physics.QCDZornChargeConjugationBridge
import InfoGeometry.Physics.QCDNativeZornColorRepresentation

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
  | nativeFaithfulZornColorRepresentation
  | canonicalComplexZornEquivalence
  | zornCliffordFureyIntertwiner
  | nativeDiracSpinorColorRepresentation
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
  , .nativeFaithfulZornColorRepresentation
  , .canonicalComplexZornEquivalence
  , .zornCliffordFureyIntertwiner
  , .nativeDiracSpinorColorRepresentation
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
  | .nativeFaithfulZornColorRepresentation =>
      ⟨.nativeFaithfulZornColorRepresentation,
        "faithful gl3 representation on the native complex Zorn upper color lane",
        .theorem,
        some ``InfoGeometry.Physics.QCDNativeZornColorRepresentation.native_zorn_color_representation_packet,
        "The defining matrix action on `Fin 3 -> C` is faithful, preserves multiplication and commutators, and embeds injectively as the pure upper Zorn lane."⟩
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
  | .nativeDiracSpinorColorRepresentation =>
      ⟨.nativeDiracSpinorColorRepresentation,
        "richer faithful gl3 action on a native Zorn Dirac-spinor carrier",
        .openDebt, none,
        "The downstream `ZornColorLieRepresentation` proves a stronger faithful action on `DiracSpinor16`; migrating its Peirce/chiral spinor carrier remains separate debt."⟩


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
