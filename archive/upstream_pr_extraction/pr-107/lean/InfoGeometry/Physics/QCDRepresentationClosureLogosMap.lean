import Lean
import InfoGeometry.Canonical.SpineAttributes
import InfoGeometry.Physics.QCDRepresentationClosureInterfaces
import InfoGeometry.Physics.QCDArchitectureSynthesis

/-!
# Audited representation-closure frontier

This ledger isolates the last representation-theoretic seam of the QCD
structural lane.  The generic intertwiner interface and theorem-level
architecture capstone are formal.  A concrete intertwiner from the complex
triplet-plus-singlet color-spinor representation into a complexified Furey
`Cl(5,5)` carrier remains explicit open debt.
-/

open Lean Elab Command
open InfoGeometry.Canonical

namespace InfoGeometry.Physics.QCDRepresentationClosureLogosMap

inductive Status where
  | theorem
  | structuralBridge
  | openDebt
  deriving DecidableEq, Repr, Inhabited

inductive Concept where
  | representationIntertwinerInterface
  | representationFockCapstone
  | monodromySchurCapstone
  | theoremSafeArchitectureCapstone
  | colorSpinorToFureyIntertwiner
  | fureyTargetSU3Action
  | fureyMinimalLeftIdeal
  deriving DecidableEq, Repr, Inhabited

structure Entry where
  concept : Concept
  phrase : String
  status : Status
  owner : Option Name
  boundary : String
  deriving Repr, Inhabited

def allConcepts : List Concept :=
  [ .representationIntertwinerInterface
  , .representationFockCapstone
  , .monodromySchurCapstone
  , .theoremSafeArchitectureCapstone
  , .colorSpinorToFureyIntertwiner
  , .fureyTargetSU3Action
  , .fureyMinimalLeftIdeal
  ]

def entry : Concept → Entry
  | .representationIntertwinerInterface =>
      ⟨.representationIntertwinerInterface,
        "generic color-representation intertwiner interface",
        .structuralBridge,
        some ``InfoGeometry.Physics.QCDRepresentationClosureInterfaces.ColorRepresentationIntertwiner.map_commutator,
        "A supplied intertwiner transports the native color-spinor commutator action to an arbitrary complex target representation; no Furey target is constructed here."⟩
  | .representationFockCapstone =>
      ⟨.representationFockCapstone,
        "SU(3) representation / exterior-Furey / thirds-spectrum capstone",
        .structuralBridge,
        some ``InfoGeometry.Physics.QCDArchitectureSynthesis.representation_fock_packet,
        "Packages independently proved representation, exterior injection, conjugate-Furey basis membership, and occupation-spectrum facts without identifying the carriers."⟩
  | .monodromySchurCapstone =>
      ⟨.monodromySchurCapstone,
        "Schur / Artin / twelvefold / anyon capstone",
        .structuralBridge,
        some ``InfoGeometry.Physics.QCDArchitectureSynthesis.monodromy_schur_packet,
        "Packages exact identities on distinct carriers; no angular, neutrino, or physical anyon interpretation is asserted."⟩
  | .theoremSafeArchitectureCapstone =>
      ⟨.theoremSafeArchitectureCapstone,
        "full theorem-safe QCD structural architecture packet",
        .structuralBridge,
        some ``InfoGeometry.Physics.QCDArchitectureSynthesis.theorem_safe_architecture_packet,
        "Dependency capstone only; it does not claim the represented carriers are isomorphic."⟩
  | .colorSpinorToFureyIntertwiner =>
      ⟨.colorSpinorToFureyIntertwiner,
        "explicit ColorSpinor4 to complexified Furey intertwiner",
        .openDebt, none,
        "Requires a concrete complex target carrier, linear map, target SU(3) action, and proof of equivariance."⟩
  | .fureyTargetSU3Action =>
      ⟨.fureyTargetSU3Action,
        "native SU(3) action preserving the Furey span",
        .openDebt, none,
        "The native SU(3) action is proved on ColorSpinor4, not yet on the real Cl(5,5) Furey span or a specified complexification."⟩
  | .fureyMinimalLeftIdeal =>
      ⟨.fureyMinimalLeftIdeal,
        "Furey span is a minimal left ideal",
        .openDebt, none,
        "The current owner is a finite submodule span with selected membership theorems; full left-action stability and minimality are not proved."⟩


def auditRepresentationClosure : CoreM Unit := do
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
  if failures.isEmpty then
    logInfo m!"QCD representation-closure audit PASS: {allConcepts.length} concepts."
  else
    for failure in failures do
      logError m!"QCD REPRESENTATION-CLOSURE FAILURE: {failure}"
    throwError "QCD representation-closure audit failed"

elab "#audit_qcd_representation_closure" : command =>
  Command.liftCoreM auditRepresentationClosure

attribute [spine_object] Concept Entry

end InfoGeometry.Physics.QCDRepresentationClosureLogosMap
