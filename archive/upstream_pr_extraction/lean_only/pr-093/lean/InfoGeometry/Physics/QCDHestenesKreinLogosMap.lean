import Lean
import InfoGeometry.Canonical.SpineAttributes
import InfoGeometry.Physics.QCDHestenesKreinSynthesis

open Lean Elab Command
open InfoGeometry.Canonical

namespace InfoGeometry.Physics.QCDHestenesKreinLogosMap

inductive Status where
  | theorem
  | structuralBridge
  | openDebt
  deriving DecidableEq, Repr, Inhabited

inductive Concept where
  | realColorInternalComplex
  | realColorConjugation
  | realColorRepresentation
  | fockHestenesPhase
  | realZornFureyCarrier
  | zornFockInternalComplexIntertwiner
  | fockColorActionCommutation
  | colorSpinorFureyEquivariance
  deriving DecidableEq, Repr, Inhabited

structure Entry where
  concept : Concept
  phrase : String
  status : Status
  owner : Option Name
  boundary : String
  deriving Repr, Inhabited

def allConcepts : List Concept :=
  [ .realColorInternalComplex
  , .realColorConjugation
  , .realColorRepresentation
  , .fockHestenesPhase
  , .realZornFureyCarrier
  , .zornFockInternalComplexIntertwiner
  , .fockColorActionCommutation
  , .colorSpinorFureyEquivariance
  ]


def entry : Concept → Entry
  | .realColorInternalComplex =>
      ⟨.realColorInternalComplex,
        "real three-colour carrier with internal square-minus-one Hestenes axis",
        .theorem,
        some ``InfoGeometry.Physics.QCDHestenesRealColorRepresentation.realColorJ_sq,
        "The real colour carrier uses a pointwise two-plane rotation J with J^2=-I."⟩
  | .realColorConjugation =>
      ⟨.realColorConjugation,
        "real-linear conjugation involution anticommutes with the internal complex axis",
        .theorem,
        some ``InfoGeometry.Physics.QCDHestenesRealColorRepresentation.realColorConj_anticomm_J,
        "C^2=I is theorem-owned separately and C J = -J C is proved on the real carrier."⟩
  | .realColorRepresentation =>
      ⟨.realColorRepresentation,
        "faithful realification of the complex three-colour representation commuting with J",
        .theorem,
        some ``InfoGeometry.Physics.QCDHestenesRealColorRepresentation.hestenes_real_color_packet,
        "The transported gl3(C) action is faithful, preserves commutators, and commutes with J."⟩
  | .fockHestenesPhase =>
      ⟨.fockHestenesPhase,
        "real Cl(5,5) master Fock Hestenes phase",
        .theorem,
        some ``InfoGeometry.Physics.QCDHestenesKreinFockPhaseBridge.two_sheet_and_fock_complex_axes_packet,
        "The five-mode master phase squares to -I and anticommutes with master chirality."⟩
  | .realZornFureyCarrier =>
      ⟨.realZornFureyCarrier,
        "real canonical Zorn carrier injects into the Cl(5,5) Furey carrier",
        .structuralBridge,
        some ``InfoGeometry.Physics.QCDHestenesKreinSynthesis.hestenes_zorn_furey_carrier_packet,
        "The injection is real-linear and basis-exact; no multiplicative Zorn-to-Clifford map is claimed."⟩
  | .zornFockInternalComplexIntertwiner =>
      ⟨.zornFockInternalComplexIntertwiner,
        "Zorn/Furey carrier map intertwines internal complex structures",
        .openDebt, none,
        "A theorem Phi J_Z = J_F Phi still requires compatible J operators on the actual source and target carrier map."⟩
  | .fockColorActionCommutation =>
      ⟨.fockColorActionCommutation,
        "SU(3) colour action on the master Fock carrier commutes with the Hestenes phase",
        .openDebt, none,
        "No native SU(3) action on the 32D master Fock carrier is supplied by this lane."⟩
  | .colorSpinorFureyEquivariance =>
      ⟨.colorSpinorFureyEquivariance,
        "ColorSpinor4/Furey real-linear SU(3)-equivariant intertwiner",
        .openDebt, none,
        "The generic intertwiner shape is owned elsewhere; the concrete Furey target action remains to be constructed."⟩


def auditHestenesKreinLogos : CoreM Unit := do
  let env ← getEnv
  let mut failures : Array String := #[]
  for c in allConcepts do
    let e := entry c
    match e.status, e.owner with
    | .openDebt, none => pure ()
    | .openDebt, some n =>
        failures := failures.push s!"open-debt entry unexpectedly names owner {n}"
    | _, none =>
        failures := failures.push s!"formal Hestenes/Krein entry has no owner: {repr c}"
    | _, some n =>
        unless env.contains n do
          failures := failures.push s!"missing Hestenes/Krein owner declaration: {n} ({repr c})"
  if failures.isEmpty then
    logInfo m!"Hestenes/Krein QCD Logos audit PASS: {allConcepts.length} concepts."
  else
    for failure in failures do
      logError m!"HESTENES-KREIN LOGOS FAILURE: {failure}"
    throwError "Hestenes/Krein QCD Logos audit failed"

elab "#audit_qcd_hestenes_krein_logos" : command =>
  Command.liftCoreM auditHestenesKreinLogos

attribute [spine_object] Concept Entry

end InfoGeometry.Physics.QCDHestenesKreinLogosMap
