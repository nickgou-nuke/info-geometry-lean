import Lean
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SpineAttributes
import InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient
import InfoGeometry.Physics.NuclearKleinParameterBundle
import InfoGeometry.Physics.NuclearKleinSpectralDescentBridge
import InfoGeometry.Physics.NuclearKleinPinWallpaperBridge
import InfoGeometry.Physics.NuclearKleinPresentationOperatorBridge

/-!
# Audited Logos/DAG map for the nuclear Klein topology lane

This metadata layer records only theorem-supported global-topology statements.
The finite Klein quotient, equivariant nuclear Hamiltonian, quotient descent of
effective observables, common spectral quotient, Pin/wallpaper structural
packet, and cross-domain reflection/presentation packet are formal nodes.
Stronger physical/global claims remain explicit open debt.
-/

open Lean Elab Command
open InfoGeometry.Canonical

namespace InfoGeometry.Physics.NuclearKleinTopologyLogosMap

inductive Status where
  | definition | theorem | structuralBridge | openDebt
  deriving DecidableEq, Repr, Inhabited

inductive Concept where
  | finiteKleinOrbitQuotient
  | kleinEquivariantHamiltonian
  | internalParityHolonomy
  | schurObservableDescent
  | commonKleinSpectralDescent
  | pinWallpaperKleinCompatibility
  | crossDomainReflectionPresentation
  | globalKleinClassifyingSpace
  | nuclearPinStructure
  | mobiusEigenbranchExchange
  | berryPhasePi
  | massSpectrometryKleinEnvelope
  | orbitrapKleinTopology
  | zornVorticityKleinHolonomy
  deriving DecidableEq, Repr, Inhabited

structure Entry where
  concept : Concept
  phrase : String
  status : Status
  owner : Option Name
  boundary : String
  deriving Repr, Inhabited

inductive Edge where
  | quotient_to_equivariantField
  | equivariantField_to_holonomy
  | equivariantField_to_schurDescent
  | schurDescent_to_commonSpectrum
  | quotient_to_pinWallpaper
  | holonomy_to_crossDomainPresentation
  deriving DecidableEq, Repr, Inhabited

def edgeEndpoints : Edge → Concept × Concept
  | .quotient_to_equivariantField => (.finiteKleinOrbitQuotient, .kleinEquivariantHamiltonian)
  | .equivariantField_to_holonomy => (.kleinEquivariantHamiltonian, .internalParityHolonomy)
  | .equivariantField_to_schurDescent => (.kleinEquivariantHamiltonian, .schurObservableDescent)
  | .schurDescent_to_commonSpectrum => (.schurObservableDescent, .commonKleinSpectralDescent)
  | .quotient_to_pinWallpaper => (.finiteKleinOrbitQuotient, .pinWallpaperKleinCompatibility)
  | .holonomy_to_crossDomainPresentation => (.internalParityHolonomy, .crossDomainReflectionPresentation)

def allConcepts : List Concept :=
  [ .finiteKleinOrbitQuotient, .kleinEquivariantHamiltonian,
    .internalParityHolonomy, .schurObservableDescent,
    .commonKleinSpectralDescent, .pinWallpaperKleinCompatibility,
    .crossDomainReflectionPresentation,
    .globalKleinClassifyingSpace, .nuclearPinStructure,
    .mobiusEigenbranchExchange, .berryPhasePi,
    .massSpectrometryKleinEnvelope, .orbitrapKleinTopology,
    .zornVorticityKleinHolonomy ]

def allEdges : List Edge :=
  [ .quotient_to_equivariantField, .equivariantField_to_holonomy,
    .equivariantField_to_schurDescent, .schurDescent_to_commonSpectrum,
    .quotient_to_pinWallpaper, .holonomy_to_crossDomainPresentation ]

def entry : Concept → Entry
  | .finiteKleinOrbitQuotient =>
      ⟨.finiteKleinOrbitQuotient, "finite Klein glide orbit quotient", .definition,
        some ``InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient.KleinHexQuotient,
        "A genuine finite orbit quotient; not a theorem identifying the continuum physical parameter manifold."⟩
  | .kleinEquivariantHamiltonian =>
      ⟨.kleinEquivariantHamiltonian, "Klein-equivariant operator Hamiltonian field", .definition,
        some ``InfoGeometry.Physics.NuclearKleinParameterBundle.KleinEquivariantHamiltonian,
        "The field lives on the finite torus cover and transforms by sign reflection under the glide."⟩
  | .internalParityHolonomy =>
      ⟨.internalParityHolonomy, "internal-parity realization of one base glide", .theorem,
        some ``InfoGeometry.Physics.NuclearKleinParameterBundle.KleinEquivariantHamiltonian.internalParity_holonomy,
        "Internal parity conjugation matches the supplied glide-equivariance law; not a classification of all holonomies."⟩
  | .schurObservableDescent =>
      ⟨.schurObservableDescent, "Schur effective observable descends to Klein quotient", .theorem,
        some ``InfoGeometry.Physics.NuclearKleinParameterBundle.KleinEquivariantHamiltonian.quotientEffectiveOperator_mk,
        "The effective operator is glide invariant and therefore defines an ordinary quotient function."⟩
  | .commonKleinSpectralDescent =>
      ⟨.commonKleinSpectralDescent, "nuclear and Dirac observables on a common Klein quotient", .structuralBridge,
        some ``InfoGeometry.Physics.NuclearKleinSpectralDescentBridge.common_klein_quotient_packet,
        "The observables share a quotient base; no equality or physical identification is asserted."⟩
  | .pinWallpaperKleinCompatibility =>
      ⟨.pinWallpaperKleinCompatibility, "nuclear Klein and Pin/wallpaper structural compatibility", .structuralBridge,
        some ``InfoGeometry.Physics.NuclearKleinPinWallpaperBridge.nuclear_wallpaper_klein_relation_packet,
        "Finite Klein-compatible packets coexist; conjugators and physical Pin structures are not identified."⟩
  | .crossDomainReflectionPresentation =>
      ⟨.crossDomainReflectionPresentation,
        "nuclear holonomy / spectroscopy grading / Klein-presentation packet", .structuralBridge,
        some ``InfoGeometry.Physics.NuclearKleinPresentationOperatorBridge.nuclear_spectroscopy_klein_presentation_packet,
        "Three proved reflection relations are packaged on distinct carriers; no global Klein topology for the spectroscopy carrier is inferred."⟩
  | .globalKleinClassifyingSpace =>
      ⟨.globalKleinClassifyingSpace, "Klein bottle is exact global classifying space", .openDebt, none,
        "No theorem identifies the full physical parameter space with a Klein bottle or proves a universal classifying property."⟩
  | .nuclearPinStructure =>
      ⟨.nuclearPinStructure, "global Pin± structure on nuclear parameter bundle", .openDebt, none,
        "Finite Pin/wallpaper bridges exist, but no Pin structure theorem for this nuclear bundle exists."⟩
  | .mobiusEigenbranchExchange =>
      ⟨.mobiusEigenbranchExchange, "Möbius eigenbranch exchange", .openDebt, none,
        "Existing quotient band branches are glide invariant; no branch-swap monodromy theorem is proved."⟩
  | .berryPhasePi =>
      ⟨.berryPhasePi, "Berry phase pi from Klein cycle", .openDebt, none,
        "No Berry connection, loop integral, or holonomy phase theorem is owned by this lane."⟩
  | .massSpectrometryKleinEnvelope =>
      ⟨.massSpectrometryKleinEnvelope, "mass-spectrometry doubled operator has Klein global envelope", .openDebt, none,
        "The doubled operator has a Z2 grading identity and now appears in a cross-domain Klein-presentation packet, but no theorem constructs its global parameter quotient as Klein."⟩
  | .orbitrapKleinTopology =>
      ⟨.orbitrapKleinTopology, "Orbitrap/C-trap recycling has Klein topology", .openDebt, none,
        "No instrument trajectory or phase-space quotient theorem establishes this physical topology."⟩
  | .zornVorticityKleinHolonomy =>
      ⟨.zornVorticityKleinHolonomy, "Zorn vorticity is Klein holonomy", .openDebt, none,
        "The Zorn associator defect is formalized algebraically, but not identified with nuclear vorticity or Klein holonomy."⟩

def Concept.isFormalized (c : Concept) : Bool :=
  match (entry c).status, (entry c).owner with
  | .openDebt, _ => false
  | _, some _ => true
  | _, none => false

def auditNuclearKleinTopologyLogos : CoreM Unit := do
  let env ← getEnv
  let mut failures : Array String := #[]
  for c in allConcepts do
    let e := entry c
    match e.status, e.owner with
    | .openDebt, none => pure ()
    | .openDebt, some n => failures := failures.push s!"open-debt entry unexpectedly names owner {n}"
    | _, none => failures := failures.push s!"formal entry has no owner: {repr c}"
    | _, some n => unless env.contains n do failures := failures.push s!"missing owner declaration: {n} ({repr c})"
  for edge in allEdges do
    let ep := edgeEndpoints edge
    unless ep.1.isFormalized && ep.2.isFormalized do
      failures := failures.push s!"DAG edge touches open debt: {repr edge}"
  if failures.isEmpty then
    logInfo m!"NuclearKleinTopology Logos audit PASS: {allConcepts.length} concepts and {allEdges.length} formal edges."
  else
    for failure in failures do logError m!"NUCLEAR KLEIN TOPOLOGY LOGOS FAILURE: {failure}"
    throwError "NuclearKleinTopology Logos audit failed"

elab "#audit_nuclear_klein_topology_logos" : command =>
  Command.liftCoreM auditNuclearKleinTopologyLogos

end InfoGeometry.Physics.NuclearKleinTopologyLogosMap
