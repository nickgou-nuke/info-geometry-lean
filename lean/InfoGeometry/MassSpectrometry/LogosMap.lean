import Lean
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SpineAttributes
import InfoGeometry.MassSpectrometry.PeakSpectrum
import InfoGeometry.MassSpectrometry.MellinMassEncoding
import InfoGeometry.MassSpectrometry.PeakFragmentMatching
import InfoGeometry.MassSpectrometry.BirkhoffAssignment
import InfoGeometry.MassSpectrometry.FragmentationDAG
import InfoGeometry.MassSpectrometry.ValuedFragmentationDAG
import InfoGeometry.MassSpectrometry.StochasticFragmentGrammar
import InfoGeometry.MassSpectrometry.DirectedOperatorDoubling
import InfoGeometry.MassSpectrometry.CausalCrossGramian
import InfoGeometry.MassSpectrometry.CausalRetraction
import InfoGeometry.MassSpectrometry.ChemicalGraph
import InfoGeometry.MassSpectrometry.FragmentationColimit
import InfoGeometry.MassSpectrometry.MolecularFragmentColimit
import InfoGeometry.MassSpectrometry.LinearBSplineKAN
import InfoGeometry.MassSpectrometry.VerifiedInferenceArchitecture

/-!
# Language-to-Logos map for the mass-spectrometry corridor

This module is deliberately metadata, not a new physical theory. It gives the
repository a machine-readable Rosetta surface from informal cross-domain
vocabulary to exact Lean declarations.

The status field distinguishes four cases:

* `literalDefinition`: an informal term is represented directly by a Lean type
  or definition;
* `provedTheorem`: the relevant mathematical claim has a theorem owner;
* `structuralBridge`: the Lean declaration proves a structural/algebraic bridge
  but not a literal physical identification;
* `openDebt`: the phrase has no theorem owner yet and must not be promoted to a
  verified claim.

`#audit_mass_spectrometry_logos` verifies that every entry advertised as
formalized names a declaration in the current Lean environment. This makes the
map usable by declaration-DAG tooling without relying on fuzzy name matching.
-/

open Lean Elab Command
open InfoGeometry.Canonical

namespace InfoGeometry.MassSpectrometry

/-- Epistemic status of an informal-to-formal mapping. -/
inductive LogosStatus where
  | literalDefinition
  | provedTheorem
  | structuralBridge
  | openDebt
  deriving DecidableEq, Repr, Inhabited

/-- Controlled vocabulary for the principal cross-domain concepts in the
mass-spectrometry formalization. -/
inductive LogosConcept where
  | peakSpectrum
  | canonicalSpectralSentence
  | commonScaleInvariantMassCoordinate
  | hardPeakFragmentMatching
  | softBirkhoffAssignment
  | fragmentationDAG
  | physicalMassDescent
  | substochasticOpenGrammar
  | pathSurprisal
  | directedCrossGramian
  | causalLogMassCone
  | moorePenroseRetraction
  | chiralOperatorDoubling
  | molecularGraph
  | fragmentationCarrierColimit
  | molecularFragmentColimit
  | linearBSplineKAN
  | certifiedStructuralInference
  | majoranaPhysicalIdentification
  | smilesEquivalence
  | universalKANApproximation
  | empiricalIdentificationAccuracy
  | operatorBerezinianTermination
  deriving DecidableEq, Repr, Inhabited

/-- One Rosetta entry connecting prose vocabulary to the theorem DAG. -/
structure LogosEntry where
  concept : LogosConcept
  phrase : String
  status : LogosStatus
  owner : Option Name
  boundary : String
  deriving Repr, Inhabited

/-- Authoritative finite vocabulary used by the audit. -/
def allLogosConcepts : List LogosConcept :=
  [ .peakSpectrum
  , .canonicalSpectralSentence
  , .commonScaleInvariantMassCoordinate
  , .hardPeakFragmentMatching
  , .softBirkhoffAssignment
  , .fragmentationDAG
  , .physicalMassDescent
  , .substochasticOpenGrammar
  , .pathSurprisal
  , .directedCrossGramian
  , .causalLogMassCone
  , .moorePenroseRetraction
  , .chiralOperatorDoubling
  , .molecularGraph
  , .fragmentationCarrierColimit
  , .molecularFragmentColimit
  , .linearBSplineKAN
  , .certifiedStructuralInference
  , .majoranaPhysicalIdentification
  , .smilesEquivalence
  , .universalKANApproximation
  , .empiricalIdentificationAccuracy
  , .operatorBerezinianTermination
  ]

/-- Exact semantic ledger. `none` is intentional closure debt, not a missing
name guessed by the mapper. -/
def logosEntry : LogosConcept → LogosEntry
  | .peakSpectrum =>
      ⟨.peakSpectrum, "mass-spectral peak", .literalDefinition,
        some ``InfoGeometry.MassSpectrometry.Peak,
        "Positive mass and nonnegative intensity only; no chemical identity is implied."⟩
  | .canonicalSpectralSentence =>
      ⟨.canonicalSpectralSentence, "canonical spectral sentence", .provedTheorem,
        some ``InfoGeometry.MassSpectrometry.Spectrum.canonicalize,
        "Canonicalization is sorting/permutation preservation, not semantic parsing."⟩
  | .commonScaleInvariantMassCoordinate =>
      ⟨.commonScaleInvariantMassCoordinate, "Mellin/log-mass scale coordinate", .provedTheorem,
        some ``InfoGeometry.MassSpectrometry.relative_log_mass_scale_invariant,
        "Common multiplicative mass scaling cancels in relative log mass; arbitrary calibration drift does not."⟩
  | .hardPeakFragmentMatching =>
      ⟨.hardPeakFragmentMatching, "hard one-to-one peak/fragment matching", .literalDefinition,
        some ``InfoGeometry.MassSpectrometry.hardAssignment,
        "A hard assignment is a permutation matrix; chemistry is not inferred by this definition."⟩
  | .softBirkhoffAssignment =>
      ⟨.softBirkhoffAssignment, "soft Birkhoff assignment", .provedTheorem,
        some ``InfoGeometry.MassSpectrometry.softAssignment_birkhoff_decomposition,
        "A doubly stochastic matrix is a convex mixture of permutations, not itself a deterministic matching."⟩
  | .fragmentationDAG =>
      ⟨.fragmentationDAG, "fragmentation causal DAG", .literalDefinition,
        some ``InfoGeometry.MassSpectrometry.FragmentationDAG,
        "Acyclicity is certified by strict rank descent."⟩
  | .physicalMassDescent =>
      ⟨.physicalMassDescent, "neutral-loss / physical mass descent", .literalDefinition,
        some ``InfoGeometry.MassSpectrometry.ValuedFragmentationDAG,
        "Physical mass descent is separate from the abstract natural-valued DAG rank."⟩
  | .substochasticOpenGrammar =>
      ⟨.substochasticOpenGrammar, "open lossy fragmentation grammar", .literalDefinition,
        some ``InfoGeometry.MassSpectrometry.StochasticGrammar,
        "Rows are substochastic and terminal deficit represents unresolved termination/loss."⟩
  | .pathSurprisal =>
      ⟨.pathSurprisal, "fragmentation-path surprisal", .literalDefinition,
        some ``InfoGeometry.MassSpectrometry.StochasticGrammar.pathSurprisal,
        "This is negative log path weight, not a claim of unique mechanistic reconstruction."⟩
  | .directedCrossGramian =>
      ⟨.directedCrossGramian, "directed cross-Gramian", .structuralBridge,
        some ``InfoGeometry.MassSpectrometry.crossGramOperator,
        "Z₁ Z₂ᵀ may carry a skew part; it is not identified with generic Transformer attention semantics."⟩
  | .causalLogMassCone =>
      ⟨.causalLogMassCone, "forward log-mass causal cone", .provedTheorem,
        some ``InfoGeometry.MassSpectrometry.logMassConeMask_support,
        "The mask certifies support in the chosen order cone; causality is an encoded model constraint."⟩
  | .moorePenroseRetraction =>
      ⟨.moorePenroseRetraction, "lossy Moore-Penrose reconstruction", .structuralBridge,
        some ``InfoGeometry.MassSpectrometry.CausalRetraction,
        "Projectors/retractions are certified; global invertibility is not asserted."⟩
  | .chiralOperatorDoubling =>
      ⟨.chiralOperatorDoubling, "forward/reverse chiral doubling", .provedTheorem,
        some ``InfoGeometry.MassSpectrometry.grading_anticommute_doubledOperator,
        "This is a Z₂-graded matrix identity."⟩
  | .molecularGraph =>
      ⟨.molecularGraph, "finite molecular graph", .literalDefinition,
        some ``InfoGeometry.MassSpectrometry.MolecularGraph,
        "Atoms and bond kinds are explicit finite labels; valence completeness and conformers are outside the owner."⟩
  | .fragmentationCarrierColimit =>
      ⟨.fragmentationCarrierColimit, "fragmentation-indexed carrier colimit", .literalDefinition,
        some ``InfoGeometry.MassSpectrometry.FragmentVertexDiagram.carrierColimit,
        "This is the genuine Mathlib colimit of the supplied Type-valued functor."⟩
  | .molecularFragmentColimit =>
      ⟨.molecularFragmentColimit, "molecular fragment reconstruction colimit", .structuralBridge,
        some ``InfoGeometry.MassSpectrometry.MolecularFragmentDiagram.VertexColimit,
        "The universal property is currently at the vertex-carrier Type level; labelled-graph categorical universality is stronger debt."⟩
  | .linearBSplineKAN =>
      ⟨.linearBSplineKAN, "continuous B-spline KAN channel", .literalDefinition,
        some ``InfoGeometry.MassSpectrometry.LinearBSplineKANData,
        "The owner proves the degree-one compactly supported specialization, not universal approximation."⟩
  | .certifiedStructuralInference =>
      ⟨.certifiedStructuralInference, "valid-by-construction inverse output", .provedTheorem,
        some ``InfoGeometry.MassSpectrometry.finiteValuedFragmentationModel_structurallyAdmissible,
        "Only encoded structural invariants are certified; empirical correctness and regulatory validity are not."⟩
  | .majoranaPhysicalIdentification =>
      ⟨.majoranaPhysicalIdentification, "molecular fragment = physical Majorana mode", .openDebt,
        none,
        "The repository has an algebraic Majorana/Pfaffian bridge only; no physical identity theorem exists."⟩
  | .smilesEquivalence =>
      ⟨.smilesEquivalence, "SMILES equivalence / serialization correctness", .openDebt,
        none,
        "No parser, quotient, or serialization theorem owner exists in this corridor."⟩
  | .universalKANApproximation =>
      ⟨.universalKANApproximation, "universal Kolmogorov-Arnold/B-spline approximation", .openDebt,
        none,
        "No density or universal representation theorem is asserted."⟩
  | .empiricalIdentificationAccuracy =>
      ⟨.empiricalIdentificationAccuracy, "empirical molecular-identification accuracy", .openDebt,
        none,
        "Dataset performance is empirical evidence, not a theorem of the formal architecture."⟩
  | .operatorBerezinianTermination =>
      ⟨.operatorBerezinianTermination,
        "operator Berezinian / Taylor-Grassmann termination",
        .openDebt,
        none,
        "Finite nilpotent-soul polynomial truncation and noncommutative Schur elimination are formalized, but no Berezinian owner or generic analytic Taylor theorem exists yet."⟩

/-- A concept is formally owned exactly when its Rosetta entry carries an owner
name and is not marked as open debt. -/
def LogosConcept.isFormalized (c : LogosConcept) : Bool :=
  match (logosEntry c).status, (logosEntry c).owner with
  | .openDebt, _ => false
  | _, some _ => true
  | _, none => false

/-- Machine audit: every advertised formal owner must exist, while open debt
must deliberately have no owner. -/
def auditMassSpectrometryLogos : CoreM Unit := do
  let env ← getEnv
  let mut failures : Array String := #[]
  for c in allLogosConcepts do
    let e := logosEntry c
    match e.status, e.owner with
    | .openDebt, none => pure ()
    | .openDebt, some n =>
        failures := failures.push s!"open-debt entry unexpectedly names owner {n}"
    | _, none =>
        failures := failures.push s!"formal entry has no owner: {repr c}"
    | _, some n =>
        if env.contains n then
          pure ()
        else
          failures := failures.push s!"owner declaration missing: {n} ({repr c})"
  if failures.isEmpty then
    logInfo m!"MassSpectrometry Logos audit PASS: {allLogosConcepts.length} concepts mapped with explicit theorem boundaries."
  else
    for failure in failures do
      logError m!"LOGOS MAP FAILURE: {failure}"
    throwError "MassSpectrometry Logos audit failed"

/-- Command-line audit surface for the language-to-Logos ledger. -/
elab "#audit_mass_spectrometry_logos" : command => do
  Command.liftCoreM auditMassSpectrometryLogos

attribute [spine_object] LogosConcept LogosEntry

end InfoGeometry.MassSpectrometry
