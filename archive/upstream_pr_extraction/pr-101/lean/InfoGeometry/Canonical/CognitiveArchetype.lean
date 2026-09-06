import InfoGeometry.Canonical.GrothendieckErlangenProjectiveBridge
import InfoGeometry.Canonical.TessellationCocycleBridge
import InfoGeometry.Canonical.ProofCausalityBridge

/-!
# InfoGeometry.Canonical.CognitiveArchetype

Canonical archetype registry for recurring cross-domain operator patterns.

This file does not claim that a pattern is new mathematics. It records stable
recurrences already owned by the repository and provides a conservative
keyword-based detector over them.
-/

namespace InfoGeometry.Canonical.CognitiveArchetype

inductive ArchetypeKind
  | involutionProjector
  | cocycleTransport
  | projectiveNormalization
  | symmetryInvariantGeometry
  | grothendieckCompletion
  deriving DecidableEq

inductive ArchetypeStatus
  | recognized
  deriving DecidableEq

def ArchetypeKind.label : ArchetypeKind → String
  | .involutionProjector => "InvolutionProjector"
  | .cocycleTransport => "CocycleTransport"
  | .projectiveNormalization => "ProjectiveNormalization"
  | .symmetryInvariantGeometry => "SymmetryInvariantGeometry"
  | .grothendieckCompletion => "GrothendieckCompletion"

/-- A recurring cross-domain pattern with a name and keyword triggers. -/
structure ArchetypeTemplate where
  name : ArchetypeKind
  triggerTerms : Array String
  ownerSurfaces : Array Lean.Name
  status : ArchetypeStatus

namespace ArchetypeTemplate

/-- A template is detected when all trigger terms occur in the observed tags. -/
def detects (T : ArchetypeTemplate) (observedTerms : Array String) : Bool :=
  T.triggerTerms.all (fun t => observedTerms.contains t)

end ArchetypeTemplate

/-- A detected archetype along with the observed terms that triggered it. -/
structure DetectedArchetype where
  template : ArchetypeTemplate
  observedTerms : Array String

namespace DetectedArchetype

/-- A detected archetype is valid precisely when its template matches the observed terms. -/
def isValid (A : DetectedArchetype) : Bool :=
  A.template.detects A.observedTerms

end DetectedArchetype

/-- Recurring archetypes currently recognized by the repository. -/
def knownArchetypes : Array ArchetypeTemplate :=
  #[
    { name := .involutionProjector
      triggerTerms := #["O^2 = I", "d = (I+O)/2", "δ = (I-O)/2", "Δ_H = 0"]
      ownerSurfaces := #[
        `InfoGeometry.Causal.Algebra.CausalOrientation,
        `InfoGeometry.Causal.Algebra.d_sq_eq_d,
        `InfoGeometry.Causal.Algebra.δ_sq_eq_δ,
        `InfoGeometry.Causal.Algebra.Δ_H_zero,
        `InfoGeometry.Canonical.ProofCausalityBridge.d_sq_eq_d,
        `InfoGeometry.Canonical.ProofCausalityBridge.δ_sq_eq_δ,
        `InfoGeometry.Canonical.ProofCausalityBridge.Δ_H_zero]
      status := .recognized },
    { name := .cocycleTransport
      triggerTerms := #["det(exp(A)) = exp(tr(A))", "exact phase", "cocycle", "transport"]
      ownerSurfaces := #[
        `InfoGeometry.Cocycle.MatrixDetExpTrace.det_exp_eq_exp_trace,
        `InfoGeometry.Canonical.BerezinianTrace.det_exp_eq_exp_tr,
        `InfoGeometry.Canonical.HodgeKreinDeterminantBridge.det_exp_eq_exp_trace,
        `InfoGeometry.Algebraic.ExactPhaseCocycle.exactBerryPhase_one,
        `InfoGeometry.Algebraic.CartanCocycle.toRotorCocycle]
      status := .recognized },
    { name := .projectiveNormalization
      triggerTerms := #["positive ray", "normalizedShape", "sum to one", "projective count"]
      ownerSurfaces := #[
        `InfoGeometry.GromovWittenErlangen.GWProjectiveCountCalibration.normalizedShape_scale_counts,
        `InfoGeometry.GromovWittenErlangen.GWProjectiveCountCalibration.normalizedShape_sum_eq_one,
        `InfoGeometry.GromovWittenErlangen.GWCanonicalCountRayBridge.projectiveHamiltonianProfile_eq_relativeModularPotential,
        `InfoGeometry.GromovWittenErlangen.ProjectiveCountBridge.normalizedShape_sum_eq_one]
      status := .recognized },
    { name := .symmetryInvariantGeometry
      triggerTerms := #["geometry as invariant", "symmetry action", "Casimir", "Onsager"]
      ownerSurfaces := #[
        `InfoGeometry.Canonical.ErlangenOperator2.geometry_as_symmetry_invariants,
        `InfoGeometry.Canonical.ErlangenOperator2.erlangen_operator_geometry_closure,
        `InfoGeometry.Canonical.ErlangenOperator2Bridge.coadjoint_geometry_as_symmetry_invariants,
        `InfoGeometry.Canonical.ErlangenOperator2Bridge.state_geometry_as_symmetry_invariants]
      status := .recognized },
    { name := .grothendieckCompletion
      triggerTerms := #["Grothendieck", "ℕ", "ℤ", "completion"]
      ownerSurfaces := #[
        `InfoGeometry.Canonical.GrothendieckGroup.grothendieckEquivInt,
        `InfoGeometry.Canonical.K0Functor.K0_equiv_int]
      status := .recognized }
  ]

/-- Return all detected archetypes with their observed terms. -/
def detectedArchetypes (observedTerms : Array String) : Array DetectedArchetype :=
  knownArchetypes.filter (fun T => T.detects observedTerms) |>.map (fun T =>
    { template := T, observedTerms := observedTerms })

end InfoGeometry.Canonical.CognitiveArchetype
