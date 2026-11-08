import Mathlib.CategoryTheory.Category.Preorder
import InfoGeometry.Meta.EpistemicCompilerChain
import InfoGeometry.Epistemology.EpistemicFunctor
import InfoGeometry.Causal.FiniteDependencyCompiler
import InfoGeometry.Topology.ChiralDirectedGraphHomotopy
import InfoGeometry.Epistemology.ArchetypeHomotopyFramework
import InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge
import InfoGeometry.Twistor.PenroseIncidence
import InfoGeometry.Twistor.ChiralTwistorSheets
import InfoGeometry.Twistor.PenroseSignedCCRGeometry
import InfoGeometry.Twistor.FiniteAmbitwistorParaKahler

/-!
# Compositional epistemic compiler

This module connects the existing typed-archetype gate, finite prerequisite
poset, dependency scheduler, and directed path homotopy owner.  The target
category is Mathlib's preorder category on the existing
`CompilationArchetype`; the graph-to-category map is therefore forced to
carry a genuine prerequisite proof on every edge.
-/

namespace InfoGeometry.MetaCompiler.Integration

open CategoryTheory
open InfoGeometry.MetaCompiler
open InfoGeometry.Epistemology.EpistemicFunctor
open InfoGeometry.Epistemology.EpistemicFunctor.CompilationArchetype
open InfoGeometry.Causal.FiniteDependencyCompiler
open InfoGeometry.Topology
open InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.ChiralTwistorSheets
open InfoGeometry.Twistor.PenroseSignedCCRGeometry
open InfoGeometry.Twistor.FiniteAmbitwistorParaKahler
open InfoGeometry.Twistor.PenroseTwistor

/-- Only proved archetypes contribute to the semantic-evidence branch of the
    finite compiler poset. Candidate and validated items remain at raw intake;
    validation alone is not promoted to kernel evidence. -/
def statusEvidenceStage : Status → CompilationArchetype
  | .candidate => rawStreamToken
  | .validated => rawStreamToken
  | .proved => proofEvidence

/-- The workflow poset as the generic prerequisite graph from the
epistemic/homotopy owner. -/
abbrev compilationPrerequisiteGraph : ChiralDigraph :=
  InfoGeometry.Epistemology.ArchetypeHomotopyFramework.prerequisiteGraph
    CompilationArchetype

/-- Any directed proof graph whose edges carry prerequisite inequalities has a
    canonical map to the finite epistemic prerequisite graph. -/
def prerequisiteGraphHom (G : ChiralDigraph)
    (vertex : G.Vertex → CompilationArchetype)
    (edgeRespectsPrerequisite : ∀ {u v}, G.edge u v → vertex u ≤ vertex v) :
    ChiralDigraphHom G compilationPrerequisiteGraph :=
  InfoGeometry.Epistemology.ArchetypeHomotopyFramework.prerequisiteGraphHom
    vertex edgeRespectsPrerequisite

/-- Every directed path transports to a causal comparison in the owner
    prerequisite poset. -/
theorem mapPath_prerequisite
    {G : ChiralDigraph} (F : ChiralDigraphHom G compilationPrerequisiteGraph)
    {u v : G.Vertex} (p : DirectedPath G u v) :
    F.mapVertex u ≤ F.mapVertex v := by
  exact InfoGeometry.Epistemology.ArchetypeHomotopyFramework.mapPath_le F p

/-- Legacy universal-quotient endpoint comparison. This proves reachability
ordering only; it does not certify an elementary path homotopy. -/
theorem legacyPathClass_prerequisite
    {G : ChiralDigraph} (F : ChiralDigraphHom G compilationPrerequisiteGraph)
    {u v : G.Vertex} (p : DirectedPathClass G u v) :
    F.mapVertex u ≤ F.mapVertex v := by
  exact InfoGeometry.Epistemology.ArchetypeHomotopyFramework.legacyPathClass_le F p

/- Compatibility adapter for the legacy quotient. New evidence-bearing
   developments should use `presentedPathEpistemicFunctor` below. -/
section HomotopyFunctor

variable {G : ChiralDigraph}
variable [hRight : Fact (HomotopyAppendCompatible G)]
variable [hLeft : Fact (HomotopyAppendLeftCompatible G)]

local instance : Category (ChiralPathQuotientCategory G) :=
  ChiralPathQuotientCategory.category G hRight.out hLeft.out

/-- The legacy universal path quotient maps to the prerequisite preorder.
    Its morphisms witness endpoint reachability only. -/
def legacyDirectedHomotopyEpistemicFunctor
    (F : ChiralDigraphHom G compilationPrerequisiteGraph) :
    ChiralPathQuotientCategory G ⥤ CompilationArchetype :=
  InfoGeometry.Epistemology.ArchetypeHomotopyFramework.legacyUniversalPathFunctor F

/-- A declared path presentation maps to the prerequisite preorder without
using the legacy universal two-cell relation. -/
def presentedPathEpistemicFunctor {P : DirectedPathPresentation G}
    (F : ChiralDigraphHom G compilationPrerequisiteGraph) :
    PresentedPathCategory P ⥤ CompilationArchetype :=
  InfoGeometry.Epistemology.ArchetypeHomotopyFramework.presentedPathFunctor F

end HomotopyFunctor

/-- The epistemic scheduler executes its canonical finite poset schedule as
    the very list certified by the owner validity theorem. -/
theorem canonicalPipeline_compiles :
    compile (Node := CompilationArchetype) ∅ canonicalPipeline =
      some canonicalPipeline :=
  compile_of_valid canonicalPipeline_valid

/-- The evidence node required by kernel admission occurs strictly before the
    admission node in the executable schedule. -/
theorem proofEvidence_precedes_kernelAdmission :
    canonicalPipeline.idxOf proofEvidence <
      canonicalPipeline.idxOf kernelCertifiedAdmission := by
  decide

/-- The type-indexed promotion gate supplies claim evidence at the same
    `proofEvidence` stage that the finite scheduler places before kernel
    admission. -/
theorem promotion_supplies_scheduled_evidence
    {Input : Type} {s : Status} (arch : TypedArchetype Input s)
    (proof : ∀ x, arch.claim x) :
    (∀ x, (TypedArchetype.promoteToProved arch proof).claim x) ∧
      statusEvidenceStage Status.proved = proofEvidence ∧
      proofEvidence ∈ canonicalPipeline ∧
      canonicalPipeline.idxOf proofEvidence <
        canonicalPipeline.idxOf kernelCertifiedAdmission := by
  refine ⟨proof, rfl, ?_, proofEvidence_precedes_kernelAdmission⟩
  decide

/-- Promotion preserves the metadata phase consumed by the phase-order owner,
    so typed evidence cannot silently move to a different workflow phase. -/
@[simp] theorem promotion_preserves_phase
    {Input : Type} {s : Status} (arch : TypedArchetype Input s)
    (proof : ∀ x, arch.claim x) :
    (TypedArchetype.promoteToProved arch proof).phase = arch.phase := rfl

/-! ## Local beta commuting cells

The beta relation has a genuine elementary diamond when the redexes occur in
the two separate branches of an application. This presentation declares only
that local interchange law; it does not assert unrestricted confluence. -/

/-- The directed graph whose edges are the lambda owner's capture-avoiding
one-step beta reductions. Its constant chiral label adds no semantic claim. -/
noncomputable def lambdaBetaDigraph : ChiralDigraph where
  Vertex := LambdaTerm
  edge := LambdaBetaStep
  edge_decidable := fun _ _ => Classical.propDecidable _
  sector := fun _ => .left
  allowedTransition := fun _ _ => True
  transition_decidable := fun _ _ => Classical.propDecidable _
  edge_allowed := by intro u v h; trivial

/-- The local square formed by reducing the function and argument branches of
an application in either order. -/
def lambdaBetaBranchCell {u v : LambdaTerm}
    (p q : DirectedPath lambdaBetaDigraph u v) : Prop :=
  match u, v with
  | LambdaTerm.app f a, LambdaTerm.app f' a' =>
      ∃ (hf : LambdaBetaStep f f') (ha : LambdaBetaStep a a'),
        p = @DirectedPath.cons lambdaBetaDigraph _ _ _
          (LambdaBetaStep.appFunction hf)
          (@DirectedPath.cons lambdaBetaDigraph _ _ _
            (LambdaBetaStep.appArgument ha)
            (DirectedPath.refl (G := lambdaBetaDigraph) (LambdaTerm.app f' a'))) ∧
        q = @DirectedPath.cons lambdaBetaDigraph _ _ _
          (LambdaBetaStep.appArgument ha)
          (@DirectedPath.cons lambdaBetaDigraph _ _ _
            (LambdaBetaStep.appFunction hf)
            (DirectedPath.refl (G := lambdaBetaDigraph) (LambdaTerm.app f' a')))
  | _, _ => False

/-- The lambda beta presentation identifies exactly the independent-branch
diamonds. -/
noncomputable def lambdaBetaPathPresentation :
    DirectedPathPresentation lambdaBetaDigraph where
  cell := lambdaBetaBranchCell

/-- The two orders of independent application-branch beta reduction denote
the same path in the presented category. -/
theorem lambdaBeta_branch_diamond {f f' a a' : LambdaTerm}
    (hf : LambdaBetaStep f f') (ha : LambdaBetaStep a a') :
    PresentedPathHomotopy lambdaBetaPathPresentation
      (@DirectedPath.cons lambdaBetaDigraph _ _ _ (LambdaBetaStep.appFunction hf)
        (@DirectedPath.cons lambdaBetaDigraph _ _ _ (LambdaBetaStep.appArgument ha)
          (DirectedPath.refl (G := lambdaBetaDigraph) (LambdaTerm.app f' a'))))
      (@DirectedPath.cons lambdaBetaDigraph _ _ _ (LambdaBetaStep.appArgument ha)
        (@DirectedPath.cons lambdaBetaDigraph _ _ _ (LambdaBetaStep.appFunction hf)
          (DirectedPath.refl (G := lambdaBetaDigraph) (LambdaTerm.app f' a')))) := by
  apply Relation.EqvGen.rel
  apply ContextualPathRewrite.generator
  exact ⟨hf, ha, rfl, rfl⟩

/-! ## Twistor-labelled beta computation

This layer uses the existing Penrose spinor pair as the node payload and the
actual de Bruijn beta-step relation from the lambda owner. A wire carries its
own prerequisite proof; neither twistor incidence nor beta reduction alone is
claimed to imply a compiler-stage order.
-/

inductive NetColor
  | black
  | white
  deriving DecidableEq, Repr

inductive NetFlow
  | forward
  | backward
  deriving DecidableEq, Repr

/-- A computation node carrying a genuine Penrose incidence point and spinor.
The twistor is derived from the owner's incidence linear map, not postulated
as an unrelated pair. -/
structure TwistorLambdaState where
  spacetimePoint : ComplexSpacetime
  incidenceSpinor : Spinor2
  /-- The conjugate twistor is an independent geometric datum, constrained
      by the owned finite ambitwistor incidence relation below. -/
  conjugateTwistor : DualTwistor4
  term : LambdaTerm
  stage : CompilationArchetype
  color : NetColor
  flow : NetFlow
  ambitwistorIncidence : IsAmbitwistor conjugateTwistor
    (incidenceLinearMap spacetimePoint incidenceSpinor)

/-- The Penrose twistor determined by the state, in the owner's native carrier. -/
def TwistorLambdaState.twistor (s : TwistorLambdaState) : Twistor4 :=
  incidenceLinearMap s.spacetimePoint s.incidenceSpinor

/-- A node lies on the finite ambitwistor correspondence exactly when its
    conjugate twistor pairs to zero with its Penrose incidence twistor. -/
def TwistorLambdaState.IsIncident (s : TwistorLambdaState) : Prop :=
  IsAmbitwistor s.conjugateTwistor s.twistor

/-- The incidence twistor represented in the signed CCR coefficient frame.
This composes the concrete incidence map, the owned four-coordinate carrier
equivalence, and the signed conjugation embedding. The codomain is the CCR
coefficient pair; it is not identified here with the algebraic dual twistor. -/
noncomputable def TwistorLambdaState.signedTwistor (s : TwistorLambdaState) :
    InfoGeometry.Twistor.PenrosePolynomialCCR.Coeff :=
  signedPair (penroseTwistor4CarrierEquiv s.twistor)

/-- The actual algebraic dual twistor represented by the Penrose pairing. -/
noncomputable def TwistorLambdaState.dualTwistor (s : TwistorLambdaState) :
    Module.Dual ℝ TwistorCarrier :=
  twistorToDual (penroseTwistor4CarrierEquiv s.twistor)

@[simp] theorem TwistorLambdaState.signedTwistor_eq (s : TwistorLambdaState) :
    s.signedTwistor = signedPair (penroseTwistor4CarrierEquiv
      (incidenceLinearMap s.spacetimePoint s.incidenceSpinor)) := rfl

/-- The signed coefficient payload retains the incidence spinor: the second
component of the incidence twistor recovers it, and both owner maps are
injective. -/
theorem TwistorLambdaState.signedTwistor_injective
    (x : ComplexSpacetime) (π ρ : Spinor2)
    (h : signedPair (penroseTwistor4CarrierEquiv (incidenceLinearMap x π)) =
      signedPair (penroseTwistor4CarrierEquiv (incidenceLinearMap x ρ))) : π = ρ := by
  apply incidenceLinearMap_injective x
  apply penroseTwistor4CarrierEquiv.injective
  apply signedPair_injective
  exact h

/-- The incidence spinor is recoverable from the covector defined by the
nondegenerate Penrose pairing. -/
theorem TwistorLambdaState.dualTwistor_injective
    (x : ComplexSpacetime) (π ρ : Spinor2)
    (h : twistorToDual (penroseTwistor4CarrierEquiv (incidenceLinearMap x π)) =
      twistorToDual (penroseTwistor4CarrierEquiv (incidenceLinearMap x ρ))) : π = ρ := by
  apply incidenceLinearMap_injective x
  apply penroseTwistor4CarrierEquiv.injective
  exact twistorToDual_injective h

/-- The signed CCR conjugate block evaluates to the actual dual-twistor
functional, so the coefficient frame is tied to the dual by the owned pairing. -/
theorem TwistorLambdaState.dualTwistor_eq_signedCoordinates
    (s : TwistorLambdaState) (w : TwistorCarrier) :
    s.dualTwistor w =
      2 * (InfoGeometry.Twistor.PenrosePolynomialCCR.contraction
        w s.signedTwistor.2).re := by
  change twistorToDual (penroseTwistor4CarrierEquiv s.twistor) w = _
  rw [twistorToDual_apply_signedPair]
  rfl

@[simp] theorem TwistorLambdaState.twistor_eq_incidence (s : TwistorLambdaState) :
    s.twistor = (Complex.I • omegaLinearMap s.spacetimePoint s.incidenceSpinor,
      s.incidenceSpinor) := rfl

/-- A forward computation wire: one beta step, fixed external twistor data,
opposite black/white endpoint colors, and an explicit prerequisite proof. -/
structure TwistorLambdaWire (source target : TwistorLambdaState) where
  beta : LambdaBetaStep source.term target.term
  point_preserved : source.spacetimePoint = target.spacetimePoint
  spinor_preserved : source.incidenceSpinor = target.incidenceSpinor
  conjugateTwistor_preserved : source.conjugateTwistor = target.conjugateTwistor
  color_flips : source.color ≠ target.color
  flow_flips : source.flow ≠ target.flow
  prerequisite : source.stage ≤ target.stage

/-- Build a wire when the external incidence data are fixed, the chiral and
flow labels flip, and the stages are ordered. This packages only the wire
invariants; beta reduction remains an explicit argument. -/
theorem TwistorLambdaWire.ofBeta {source target : TwistorLambdaState}
    (hβ : LambdaBetaStep source.term target.term)
    (hpoint : source.spacetimePoint = target.spacetimePoint)
    (hspinor : source.incidenceSpinor = target.incidenceSpinor)
    (hconjugate : source.conjugateTwistor = target.conjugateTwistor)
    (hcolor : source.color ≠ target.color) (hflow : source.flow ≠ target.flow)
    (hstage : source.stage ≤ target.stage) : TwistorLambdaWire source target :=
  ⟨hβ, hpoint, hspinor, hconjugate, hcolor, hflow, hstage⟩

/-- A nonzero spinor and a nonzero conjugate spinor on the zero incidence
plane. Their disjoint coordinate supports make the owned ambitwistor pairing
vanish. -/
def twistorWireModelSpinor : Spinor2 := fun i => if i = 0 then 1 else 0

def twistorWireModelConjugate : DualTwistor4 :=
  (fun _ => 0, fun i => if i = 1 then 1 else 0)

theorem twistorWireModelSpinor_ne_zero : twistorWireModelSpinor ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [twistorWireModelSpinor] at h0

theorem twistorWireModelConjugate_ne_zero : twistorWireModelConjugate ≠ 0 := by
  intro h
  have hs := congrArg Prod.snd h
  have h1 := congrFun hs 1
  norm_num [twistorWireModelConjugate] at h1

theorem twistorWireModel_incident :
    IsAmbitwistor twistorWireModelConjugate
      (incidenceLinearMap (0 : ComplexSpacetime) twistorWireModelSpinor) := by
  have hzero : omegaLinearMap (0 : ComplexSpacetime) twistorWireModelSpinor = 0 := by
    rw [omegaLinearMap_apply]
    simp
  rw [incidenceLinearMap_apply, hzero]
  simp [IsAmbitwistor, ambitwistorPairing, spinorPairing,
    twistorWireModelConjugate, twistorWireModelSpinor]

def twistorWireModelSource : TwistorLambdaState where
  spacetimePoint := 0
  incidenceSpinor := twistorWireModelSpinor
  conjugateTwistor := twistorWireModelConjugate
  term := LambdaTerm.app
    (LambdaTerm.app (LambdaTerm.abs (.var 0)) (.var 0)) (.var 0)
  stage := .rawStreamToken
  color := .black
  flow := .forward
  ambitwistorIncidence := twistorWireModel_incident

def twistorWireModelTarget : TwistorLambdaState where
  spacetimePoint := 0
  incidenceSpinor := twistorWireModelSpinor
  conjugateTwistor := twistorWireModelConjugate
  term := LambdaTerm.app (.var 0) (.var 0)
  stage := .rawStreamToken
  color := .white
  flow := .backward
  ambitwistorIncidence := twistorWireModel_incident

/-- A closed, nondegenerate wire witness: one contextual identity-redex step
with both incidence spinors nonzero and the ambient incidence condition met. -/
theorem twistorLambdaWireModel :
    TwistorLambdaWire twistorWireModelSource twistorWireModelTarget :=
  TwistorLambdaWire.ofBeta
    (LambdaBetaStep.appFunction (LambdaBetaStep.identity (.var 0)))
    rfl rfl rfl (by decide) (by decide) le_rfl

private def netColorSector : NetColor → ChiralSector
  | .black => .left
  | .white => .right

/-- Directed graph of the proof-carrying, twistor-labelled beta wires. -/
noncomputable def twistorLambdaDigraph : ChiralDigraph where
  Vertex := TwistorLambdaState
  edge := fun u v => Nonempty (TwistorLambdaWire u v)
  edge_decidable := fun _ _ => Classical.propDecidable _
  sector := fun s => netColorSector s.color
  allowedTransition := fun a b => a ≠ b
  transition_decidable := fun _ _ => Classical.propDecidable _
  edge_allowed := by
    rintro u v ⟨wire⟩
    cases hu : u.color <;> cases hv : v.color
    · exact False.elim (wire.color_flips (hu.trans hv.symm))
    · decide
    · decide
    · exact False.elim (wire.color_flips (hu.trans hv.symm))

/-- Canonical source of a labelled branch square. -/
def twistorBranchSource (x : ComplexSpacetime) (π : Spinor2)
    (W : DualTwistor4) (hInc : IsAmbitwistor W (incidenceLinearMap x π))
    (stage : CompilationArchetype) (f a : LambdaTerm) : TwistorLambdaState :=
  ⟨x, π, W, LambdaTerm.app f a, stage, .black, .forward, hInc⟩

/-- Intermediate node after reducing the function branch. -/
def twistorBranchFunctionNode (x : ComplexSpacetime) (π : Spinor2)
    (W : DualTwistor4) (hInc : IsAmbitwistor W (incidenceLinearMap x π))
    (stage : CompilationArchetype) (f' a : LambdaTerm) : TwistorLambdaState :=
  ⟨x, π, W, LambdaTerm.app f' a, stage, .white, .backward, hInc⟩

/-- Intermediate node after reducing the argument branch. -/
def twistorBranchArgumentNode (x : ComplexSpacetime) (π : Spinor2)
    (W : DualTwistor4) (hInc : IsAmbitwistor W (incidenceLinearMap x π))
    (stage : CompilationArchetype) (f a' : LambdaTerm) : TwistorLambdaState :=
  ⟨x, π, W, LambdaTerm.app f a', stage, .white, .backward, hInc⟩

/-- Common target of the two independent branch reductions. -/
def twistorBranchTarget (x : ComplexSpacetime) (π : Spinor2)
    (W : DualTwistor4) (hInc : IsAmbitwistor W (incidenceLinearMap x π))
    (stage : CompilationArchetype) (f' a' : LambdaTerm) : TwistorLambdaState :=
  ⟨x, π, W, LambdaTerm.app f' a', stage, .black, .forward, hInc⟩

/-- The twistor-labelled path that reduces the function branch first. -/
def twistorBranchFunctionThenArgumentPath
    (x : ComplexSpacetime) (π : Spinor2) (W : DualTwistor4)
    (hInc : IsAmbitwistor W (incidenceLinearMap x π))
    (stage : CompilationArchetype)
    {f f' a a' : LambdaTerm} (hf : LambdaBetaStep f f') (ha : LambdaBetaStep a a') :
    DirectedPath twistorLambdaDigraph
      (twistorBranchSource x π W hInc stage f a) (twistorBranchTarget x π W hInc stage f' a') := by
  let source := twistorBranchSource x π W hInc stage f a
  let middle := twistorBranchFunctionNode x π W hInc stage f' a
  let target := twistorBranchTarget x π W hInc stage f' a'
  refine @DirectedPath.cons twistorLambdaDigraph source middle target ?_
    (@DirectedPath.cons twistorLambdaDigraph middle target target ?_
      (DirectedPath.refl (G := twistorLambdaDigraph) target))
  · exact ⟨TwistorLambdaWire.ofBeta (LambdaBetaStep.appFunction hf)
      rfl rfl rfl (by simp [source, middle, twistorBranchSource, twistorBranchFunctionNode])
      (by simp [source, middle, twistorBranchSource, twistorBranchFunctionNode]) le_rfl⟩
  · exact ⟨TwistorLambdaWire.ofBeta (LambdaBetaStep.appArgument ha)
      rfl rfl rfl (by simp [middle, target, twistorBranchFunctionNode, twistorBranchTarget])
      (by simp [middle, target, twistorBranchFunctionNode, twistorBranchTarget]) le_rfl⟩

/-- The twistor-labelled path that reduces the argument branch first. -/
def twistorBranchArgumentThenFunctionPath
    (x : ComplexSpacetime) (π : Spinor2) (W : DualTwistor4)
    (hInc : IsAmbitwistor W (incidenceLinearMap x π))
    (stage : CompilationArchetype)
    {f f' a a' : LambdaTerm} (hf : LambdaBetaStep f f') (ha : LambdaBetaStep a a') :
    DirectedPath twistorLambdaDigraph
      (twistorBranchSource x π W hInc stage f a) (twistorBranchTarget x π W hInc stage f' a') := by
  let source := twistorBranchSource x π W hInc stage f a
  let middle := twistorBranchArgumentNode x π W hInc stage f a'
  let target := twistorBranchTarget x π W hInc stage f' a'
  refine @DirectedPath.cons twistorLambdaDigraph source middle target ?_
    (@DirectedPath.cons twistorLambdaDigraph middle target target ?_
      (DirectedPath.refl (G := twistorLambdaDigraph) target))
  · exact ⟨TwistorLambdaWire.ofBeta (LambdaBetaStep.appArgument ha)
      rfl rfl rfl (by simp [source, middle, twistorBranchSource, twistorBranchArgumentNode])
      (by simp [source, middle, twistorBranchSource, twistorBranchArgumentNode]) le_rfl⟩
  · exact ⟨TwistorLambdaWire.ofBeta (LambdaBetaStep.appFunction hf)
      rfl rfl rfl (by simp [middle, target, twistorBranchArgumentNode, twistorBranchTarget])
      (by simp [middle, target, twistorBranchArgumentNode, twistorBranchTarget]) le_rfl⟩

/-- The concrete twistor computation graph maps to the finite prerequisite
poset by projecting each node's phase; the edge proof is carried by the wire. -/
noncomputable def twistorLambdaEpistemicHom :
    ChiralDigraphHom twistorLambdaDigraph compilationPrerequisiteGraph :=
  prerequisiteGraphHom twistorLambdaDigraph (fun s => s.stage)
    (by
      intro u v e
      rcases e with ⟨wire⟩
      exact wire.prerequisite)

/-- Every graph path is a genuine multi-step beta computation. -/
inductive LambdaBetaReachable : LambdaTerm → LambdaTerm → Prop
  | refl (t) : LambdaBetaReachable t t
  | step {t u v} : LambdaBetaStep t u → LambdaBetaReachable u v →
      LambdaBetaReachable t v

theorem twistorPath_beta_reachable {u v : TwistorLambdaState}
    (p : DirectedPath twistorLambdaDigraph u v) :
    LambdaBetaReachable u.term v.term := by
  refine DirectedPath.rec
    (motive := fun {a b : TwistorLambdaState}
      (_ : DirectedPath twistorLambdaDigraph a b) =>
        LambdaBetaReachable a.term b.term) ?_ ?_ p
  · intro a
    exact .refl _
  · intro a b c e q ih
    rcases e with ⟨wire⟩
    exact .step wire.beta ih

/-- Every graph path transports its source archetype to a genuine prerequisite
of its target archetype. -/
theorem twistorPath_prerequisite {u v : TwistorLambdaState}
    (p : DirectedPath twistorLambdaDigraph u v) :
    u.stage ≤ v.stage := by
  exact mapPath_prerequisite twistorLambdaEpistemicHom p

/-- The strict twistor-path presentation declares precisely the labelled
independent-branch beta squares. Each generator has identical incidence data
and stage at all four vertices, with alternating black/white and
forward/backward labels. -/
noncomputable def twistorLambdaPathPresentation :
    DirectedPathPresentation twistorLambdaDigraph where
  cell := fun {_u _v} p q =>
    ∃ (x : ComplexSpacetime) (π : Spinor2) (W : DualTwistor4)
      (hInc : IsAmbitwistor W (incidenceLinearMap x π))
      (stage : CompilationArchetype)
      (f f' a a' : LambdaTerm) (hf : LambdaBetaStep f f')
      (ha : LambdaBetaStep a a'),
      HEq p (twistorBranchFunctionThenArgumentPath x π W hInc stage hf ha) ∧
      HEq q (twistorBranchArgumentThenFunctionPath x π W hInc stage hf ha)

/-- The two valid twistor-labelled routes around an independent beta square
are equal in the presented path category. -/
theorem twistorLambda_beta_branch_diamond
    (x : ComplexSpacetime) (π : Spinor2) (stage : CompilationArchetype)
    (W : DualTwistor4) (hInc : IsAmbitwistor W (incidenceLinearMap x π))
    {f f' a a' : LambdaTerm} (hf : LambdaBetaStep f f')
    (ha : LambdaBetaStep a a') :
    PresentedPathHomotopy twistorLambdaPathPresentation
      (twistorBranchFunctionThenArgumentPath x π W hInc stage hf ha)
      (twistorBranchArgumentThenFunctionPath x π W hInc stage hf ha) := by
  apply Relation.EqvGen.rel
  apply ContextualPathRewrite.generator
  exact ⟨x, π, W, hInc, stage, f, f', a, a', hf, ha, HEq.rfl, HEq.rfl⟩

/-- The prerequisite comparison is well-defined on the strict presented path
quotient: any two representatives have the same endpoints, and order proofs
are propositionally unique. -/
theorem twistorPresentedPath_prerequisite {u v : TwistorLambdaState}
    (p : PresentedPathClass twistorLambdaPathPresentation u v) :
    u.stage ≤ v.stage := by
  exact InfoGeometry.Epistemology.ArchetypeHomotopyFramework.presentedPathClass_le
    twistorLambdaEpistemicHom twistorLambdaPathPresentation p

/-- The presented path category of the twistor-labelled beta graph maps into
the finite epistemic prerequisite poset. Its only declared equations are the
independent-branch beta diamonds. -/
noncomputable def twistorLambdaPresentedFunctor :
    PresentedPathCategory twistorLambdaPathPresentation ⥤ CompilationArchetype :=
  presentedPathEpistemicFunctor twistorLambdaEpistemicHom

/-- Twistor data is constant along a computational path; this model does not
identify beta reduction with spacetime displacement. -/
theorem twistorPath_preserves_twistor {u v : TwistorLambdaState}
    (p : DirectedPath twistorLambdaDigraph u v) :
    u.twistor = v.twistor := by
  refine DirectedPath.rec
    (motive := fun {a b : TwistorLambdaState}
      (_ : DirectedPath twistorLambdaDigraph a b) => a.twistor = b.twistor) ?_ ?_ p
  · intro a
    rfl
  · intro a b c e q ih
    rcases e with ⟨wire⟩
    simp only [TwistorLambdaState.twistor]
    rw [wire.point_preserved, wire.spinor_preserved]
    exact ih

/-- The signed conjugate-coordinate payload is constant along a computation
path because it is functorially obtained from the preserved incidence twistor. -/
theorem twistorPath_preserves_signedTwistor {u v : TwistorLambdaState}
    (p : DirectedPath twistorLambdaDigraph u v) :
    u.signedTwistor = v.signedTwistor := by
  change signedPair (penroseTwistor4CarrierEquiv u.twistor) =
    signedPair (penroseTwistor4CarrierEquiv v.twistor)
  rw [twistorPath_preserves_twistor p]

/-- The actual pairing-defined dual twistor is preserved along a computation
path because its primal incidence twistor is preserved. -/
theorem twistorPath_preserves_dualTwistor {u v : TwistorLambdaState}
    (p : DirectedPath twistorLambdaDigraph u v) :
    u.dualTwistor = v.dualTwistor := by
  change twistorToDual (penroseTwistor4CarrierEquiv u.twistor) =
    twistorToDual (penroseTwistor4CarrierEquiv v.twistor)
  rw [twistorPath_preserves_twistor p]

/-- The finite ambitwistor pairing is preserved along a computation path:
the conjugate leg is wire-invariant and the primal leg is preserved by
Penrose incidence. -/
theorem twistorPath_preserves_ambitwistorPairing {u v : TwistorLambdaState}
    (p : DirectedPath twistorLambdaDigraph u v) :
    ambitwistorPairing u.conjugateTwistor u.twistor =
      ambitwistorPairing v.conjugateTwistor v.twistor := by
  have hW : u.conjugateTwistor = v.conjugateTwistor := by
    refine DirectedPath.rec
      (motive := fun {a b : TwistorLambdaState}
        (_ : DirectedPath twistorLambdaDigraph a b) =>
          a.conjugateTwistor = b.conjugateTwistor) ?_ ?_ p
    · intro a
      rfl
    · intro a b c e q ih
      rcases e with ⟨wire⟩
      exact wire.conjugateTwistor_preserved.trans ih
  rw [hW, twistorPath_preserves_twistor p]

/-- The source and target incidence equations agree because both are the
concrete zero-pairing condition from the finite ambitwistor owner. -/
theorem twistorPath_preserves_ambitwistorIncidence {u v : TwistorLambdaState}
    (p : DirectedPath twistorLambdaDigraph u v) :
    IsAmbitwistor u.conjugateTwistor u.twistor ↔
      IsAmbitwistor v.conjugateTwistor v.twistor := by
  change ambitwistorPairing u.conjugateTwistor u.twistor = 0 ↔
    ambitwistorPairing v.conjugateTwistor v.twistor = 0
  rw [twistorPath_preserves_ambitwistorPairing p]

end InfoGeometry.MetaCompiler.Integration
