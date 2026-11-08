import Mathlib.CategoryTheory.Category.Preorder
import InfoGeometry.Meta.EpistemicCompilerChain
import InfoGeometry.Epistemology.EpistemicFunctor
import InfoGeometry.Causal.CertifiedDependencyCompiler
import InfoGeometry.Meta.EnvironmentDependencyBridge
import InfoGeometry.Topology.ChiralDirectedGraphHomotopy
import InfoGeometry.QuantumContext.CanonicalArchetypeCausalPoset

/-!
# Generic theorems assembling the epistemic compilation owners

The target of the graph-to-order map is any existing preorder. The compiler
workflow order `CompilationArchetype` and the domain order
`CanonicalArchetype` are distinct carriers; no order map between them is
invented here. The results below use the repository's `ChiralDigraphHom`,
path-quotient category, certified scheduler, and status-indexed promotion
directly.
-/

namespace InfoGeometry.Epistemology.ArchetypeHomotopyFramework

open CategoryTheory
open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.ProofCarryingSchedule
open InfoGeometry.Causal.FiniteDependencyCompiler
open InfoGeometry.Causal.CertifiedDependencyCompiler
open InfoGeometry.Epistemology.EpistemicFunctor
open InfoGeometry.MetaCompiler
open InfoGeometry.Topology

universe u

/-- A preorder, viewed as a chiral digraph with order comparisons as edges.
The auxiliary sector data is constant; it carries no extra causal claim. -/
abbrev prerequisiteGraph (Stage : Type u) [Preorder Stage] [DecidableLE Stage] :
    ChiralDigraph where
  Vertex := Stage
  edge := fun a b => a ≤ b
  edge_decidable := fun a b => inferInstance
  sector := fun _ => ChiralSector.left
  allowedTransition := fun _ _ => True
  transition_decidable := fun _ _ => isTrue trivial
  edge_allowed := by intro a b h; trivial

/-- Construct the repository-owned graph morphism from an edge-monotone
stage assignment. Every mapped edge is justified by `edge_mono`. -/
def prerequisiteGraphHom {G : ChiralDigraph} {Stage : Type u}
    [Preorder Stage] [DecidableLE Stage]
    (stage : G.Vertex → Stage)
    (edge_mono : ∀ {a b : G.Vertex}, G.edge a b → stage a ≤ stage b) :
    ChiralDigraphHom G (prerequisiteGraph Stage) where
  mapVertex := stage
  mapEdge := edge_mono
  mapTransition _ := trivial

/-- A graph morphism to an order graph sends every directed path to a genuine
prerequisite comparison. -/
theorem mapPath_le {G : ChiralDigraph} {Stage : Type u}
    [Preorder Stage] [DecidableLE Stage]
    (F : ChiralDigraphHom G (prerequisiteGraph Stage))
    {a b : G.Vertex} (p : DirectedPath G a b) :
    (F.mapVertex a : Stage) ≤ F.mapVertex b := by
  induction p with
  | refl => exact le_rfl
  | cons edge tail ih => exact le_trans (F.mapEdge edge) ih

/-- The legacy quotient gives an endpoint comparison in a preorder. Its
underlying two-cell relation is not evidence of a chosen path homotopy. -/
theorem legacyPathClass_le {G : ChiralDigraph} {Stage : Type u}
    [Preorder Stage] [DecidableLE Stage]
    (F : ChiralDigraphHom G (prerequisiteGraph Stage))
    {a b : G.Vertex} (p : DirectedPathClass G a b) :
    (F.mapVertex a : Stage) ≤ F.mapVertex b :=
  Quot.lift (fun q => mapPath_le F q) (fun _ _ _ => Subsingleton.elim _ _) p

/-- An explicitly presented path class also gives a prerequisite comparison.
The proof only uses the declared graph edges; two-cell relations preserve the
path endpoints by their dependent type and therefore need no semantic
interpretation in a thin preorder. -/
theorem presentedPathClass_le {G : ChiralDigraph} {Stage : Type u}
    [Preorder Stage] [DecidableLE Stage]
    (F : ChiralDigraphHom G (prerequisiteGraph Stage))
    (P : DirectedPathPresentation G) {a b : G.Vertex}
    (p : PresentedPathClass P a b) :
    (F.mapVertex a : Stage) ≤ F.mapVertex b :=
  Quot.lift (fun q => mapPath_le F q)
    (fun _ _ _ => Subsingleton.elim _ _) p

section CategoricalAction

variable {G : ChiralDigraph} {Stage : Type u}
    [Preorder Stage] [DecidableLE Stage]
    [hRight : Fact (HomotopyAppendCompatible G)]
    [hLeft : Fact (HomotopyAppendLeftCompatible G)]

local instance : Category (ChiralPathQuotientCategory G) :=
  ChiralPathQuotientCategory.category G hRight.out hLeft.out

/-- The legacy universal path quotient maps into any represented prerequisite
preorder. Its morphisms witness reachability only, not a chosen homotopy. -/
def legacyUniversalPathFunctor
    (F : ChiralDigraphHom G (prerequisiteGraph Stage)) :
    ChiralPathQuotientCategory G ⥤ Stage where
  obj := F.mapVertex
  map := fun p => homOfLE (legacyPathClass_le F p)
  map_id := by intro X; apply Subsingleton.elim
  map_comp := by intro X Y Z f g; apply Subsingleton.elim

/-- The category functor associated to a declared path presentation. This is
the evidence-bearing route for presented homotopies; the legacy quotient
above is retained for compatibility with older owners whose two-cell
relation is universal. -/
def presentedPathFunctor {P : DirectedPathPresentation G}
    (F : ChiralDigraphHom G (prerequisiteGraph Stage)) :
    PresentedPathCategory P ⥤ Stage where
  obj := F.mapVertex
  map := fun p => homOfLE (presentedPathClass_le F P p)
  map_id := by intro X; apply Subsingleton.elim
  map_comp := by intro X Y Z f g; apply Subsingleton.elim

end CategoricalAction

/-! ## Proof obtained from a successful scheduler execution -/

/-- Pointwise evidence at a node in the returned environment is obtained from
the actual `compileCertified` result, not from an unrelated witness state. -/
theorem compileCertified_proves_mem {Stage : Type u} [PartialOrder Stage]
    [DecidableEq Stage] [Fintype Stage] [DecidableLT Stage]
    {statement : Stage → Prop}
    (rules : ProofRules statement) (state : CertifiedState statement)
    (pending : List Stage) (completed : CertifiedState statement)
    (compiled : compileCertified rules state pending = some completed)
    {node : Stage} (covered : node ∈ completed.environment) : statement node := by
  obtain ⟨schedule, scheduled, valid, _permutation, _environment⟩ :=
    compileCertified_sound compiled
  have generated := compileCertified_eq_some (rules := rules)
    (state := state) (pending := pending) scheduled
  have result_eq : state.execute rules schedule valid = completed :=
    Option.some.inj (generated.symm.trans compiled)
  rw [← result_eq] at covered
  exact (state.execute rules schedule valid).proofs node covered

/-! ## Kernel promotion of the represented claims -/

/-- The scheduler's kernel-checked output promotes the actual propositions
attached to graph vertices. The graph-to-stage map and coverage of compiled
stages are explicit hypotheses; the resulting archetype stores the derived
proof function at status `.proved`. -/
def promoteCompiledGraphVertices {G : ChiralDigraph} {Stage : Type u}
    [PartialOrder Stage] [DecidableEq Stage] [Fintype Stage]
    [DecidableLT Stage] [DecidableLE Stage]
    (F : ChiralDigraphHom G (prerequisiteGraph Stage))
    (statement : Stage → Prop) (rules : ProofRules statement)
    (state : CertifiedState statement) (pending : List Stage)
    (completed : CertifiedState statement)
    (compiled : compileCertified rules state pending = some completed)
    (covered : ∀ v : G.Vertex, F.mapVertex v ∈ completed.environment)
    (phase : Nat) : TypedArchetype G.Vertex .proved := by
  let candidate : TypedArchetype G.Vertex .candidate :=
    { name := Lean.Name.str Lean.Name.anonymous "compiledGraphVertexClaims"
      phase := phase
      claim := fun v => statement (F.mapVertex v)
      evidence := trivial }
  exact candidate.promoteToProved (fun v =>
    compileCertified_proves_mem rules state pending completed compiled (covered v))

/-- Discharge of the promoted archetype is exactly the scheduler-derived
proposition at the mapped prerequisite stage. -/
theorem promoteCompiledGraphVertices_discharge {G : ChiralDigraph}
    {Stage : Type u} [PartialOrder Stage] [DecidableEq Stage]
    [Fintype Stage] [DecidableLT Stage] [DecidableLE Stage]
    (F : ChiralDigraphHom G (prerequisiteGraph Stage))
    (statement : Stage → Prop) (rules : ProofRules statement)
    (state : CertifiedState statement) (pending : List Stage)
    (completed : CertifiedState statement)
    (compiled : compileCertified rules state pending = some completed)
    (covered : ∀ v : G.Vertex, F.mapVertex v ∈ completed.environment)
    (phase : Nat) (v : G.Vertex) :
    (promoteCompiledGraphVertices F statement rules state pending completed
      compiled covered phase).claim v :=
  (promoteCompiledGraphVertices F statement rules state pending completed
    compiled covered phase).discharge v

/-- A compiler-derived proposition and a declaration lookup are both indexed
by the same mapped stage. This records co-presence only: the correspondence
does not identify the declaration's Lean type with `statement`, and no such
type-level identification is inferred here. -/
theorem compiledClaim_coPresentWithMappedDeclaration {G : ChiralDigraph}
    {Stage : Type u} [PartialOrder Stage] [DecidableEq Stage]
    [Fintype Stage] [DecidableLT Stage] [DecidableLE Stage]
    {environment : Lean.Environment}
    (correspondence : InfoGeometry.MetaCompiler.EnvironmentBridge.EnvironmentCorrespondence
      environment Stage)
    (F : ChiralDigraphHom G (prerequisiteGraph Stage))
    (statement : Stage → Prop) (rules : ProofRules statement)
    (state : CertifiedState statement) (pending : List Stage)
    (completed : CertifiedState statement)
    (compiled : compileCertified rules state pending = some completed)
    (covered : ∀ v : G.Vertex, F.mapVertex v ∈ completed.environment)
    (phase : Nat) (v : G.Vertex) :
    (∃ info, environment.toKernelEnv.find?
      (correspondence.declaration (F.mapVertex v)) = some info) ∧
      (promoteCompiledGraphVertices F statement rules state pending completed
        compiled covered phase).claim v := by
  exact ⟨correspondence.node_present (F.mapVertex v),
    promoteCompiledGraphVertices_discharge F statement rules state pending
      completed compiled covered phase v⟩

/-! ## Decidable strict order for the domain archetype poset

`CanonicalArchetypeCausalPoset` owns the finite partial order and its
decidable non-strict relation. This adapter derives `<` from those owner
relations for the executable scheduler without registering a new global
instance. -/

@[instance_reducible] def canonicalArchetypeDecidableLT : DecidableLT
    InfoGeometry.QuantumContext.CanonicalArchetypeCausalPoset.CanonicalArchetype :=
  fun a b => decidable_of_iff (a ≤ b ∧ ¬ b ≤ a) lt_iff_le_not_ge.symm

/-! ## The repository archetype poset as the integrated target

The canonical archetype labels are the finite prerequisite poset owned by
`CanonicalArchetypeCausalPoset`.  The theorem below connects its actual
homotopy-category morphisms to evidence produced by the certified scheduler.
It takes the scheduler's successful execution and vertex coverage explicitly;
neither path homotopy nor a label alone manufactures mathematical evidence.
-/

open InfoGeometry.QuantumContext.CanonicalArchetypeCausalPoset

/-- The owned finite prerequisite order, represented as a directed graph so
that repository proof graphs can map into it by edge-monotone label maps. -/
abbrev canonicalArchetypePrerequisiteGraph : ChiralDigraph :=
  prerequisiteGraph CanonicalArchetype

section CanonicalArchetypeHomotopy

variable {G : ChiralDigraph}
variable [hRight : Fact (HomotopyAppendCompatible G)]
variable [hLeft : Fact (HomotopyAppendLeftCompatible G)]

local instance : DecidableLT CanonicalArchetype := canonicalArchetypeDecidableLT

local instance : Category (ChiralPathQuotientCategory G) :=
  ChiralPathQuotientCategory.category G hRight.out hLeft.out

/-- A graph labelled in the canonical finite poset induces the legacy
universal reachability functor into that same poset. -/
def legacyCanonicalArchetypeReachabilityFunctor
    (F : ChiralDigraphHom G canonicalArchetypePrerequisiteGraph) :
    ChiralPathQuotientCategory G ⥤ CanonicalArchetype :=
  legacyUniversalPathFunctor F

/-- A legacy quotient morphism gives an endpoint prerequisite comparison,
while the successful scheduler run separately supplies endpoint claims.
Neither claim is inferred from the quotient morphism. -/
theorem legacyReachability_with_compiledPromotion
    (F : ChiralDigraphHom G canonicalArchetypePrerequisiteGraph)
    (statement : CanonicalArchetype → Prop)
    (rules : ProofRules statement)
    (state : CertifiedState statement)
    (pending : List CanonicalArchetype)
    (completed : CertifiedState statement)
    (compiled : compileCertified rules state pending = some completed)
    (covered : ∀ x : G.Vertex, F.mapVertex x ∈ completed.environment)
    (phase : Nat) {u v : G.Vertex} (p : DirectedPathClass G u v) :
    (legacyCanonicalArchetypeReachabilityFunctor F).map p =
        homOfLE (legacyPathClass_le F p) ∧
      (promoteCompiledGraphVertices F statement rules state pending
        completed compiled covered phase).claim u ∧
      (promoteCompiledGraphVertices F statement rules state pending
        completed compiled covered phase).claim v := by
  exact ⟨rfl,
    promoteCompiledGraphVertices_discharge F statement rules state pending
      completed compiled covered phase u,
    promoteCompiledGraphVertices_discharge F statement rules state pending
      completed compiled covered phase v⟩

end CanonicalArchetypeHomotopy

end InfoGeometry.Epistemology.ArchetypeHomotopyFramework
