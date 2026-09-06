import Std

/-!
InfoGeometry/ProofTelemetry/Kernel.lean

Lean-native proof-telemetry kernel.

This module ports the deterministic core of the Paperproof/Jixia Python
telemetry scripts into Lean data structures and pure functions:

* proof states as goals, hypotheses, tactics, and references;
* tactic-effect labels;
* semantic-tableau strategy profiles;
* Paperproof-style proof forests;
* lightweight graph checkers.

No JSON parsing, subprocess orchestration, editor RPC, Arango query, Jixia
execution, or LLM call is performed here.  Those remain integration concerns.
Lean owns the exact deterministic kernel and its checkable invariants.
-/

namespace InfoGeometry.ProofTelemetry

/-- A pretty-printed proof goal. -/
structure ProofGoal where
  id : String := ""
  text : String
deriving Repr, DecidableEq, Inhabited

/-- A pretty-printed local hypothesis. -/
structure ProofHypothesis where
  id : String := ""
  name : String
  type : String
deriving Repr, DecidableEq, Inhabited

/-- One tactic transition, in Paperproof/Jixia style. -/
structure ProofStep where
  index : Nat
  tactic : String
  goalsBefore : Array ProofGoal := #[]
  goalsAfter : Array ProofGoal := #[]
  hypothesesBefore : Array ProofHypothesis := #[]
  hypothesesAfter : Array ProofHypothesis := #[]
  references : Array String := #[]
deriving Repr, DecidableEq, Inhabited

/-- A proof trace attached to one theorem or source file. -/
structure PaperproofTrace where
  id : String
  theoremName : String := ""
  sourceFile : String := ""
  steps : Array ProofStep := #[]
deriving Repr, DecidableEq

/-- Coarse tactic-effect labels used as training/control metadata. -/
inductive TacticEffect where
  | closesGoal
  | splitsGoal
  | addsHypothesis
  | introducesBinder
  | constructsGoal
  | rewritesOrSimplifies
  | usesTermOrLemma
  | branchesContext
  | createsIntermediateClaim
  | startsTableauMode
  | contradictionEntry
  | contradictionClosure
  | closesTableauBranch
  | unknownEffect
deriving Repr, DecidableEq

/-- Proof-strategy labels for semantic-tableau-like proofs. -/
inductive TableauLabel where
  | contradictionEntry
  | topDownFalseGoal
  | branchingTableau
  | branchClosing
deriving Repr, DecidableEq

def uniqueEffects (xs : List TacticEffect) : List TacticEffect :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def uniqueTableauLabels (xs : List TableauLabel) : List TableauLabel :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def tacticFamily (tactic : String) : String :=
  match tactic.trimAscii.toString.splitOn " " with
  | [] => ""
  | head :: _ => head

def isIntroFamily (fam : String) : Bool :=
  fam == "intro" || fam == "rintro" || fam == "intros"

def isConstructorFamily (fam : String) : Bool :=
  fam == "constructor" || fam == "constructor'"

def isRewriteFamily (fam : String) : Bool :=
  fam == "rw" || fam == "rewrite" || fam == "simp" ||
    fam == "simpa" || fam == "simp_all"

def isTermFamily (fam : String) : Bool :=
  fam == "apply" || fam == "exact" || fam == "refine"

def isBranchFamily (fam : String) : Bool :=
  fam == "cases" || fam == "cases'" || fam == "rcases" ||
    fam == "induction" || fam == "induction'"

def isIntermediateFamily (fam : String) : Bool :=
  fam == "have" || fam == "suffices"

def isTableauEntryFamily (fam : String) : Bool :=
  fam == "by_contra" || fam == "by_contra!" ||
    fam == "contrapose" || fam == "contrapose!"

def isContradictionFamily (fam : String) : Bool :=
  fam == "contradiction" || fam == "exfalso"

def containsContradictionToken (tactic : String) : Bool :=
  tactic.contains "False.elim" || tactic.contains "false.elim" ||
    tactic.contains "not.elim" || tactic.contains "absurd" ||
    tactic.contains "contradiction"

/-- Conservative tactic-effect classifier. -/
def tacticEffects (step : ProofStep) : List TacticEffect :=
  let fam := tacticFamily step.tactic
  let base :=
    ([] : List TacticEffect)
      ++ (if step.goalsAfter.isEmpty then [.closesGoal] else [])
      ++ (if step.goalsAfter.size > step.goalsBefore.size then [.splitsGoal] else [])
      ++ (if step.hypothesesAfter.size > step.hypothesesBefore.size then [.addsHypothesis] else [])
      ++
        (if isTableauEntryFamily fam then
          [.startsTableauMode, .contradictionEntry]
        else if isIntroFamily fam then
          [.introducesBinder]
        else if isConstructorFamily fam then
          [.constructsGoal]
        else if isRewriteFamily fam then
          [.rewritesOrSimplifies]
        else if isTermFamily fam then
          [.usesTermOrLemma]
        else if isBranchFamily fam then
          [.branchesContext]
        else if isIntermediateFamily fam then
          [.createsIntermediateClaim]
        else [])
      ++
        (if isContradictionFamily fam || containsContradictionToken step.tactic then
          [.contradictionClosure, .closesTableauBranch]
        else [])
  let out := uniqueEffects base
  if out.isEmpty then [.unknownEffect] else out

def falseGoal (g : ProofGoal) : Bool :=
  let t := g.text.trimAscii.toString
  t == "False" || t == "⊢ False" || t.endsWith ": False"

def stepHasFalseGoal (step : ProofStep) : Bool :=
  step.goalsBefore.any falseGoal || step.goalsAfter.any falseGoal

def isTableauEntryStep (step : ProofStep) : Bool :=
  isTableauEntryFamily (tacticFamily step.tactic) ||
    tacticFamily step.tactic == "by_cases"

def isContradictionClosureStep (step : ProofStep) : Bool :=
  isContradictionFamily (tacticFamily step.tactic) ||
    containsContradictionToken step.tactic ||
    (step.goalsBefore.any falseGoal && step.goalsAfter.isEmpty)

/-- Semantic-tableau-style profile for one trace. -/
structure TableauProfile where
  traceId : String
  tableauLike : Bool
  entryTactic : Option String
  falseGoalSteps : Nat
  branchingSteps : Nat
  closingSteps : Nat
  contradictionClosureSteps : Nat
  strategyLabels : List TableauLabel
deriving Repr, DecidableEq

def tableauProfile (trace : PaperproofTrace) : TableauProfile :=
  let entrySteps := trace.steps.filter isTableauEntryStep
  let falseSteps := trace.steps.filter stepHasFalseGoal
  let branchingSteps := trace.steps.filter (fun s => s.goalsAfter.size > s.goalsBefore.size)
  let closingSteps := trace.steps.filter (fun s => s.goalsAfter.isEmpty)
  let closureSteps := trace.steps.filter isContradictionClosureStep
  let labels := uniqueTableauLabels <|
    ([] : List TableauLabel)
      ++ (if entrySteps.isEmpty then [] else [.contradictionEntry])
      ++ (if falseSteps.isEmpty then [] else [.topDownFalseGoal])
      ++ (if branchingSteps.isEmpty then [] else [.branchingTableau])
      ++ (if closureSteps.isEmpty && closingSteps.isEmpty then [] else [.branchClosing])
  {
    traceId := trace.id
    tableauLike := !entrySteps.isEmpty &&
      (!falseSteps.isEmpty || !closureSteps.isEmpty || !closingSteps.isEmpty)
    entryTactic := entrySteps[0]?.map (·.tactic)
    falseGoalSteps := falseSteps.size
    branchingSteps := branchingSteps.size
    closingSteps := closingSteps.size
    contradictionClosureSteps := closureSteps.size
    strategyLabels := labels
  }

inductive ProofNodeKind where
  | proof
  | goal
  | tactic
  | hypothesis
  | reference
  | closedGoal
deriving Repr, DecidableEq

inductive ProofEdgeRole where
  | containsTactic
  | transformedBy
  | producesGoal
  | goalChild
  | availableHypothesis
  | closesGoal
  | dependsOn
deriving Repr, DecidableEq

structure ProofNode where
  id : String
  kind : ProofNodeKind
  text : String := ""
  stepIndex : Nat := 0
deriving Repr, DecidableEq

structure ProofEdge where
  source : String
  target : String
  role : ProofEdgeRole
deriving Repr, DecidableEq

structure ProofForest where
  traceId : String
  nodes : Array ProofNode
  edges : Array ProofEdge
deriving Repr, DecidableEq

def goalNodeId (traceId : String) (stepIndex : Nat) (side : String) (idx : Nat) (g : ProofGoal) : String :=
  if g.id.isEmpty then
    s!"goal:{traceId}:{stepIndex}:{side}:{idx}:{g.text}"
  else
    s!"goal:{traceId}:{g.id}"

def hypNodeId (traceId : String) (stepIndex : Nat) (side : String) (idx : Nat) (h : ProofHypothesis) : String :=
  if h.id.isEmpty then
    s!"hyp:{traceId}:{stepIndex}:{side}:{idx}:{h.name}:{h.type}"
  else
    s!"hyp:{traceId}:{h.id}"

private def pushUniqueNode (nodes : Array ProofNode) (node : ProofNode) : Array ProofNode :=
  if nodes.any (fun n => n.id == node.id) then nodes else nodes.push node

/-- Build a Paperproof-style proof forest from a trace. -/
def proofForest (trace : PaperproofTrace) : ProofForest :=
  Id.run do
    let rootId := s!"proof:{trace.id}"
    let mut nodes := #[{ id := rootId, kind := .proof, text := trace.theoremName }]
    let mut edges : Array ProofEdge := #[]
    for step in trace.steps do
      let tacticId := s!"tactic:{trace.id}:{step.index}:{step.tactic}"
      nodes := pushUniqueNode nodes { id := tacticId, kind := .tactic, text := step.tactic, stepIndex := step.index }
      edges := edges.push { source := rootId, target := tacticId, role := .containsTactic }

      let mut beforeIds : Array String := #[]
      for i in [:step.goalsBefore.size] do
        let g := step.goalsBefore[i]!
        let gid := goalNodeId trace.id step.index "before" i g
        beforeIds := beforeIds.push gid
        nodes := pushUniqueNode nodes { id := gid, kind := .goal, text := g.text, stepIndex := step.index }
        edges := edges.push { source := gid, target := tacticId, role := .transformedBy }

      for i in [:step.goalsAfter.size] do
        let g := step.goalsAfter[i]!
        let gid := goalNodeId trace.id step.index "after" i g
        nodes := pushUniqueNode nodes { id := gid, kind := .goal, text := g.text, stepIndex := step.index }
        edges := edges.push { source := tacticId, target := gid, role := .producesGoal }
        for bid in beforeIds do
          edges := edges.push { source := bid, target := gid, role := .goalChild }

      if step.goalsAfter.isEmpty then
        let closedId := s!"closed:{trace.id}:{step.index}:{step.tactic}"
        nodes := pushUniqueNode nodes { id := closedId, kind := .closedGoal, text := "no goals", stepIndex := step.index }
        edges := edges.push { source := tacticId, target := closedId, role := .closesGoal }

      for i in [:step.hypothesesBefore.size] do
        let hyp := step.hypothesesBefore[i]!
        let hid := hypNodeId trace.id step.index "before" i hyp
        nodes := pushUniqueNode nodes { id := hid, kind := .hypothesis, text := s!"{hyp.name} : {hyp.type}", stepIndex := step.index }
        edges := edges.push { source := hid, target := tacticId, role := .availableHypothesis }

      for i in [:step.references.size] do
        let ref := step.references[i]!
        let rid := s!"ref:{trace.id}:{ref}"
        nodes := pushUniqueNode nodes { id := rid, kind := .reference, text := ref, stepIndex := step.index }
        edges := edges.push { source := tacticId, target := rid, role := .dependsOn }

    return { traceId := trace.id, nodes, edges }

def nodeIds (forest : ProofForest) : Array String :=
  forest.nodes.map (·.id)

def hasNode (forest : ProofForest) (id : String) : Bool :=
  forest.nodes.any (fun n => n.id == id)

def checkEdgeEndpoints (forest : ProofForest) : Bool :=
  forest.edges.all (fun e => hasNode forest e.source && hasNode forest e.target)

def checkClosesGoalTargets (forest : ProofForest) : Bool :=
  forest.edges.all fun e =>
    if e.role == .closesGoal then
      forest.nodes.any (fun n => n.id == e.target && n.kind == .closedGoal)
    else
      true

/-- Lightweight proof-forest checker. -/
def checkProofForest (forest : ProofForest) : Bool :=
  checkEdgeEndpoints forest && checkClosesGoalTargets forest

theorem checkProofForest_edgeEndpoints
    (forest : ProofForest)
    (h : checkProofForest forest = true) :
    checkEdgeEndpoints forest = true := by
  unfold checkProofForest at h
  cases h₁ : checkEdgeEndpoints forest <;> simp [h₁] at h ⊢

theorem checkProofForest_closesGoalTargets
    (forest : ProofForest)
    (h : checkProofForest forest = true) :
    checkClosesGoalTargets forest = true := by
  unfold checkProofForest at h
  cases h₁ : checkEdgeEndpoints forest <;> cases h₂ : checkClosesGoalTargets forest <;> simp [h₁, h₂] at h ⊢

end InfoGeometry.ProofTelemetry
