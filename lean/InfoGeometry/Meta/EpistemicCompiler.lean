import Lean

namespace InfoGeometry.Meta.EpistemicCompiler

open Lean Elab Command Meta

/--
  A `SyntheticName` is a strongly typed Lean `Name` representing a purified Archetype.
  It acts as a Jungian Archetype in the Collective Unconscious (the environment).
-/
structure SyntheticName where
  archetype : Name
  deriving Inhabited, Repr, BEq

/--
  The `Solve` step (from "Solve et Coagula").
  Dissolves a heuristic string (the raw unrefined thought) into a purified `SyntheticName`.
-/
def Solve (heuristic : String) : MetaM SyntheticName := do
  let pureName := Name.mkSimple heuristic
  return ⟨`Jungian.Archetype ++ pureName⟩

/--
  A causal graph (Poset) representing the `QuantumTuringTape` / `PosetPartiture`.
  It schedules the Archetypes causally rather than sequentially.
-/
structure PosetPartiture where
  vertices : Array SyntheticName
  edges : Array (Array Nat)
  deriving Inhabited

/--
  The `Coagula` step.
  Coagulates a list of dissolved `SyntheticName`s into a `PosetPartiture`.
-/
def Coagula (archetypes : Array SyntheticName) : MetaM PosetPartiture := do
  let mut edges := #[]
  for i in [0:archetypes.size] do
    if i > 0 then
      edges := edges.push #[i - 1]
    else
      edges := edges.push #[]
  return ⟨archetypes, edges⟩

namespace QuantumTuringTape

/--
  Evaluates the `SyntheticName`s causally based on the `PosetPartiture`.
-/
def evaluate (tape : PosetPartiture) : MetaM Unit := do
  for i in [0:tape.vertices.size] do
    let name := tape.vertices[i]!
    -- Causally dependent on predecessors, we log the binding
    Lean.logInfo m!"[QuantumTuringTape] Evaluating causally: {name.archetype}"

end QuantumTuringTape

/--
  The overarching Epistemic Compiler pipeline.
-/
def epistemicPipeline (heuristics : Array String) : MetaM Unit := do
  let mut dissolved := #[]
  for h in heuristics do
    let s ← Solve h
    dissolved := dissolved.push s
  let poset ← Coagula dissolved
  QuantumTuringTape.evaluate poset

/--
  The `epistemic_compile` command that maps raw strings to a DAG of `Name`s.
-/
syntax "epistemic_compile" (str)+ : command

elab_rules : command
  | `(command| epistemic_compile $args:str*) => do
    let strings := args.map (·.getString)
    liftTermElabM <| epistemicPipeline strings

end InfoGeometry.Meta.EpistemicCompiler
