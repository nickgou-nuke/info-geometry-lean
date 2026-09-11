import Lean
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

namespace FormalAgentLib

inductive BaseType where
  | TUnit : BaseType
  | TString : BaseType
  | TInt : BaseType
  | TFloat : BaseType
  | TBool : BaseType
  | TJson : BaseType
  | TList : BaseType → BaseType
  | TDict : BaseType → BaseType → BaseType
  | TSet : BaseType → BaseType
  | TOption : BaseType → BaseType
  | TRecord : List (String × BaseType) → BaseType
  | TUnknown : BaseType
  deriving Repr, Inhabited, BEq

inductive StepType where
  | forEachLoop
  | whileLoop
  | conditional
  | setVariable
  | incrementVariable
  | switchBranch
  | returnValue
  | save
  | input
  | discover
  | evaluate
  | validate
  | task
  | step
  | parallel
  | call
  | gather
  | synthesize
  deriving Repr, BEq, Inhabited

abbrev NodeId := Nat

structure TypedVar where
  name : String
  type : BaseType
  deriving Repr, Inhabited, BEq

structure WorkflowNode where
  id : NodeId
  name : Option String
  stepType : StepType
  reads : List TypedVar
  writes : List TypedVar
  llmInstruction : Option String
  deriving Repr, BEq, Inhabited

inductive WorkflowEdge where
  | seqEdge (fromNode : NodeId) (toNode : NodeId)
  | branchEdge (cond : NodeId) (thenEntry : NodeId) (elseEntry : NodeId)
  | loopEdge (header : NodeId) (bodyEntry : NodeId) (exit : NodeId)
  | loopBackEdge (bodyEnd : NodeId) (header : NodeId)
  | forkEdge (forkNode : NodeId) (branches : List NodeId)
  | joinEdge (branches : List NodeId) (joinNode : NodeId)
  | switchEdge (switchNode : NodeId) (cases : List NodeId) (defaultCase : Option NodeId)
  deriving Repr, BEq, Inhabited

structure WorkflowGraph where
  nodes : List WorkflowNode
  edges : List WorkflowEdge
  entry : NodeId
  exits : List NodeId
  parameters : List TypedVar
  deriving Repr, BEq, Inhabited

end FormalAgentLib
