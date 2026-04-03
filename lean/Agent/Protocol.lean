import Lean
import Lean.Data.Json.FromToJson.Basic

open Lean

namespace IG.Compiler

structure BridgeVersion where
  schema : Nat
  protocol : String
deriving Inhabited, BEq, FromJson, ToJson

def bridgeVersion : BridgeVersion :=
  { schema := 1, protocol := "ig.compiler/v1" }

structure SessionId where
  value : String
deriving Inhabited, BEq, Hashable, FromJson, ToJson

structure GoalId where
  sessionId : SessionId
  revision : Nat
  value : String
deriving Inhabited, BEq, Hashable, FromJson, ToJson

structure EnvFingerprint where
  leanToolchain : String
  importRoot : String
  namespaceHint : String
  oleanHash : String
  artifactSchema : Nat
deriving Inhabited, BEq, FromJson, ToJson

structure ResponseMeta where
  version : BridgeVersion
  sessionId : SessionId
  revision : Nat
  env : EnvFingerprint
deriving Inhabited, BEq, FromJson, ToJson

def BridgeVersion.isSupported (v : BridgeVersion) : Bool :=
  v == bridgeVersion

inductive Severity where
  | info
  | warning
  | error
deriving Inhabited, BEq, FromJson, ToJson

inductive ErrorPhase where
  | parse
  | elaboration
  | proofState
  | validation
  | protocol
deriving Inhabited, BEq, FromJson, ToJson

inductive ErrorClassificationProvenance where
  | leanTag
  | messagePattern
  | bridgeRule
  | fallback
deriving Inhabited, BEq, FromJson, ToJson

inductive ExprHeadSource where
  | exprSemantic
  | textHeuristic
  | unavailable
deriving Inhabited, BEq, FromJson, ToJson

inductive CompilerErrorCode where
  | parseError
  | elaborationError
  | unsolvedGoals
  | typeclassSearchFailed
  | unknownConstant
  | declarationNotFound
  | containsSorry
  | staleGoal
  | unsupportedProtocolVersion
  | invalidSession
  | staleSnapshot
  | timeout
  | internal
deriving Inhabited, BEq, FromJson, ToJson

structure CompilerError where
  code : CompilerErrorCode
  phase : ErrorPhase
  severity : Severity
  message : String
  classificationProvenance : ErrorClassificationProvenance := .fallback
  file : Option String := none
  /-- 0-based LSP line if available. -/
  line : Option Nat := none
  /-- 0-based LSP column if available. -/
  column : Option Nat := none
deriving Inhabited, BEq, FromJson, ToJson

structure LocalDeclView where
  fvarId : String
  userName : String
  binderKind : String := "default"
  type : String
  typeHead : Option String := none
  typeHeadSource : ExprHeadSource := .unavailable
  typeHeadFingerprint : Option String := none
  value : Option String := none
  isLet : Bool := false
  isInstance : Bool := false
  isImplementationDetail : Bool := false
deriving Inhabited, BEq, FromJson, ToJson

structure GoalView where
  goalId : GoalId
  pretty : String
  locals : Array LocalDeclView
  target : String
  targetHead : Option String := none
  targetHeadSource : ExprHeadSource := .unavailable
  targetHeadFingerprint : Option String := none
deriving Inhabited, BEq, FromJson, ToJson

structure GetProofStateParams where
  version : BridgeVersion := bridgeVersion
  posLine : Nat := 0
  posCharacter : Nat := 0
deriving Inhabited, BEq, FromJson, ToJson

structure GetProofStateResult where
  ok : Bool
  responseMeta : ResponseMeta
  diagnostics : Array CompilerError := #[]
  goals : Array GoalView := #[]
deriving Inhabited, BEq, FromJson, ToJson

structure GetEnvFingerprintParams where
  version : BridgeVersion := bridgeVersion
deriving Inhabited, BEq, FromJson, ToJson

structure GetEnvFingerprintResult where
  ok : Bool
  responseMeta : ResponseMeta
  diagnostics : Array CompilerError := #[]
deriving Inhabited, BEq, FromJson, ToJson

structure CheckSnippetParams where
  version : BridgeVersion := bridgeVersion
  posLine : Nat := 0
  posCharacter : Nat := 0
deriving Inhabited, BEq, FromJson, ToJson

structure CheckSnippetResult where
  ok : Bool
  responseMeta : ResponseMeta
  diagnostics : Array CompilerError := #[]
  goals : Array GoalView := #[]
  goalCount : Nat := 0
deriving Inhabited, BEq, FromJson, ToJson

structure ValidateDeclParams where
  version : BridgeVersion := bridgeVersion
  declName : String
deriving Inhabited, BEq, FromJson, ToJson

structure ValidateDeclResult where
  ok : Bool
  responseMeta : ResponseMeta
  diagnostics : Array CompilerError := #[]
  declFound : Bool := false
  theoremType : String := ""
  theoremTypeHead : Option String := none
  theoremTypeHeadSource : ExprHeadSource := .unavailable
  hasSorry : Bool := false
deriving Inhabited, BEq, FromJson, ToJson

end IG.Compiler
