import Lean.Server.Rpc.RequestHandling

import Agent.CompilerBridgeCore

open Lean
open Lean.Server
open Lean.Server.RequestM

namespace IG.Compiler

private def unsupportedGetProofState (responseMeta : ResponseMeta) (err : CompilerError) :
    GetProofStateResult :=
  {
    ok := false
    responseMeta := responseMeta
    diagnostics := #[err]
    goals := #[]
  }

def getProofState (params : GetProofStateParams) : RequestM (RequestTask GetProofStateResult) := do
  let doc ← readDoc
  let responseMeta ← responseMetaOfDoc doc
  match validateVersion params.version responseMeta with
  | some err =>
      RequestM.pureTask <| pure (unsupportedGetProofState responseMeta err)
  | none =>
      let stateTask ← proofStateTaskAt doc params.posLine params.posCharacter
      RequestM.mapRequestTaskCheap stateTask fun state => do
        return {
          ok := diagnosticsOk state.diagnostics
          responseMeta := state.responseMeta
          diagnostics := state.diagnostics
          goals := state.goals
        }

private def unsupportedGetEnvFingerprint (responseMeta : ResponseMeta) (err : CompilerError) :
    GetEnvFingerprintResult :=
  {
    ok := false
    responseMeta := responseMeta
    diagnostics := #[err]
  }

def getEnvFingerprint (params : GetEnvFingerprintParams) :
    RequestM (RequestTask GetEnvFingerprintResult) := do
  let doc ← readDoc
  let responseMeta ← responseMetaOfDoc doc
  match validateVersion params.version responseMeta with
  | some err =>
      RequestM.pureTask <| pure (unsupportedGetEnvFingerprint responseMeta err)
  | none =>
      RequestM.pureTask do
        let diagnostics ← docDiagnostics doc
        return {
          ok := diagnosticsOk diagnostics
          responseMeta := responseMeta
          diagnostics := diagnostics
        }

private def unsupportedCheckSnippet (responseMeta : ResponseMeta) (err : CompilerError) :
    CheckSnippetResult :=
  {
    ok := false
    responseMeta := responseMeta
    diagnostics := #[err]
    goals := #[]
    goalCount := 0
  }

def checkSnippet (params : CheckSnippetParams) : RequestM (RequestTask CheckSnippetResult) := do
  let doc ← readDoc
  let responseMeta ← responseMetaOfDoc doc
  match validateVersion params.version responseMeta with
  | some err =>
      RequestM.pureTask <| pure (unsupportedCheckSnippet responseMeta err)
  | none =>
      let stateTask ← proofStateTaskAt doc params.posLine params.posCharacter
      RequestM.mapRequestTaskCheap stateTask fun state => do
        return {
          ok := diagnosticsOk state.diagnostics
          responseMeta := state.responseMeta
          diagnostics := state.diagnostics
          goals := state.goals
          goalCount := state.goals.size
        }

private def unsupportedValidateDecl (responseMeta : ResponseMeta) (err : CompilerError) :
    ValidateDeclResult :=
  {
    ok := false
    responseMeta := responseMeta
    diagnostics := #[err]
    declFound := false
    theoremType := ""
    theoremTypeHead := none
    theoremTypeHeadSource := .unavailable
    hasSorry := false
  }

def validateDecl (params : ValidateDeclParams) : RequestM (RequestTask ValidateDeclResult) := do
  let doc ← readDoc
  let responseMeta ← responseMetaOfDoc doc
  match validateVersion params.version responseMeta with
  | some err =>
      RequestM.pureTask <| pure (unsupportedValidateDecl responseMeta err)
  | none =>
      let snapTask ← finalSnapshotTask doc
      RequestM.mapRequestTaskCheap snapTask fun snap => do
        let mut diagnostics ← docDiagnostics doc
        let declInfo? := findDeclInfo? snap.env params.declName
        let theoremType ←
          match declInfo? with
          | some declInfo => ppExprAtSnapshot snap declInfo.type
          | none => pure ""
        let (theoremTypeHead, theoremTypeHeadSource) := headMetaOfText theoremType
        let hasSorry := declInfo?.map constantHasSorry |>.getD false
        if declInfo?.isNone then
          diagnostics := diagnostics.push (declarationNotFoundError params.declName)
        if hasSorry then
          diagnostics := diagnostics.push (containsSorryError params.declName)
        let declFound := declInfo?.isSome
        return {
          ok := declFound && !hasSorry && diagnosticsOk diagnostics
          responseMeta := responseMeta
          diagnostics := diagnostics
          declFound := declFound
          theoremType := theoremType
          theoremTypeHead := theoremTypeHead
          theoremTypeHeadSource := theoremTypeHeadSource
          hasSorry := hasSorry
        }

end IG.Compiler
