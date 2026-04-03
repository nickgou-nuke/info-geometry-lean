import Lean.Server
import Lean.Server.Rpc.RequestHandling

import Agent.ProofStateExport

open Lean
open Lean.Server

builtin_initialize
  registerBuiltinRpcProcedure
    `IG.Compiler.getProofState
    IG.Compiler.GetProofStateParams
    IG.Compiler.GetProofStateResult
    IG.Compiler.getProofState
  registerBuiltinRpcProcedure
    `IG.Compiler.checkSnippet
    IG.Compiler.CheckSnippetParams
    IG.Compiler.CheckSnippetResult
    IG.Compiler.checkSnippet
  registerBuiltinRpcProcedure
    `IG.Compiler.validateDecl
    IG.Compiler.ValidateDeclParams
    IG.Compiler.ValidateDeclResult
    IG.Compiler.validateDecl
  registerBuiltinRpcProcedure
    `IG.Compiler.getEnvFingerprint
    IG.Compiler.GetEnvFingerprintParams
    IG.Compiler.GetEnvFingerprintResult
    IG.Compiler.getEnvFingerprint
