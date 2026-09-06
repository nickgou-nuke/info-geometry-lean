import Lean.Server
import Lean.Server.Rpc.RequestHandling

import DAG.ServerExport

open Lean
open Lean.Server

builtin_initialize
  registerBuiltinRpcProcedure
    `DAG.Server.semanticBlocks
    DAG.Server.SemanticBlocksParams
    Json
    DAG.Server.semanticBlocks
