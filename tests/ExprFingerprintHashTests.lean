/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import DAG.ExprFingerprint
import Lean.Elab.Tactic.Guard
import Lean.Data.Json

open Lean

private def repeatedSubtree : Expr :=
  .app (.app (.const `f []) (.const `x []))
    (.app (.const `f []) (.const `x []))

private def singleLeaf : Expr :=
  .app (.app (.const `f []) (.const `x [])) (.const `x [])

private def metadataTrue : Expr :=
  .mdata (MData.empty.insert `flag (DataValue.ofBool true)) (.const `x [])

private def metadataFalse : Expr :=
  .mdata (MData.empty.insert `flag (DataValue.ofBool false)) (.const `x [])

/- Repeating a subtree must not disappear from the expression fingerprint. -/
#guard (DAG.computeFingerprint repeatedSubtree).shapeHash !=
  (DAG.computeFingerprint singleLeaf).shapeHash

/- Metadata is intentionally erased from the fingerprint. -/
#guard (DAG.computeFingerprint metadataTrue).shapeHash ==
  (DAG.computeFingerprint metadataFalse).shapeHash

/- UInt64 hashes are serialized as exact decimal JSON strings for Arango. -/
#guard Json.compress (toJson (18446744073709551615 : UInt64)) ==
  "\"18446744073709551615\""
