/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import DAG.TermDigest
import DAG.Schema
import Lean.Elab.Tactic.Guard

/-!
Known-answer tests for `DAG.Sha256` and `DAG.TermDigest` (`lean-expr-debruijn-v4`).

The expected term digests were produced by the independent Python reference
`igf.graph.decl_schema.term_digest`; agreement checks the byte encoding across
both implementations.
-/

open Lean

/- FIPS 180-4 / NIST known answers. -/
#guard DAG.Sha256.hexDigestString "" ==
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard DAG.Sha256.hexDigestString "abc" ==
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard DAG.Sha256.hexDigestString (String.ofList (List.replicate 1000 'a')) ==
  "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3"

private def prop : Expr := .sort .zero
private def d (e : Expr) : String := (DAG.TermDigest.compute e).digest

private def idX : Expr := .lam `x prop (.bvar 0) .default
private def idY : Expr := .lam `y prop (.bvar 0) .implicit
private def idMData : Expr :=
  .mdata (MData.empty.insert `flag (DataValue.ofBool true))
    (.lam `z prop (.mdata MData.empty (.bvar 0)) .default)
private def constLam : Expr := .lam `x prop (.bvar 1) .default

/- Alpha-invariance: binder names and binder info are erased. -/
#guard d idX == d idY
/- `mdata` wrappers are transparent. -/
#guard d idX == d idMData
/- De Bruijn structure is kept. -/
#guard d idX != d constLam

/- Cross-implementation vectors (Python reference). -/
#guard d idX == "51b33626ac2f34eee2d5780e6bda57c03a3dcb09881c177df6b0f8dfde28907f"
#guard (DAG.TermDigest.compute idX).nodeCount == 3
#guard d constLam == "e3549051551d390f73ea52c170039f044fb17d11afc23731f1065ee4cb477b13"
#guard d (.const `Nat []) == "b9bd90cef763e5b28ff9b3fd950f99027a88b3fbf56353c85f33620c88fb7605"
#guard d (.app (.const `Nat.succ []) (.lit (.natVal 42))) ==
  "f64a8926c3126d626032db8569d478625d5e281c9db6bf5d3373cf102e60eaec"
#guard d (.lit (.strVal "ab")) == "fa0bd14bbac9fd85b3f4d8158951e6eb621d801db19b15110fb82e1500ad581d"
#guard d (.forallE `α (.sort (.succ (.param `u))) (.bvar 0) .default) ==
  "2e345e048fb3480fe8e6a9e18235a8091b1088266bb559901607bc924a23e893"
#guard d (.letE `n (.const `Nat []) (.lit (.natVal 0)) (.bvar 0) false) ==
  "026f6f150899f15894277f3450c33077375fc167d2300dd9a30a18e3355e93d4"
#guard d (.proj `Prod 0 (.bvar 0)) == "1ec33bbcf0f94981c2781059587ea018e38cfc00ae42f2515120365ff2d32bcd"
#guard d (.const `List.map [.param `u, .succ .zero]) ==
  "3cc6e6a3692ba781ab6bd740d92f97c9a1579166ba0da12ad5afca0f07208af8"

/- Open terms: run-local ids are erased but flagged. -/
private def openTerm : Expr := .app (.fvar ⟨`h⟩) (.bvar 0)
#guard d openTerm == "d25df22c974adbeab5281386b58b18b8a921b5afab7fbb020ea9692d81204eee"
#guard (DAG.TermDigest.compute openTerm).openTerm
#guard d (.app (.fvar ⟨`h⟩) (.bvar 0)) == d (.app (.fvar ⟨`other⟩) (.bvar 0))

/- L0 / L3 keys agree with the Python importer (`igf.graph.decl_schema`) and live Arango rows. -/
#guard DAG.Schema.declKey `InfoGeometry.AQFT.Pin55Pullback.bladeMatrixEquiv ==
  "d_f7bec2f5913b1e7a496a4a2aced3f82318f04198"
#guard DAG.Schema.edgeKey "A.b" "type" "C.d" == "e_09abd75daf5e87ea802f2fe7bec241b73bc56c5a"
