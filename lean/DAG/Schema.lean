/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Lean
import DAG.Basic
import DAG.Sha256

/-!
# DAG extraction schema (`info_geometry.dag_schema.v1`)

Single Lean owner of the rules every DAG extractor must share, so exported
layers stay consistent with each other and with the in-Lean operators:

* **L0 keys**: `declKey n = "d_" ++ sha256(n.toString)[:40]`
  (identical to `igf.graph.decl_schema.decl_key` and the Arango importers);
* **L3 edges**: `DAG.edgesFromConstantInfo` from `DAG.Basic` — the same rule the
  SCC / Hydrate / TwoComplex / Hodge operators compute on (constants plus
  `Expr.proj` structure heads, `value?` with `allowOpaque := true`, self-loops
  kept) — restricted to declarations this run emits;
* the declaration filter, namespace filter and kind vocabulary;
* source ranges (start, end, selection) for linking back to code.
-/

open Lean

namespace DAG.Schema

def schemaVersion : String := "info_geometry.dag_schema.v1"

/-- Kind vocabulary (matches the historical Indexer strings). -/
def kindString : ConstantInfo → String
  | .thmInfo _    => "theorem"
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .quotInfo _   => "quotient"
  | .ctorInfo _   => "constructor"
  | .recInfo _    => "recursor"

def edgeKindString : EdgeKind → String
  | .type  => "type"
  | .value => "value"

/-- Auto-generated / unstable names excluded from extraction. -/
def shouldIndexDeclString (s : String) : Bool :=
  !(s.contains "._" || s.endsWith "match_" || s.endsWith "proof_" || s.endsWith "injEq")

/-- Comma-separated namespace prefixes; empty or `*` means no filter. -/
def parseNamespaceFilters (s : String) : Option (List String) :=
  let parts :=
    (s.splitOn ",").map (fun part => part.trimAscii.toString) |>.filter (fun x => x != "" && x != "*")
  if parts.isEmpty then none else some parts

/-- `n` is `p` or lies under `p.` for some filter `p`. -/
def inNamespaceFilters (nsFilters : Option (List String)) (n : Name) : Bool :=
  match nsFilters with
  | none => true
  | some filters =>
      let s := toString n
      filters.any (fun p => s = p || s.startsWith (p ++ "."))

/-- Declarations a run emits: in the environment, inside the filters, stable name. -/
def isIndexed (env : Environment) (nsFilters : Option (List String)) (n : Name) : Bool :=
  env.contains n && inNamespaceFilters nsFilters n && shouldIndexDeclString n.toString

/-- L0 declaration key. -/
def declKey (n : Name) : String :=
  "d_" ++ (DAG.Sha256.hexDigestString n.toString).take 40

/-- Deterministic L3 edge key over `src|kind|dst` (names as emitted). -/
def edgeKey (src kind dst : String) : String :=
  "e_" ++ (DAG.Sha256.hexDigestString s!"{src}|{kind}|{dst}").take 40

/-- L3 edges of a constant: the `DAG.Basic` rule restricted to emitted declarations.
Duplicates (same target and kind) are already removed by `Basic` (`NameSet`). -/
def indexedEdges (env : Environment) (nsFilters : Option (List String)) (ci : ConstantInfo) :
    Array (Name × EdgeKind) :=
  (edgesFromConstantInfo ci).filter fun (dst, _) => isIndexed env nsFilters dst

/-- Source range of a declaration (1-based lines, 0-based UTF-8 codepoint columns as in Lean). -/
structure SourceRange where
  line : Nat := 0
  column : Nat := 0
  endLine : Nat := 0
  endColumn : Nat := 0
  selectionLine : Nat := 0
  selectionColumn : Nat := 0
  selectionEndLine : Nat := 0
  selectionEndColumn : Nat := 0
deriving ToJson, FromJson, Repr, Inhabited

/-- Ranges from `findDeclarationRanges?`; all zeros when unavailable. -/
def sourceRange (n : Name) : MetaM SourceRange := do
  match ← findDeclarationRanges? n with
  | some dr =>
      return {
        line := dr.range.pos.line, column := dr.range.pos.column
        endLine := dr.range.endPos.line, endColumn := dr.range.endPos.column
        selectionLine := dr.selectionRange.pos.line
        selectionColumn := dr.selectionRange.pos.column
        selectionEndLine := dr.selectionRange.endPos.line
        selectionEndColumn := dr.selectionRange.endPos.column }
  | none => return {}

/-- Repository-relative path when `file` lies under `root`, otherwise `file` unchanged. -/
def relativeTo (root file : String) : String :=
  let root := if root.endsWith "/" then root else root ++ "/"
  if file.startsWith root then (file.drop root.length).toString else file

end DAG.Schema
