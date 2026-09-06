import Lean
import Lean.Data.Json

open Lean Meta

namespace DAG.KernelEquivalenceExport

/--
Input row for a Lean/kernel equivalence check.

The exporter intentionally accepts plain JSONL so Python candidate generators can
remain candidate generators only.  Equivalence promotion happens here, inside
Lean, through `Meta.isDefEq`.
-/
structure PairRow where
  sourceDecl : String
  targetDecl : String
deriving Repr

structure KernelEquivalenceRow where
  sourceDecl : String
  targetDecl : String
  mode : String
  sourceFound : Bool
  targetFound : Bool
  sourceKind : String
  targetKind : String
  sameKind : Bool
  kernelTypeDefEq : Bool
  kernelValueDefEq : Bool
  sourceHasValue : Bool
  targetHasValue : Bool
  leanVerified : Bool
  safeForAutoRewrite : Bool
  certificateKind : String
  verificationTier : String
  proofAuthority : String
  checker : String
  certificateHash : String
  error : String := ""
deriving Repr, ToJson

private def dottedName (s : String) : Name :=
  (s.splitOn ".").foldl (init := Name.anonymous) fun acc part =>
    if part.isEmpty then acc else Name.str acc part

private def parseImports (s : String) : Array Import :=
  let mods := (s.splitOn ",").filter (fun x => x != "")
  mods.foldl (init := #[]) fun acc m => acc.push { module := dottedName m }

private def kindString : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .quotInfo _ => "quot"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "recursor"

private def constantValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .thmInfo info => some info.value
  | .defnInfo info => some info.value
  | .axiomInfo _ => none
  | .opaqueInfo _ => none
  | .inductInfo _ => none
  | .quotInfo _ => none
  | .ctorInfo _ => none
  | .recInfo _ => none

private def stableHashString (s : String) : String :=
  s!"lean-kernel-hash:{(hash s).toNat}"

private def certificateHash
    (source target mode : String)
    (typeDefEq valueDefEq leanVerified : Bool) : String :=
  stableHashString s!"lean-kernel-equivalence|{source}|{target}|{mode}|{typeDefEq}|{valueDefEq}|{leanVerified}"

private def isAllowedMode (mode : String) : Bool :=
  mode == "type" || mode == "value" || mode == "type-and-value"

private def verifiedByMode (mode : String) (typeDefEq valueDefEq : Bool) : Bool :=
  match mode with
  | "type" => typeDefEq
  | "value" => valueDefEq
  | "type-and-value" => typeDefEq && valueDefEq
  | _ => false

private def safeForAutoRewriteByMode
    (mode : String)
    (typeDefEq valueDefEq sourceHasValue targetHasValue : Bool) : Bool :=
  match mode with
  | "type" => false
  | "value" => typeDefEq && valueDefEq && sourceHasValue && targetHasValue
  | "type-and-value" => typeDefEq && valueDefEq && sourceHasValue && targetHasValue
  | _ => false

private def tierByMode (mode : String) : String :=
  match mode with
  | "type" => "lean_kernel_type_defeq"
  | "value" => "lean_kernel_value_defeq"
  | "type-and-value" => "lean_kernel_type_and_value_defeq"
  | _ => "lean_kernel_invalid_mode"

private def defEq (a b : Expr) : MetaM Bool := do
  withNewMCtxDepth <| withTransparency .all <| isDefEq a b

private def checkPair (mode : String) (source target : Name) : MetaM KernelEquivalenceRow := do
  let env ← getEnv
  let sourceDecl := toString source
  let targetDecl := toString target
  match env.find? source, env.find? target with
  | none, none =>
      let h := certificateHash sourceDecl targetDecl mode false false false
      pure {
        sourceDecl := sourceDecl, targetDecl := targetDecl, mode := mode
        sourceFound := false, targetFound := false
        sourceKind := "missing", targetKind := "missing", sameKind := false
        kernelTypeDefEq := false, kernelValueDefEq := false
        sourceHasValue := false, targetHasValue := false
        leanVerified := false, safeForAutoRewrite := false
        certificateKind := "lean_kernel_equivalence"
        verificationTier := tierByMode mode
        proofAuthority := "lean-kernel-isDefEq"
        checker := "Lean.Meta.isDefEq"
        certificateHash := h
        error := "source and target declarations not found"
      }
  | none, some targetCi =>
      let h := certificateHash sourceDecl targetDecl mode false false false
      pure {
        sourceDecl := sourceDecl, targetDecl := targetDecl, mode := mode
        sourceFound := false, targetFound := true
        sourceKind := "missing", targetKind := kindString targetCi, sameKind := false
        kernelTypeDefEq := false, kernelValueDefEq := false
        sourceHasValue := false, targetHasValue := (constantValue? targetCi).isSome
        leanVerified := false, safeForAutoRewrite := false
        certificateKind := "lean_kernel_equivalence"
        verificationTier := tierByMode mode
        proofAuthority := "lean-kernel-isDefEq"
        checker := "Lean.Meta.isDefEq"
        certificateHash := h
        error := "source declaration not found"
      }
  | some sourceCi, none =>
      let h := certificateHash sourceDecl targetDecl mode false false false
      pure {
        sourceDecl := sourceDecl, targetDecl := targetDecl, mode := mode
        sourceFound := true, targetFound := false
        sourceKind := kindString sourceCi, targetKind := "missing", sameKind := false
        kernelTypeDefEq := false, kernelValueDefEq := false
        sourceHasValue := (constantValue? sourceCi).isSome, targetHasValue := false
        leanVerified := false, safeForAutoRewrite := false
        certificateKind := "lean_kernel_equivalence"
        verificationTier := tierByMode mode
        proofAuthority := "lean-kernel-isDefEq"
        checker := "Lean.Meta.isDefEq"
        certificateHash := h
        error := "target declaration not found"
      }
  | some sourceCi, some targetCi =>
      let typeDefEq ← defEq sourceCi.type targetCi.type
      let sourceVal? := constantValue? sourceCi
      let targetVal? := constantValue? targetCi
      let valueDefEq ←
        match sourceVal?, targetVal? with
        | some sourceVal, some targetVal => defEq sourceVal targetVal
        | _, _ => pure false
      let leanVerified := verifiedByMode mode typeDefEq valueDefEq
      let sourceHasValue := sourceVal?.isSome
      let targetHasValue := targetVal?.isSome
      let safeForAutoRewrite :=
        safeForAutoRewriteByMode mode typeDefEq valueDefEq sourceHasValue targetHasValue
      let h := certificateHash sourceDecl targetDecl mode typeDefEq valueDefEq leanVerified
      pure {
        sourceDecl := sourceDecl, targetDecl := targetDecl, mode := mode
        sourceFound := true, targetFound := true
        sourceKind := kindString sourceCi, targetKind := kindString targetCi
        sameKind := kindString sourceCi == kindString targetCi
        kernelTypeDefEq := typeDefEq
        kernelValueDefEq := valueDefEq
        sourceHasValue := sourceHasValue
        targetHasValue := targetHasValue
        leanVerified := leanVerified
        safeForAutoRewrite := safeForAutoRewrite
        certificateKind := "lean_kernel_equivalence"
        verificationTier := tierByMode mode
        proofAuthority := "lean-kernel-isDefEq"
        checker := "Lean.Meta.isDefEq"
        certificateHash := h
        error := ""
      }

private def readPairs (path : System.FilePath) : IO (Array PairRow) := do
  let content ← IO.FS.readFile path
  let mut rows : Array PairRow := #[]
  for raw in content.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.isEmpty then
      continue
    match Json.parse line with
    | Except.error err =>
        throw <| IO.userError s!"could not parse JSONL row in {path}: {err}"
    | Except.ok json =>
        let source ←
          match json.getObjValAs? String "sourceDecl" with
          | Except.ok value => pure value
          | Except.error err => throw <| IO.userError s!"missing sourceDecl in {path}: {err}"
        let target ←
          match json.getObjValAs? String "targetDecl" with
          | Except.ok value => pure value
          | Except.error err => throw <| IO.userError s!"missing targetDecl in {path}: {err}"
        rows := rows.push { sourceDecl := source, targetDecl := target }
  pure rows

private def writeJsonl {α} [ToJson α] (path : System.FilePath) (rows : Array α) : IO Unit := do
  match path.parent with
  | some parent => IO.FS.createDirAll parent
  | none => pure ()
  let lines := String.intercalate "\n" <| rows.toList.map (fun row => (toJson row).compress)
  IO.FS.writeFile path (lines ++ if rows.isEmpty then "" else "\n")

private def runMetaWithEnv (env : Environment) (x : MetaM α) : IO α := do
  let (result, _) ← (MetaM.run' (ctx := {}) (s := {}) x).toIO
    { fileName := "<DAG.KernelEquivalenceExport>"
      fileMap := default
      options := ({} : Options)
    }
    { env := env }
  pure result

private def runExport
    (importModsStr pairsPathStr outPathStr mode : String) : IO UInt32 := do
  if !isAllowedMode mode then
    IO.eprintln s!"invalid mode: {mode}; expected type, value, or type-and-value"
    return 1
  let pairsPath := System.FilePath.mk pairsPathStr
  let outPath := System.FilePath.mk outPathStr
  let pairs ← readPairs pairsPath
  let env ← importModules (parseImports importModsStr) {} 0
  let rows ← runMetaWithEnv env do
    let mut out : Array KernelEquivalenceRow := #[]
    for row in pairs do
      out := out.push (← checkPair mode (dottedName row.sourceDecl) (dottedName row.targetDecl))
    pure out
  writeJsonl outPath rows
  IO.println s!"[KernelEquivalenceExport] checked pairs={pairs.size}"
  IO.println s!"[KernelEquivalenceExport] wrote {outPathStr}"
  pure 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [importModsStr, pairsPath, outPath] =>
      runExport importModsStr pairsPath outPath "type"
  | [importModsStr, pairsPath, outPath, "--mode", mode] =>
      runExport importModsStr pairsPath outPath mode
  | _ =>
      IO.eprintln "usage: KernelEquivalenceExport <import-module[,module2,...]> <pairs.jsonl> <out.jsonl> [--mode type|value|type-and-value]"
      IO.eprintln "input JSONL rows require: {\"sourceDecl\":\"A.foo\",\"targetDecl\":\"B.bar\"}"
      pure 1

end DAG.KernelEquivalenceExport

def main (args : List String) : IO UInt32 :=
  DAG.KernelEquivalenceExport.main args
