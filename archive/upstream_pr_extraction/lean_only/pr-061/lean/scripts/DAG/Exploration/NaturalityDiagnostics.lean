import Lean
import DAG.Functor
import InfoGeometry.Canonical.SpineAttributes

/-!
# scripts.DAG.Exploration.NaturalityDiagnostics

Diagnostic pass for the `@[spine_functor]` layer that sits above the strict
unary morphism engine.

Usage:
`lake env lean --run lean/scripts/DAG/Exploration/NaturalityDiagnostics.lean [module] [namespace]`

Defaults:
- module: `InfoGeometry.Canonical.All`
- namespace: `InfoGeometry`
-/

open Lean
open DAG
open InfoGeometry.Canonical

private def defaultModule : String :=
  "InfoGeometry.Canonical.All"

private def defaultNamespace : String :=
  "InfoGeometry"

private def argD (args : Array String) (idx : Nat) (fallback : String) : String :=
  args.getD idx fallback

private def headConst? (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const n _ => some n
  | _ => none

private partial def collectExplicitDomains (e : Expr) (acc : Array Expr := #[]) : Array Expr × Expr :=
  match e with
  | .forallE _ d b bi =>
      if bi.isExplicit then
        collectExplicitDomains b (acc.push d)
      else
        collectExplicitDomains b acc
  | _ => (acc, e)

structure FunctorSignature where
  decl : Name
  kind? : Option SpineFunctorKind
  explicitArity : Nat
  explicitDomainHeads : Array (Option Name)
  spineInputHeads : Array Name
  resultHead? : Option Name
  deriving Repr

private def summarizeFunctorSignature (env : Environment) (declName : Name) (type : Expr) :
    FunctorSignature :=
  let (domains, result) := collectExplicitDomains type
  let explicitDomainHeads := domains.map headConst?
  let spineInputHeads := domains.foldl (init := #[]) fun acc domain =>
    match headConst? domain with
    | some n =>
        if isSpineObject env n then acc.push n else acc
    | none => acc
  { decl := declName
    kind? := spineFunctorKind? env declName
    explicitArity := domains.size
    explicitDomainHeads := explicitDomainHeads
    spineInputHeads := spineInputHeads
    resultHead? := headConst? result
  }

private def sortSignatures (sigs : Array FunctorSignature) : Array FunctorSignature :=
  sigs.qsort fun a b => a.decl.toString < b.decl.toString

private def taggedFunctorDecls (env : Environment) (ns? : Option Name := none) : Array Name :=
  let decls := env.constants.fold (init := #[]) fun acc declName _ =>
    if let some ns := ns? then
      if !ns.isPrefixOf declName then
        acc
      else if isSpineFunctor env declName then
        acc.push declName
      else
        acc
    else if isSpineFunctor env declName then
      acc.push declName
    else
      acc
  decls.qsort fun a b => a.toString < b.toString

private def renderHeadList (heads : Array (Option Name)) : String :=
  if heads.isEmpty then
    "[]"
  else
    let parts := heads.map fun
      | some n => n.toString
      | none => "_"
    "[" ++ String.intercalate ", " parts.toList ++ "]"

private def renderNames (names : Array Name) : String :=
  if names.isEmpty then
    "[]"
  else
    "[" ++ String.intercalate ", " ((names.map toString).toList) ++ "]"

private def roleLabel (kind : SpineFunctorKind) : String :=
  match kind with
  | .lift => "lift"
  | .constructor => "constructor"
  | .responder => "responder"

private def obligationLabel (kind : SpineFunctorKind) : String :=
  match kind with
  | .lift => "lift naturality"
  | .constructor => "constructor compatibility"
  | .responder => "responder compatibility"

private def signatureMismatchReason? (sig : FunctorSignature) : Option String :=
  match sig.kind? with
  | none => some "missing or ambiguous functor role tag"
  | some .constructor =>
      if sig.explicitArity != 1 then
        some s!"constructor expected unary explicit arity, got {sig.explicitArity}"
      else
        none
  | some .lift =>
      if sig.explicitArity < 2 then
        some s!"lift expected at least two explicit inputs, got {sig.explicitArity}"
      else
        none
  | some .responder =>
      if sig.explicitArity < 2 then
        some s!"responder expected at least two explicit inputs, got {sig.explicitArity}"
      else
        none

private def printSignatureGroup (title : String) (sigs : Array FunctorSignature) : IO Unit := do
  IO.println title
  if sigs.isEmpty then
    IO.println "  <none>"
  else
    for sig in sortSignatures sigs do
      let role :=
        match sig.kind? with
        | some kind => roleLabel kind
        | none => "unclassified"
      let obligation :=
        match sig.kind? with
        | some kind => obligationLabel kind
        | none => "unresolved"
      IO.println s!"  {sig.decl}"
      IO.println s!"    role: {role}"
      IO.println s!"    obligation: {obligation}"
      IO.println s!"    explicit arity: {sig.explicitArity}"
      IO.println s!"    explicit heads: {renderHeadList sig.explicitDomainHeads}"
      IO.println s!"    spine inputs: {renderNames sig.spineInputHeads}"
      IO.println s!"    result head: {(sig.resultHead?.map toString).getD "_"}"

private def printMismatchGroup (sigs : Array FunctorSignature) : IO Unit := do
  IO.println "--- Signature Mismatches ---"
  if sigs.isEmpty then
    IO.println "  <none>"
  else
    for sig in sortSignatures sigs do
      IO.println s!"  {sig.decl}"
      IO.println s!"    {(signatureMismatchReason? sig).getD "unknown mismatch"}"

def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)

  let argv := args.toArray
  let moduleStr := argD argv 0 defaultModule
  let namespaceStr := argD argv 1 defaultNamespace
  let moduleName := moduleStr.toName
  let namespaceName := namespaceStr.toName

  let env ← Lean.importModules #[{ module := moduleName }] {}
  let canonicalMorphisms ← DAG.getAllMorphisms env (some namespaceName) (strict := true)
  let functorDecls := taggedFunctorDecls env (some namespaceName)
  let signatures := functorDecls.foldl (init := #[]) fun acc declName =>
    match env.find? declName with
    | some ci => acc.push (summarizeFunctorSignature env declName ci.type)
    | none => acc

  let lifts := signatures.filter fun sig => sig.kind? == some .lift
  let constructors := signatures.filter fun sig => sig.kind? == some .constructor
  let responders := signatures.filter fun sig => sig.kind? == some .responder
  let mismatches := signatures.filter fun sig => (signatureMismatchReason? sig).isSome

  IO.println s!"[NaturalityDiagnostics] module={moduleStr} namespace={namespaceStr}"
  IO.println ""
  IO.println "=== Naturality Diagnostic ==="
  IO.println s!"Canonical unary morphisms: {canonicalMorphisms.size}"
  IO.println s!"Tagged functors: {signatures.size}"
  IO.println s!"Lift candidates: {lifts.size}"
  IO.println s!"Constructor candidates: {constructors.size}"
  IO.println s!"Responder candidates: {responders.size}"
  IO.println s!"Signature mismatches: {mismatches.size}"
  IO.println ""

  printSignatureGroup "--- Lift Naturality Candidates ---" lifts
  IO.println ""
  printSignatureGroup "--- Constructor Compatibility Candidates ---" constructors
  IO.println ""
  printSignatureGroup "--- Responder Compatibility Candidates ---" responders
  IO.println ""
  printMismatchGroup mismatches

  return 0
