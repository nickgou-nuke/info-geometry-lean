import Lean
import DAG.Functor
import DAG.LiftNaturality
import InfoGeometry.Canonical.SpineAttributes

/-!
# scripts.DAG.Exploration.NaturalityPromoter

Report-only promoter for `@[spine_functor]` naturality obligations. This does
not emit Lean theorem stubs yet; it writes a quarantined Markdown report.

Usage:
`lake env lean --run lean/scripts/DAG/Exploration/NaturalityPromoter.lean [module] [namespace] [output]`

Defaults:
- module: `InfoGeometry.Canonical.All`
- namespace: `InfoGeometry`
- output: `reports/naturality-promoter.md`
-/

open Lean
open DAG
open InfoGeometry.Canonical

private def defaultModule : String :=
  "InfoGeometry.Canonical.All"

private def defaultNamespace : String :=
  "InfoGeometry"

private def defaultOutput : String :=
  "reports/naturality-promoter.md"

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
      | some n => s!"`{n}`"
      | none => "`_`"
    "[" ++ String.intercalate ", " parts.toList ++ "]"

private def renderNames (names : Array Name) : String :=
  if names.isEmpty then
    "[]"
  else
    "[" ++ String.intercalate ", " ((names.map fun n => s!"`{n}`").toList) ++ "]"

private def roleLabel (kind : SpineFunctorKind) : String :=
  match kind with
  | .lift => "lift"
  | .constructor => "constructor"
  | .responder => "responder"

private def obligationLabel (kind : SpineFunctorKind) : String :=
  match kind with
  | .lift => "Lift naturality"
  | .constructor => "Constructor compatibility"
  | .responder => "Responder compatibility"

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

private def renderSignature (sig : FunctorSignature) : String :=
  let role := sig.kind?.map roleLabel |>.getD "unclassified"
  let obligation := sig.kind?.map obligationLabel |>.getD "Unresolved"
  s!"- declaration: `{sig.decl}`\n" ++
    s!"  role: `{role}`\n" ++
    s!"  obligation: `{obligation}`\n" ++
    s!"  explicit arity: `{sig.explicitArity}`\n" ++
    s!"  explicit heads: {renderHeadList sig.explicitDomainHeads}\n" ++
    s!"  spine inputs: {renderNames sig.spineInputHeads}\n" ++
    s!"  result head: `{(sig.resultHead?.map toString).getD "_"}`\n"

private def renderLiftSeedSummary (seed : LiftSeed) : String :=
  s!"- theorem: `{seed.theoremName}`\n" ++
    s!"  heads: {renderNames seed.headLiftMentions}\n" ++
    s!"  normalized defeq: `{seed.normDefEq}`\n"

private def renderLiftSeedGroup (seeds : Array LiftSeed) : String :=
  if seeds.isEmpty then
    "## Known lift patterns\n\n<none>\n\n"
  else
    let body := String.join <| (seeds.qsort fun a b => a.theoremName.toString < b.theoremName.toString).toList.map fun seed =>
      renderLiftSeedSummary seed ++ "\n"
    "## Known lift patterns\n\n" ++ body

private def renderGroup (title : String) (sigs : Array FunctorSignature) : String :=
  if sigs.isEmpty then
    s!"## {title}\n\n<none>\n\n"
  else
    let body := String.join <| (sortSignatures sigs).toList.map fun sig =>
      renderSignature sig ++ "\n"
    s!"## {title}\n\n{body}"

private def renderMismatchGroup (sigs : Array FunctorSignature) : String :=
  if sigs.isEmpty then
    "## Signature mismatches\n\n<none>\n"
  else
    let body := String.join <| (sortSignatures sigs).toList.map fun sig =>
      s!"- `{sig.decl}`: {(signatureMismatchReason? sig).getD "unknown mismatch"}\n"
    "## Signature mismatches\n\n" ++ body

private def renderReport
    (moduleStr namespaceStr : String)
    (canonicalMorphisms : Array MorphismInfo)
    (signatures lifts constructors responders mismatches : Array FunctorSignature)
    (liftSeeds : Array LiftSeed) : String :=
  let normalizedLiftSeedCount := liftSeeds.foldl (init := 0) fun acc seed => acc + if seed.normDefEq then 1 else 0
  let header :=
    s!"# Naturality Promotion Report\n\n" ++
    s!"- module: `{moduleStr}`\n" ++
    s!"- namespace: `{namespaceStr}`\n" ++
    s!"- canonical unary morphisms: `{canonicalMorphisms.size}`\n" ++
    s!"- tagged functors: `{signatures.size}`\n" ++
    s!"- lift candidates: `{lifts.size}`\n" ++
    s!"- known lift patterns: `{liftSeeds.size}`\n" ++
    s!"- normalized lift patterns: `{normalizedLiftSeedCount}`\n" ++
    s!"- constructor candidates: `{constructors.size}`\n" ++
    s!"- responder candidates: `{responders.size}`\n" ++
    s!"- signature mismatches: `{mismatches.size}`\n\n"
  header ++
    renderLiftSeedGroup liftSeeds ++
    renderGroup "Lift naturality obligations" lifts ++
    renderGroup "Constructor compatibility obligations" constructors ++
    renderGroup "Responder compatibility obligations" responders ++
    renderMismatchGroup mismatches

def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)

  let argv := args.toArray
  let moduleStr := argD argv 0 defaultModule
  let namespaceStr := argD argv 1 defaultNamespace
  let outputPath := argD argv 2 defaultOutput
  let moduleName := moduleStr.toName
  let namespaceName := namespaceStr.toName

  let env ← Lean.importModules #[{ module := moduleName }] {}
  let canonicalMorphisms ← DAG.getAllMorphisms env (some namespaceName) (strict := true)
  let ctxCore : Core.Context := { fileName := "<NaturalityPromoter>", fileMap := default }
  let sCore : Core.State := { env := env }
  let ((liftSeeds, _), _) ← (collectLiftSeeds env namespaceName).toIO ctxCore sCore
  let functorDecls := taggedFunctorDecls env (some namespaceName)
  let signatures := functorDecls.foldl (init := #[]) fun acc declName =>
    match env.find? declName with
    | some ci => acc.push (summarizeFunctorSignature env declName ci.type)
    | none => acc
  let lifts := signatures.filter fun sig => sig.kind? == some .lift
  let constructors := signatures.filter fun sig => sig.kind? == some .constructor
  let responders := signatures.filter fun sig => sig.kind? == some .responder
  let mismatches := signatures.filter fun sig => (signatureMismatchReason? sig).isSome
  let report := renderReport moduleStr namespaceStr canonicalMorphisms signatures lifts constructors responders mismatches liftSeeds

  IO.FS.writeFile outputPath report
  IO.println s!"[NaturalityPromoter] tagged functors: {signatures.size}"
  IO.println s!"[NaturalityPromoter] lift/constructor/responder: {lifts.size}/{constructors.size}/{responders.size}"
  IO.println s!"[NaturalityPromoter] known lift patterns: {liftSeeds.size}"
  IO.println s!"[NaturalityPromoter] signature mismatches: {mismatches.size}"
  IO.println s!"[NaturalityPromoter] wrote report: {outputPath}"
  return 0
