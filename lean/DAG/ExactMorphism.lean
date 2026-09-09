import Lean
import DAG.Basic
import InfoGeometry.Canonical.SpineAttributes

/-!
# Exact Category-Theoretic Morphism Engine

Replaces the heuristic WL-hash-based commutativity check in `DAG.Functor`
with exact kernel-trusted `isDefEq` verification.

## Architecture

1. **Morphism extraction** runs in `MetaM` using `whnf` + `forallTelescope`
   to correctly resolve implicit/instance binders. Declarations are admitted
   only if they satisfy the **unary morphism contract**: exactly one explicit
   binder, with the result type not depending on that binder.

2. **Closed metadata**: `MorphismEntry` stores only `Name`-level data that is
   safe to persist across `MetaM` contexts and `.olean` files. Domain and
   codomain `Expr`s are **never** stored — they are re-extracted on demand
   from the closed declaration type via `getConstInfo`.

3. **Application construction** uses `mkAppM` to let Lean synthesize implicit
   and instance arguments automatically, replacing the brittle
   `mkApp (mkConst ...)` pattern.

4. **Commutativity checking** constructs `h ∘ f` and `k ∘ g` via `mkAppM`
   under a fresh local binder and tests `Lean.Meta.isDefEq`, giving a
3. **No Local Escapes**: The `withUnaryMorphismSignature` callback replaces `rehydrateDomCod` and guarantees that telescope-local variables do not escape to the enclosing `MetaM` environment.

4. **Controlled Indexing**: Morphism harvesting is a pure read. Cache mutation happens strictly through the `#index_morphisms` command with built-in deduplication.

*Note on Cache Usage*: The persistent cache exists and is explicitly indexable, but the current square finder (`findCommutativeSquaresFromHarvest`) performs candidate generation from an in-memory harvest, not yet directly from the persisted cache.

5. **Span/cospan candidate detection** identifies pullback-shaped and
   pushout-shaped subgraphs in the declaration DAG. This is topological
   candidate detection only — no universal-property verification is performed.

6. **Persistent cache** via `SimplePersistentEnvExtension` stores closed
   `MorphismEntry` records. `harvestMorphisms` populates the cache;
   `findCommutativeSquaresFromHarvest` consumes a pre-built harvest.
   Phase 1 (cached hash-join candidate generation) then
   Phase 2 (on-demand `MetaM` rehydration and `isDefEq` verification).

The spine-attribute path (`@[spine_morphism]`) is the primary authority.
The heuristic name-based path is retained only as a discovery fallback.

## Soundness Scope

This engine is sound for **validated unary top-level morphism declarations**:
declarations with exactly one explicit term argument that is the morphism input,
where every other argument is implicit or instance-inferred, and the result type
does not depend on the input. Declarations outside this fragment are rejected
at extraction time.

The named-morphism-type recognizer (`Hom`/`Equiv`/`Iso`/`Map` suffix check) is
not part of the unary contract — it only appears in the looser
`extractMorphismSignatureM` used for pretty-printing and heuristic discovery.
-/

open Lean Meta

namespace DAG

/-! ### Trace diagnostics -/

initialize registerTraceClass `DAG.Morphism
initialize registerTraceClass `DAG.Morphism.admit
initialize registerTraceClass `DAG.Morphism.reject
initialize registerTraceClass `DAG.Commutativity
initialize registerTraceClass `DAG.Commutativity.rehydrate
initialize registerTraceClass `DAG.Commutativity.mkAppM
initialize registerTraceClass `DAG.Commutativity.isDefEq
initialize registerTraceClass `DAG.Cache

/-! ### Closed morphism metadata -/

/--
Closed metadata for a morphism. Contains NO `Expr` fields — only `Name`-level
data that is safe to persist across `MetaM` contexts and `.olean` serialization.

Domain and codomain `Expr`s are re-extracted on demand from the closed
declaration type via `rehydrateMorphism`.
-/
structure MorphismEntry where
  decl    : Name
  domHead : Name
  codHead : Name
  deriving Inhabited, BEq, Hashable, Repr

instance : ToString MorphismEntry where
  toString m := s!"{m.decl} : {m.domHead} → {m.codHead}"

/-! ### Persistent cache -/

/-- In-memory morphism state with precomputed hash-join indices. -/
structure MorphismState where
  entries : Array MorphismEntry := #[]
  byDom   : Std.HashMap Name (Array MorphismEntry) := {}
  byCod   : Std.HashMap Name (Array MorphismEntry) := {}
  /-- Set of declaration names already indexed, for deduplication. -/
  indexed : Std.HashSet Name := {}
  deriving Inhabited

/-- Pure insertion into the morphism state, with deduplication by declaration name. -/
def MorphismState.insert (s : MorphismState) (entry : MorphismEntry) : MorphismState :=
  if s.indexed.contains entry.decl then s
  else
    { entries := s.entries.push entry
      byDom   := s.byDom.insert entry.domHead (s.byDom.getD entry.domHead #[] |>.push entry)
      byCod   := s.byCod.insert entry.codHead (s.byCod.getD entry.codHead #[] |>.push entry)
      indexed := s.indexed.insert entry.decl }

/--
Persistent environment extension for morphism metadata.
Both `addImportedFn` and `addEntryFn` are pure — no `MetaM` dependency.
-/
initialize morphismCacheExt : SimplePersistentEnvExtension MorphismEntry MorphismState ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun arrays =>
      arrays.foldl (init := {}) fun s entries =>
        entries.foldl (init := s) fun s' e => s'.insert e
    addEntryFn := fun s e => s.insert e
  }

/-- Read the cached morphism state from the environment. -/
def getMorphismState (env : Environment) : MorphismState :=
  morphismCacheExt.getState env

/-! ### Unary morphism signature extraction -/

/--
Strict unary morphism signature extractor (callback API).

A declaration is admitted only if, after telescope expansion, it has
**exactly one explicit binder** whose body does not depend on that binder.
This is the validated fragment for which `mkAppM decl #[x]` is sound.

The named-morphism-type recognizer (`Hom`/`Equiv`/`Iso`/`Map` suffix) is
**intentionally excluded** from this function. It admits morphism *objects*
(e.g., `f : A →+* B`) which have zero explicit binders and cannot be
applied via `mkAppM decl #[x]`.

Invokes the callback `k dom cod` within the current `forallTelescope` context,
guaranteeing NO telescope fvars escape to the enclosing `MetaM` environment.
-/
def withUnaryMorphismSignature {α : Type}
    (e : Expr) (k : Expr → Expr → MetaM α) : MetaM (Option α) := do
  forallTelescope e fun xs body => do
    let mut explicitBinders : Array (Expr × LocalDecl) := #[]
    for x in xs do
      let ldecl ← x.fvarId!.getDecl
      if ldecl.binderInfo.isExplicit then
        explicitBinders := explicitBinders.push (x, ldecl)

    -- Reject if not exactly one explicit binder
    if explicitBinders.size != 1 then
      return none

    let (x, ldecl) := explicitBinders[0]!
    -- Check that the body does not depend on this binder
    let bodyAbstracted := body.abstract #[x]
    if bodyAbstracted.hasLooseBVar 0 then
      return none

    some <$> k ldecl.type body

/--
Legacy extraction (callback API).
Scans past dependent explicit binders.
Less strict than `withUnaryMorphismSignature` — used only for
the named-morphism-type recognizer path and candidate display formatting.
-/
def withMorphismSignature {α : Type}
    (e : Expr) (k : Expr → Expr → MetaM α) : MetaM (Option α) := do
  -- First try the named-morphism-type recognizer
  let ew ← whnf e
  let fn := ew.getAppFn
  let args := ew.getAppArgs
  if fn.isConst && args.size >= 2 then
    let s := fn.constName!.toString
    if s.endsWith "Hom" || s.endsWith "Equiv" || s.endsWith "Iso" || s.endsWith "Map" then
      return some (← k args[args.size - 2]! args[args.size - 1]!)
  -- Otherwise, scan past explicit binders,
  -- but allow dependent binders as long as the last explicit is non-dependent.
  forallTelescope e fun xs body => do
    for i in [:xs.size] do
      let x := xs[xs.size - 1 - i]!
      let ldecl ← x.fvarId!.getDecl
      if ldecl.binderInfo.isExplicit then
        let bodyAbstracted := body.abstract #[x]
        if !bodyAbstracted.hasLooseBVar 0 then
          return some (← k ldecl.type body)
    return none

/--
Extract the head constant of a type after `whnf` normalization.
Used for coarse prefiltering — collapses reducible aliases and wrappers.
-/
def headNameOf (e : Expr) : MetaM Name := do
  let e' ← whnf e
  pure <| match e'.getAppFn with
    | .const n _ => n
    | _ => Name.anonymous

/--
Build a closed `MorphismEntry` from a declaration.
Uses `withUnaryMorphismSignature` to enforce the unary morphism contract.
Returns `none` for declarations outside the validated fragment.

Domain and codomain `Expr`s are NOT stored — only head-constant `Name`s
(computed from `whnf`-normalized types as a coarse prefilter for
hash-join candidate generation).
-/
def mkMorphismEntry? (declName : Name) (ci : ConstantInfo) :
    MetaM (Option MorphismEntry) := do
  withUnaryMorphismSignature ci.type fun dom cod => do
    let domHead ← headNameOf dom
    let codHead ← headNameOf cod
    trace[DAG.Morphism.admit] "{declName}: {domHead} → {codHead}"
    pure { decl := declName, domHead, codHead }

/-! ### On-demand verification -/

/--
Safely apply a validated unary morphism to an argument using `mkAppM`.
This lets Lean synthesize implicit and instance parameters automatically,
replacing the brittle `mkApp (mkConst ...)` pattern.

Sound only for declarations in the validated unary fragment.
-/
def mkUnaryMorphismApp (decl : Name) (x : Expr) : MetaM Expr := do
  try
    mkAppM decl #[x]
  catch e =>
    trace[DAG.Commutativity.mkAppM] "{decl}: mkAppM failed: {← e.toMessageData.toString}"
    throw e

/-! ### Pretty-printing -/

/--
Format a morphism entry by re-extracting the signature from the closed
declaration type. Does NOT use any persisted `Expr` data.
-/
def MorphismEntry.format (m : MorphismEntry) : MetaM MessageData := do
  let env ← getEnv
  let some ci := env.find? m.decl | return m!"{m.decl} (not found)"
  -- Try the looser extractor for display
  let sig? ← withMorphismSignature ci.type fun dom cod => do
    let domFmt ← ppExpr dom
    let codFmt ← ppExpr cod
    pure (domFmt, codFmt)
  match sig? with
  | none => return m!"{m.decl} : {m.domHead} → {m.codHead}"
  | some (domFmt, codFmt) =>
    return m!"{m.decl} : {domFmt} → {codFmt}"

/-! ### Morphism harvesting -/

/-- Harvest result separating tagged (authoritative) from heuristic morphisms. -/
structure MorphismHarvest where
  tagged    : Array MorphismEntry
  heuristic : Array MorphismEntry

/--
Collect all morphisms from the environment. **Pure read** — does not mutate
the environment or populate the persistent cache.

Use `indexMorphismCache` for controlled, deduplicated cache population.

The spine-attribute path (`@[spine_morphism]`) is the primary authority.
The heuristic name-based path is used as a discovery fallback.
-/
def harvestMorphisms (env : Environment) (ns? : Option Name := none) :
    MetaM MorphismHarvest := do
  let mut tagged := #[]
  let mut heuristic := #[]
  for (name, ci) in env.constants do
    if let some ns := ns? then
      if !ns.isPrefixOf name then continue
    let isTagged := InfoGeometry.Canonical.isSpineMorphism env name
    match ← mkMorphismEntry? name ci with
    | none => pure ()
    | some entry =>
      if isTagged then
        tagged := tagged.push entry
      else
        heuristic := heuristic.push entry
  return { tagged, heuristic }

/--
Explicit, deduplicated cache-population pass.

Scans the environment for validated unary morphisms and adds them to the
persistent `morphismCacheExt`. Deduplication is enforced by
`MorphismState.insert` — repeated calls are idempotent.

This is the **only** function that mutates the environment for cache purposes.
Call it once at a controlled elaboration point (e.g., `#index_morphisms`).
-/
def indexMorphismCache (env : Environment) (ns? : Option Name := none) :
    MetaM Environment := do
  let mut currentEnv := env
  let existingState := getMorphismState env
  let mut newCount := 0
  for (name, ci) in env.constants do
    if let some ns := ns? then
      if !ns.isPrefixOf name then continue
    -- Skip already-indexed declarations
    if existingState.indexed.contains name then continue
    match ← mkMorphismEntry? name ci with
    | none => pure ()
    | some entry =>
      currentEnv := morphismCacheExt.addEntry currentEnv entry
      newCount := newCount + 1
  trace[DAG.Cache] "Indexed {newCount} new entries ({existingState.entries.size} already cached)"
  return currentEnv

/-! ### Exact commutativity checking -/

/-- Result of an exact commutativity check. -/
inductive CommutativityVerdict
  | exact       : CommutativityVerdict   -- isDefEq succeeded
  | notEqual    : CommutativityVerdict   -- isDefEq failed
  | checkFailed : String → CommutativityVerdict   -- MetaM error
  deriving Inhabited

instance : ToString CommutativityVerdict where
  toString
    | .exact => "EXACT"
    | .notEqual => "NOT_EQUAL"
    | .checkFailed msg => s!"CHECK_FAILED: {msg}"

/-- A verified commutative square with its kernel verdict. -/
structure ExactCommutativeSquare where
  f : MorphismEntry  -- A → B
  g : MorphismEntry  -- A → C
  h : MorphismEntry  -- B → D
  k : MorphismEntry  -- C → D
  verdict : CommutativityVerdict

/--
Check whether a candidate square `(f: A→B, g: A→C, h: B→D, k: C→D)`
commutes, using `isDefEq` on the compositions `h ∘ f` and `k ∘ g`.

**Two-phase design**:
- Phase 1 (caller): candidate generation via cached hash-join on head names.
- Phase 2 (this function): on-demand rehydration from closed declaration types
  + `mkAppM` application construction + `isDefEq` kernel verification.

Sound for validated unary top-level morphism declarations.
-/
def checkCommutativityExact
    (f g h k : MorphismEntry) : MetaM CommutativityVerdict := do
  try
    let env ← getEnv
    let some ci := env.find? f.decl |
      return .checkFailed s!"Could not find {f.decl}"

    let some result ← withUnaryMorphismSignature ci.type (fun fDom _ => do
      withNewMCtxDepth do
        let xTy ← whnf fDom
        withLocalDeclD `x xTy fun x => do
          let fx  ← mkUnaryMorphismApp f.decl x
          let hfx ← mkUnaryMorphismApp h.decl fx
          let gx  ← mkUnaryMorphismApp g.decl x
          let kgx ← mkUnaryMorphismApp k.decl gx
          isDefEq hfx kgx) | return .checkFailed s!"Could not re-extract signature for {f.decl}"

    if result then
      trace[DAG.Commutativity.isDefEq] "EXACT: {h.decl} ∘ {f.decl} = {k.decl} ∘ {g.decl}"
      return .exact
    else
      trace[DAG.Commutativity.isDefEq] "NOT_EQUAL: {h.decl} ∘ {f.decl} ≠ {k.decl} ∘ {g.decl}"
      return .notEqual
  catch e =>
    let msg ← e.toMessageData.toString
    trace[DAG.Commutativity] "CHECK_FAILED: {f.decl},{g.decl},{h.decl},{k.decl}: {msg}"
    return .checkFailed msg

/--
Find all commutative squares from a pre-built harvest.

**Two-phase architecture**:
- Phase 1: Hash-join candidate generation from `MorphismEntry` head names.
  Complexity is bounded by the morphism count, not the full constant count.
  Worst case is quartic in morphism count but reduced by hash-join filtering.
- Phase 2: On-demand `MetaM` rehydration and `isDefEq` verification for
  each candidate.

This is the harvest-based worker. Callers should harvest once and pass the
result here, rather than calling `harvestMorphisms` again.
-/
def findCommutativeSquaresFromHarvest
    (harvest : MorphismHarvest) (strict : Bool := true) :
    MetaM (Array ExactCommutativeSquare) := do
  let morphs := if strict then harvest.tagged else harvest.tagged ++ harvest.heuristic

  -- Phase 1: Build hash-join index by domain head name
  let mut byDom : Std.HashMap Name (Array MorphismEntry) := {}
  for m in morphs do
    byDom := byDom.insert m.domHead (byDom.getD m.domHead #[] |>.push m)

  let mut results := #[]

  for f in morphs do
    let A := f.domHead
    let B := f.codHead
    if let some gCandidates := byDom.get? A then
      for g in gCandidates do
        if f.decl == g.decl then continue
        let C := g.codHead
        if let some hCandidates := byDom.get? B then
          for h in hCandidates do
            let D := h.codHead
            if let some kCandidates := byDom.get? C then
              for k in kCandidates do
                if k.codHead != D then continue
                if h.decl == k.decl then continue
                -- Phase 2: exact kernel check
                let verdict ← checkCommutativityExact f g h k
                match verdict with
                | .exact =>
                  results := results.push { f, g, h, k, verdict }
                | .notEqual => pure ()
                | .checkFailed _ => pure ()

  return results

/--
Convenience wrapper: harvest morphisms then find commutative squares.
For callers that do not need the harvest for other analyses.
-/
def findCommutativeSquaresExact (env : Environment) (ns? : Option Name := none)
    (strict : Bool := true) :
    MetaM (Array ExactCommutativeSquare) := do
  let harvest ← harvestMorphisms env ns?
  findCommutativeSquaresFromHarvest harvest (strict := strict)

/-! ### Span/cospan candidate detection

These find topological candidates only. No universal-property verification
is performed. The candidates are shapes in the declaration DAG that could
potentially be completed to pullbacks or pushouts. -/

/-- A span: two morphisms sharing the same codomain. Topological pullback candidate. -/
structure SpanCandidate where
  f : MorphismEntry   -- A → C
  g : MorphismEntry   -- B → C
  apex : Name         -- C

/-- A cospan: two morphisms sharing the same domain. Topological pushout candidate. -/
structure CospanCandidate where
  f : MorphismEntry   -- C → A
  g : MorphismEntry   -- C → B
  base : Name         -- C

/--
Find span-shaped subgraphs: pairs `(f: A→C, g: B→C)` sharing a codomain.
Topological candidate detection only — no universal-property verification.
-/
def findSpanCandidates (harvest : MorphismHarvest) : Array SpanCandidate := Id.run do
  let morphs := harvest.tagged ++ harvest.heuristic

  let mut byCod : Std.HashMap Name (Array MorphismEntry) := {}
  for m in morphs do
    byCod := byCod.insert m.codHead (byCod.getD m.codHead #[] |>.push m)

  let mut results := #[]
  for (apex, morphsToApex) in byCod do
    if apex == Name.anonymous then continue
    for i in [:morphsToApex.size] do
      for j in [i+1:morphsToApex.size] do
        let f := morphsToApex[i]!
        let g := morphsToApex[j]!
        if f.domHead != g.domHead then
          results := results.push { f, g, apex }
  return results

/--
Find cospan-shaped subgraphs: pairs `(f: C→A, g: C→B)` sharing a domain.
Topological candidate detection only — no universal-property verification.
-/
def findCospanCandidates (harvest : MorphismHarvest) : Array CospanCandidate := Id.run do
  let morphs := harvest.tagged ++ harvest.heuristic

  let mut byDom : Std.HashMap Name (Array MorphismEntry) := {}
  for m in morphs do
    byDom := byDom.insert m.domHead (byDom.getD m.domHead #[] |>.push m)

  let mut results := #[]
  for (base, morphsFromBase) in byDom do
    if base == Name.anonymous then continue
    for i in [:morphsFromBase.size] do
      for j in [i+1:morphsFromBase.size] do
        let f := morphsFromBase[i]!
        let g := morphsFromBase[j]!
        if f.codHead != g.codHead then
          results := results.push { f, g, base }
  return results

/-! ### Definitional inverse pair detection -/

/--
Check whether two morphisms are definitional inverses.
Tests both `f(g(y)) = y` and `g(f(x)) = x` via `isDefEq`
under fresh local binders.

This detects exact inverse pairs of top-level constants.
It is NOT full categorical isomorphism detection.
-/
def checkDefinitionalInverse (f g : MorphismEntry) : MetaM Bool := do
  let env ← getEnv
  let some ciF := env.find? f.decl | return false
  let some ciG := env.find? g.decl | return false

  -- Check f ∘ g = id
  let some fog_id ← withUnaryMorphismSignature ciG.type (fun gDom _ => do
    withNewMCtxDepth do
      let yTy ← whnf gDom
      withLocalDeclD `y yTy fun y => do
        let gy  ← mkUnaryMorphismApp g.decl y
        let fgy ← mkUnaryMorphismApp f.decl gy
        isDefEq fgy y) | return false
  if !fog_id then return false

  -- Check g ∘ f = id
  let some gof_id ← withUnaryMorphismSignature ciF.type (fun fDom _ => do
    withNewMCtxDepth do
      let xTy ← whnf fDom
      withLocalDeclD `x xTy fun x => do
        let fx  ← mkUnaryMorphismApp f.decl x
        let gfx ← mkUnaryMorphismApp g.decl fx
        isDefEq gfx x) | return false

  return gof_id

/--
Scan for pairs of morphisms that act as definitional inverses.
-/
def findDefinitionalInverses (harvest : MorphismHarvest) :
    MetaM (Array (MorphismEntry × MorphismEntry)) := do
  let morphs := harvest.tagged ++ harvest.heuristic
  let mut inverses := #[]
  for i in [:morphs.size] do
    for j in [i+1:morphs.size] do
      let f := morphs[i]!
      let g := morphs[j]!
      if f.domHead == g.codHead && f.codHead == g.domHead then
        if ← checkDefinitionalInverse f g then
          inverses := inverses.push (f, g)
  return inverses

/-! ### Diagnostic summary -/

/-- Summary statistics from an exact morphism pipeline run. -/
structure ExactPipelineSummary where
  taggedMorphisms    : Nat
  heuristicMorphisms : Nat
  exactSquares       : Nat
  spanCandidates     : Nat
  cospanCandidates   : Nat
  definitionalInverses : Nat

/--
Run the full exact pipeline and return a diagnostic summary.
Harvests morphisms once and reuses the harvest across all sub-analyses.
-/
def runExactPipeline (env : Environment) (ns? : Option Name := none) :
    MetaM ExactPipelineSummary := do
  -- Single harvest, passed to all sub-analyses
  let harvest ← harvestMorphisms env ns?
  let squares ← findCommutativeSquaresFromHarvest harvest (strict := false)
  let spans := findSpanCandidates harvest
  let cospans := findCospanCandidates harvest
  let inverses ← findDefinitionalInverses harvest
  return {
    taggedMorphisms    := harvest.tagged.size
    heuristicMorphisms := harvest.heuristic.size
    exactSquares       := squares.size
    spanCandidates     := spans.size
    cospanCandidates   := cospans.size
    definitionalInverses := inverses.size
  }

/-- Print a diagnostic summary to stdout. -/
def printExactPipelineSummary (s : ExactPipelineSummary) : IO Unit := do
  IO.println "━━━ Exact Morphism Pipeline (Unary Fragment) ━━━"
  IO.println s!"  Tagged morphisms       : {s.taggedMorphisms}"
  IO.println s!"  Heuristic morphisms    : {s.heuristicMorphisms}"
  IO.println s!"  Exact comm. squares    : {s.exactSquares}"
  IO.println s!"  Span candidates        : {s.spanCandidates}"
  IO.println s!"  Cospan candidates      : {s.cospanCandidates}"
  IO.println s!"  Definitional inverses  : {s.definitionalInverses}"

/-! ### Command UI -/

open Elab Command

/-- `#find_morphisms` command: list all morphisms found in the environment (pure read). -/
syntax (name := findMorphismsCmd) "#find_morphisms" (ident)? : command

@[command_elab findMorphismsCmd]
def elabFindMorphisms : CommandElab := fun stx => do
  let ns? := stx[1].getOptional?.map (·.getId)
  liftTermElabM do
    let harvest ← harvestMorphisms (← getEnv) ns?
    let mut msg := m!"Found {harvest.tagged.size} tagged and {harvest.heuristic.size} heuristic morphisms:\n"
    msg := msg ++ "\nTagged:\n"
    for m in harvest.tagged do
      msg := msg ++ m!"  • {← m.format}\n"
    msg := msg ++ "\nHeuristic:\n"
    for m in harvest.heuristic.toList.take 30 do
      msg := msg ++ m!"  • {← m.format}\n"
    if harvest.heuristic.size > 30 then
      msg := msg ++ m!"  ... ({harvest.heuristic.size - 30} more)\n"
    logInfo msg

/-- `#find_squares` command: find and display all commutative squares (pure read). -/
syntax (name := findSquaresCmd) "#find_squares" (ident)? : command

@[command_elab findSquaresCmd]
def elabFindSquares : CommandElab := fun stx => do
  let ns? := stx[1].getOptional?.map (·.getId)
  liftTermElabM do
    let harvest ← harvestMorphisms (← getEnv) ns?
    let squares ← findCommutativeSquaresFromHarvest harvest (strict := false)
    if squares.isEmpty then
      logInfo "No commutative squares found."
    else
      let mut msg := m!"Found {squares.size} commutative squares:\n"
      for sq in squares do
        msg := msg ++ m!"\nSquare ({sq.verdict}):\n"
        msg := msg ++ m!"  {sq.f.decl} ≫ {sq.h.decl} = {sq.g.decl} ≫ {sq.k.decl}\n"
        msg := msg ++ m!"  ( {sq.f.domHead} ⎯f→ {sq.f.codHead} ⎯h→ {sq.h.codHead} )\n"
      logInfo msg

/--
`#index_morphisms` command: explicit, deduplicated cache-population pass.
This is the controlled elaboration point for populating `morphismCacheExt`.
Safe to call multiple times — deduplication is enforced.
-/
syntax (name := indexMorphismsCmd) "#index_morphisms" (ident)? : command

@[command_elab indexMorphismsCmd]
def elabIndexMorphisms : CommandElab := fun stx => do
  let ns? := stx[1].getOptional?.map (·.getId)
  liftTermElabM do
    let env ← getEnv
    let newEnv ← indexMorphismCache env ns?
    setEnv newEnv
    let state := getMorphismState newEnv
    logInfo m!"Morphism cache: {state.entries.size} entries indexed"

end DAG
