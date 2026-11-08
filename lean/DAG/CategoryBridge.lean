import Lean
import DAG.Basic
import DAG.ExactMorphism
import Mathlib.CategoryTheory.Category.Basic

/-!
# Category-Theory Bridge

Maps the declaration dependency graph into Mathlib's `CategoryTheory` framework
as a coarse **type-head–indexed quiver**.

## Architecture

Objects in the quiver are **type-head names** (e.g., `Ring`, `TopologicalSpace`),
not individual declaration names. Morphisms are `MorphismEntry` records whose
`domHead`/`codHead` match the source/target objects.

This is an ambient quiver over all morphism metadata — it is not yet a
quiver induced by a particular namespace harvest.

## Compositional Witness Search

Given a partial morphism map from a source namespace to a target namespace,
the bridge verifies:
- mapped identity obligations are checked exactly,
- mapped composable pairs are checked for existence of a compatible target witness,
- unmapped source data is skipped.
- **Object compatibility**: mapped morphisms land on the correct mapped objects.

## Soundness Scope

Sound for validated unary top-level morphism declarations only.
The `Quiver` instance is vocabulary — it does not produce a `Category` instance,
a `Functor`, or a verified composition table.
-/

open Lean Meta
open CategoryTheory

namespace DAG

/-! ### Type-head quiver -/

/--
Objects in the type-head quiver. Each object is a coarse type-head name
(e.g., `Ring`, `TopologicalSpace`), obtained from `headNameOf` during
morphism extraction.

This is explicitly NOT a declaration-level object. Multiple declarations
can share the same type head.
-/
structure HeadObj where
  head : Name
  deriving BEq, Hashable, DecidableEq, Repr

/--
The ambient type-head quiver.

Morphisms from `A` to `B` are all `MorphismEntry` records whose
`domHead` matches `A.head` and `codHead` matches `B.head`.

This instance does not depend on a particular harvested set —
it is the global quiver of all morphism metadata.
-/
instance : Quiver HeadObj where
  Hom A B := { m : MorphismEntry // m.domHead = A.head ∧ m.codHead = B.head }

/-! ### Composition and identity verification -/


/--
Cheaply check head-name compatibility before attempting `MetaM` verification.
Returns `false` if the heads obviously don't compose.
-/
def compositionHeadsCompatible (f g gf : MorphismEntry) : Bool :=
  f.codHead == g.domHead &&
  gf.domHead == f.domHead &&
  gf.codHead == g.codHead

/--
Verify that a candidate composite `gf : A → C` equals `g ∘ f`
where `f : A → B` and `g : B → C`.

Pre-checks head compatibility before entering `MetaM`.
Uses `withUnaryMorphismSignature` and `mkAppM` for sound application.
-/
def isCompositionExact (f g gf : MorphismEntry) : MetaM Bool := do
  -- Cheap head-mismatch rejection
  if !compositionHeadsCompatible f g gf then return false
  try
    let env ← getEnv
    let some ci := env.find? f.decl | return false
    let some result ← withUnaryMorphismSignature ci.type (fun fDom _ => do
      withNewMCtxDepth do
        let domExpr ← whnf fDom
        withLocalDeclD `x domExpr fun x => do
          let fx  ← mkUnaryMorphismApp f.decl x
          let gfx ← mkUnaryMorphismApp g.decl fx
          let comp_x ← mkUnaryMorphismApp gf.decl x
          isDefEq gfx comp_x) | return false
    return result
  catch _ => pure false

/--
Check whether a morphism is a definitional identity: `f(x) = x` for all `x`.
-/
def isDefinitionalIdentity (m : MorphismEntry) : MetaM Bool := do
  -- An identity must be an endomorphism
  if m.domHead != m.codHead then return false
  try
    let env ← getEnv
    let some ci := env.find? m.decl | return false
    let some result ← withUnaryMorphismSignature ci.type (fun dom _ => do
      withNewMCtxDepth do
        let domExpr ← whnf dom
        withLocalDeclD `x domExpr fun x => do
          let fx ← mkUnaryMorphismApp m.decl x
          isDefEq fx x) | return false
    return result
  catch _ => pure false

/-! ### Partial morphism map -/

/--
A partial map describing a candidate functor between two namespaces.

Uses `Std.HashMap` so unmapped objects/morphisms are distinguishable from
mapped ones (unlike a total `Name → Name` which always returns a value).
-/
structure MorphismMap where
  /-- Maps source type-head names to target type-head names. -/
  objMap : Std.HashMap Name Name
  /-- Maps source morphism declaration names to target declaration names. -/
  mapMap : Std.HashMap Name Name

/-! ### Functoriality verification -/

/-- Result of an identity preservation check. -/
structure IdentityCheck where
  srcDecl : Name
  srcHead : Name    -- the type head (should be self-loop)
  mappedHead : Option Name  -- F(A) if objMap has it
  tgtDecl : Name
  tgtIsIdentity : Bool
  objectCompatible : Bool
  deriving Inhabited

/--
Result of a composition preservation check.
`witnessFound = true` means at least one target composite was found that
matches the expected image of composition. This is a **witness log**
(one entry per composable source pair), not a minimal composition table.
-/
structure CompositionCheck where
  srcF : Name
  srcG : Name
  witness : Option Name  -- ∃ a target composite that matches (stores the name if found)
  deriving Inhabited

/-- Result of a compositional witness search across a partial map. -/
structure CompositionalBridgeVerdict where
  identityChecks    : Array IdentityCheck
  /-- Witness log: one entry per composable source pair in `mapMap`. -/
  compositionChecks : Array CompositionCheck
  /-- 
  True only if every identity and composition obligation is satisfied.
  `allOk` means that every mapped identity obligation and every mapped composable-pair
  obligation passed. Unmapped source data is skipped, not counted as failure.
  -/
  allOk : Bool

/--
Verify that a `MorphismMap` preserves identities exactly, and that for every
composable pair in the source, there exists a compatible composite witness in the target.

This is a weaker check than full `map_comp` functoriality because it does not
relate the target witness back to the actual mapped source composite.
It ensures that the target vocabulary contains enough morphisms
to support the source's compositional structure.
-/
def verifyCompositionalWitness
    (sourceMorphs targetMorphs : Array MorphismEntry)
    (mMap : MorphismMap) : MetaM CompositionalBridgeVerdict := do
  let mut idChecks := #[]
  let mut compChecks := #[]
  let mut allOk := true

  -- Precompute target map for O(1) lookups
  let mut targetMap : Std.HashMap Name MorphismEntry := {}
  for m in targetMorphs do
    targetMap := targetMap.insert m.decl m

  -- === Identity preservation ===
  for src in sourceMorphs do
    -- Only check actual definitional identities, not arbitrary endomorphisms
    if src.domHead != src.codHead then continue
    let isId ← isDefinitionalIdentity src
    if !isId then continue

    -- This is a genuine source identity on type head `src.domHead`
    let some tgtName := mMap.mapMap.get? src.decl | continue
    let some tgt := targetMap.get? tgtName | continue

    -- Check object compatibility: tgt should be an endomorphism on F(A)
    let mappedHead := mMap.objMap.get? src.domHead
    let objCompat := match mappedHead with
      | some fA => tgt.domHead == fA && tgt.codHead == fA
      | none => true  -- no object mapping specified, skip compatibility check

    -- Check that tgt is actually an identity
    let tgtIsId ← isDefinitionalIdentity tgt

    idChecks := idChecks.push {
      srcDecl := src.decl, srcHead := src.domHead,
      mappedHead, tgtDecl := tgtName,
      tgtIsIdentity := tgtIsId, objectCompatible := objCompat
    }
    if !tgtIsId || !objCompat then allOk := false

  -- === Composition preservation (existential) ===
  for f in sourceMorphs do
    for g in sourceMorphs do
      if f.codHead != g.domHead then continue
      -- f : A → B, g : B → C
      let some liftFName := mMap.mapMap.get? f.decl | continue
      let some liftGName := mMap.mapMap.get? g.decl | continue
      let some mF := targetMap.get? liftFName | continue
      let some mG := targetMap.get? liftGName | continue

      -- Object compatibility checks on mapped morphisms
      let fA := mMap.objMap.get? f.domHead
      let fB := mMap.objMap.get? f.codHead
      let fC := mMap.objMap.get? g.codHead

      let fObjOk := match fA with | some a => mF.domHead == a | none => true
      let fCodOk := match fB with | some b => mF.codHead == b | none => true
      let gDomOk := match fB with | some b => mG.domHead == b | none => true
      let gCodOk := match fC with | some c => mG.codHead == c | none => true

      if !fObjOk || !fCodOk || !gDomOk || !gCodOk then
        compChecks := compChecks.push { srcF := f.decl, srcG := g.decl, witness := none }
        allOk := false
        continue

      -- Search for an existential witness: ∃ h in target, h = mG ∘ mF
      let composites := targetMorphs.filter fun m =>
        m.domHead == mF.domHead && m.codHead == mG.codHead
      let mut foundWitness : Option Name := none
      for comp in composites do
        if ← isCompositionExact mF mG comp then
          foundWitness := some comp.decl
          break
      compChecks := compChecks.push { srcF := f.decl, srcG := g.decl, witness := foundWitness }
      if foundWitness.isNone then allOk := false

  return { identityChecks := idChecks, compositionChecks := compChecks, allOk }

/-- Print compositional witness search results. -/
def printCompositionalBridgeVerdict (v : CompositionalBridgeVerdict) : IO Unit := do
  IO.println "━━━ Compositional Witness Search (Unary Fragment) ━━━"
  IO.println s!"  Identity checks: {v.identityChecks.size}"
  for c in v.identityChecks do
    let objStr := match c.mappedHead with
      | some h => s!"F({c.srcHead}) = {h}"
      | none => s!"F({c.srcHead}) = ?"
    IO.println s!"    {c.srcDecl} → {c.tgtDecl}: id={c.tgtIsIdentity} obj={c.objectCompatible} ({objStr})"
  IO.println s!"  Composition checks: {v.compositionChecks.size}"
  for c in v.compositionChecks do
    let witStr := match c.witness with
      | some w => s!"yes ({w})"
      | none => "no"
    IO.println s!"    {c.srcF} ≫ {c.srcG}: witness={witStr}"
  IO.println s!"  All verified: {v.allOk}"

end DAG
