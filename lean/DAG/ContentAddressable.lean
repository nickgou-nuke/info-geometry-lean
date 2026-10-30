/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Lean
import DAG.Basic
import DAG.TermDigest
import InfoGeometry.Meta.Architecture
import Std

open Lean

/-!
# Content-Addressable Declaration DAG

Builds a Lean-native `Graph String` where each node is the SHA-256 Merkle
digest of a declaration's canonical (De Bruijn) expression. Alpha-equivalent
declarations share the same node, giving automatic deduplication without
name-based canonicalization.

Builds on:
- `DAG.TermDigest.compute` for SHA-256 Merkle digests of `Expr`
- `DAG.Basic.edgesFromConstantInfo` for dependency edges
- `DAG.Graph` for the graph structure

The content fingerprint of a declaration is:
  SHA-256( type_digest ++ value_digest )
where `type_digest` and `value_digest` are `TermDigest` Merkle roots over
the De Bruijn-encoded expression. Binder names are erased (only `Expr.bvar`
indices matter), so identical canonical expressions get identical keys.
Keys are fingerprints for indexing: equality of SHA-256 outputs is not used
as a proof that their inputs are equal.

`declarationArtifactKey?` is the stronger peer-artifact fingerprint. It
requires a caller-supplied environment fingerprint and dependency digests;
resolved `Expr.const` references are encoded by those digests rather than
declaration names. It returns `none` if the environment fingerprint is empty
or an expression contains an unresolved dependency. The receiver must still
rebuild and kernel-check the artifact.

-/

namespace DAG.ContentAddressable

open DAG

/-- Content key for a declaration: SHA-256 hex of `(type_digest ++ value_digest)`,
  or just `type_digest` if the declaration has no value (axiom).
  Binder names are erased by `TermDigest`; only De Bruijn structure matters. -/
def declContentKey (ci : ConstantInfo) : String :=
  match ci.value? (allowOpaque := true) with
  | some v =>
      DAG.Sha256.hexDigestString ((TermDigest.compute ci.type).digest ++ (TermDigest.compute v).digest)
  | none =>
      (TermDigest.compute ci.type).digest

/-- Unambiguous framed payload for a contextual declaration fingerprint.
Expression digests are fixed-width SHA-256 hex strings. The environment field
is length-prefixed in UTF-8 bytes, and the value tag distinguishes axioms from
declarations carrying a value. -/
private def artifactPayload (environmentFingerprint typeDigest : String)
    (valueDigest? : Option String) : String :=
  s!"{environmentFingerprint.toUTF8.size}:{environmentFingerprint}T{typeDigest}" ++
    match valueDigest? with
    | none => "N"
    | some valueDigest => "V" ++ valueDigest

/-- Build a peer-artifact fingerprint from a declaration's elaborated type
and value, the environment fingerprint, and content digests for referenced
declarations. All referenced constants must resolve through `dependencyDigest?`.

This key is a content fingerprint requiring independent kernel certification: hash equality is
not used as expression equality, and a receiving peer must kernel-check the
reconstructed declaration in its declared environment. -/
def declarationArtifactKey? (environmentFingerprint : String)
    (dependencyDigest? : Name → Option String) (ci : ConstantInfo) : Option String :=
  if environmentFingerprint == "" then none else
  let typeDigest := TermDigest.computeWithConstDigests ci.type dependencyDigest?
  if typeDigest.openTerm then none else
  match ci.value? (allowOpaque := true) with
  | none =>
      some (DAG.Sha256.hexDigestString
        (artifactPayload environmentFingerprint typeDigest.digest none))
  | some value =>
      let valueDigest := TermDigest.computeWithConstDigests value dependencyDigest?
      if valueDigest.openTerm then none else
        some (DAG.Sha256.hexDigestString
          (artifactPayload environmentFingerprint typeDigest.digest
            (some valueDigest.digest)))

/-- Resolve a declaration and its transitive constant dependencies to contextual
artifact keys. The result is sorted by declaration name before keys are
computed, so the array order is deterministic for a fixed environment and
resolver. It returns `none` if the root, any transitive dependency, the
environment fingerprint, or any referenced dependency digest is unresolved.

This is the fetch-closure companion to `declarationArtifactKey?`: the graph
records direct edges, while this function gives a peer the complete set of
content keys it must request before rebuilding and kernel-checking the root.
The caller-supplied dependency resolver must use the agreed artifact digests
for referenced declarations. -/
def declarationArtifactClosure? (environmentFingerprint : String)
    (dependencyDigest? : Name → Option String) (env : Environment)
    (declName : Name) : Option (Array String) := Id.run do
  let some _ := env.find? declName | return none
  let mut names := #[declName]
  for dep in InfoGeometry.Meta.transitivelyUsedConstants env declName do
    if !names.contains dep then
      names := names.push dep
  names := names.qsort Name.lt
  let mut keys := #[]
  for name in names do
    let some ci := env.find? name | return none
    let some key := declarationArtifactKey? environmentFingerprint dependencyDigest? ci
      | return none
    if !keys.contains key then
      keys := keys.push key
  return some keys

/-- Build a content-addressed graph from an environment.
  Nodes are unique content keys; declarations with equal keys share a node.
  Edges are type/value dependencies keyed by content key.
  Declarations whose dependencies are not in the filtered set get dangling
  edges silently dropped (same rule as `DAG.Basic.buildGraphFromEnv`). -/
def buildContentGraph (env : Environment) (nsPrefix? : Option String := none) : Graph String :=
  Id.run do
    let consts := env.constants
    let allNames : Array Name :=
      match nsPrefix? with
      | none => consts.fold (init := #[]) (fun acc n _ => acc.push n)
      | some p => consts.fold (init := #[]) (fun acc n _ =>
          if (toString n).startsWith p then acc.push n else acc)
    let constList : Array Name := allNames.qsort Name.lt
    let mut nodes : Array String := #[]
    let mut keyToIdx : Std.HashMap String Nat := {}
    for i in [:constList.size] do
      let name := constList[i]!
      match env.find? name with
      | none => pure ()
      | some ci =>
          let key := declContentKey ci
          if !keyToIdx.contains key then
            keyToIdx := keyToIdx.insert key nodes.size
            nodes := nodes.push key
    let mut forward : Array (Array (Nat × EdgeKind)) := Array.replicate nodes.size #[]
    let mut processedKeys : Std.HashSet String := {}
    for i in [:constList.size] do
      let name := constList[i]!
      match env.find? name with
      | none => pure ()
      | some ci =>
          let sourceKey := declContentKey ci
          if processedKeys.contains sourceKey then continue
          processedKeys := processedKeys.insert sourceKey
          let some sourceIdx := keyToIdx.get? sourceKey | continue
          let edges := edgesFromConstantInfo ci
          for (dep, k) in edges do
            match env.find? dep with
            | none => pure ()
            | some dci =>
                let depKey := declContentKey dci
                match keyToIdx.get? depKey with
                | none => pure ()
                | some j =>
                    forward := forward.modify sourceIdx (fun arr => arr.push (j, k))
    { nodes := nodes,
      nodeToIdx := keyToIdx,
      forward := forward }

/-- Determinism: declarations with identical type and value expressions
  get the same content key. This is the foundation of content-addressing:
  the key is a pure function of the De Bruijn expression structure. -/
theorem sameExpr_sameKey {ci₁ ci₂ : ConstantInfo}
    (hType : ci₁.type = ci₂.type)
    (hValue : ci₁.value? (allowOpaque := true) = ci₂.value? (allowOpaque := true)) :
    declContentKey ci₁ = declContentKey ci₂ := by
  have hTypeDigest : (TermDigest.compute ci₁.type).digest =
      (TermDigest.compute ci₂.type).digest := by rw [hType]
  cases h₁ : ci₁.value? (allowOpaque := true) with
  | none =>
    cases h₂ : ci₂.value? (allowOpaque := true) with
    | none =>
      simpa [declContentKey, h₁, h₂] using hTypeDigest
    | some v₂ =>
      simp [h₁, h₂] at hValue ⊢
      <;> exfalso
      <;> simp_all [hValue]
  | some v₁ =>
    cases h₂ : ci₂.value? (allowOpaque := true) with
    | none =>
      simp [h₁, h₂] at hValue ⊢
      <;> exfalso
      <;> simp_all [hValue]
    | some v₂ =>
      have hValue' : v₁ = v₂ := by simpa [h₁, h₂] using hValue
      simp [declContentKey, h₁, h₂, hTypeDigest, hValue']

/-- For declarations without values, the content key is exactly the type
digest, so key equality does imply equality of type digests in this case. -/
theorem sameAxiomKey_sameTypeDigest {ci₁ ci₂ : ConstantInfo}
    (h₁ : ci₁.value? (allowOpaque := true) = none)
    (h₂ : ci₂.value? (allowOpaque := true) = none)
    (hKey : declContentKey ci₁ = declContentKey ci₂) :
    (TermDigest.compute ci₁.type).digest = (TermDigest.compute ci₂.type).digest := by
  simpa [declContentKey, h₁, h₂] using hKey

/-- Equal expression trees have equal digests. This congruence statement alone
does not establish invariance under arbitrary alpha-renaming. -/
theorem digest_eq_of_expr_eq (e : Expr) (e' : Expr) (h : e = e') :
    (TermDigest.compute e).digest = (TermDigest.compute e').digest := by
  rw [h]

end DAG.ContentAddressable
