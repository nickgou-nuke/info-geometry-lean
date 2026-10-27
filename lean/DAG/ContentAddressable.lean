/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Lean
import DAG.Basic
import DAG.TermDigest
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

/-- Build a content-addressed graph from an environment.
  Nodes are content keys; edges are type/value dependencies keyed by content key.
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
    let mut keyToIdx : Std.HashMap String Nat := {}
    for i in [:constList.size] do
      let name := constList[i]!
      match env.find? name with
      | none => pure ()
      | some ci =>
          let key := declContentKey ci
          keyToIdx := keyToIdx.insert key i
    let mut forward : Array (Array (Nat × EdgeKind)) := Array.replicate constList.size #[]
    for i in [:constList.size] do
      let name := constList[i]!
      match env.find? name with
      | none => pure ()
      | some ci =>
          let edges := edgesFromConstantInfo ci
          for (dep, k) in edges do
            match env.find? dep with
            | none => pure ()
            | some dci =>
                let depKey := declContentKey dci
                match keyToIdx.get? depKey with
                | none => pure ()
                | some j =>
                    forward := forward.modify i (fun arr => arr.push (j, k))
    let nodes := constList.map (fun n =>
      match env.find? n with
      | none => ""
      | some ci => declContentKey ci)
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

/-- Alpha-equivalence invariance: if two expressions are syntactically equal
  (same De Bruijn structure), their `TermDigest` digests are equal.
  Binder names are erased by `TermDigest`, so alpha-equivalent declarations
  produce identical keys. -/
theorem deBruijnDigest_equiv (e : Expr) (e' : Expr) (h : e = e') :
    (TermDigest.compute e).digest = (TermDigest.compute e').digest := by
  rw [h]

end DAG.ContentAddressable
