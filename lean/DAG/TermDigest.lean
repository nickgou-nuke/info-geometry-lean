/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Lean
import DAG.Sha256

/-!
# Nameless term digests (`lean-expr-debruijn-v4`)

The L1 ("nameless") layer of the DAG extraction. Each unique subterm of a
kernel `Expr` gets a SHA-256 Merkle digest over a canonical byte encoding:

| constructor | encoded | erased |
|---|---|---|
| `bvar i` | tag, `i` (de Bruijn index) | — |
| `lam` / `forallE` | tag, type digest, body digest | binder name, binder info |
| `letE` | tag, type, value, body digests | binder name, `nonDep` |
| `app` | tag, function digest, argument digest | — |
| `const n us` | tag, `n.toString`, universe levels | — |
| `sort u` | tag, universe level | — |
| `lit` | tag, sub-tag, decimal nat or UTF-8 string | — |
| `proj S i e` | tag, `S.toString`, `i`, body digest | — |
| `mdata _ e` | the digest of `e` (wrapper is transparent) | metadata |
| `fvar` / `mvar`, level `mvar` | tag only; marks the term as open | run-local ids |

Consequences: alpha-equivalent terms have equal digests; digests do not depend
on run-local ids or on Lean's builtin hash; the encoding is reproducible in
Python (`src/igf/graph/decl_schema.py`). Universe levels are encoded
structurally (not normalized). A digest is a search key: equality claims still
require kernel checking (`isDefEq`).

Byte encoding of each node: version byte `0x04`, tag byte, payload. Naturals and
strings are length-prefixed (`u32` big-endian byte length) decimal / UTF-8.
-/

open Lean

namespace DAG.TermDigest

/-- Version label stored next to every digest. -/
def algorithmVersion : String := "lean-expr-debruijn-v4"

/-- Result of digesting one expression. -/
structure TermDigest where
  algorithmVersion : String := DAG.TermDigest.algorithmVersion
  /-- Lowercase hex SHA-256 Merkle root. -/
  digest : String
  /-- Number of unique (mdata-erased) subterm nodes. -/
  nodeCount : Nat
  /-- True if an `fvar`, `mvar` or universe `mvar` occurred (digest then ignores their ids). -/
  openTerm : Bool
deriving ToJson, FromJson, Repr, Inhabited, BEq

private def versionByte : UInt8 := 0x04

private def pushU32 (b : ByteArray) (n : Nat) : ByteArray :=
  let n := n.toUInt32
  ((b.push (n >>> 24).toUInt8).push (n >>> 16).toUInt8).push (n >>> 8).toUInt8 |>.push n.toUInt8

private def pushBytes (b : ByteArray) (x : ByteArray) : ByteArray :=
  pushU32 b x.size ++ x

private def pushStr (b : ByteArray) (s : String) : ByteArray :=
  pushBytes b s.toUTF8

private def pushNat (b : ByteArray) (n : Nat) : ByteArray :=
  pushStr b (toString n)

/-- Structural universe-level encoding; returns the bytes and whether a level mvar occurred. -/
def encodeLevel : Level → ByteArray → ByteArray × Bool
  | .zero, b => (b.push 0, false)
  | .succ l, b => encodeLevel l (b.push 1)
  | .max l₁ l₂, b =>
      let (b, o₁) := encodeLevel l₁ (b.push 2)
      let (b, o₂) := encodeLevel l₂ b
      (b, o₁ || o₂)
  | .imax l₁ l₂, b =>
      let (b, o₁) := encodeLevel l₁ (b.push 3)
      let (b, o₂) := encodeLevel l₂ b
      (b, o₁ || o₂)
  | .param n, b => (pushStr (b.push 4) n.toString, false)
  | .mvar _, b => (b.push 5, true)

/-- Node tags (stable; part of the `v4` encoding). -/
private def tagBVar : UInt8 := 0x01
private def tagFVar : UInt8 := 0x02
private def tagMVar : UInt8 := 0x03
private def tagSort : UInt8 := 0x04
private def tagConst : UInt8 := 0x05
private def tagApp : UInt8 := 0x06
private def tagLam : UInt8 := 0x07
private def tagForall : UInt8 := 0x08
private def tagLet : UInt8 := 0x09
private def tagLit : UInt8 := 0x0A
private def tagProj : UInt8 := 0x0C

/-- Canonical node bytes given already-computed child digests.
If `fvarSlot?` is provided, any `fvar id` mapped to `some slot` is encoded with
`(tagFVar, 0x01, slot)` and does NOT mark the node as an unresolved open variable;
unmapped `fvar`s use `(tagFVar, 0x00)` and mark the node as open.
Returns the bytes and whether this node itself is open. -/
def nodeBytes (e : Expr) (child : Expr → ByteArray)
    (fvarSlot? : FVarId → Option Nat := fun _ => none) : ByteArray × Bool :=
  let b0 := (ByteArray.emptyWithCapacity 80).push versionByte
  match e with
  | .bvar i => (pushNat (b0.push tagBVar) i, false)
  | .fvar id =>
      match fvarSlot? id with
      | some slot => (pushNat ((b0.push tagFVar).push 1) slot, false)
      | none => (b0.push tagFVar, true)
  | .mvar _ => (b0.push tagMVar, true)
  | .sort u => encodeLevel u (b0.push tagSort)
  | .const n us =>
      let b := pushU32 (pushStr (b0.push tagConst) n.toString) us.length
      us.foldl (init := (b, false)) fun (b, o) u =>
        let (b, o') := encodeLevel u b
        (b, o || o')
  | .app f a => ((b0.push tagApp) ++ child f ++ child a, false)
  | .lam _ ty body _ => ((b0.push tagLam) ++ child ty ++ child body, false)
  | .forallE _ ty body _ => ((b0.push tagForall) ++ child ty ++ child body, false)
  | .letE _ ty val body _ => ((b0.push tagLet) ++ child ty ++ child val ++ child body, false)
  | .lit (.natVal n) => (pushNat ((b0.push tagLit).push 0) n, false)
  | .lit (.strVal s) => (pushStr ((b0.push tagLit).push 1) s, false)
  | .proj s i body => (pushNat (pushStr (b0.push tagProj) s.toString) i ++ child body, false)
  | .mdata _ body => (child body, false) -- never hashed: handled by the caller

/-- Digest every unique subterm of `e` (iterative, sharing-aware).
Returns the memo table (`ExprStructEq` ↦ 32-byte digest), the root digest,
the node count and the open flag. -/
def digestTable (e : Expr) (fvarSlot? : FVarId → Option Nat := fun _ => none) :
    Std.HashMap ExprStructEq ByteArray × ByteArray × Nat × Bool := Id.run do
  let mut memo : Std.HashMap ExprStructEq ByteArray := {}
  let mut stack : List (Expr × Bool) := [(e, false)]
  let mut nodes := 0
  let mut isOpen := false
  while !stack.isEmpty do
    let (curr, expanded) := stack.head!
    stack := stack.tail!
    let key : ExprStructEq := ⟨curr⟩
    if memo.contains key then continue
    if !expanded then
      stack := (curr, true) :: stack
      match curr with
      | .app f a => stack := (f, false) :: (a, false) :: stack
      | .lam _ ty body _ => stack := (ty, false) :: (body, false) :: stack
      | .forallE _ ty body _ => stack := (ty, false) :: (body, false) :: stack
      | .letE _ ty val body _ => stack := (ty, false) :: (val, false) :: (body, false) :: stack
      | .mdata _ body => stack := (body, false) :: stack
      | .proj _ _ body => stack := (body, false) :: stack
      | _ => pure ()
      continue
    let child := fun (x : Expr) => memo.getD (⟨x⟩ : ExprStructEq) ByteArray.empty
    match curr with
    | .mdata _ body =>
        memo := memo.insert key (child body)
    | _ =>
        let (bytes, o) := nodeBytes curr child fvarSlot?
        isOpen := isOpen || o
        nodes := nodes + 1
        memo := memo.insert key (DAG.Sha256.digest bytes)
  let root := memo.getD (⟨e⟩ : ExprStructEq) ByteArray.empty
  return (memo, root, nodes, isOpen)

/-- Digest of one expression. -/
def compute (e : Expr) : TermDigest :=
  let (_, root, nodes, isOpen) := digestTable e
  { digest := DAG.Sha256.toHex root, nodeCount := nodes, openTerm := isOpen }

/-- Map each non-implementation-detail `FVarId` in `lctx` to its 0-based de Bruijn
level (declaration slot index `0, 1, ...` in telescope order). -/
def lctxSlotMap (lctx : LocalContext) : Std.HashMap FVarId Nat := Id.run do
  let mut slots : Std.HashMap FVarId Nat := {}
  let mut idx := 0
  for decl in lctx do
    if !decl.isImplementationDetail then
      slots := slots.insert decl.fvarId idx
      idx := idx + 1
  return slots

/-- Context-relative de Bruijn disassembly (`digestWithLctx`):
Each `fvar` bound in `lctx` is replaced by its canonical 0-based de Bruijn level
in `lctx` (without wrapping the whole `LocalContext` telescope around `e`), so
subterms in `InfoTree` get a `_uniq`-counter-free SHA-256 digest while distinguishing
which local hypothesis is referenced. -/
def digestWithLctx (lctx : LocalContext) (e : Expr) : TermDigest :=
  let slots := lctxSlotMap lctx
  let (_, root, nodes, isOpen) := digestTable e (fun id => slots.get? id)
  { digest := DAG.Sha256.toHex root, nodeCount := nodes, openTerm := isOpen }

/-- Close an open expression over a `LocalContext` telescope using `LocalContext.mkForall`
over all non-implementation-detail `FVarId`s in declaration order, then compute its
`TermDigest`. This turns locally-bound `fvar`s into canonical de Bruijn `bvar`s
together with their types/values, making `InfoTree` terms and goals alpha- and
`_uniq`-counter invariant while still distinguishing distinct local hypotheses. -/
def computeInLctx (lctx : LocalContext) (e : Expr) : TermDigest :=
  let fvars : Array Expr := lctx.foldl (init := #[]) fun acc decl =>
    if decl.isImplementationDetail then acc else acc.push (.fvar decl.fvarId)
  compute (lctx.mkForall fvars e)

end DAG.TermDigest
