/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Lean
import Std

open Lean

namespace DAG

/-- Spectral fingerprint of a Lean expression.

    Captures structural and de Bruijn binding information for candidate
    clustering and incidence graph analysis. A finite hash is a search key,
    not an identity or equivalence certificate.
-/
structure ExprFingerprint where
  /-- Version of the expression-hash algorithm used for this record. -/
  algorithmVersion : String := "lean-expr-structural-v3"
  /-- Histogram of De Bruijn depths encountered in the expression. -/
  depthHistogram : Array Nat
  /-- Total count of unique sub-expressions (DAG size). -/
  nodeCount      : Nat
  /-- Count of unique applications. -/
  appCount       : Nat
  /-- Count of unique lambda abstractions. -/
  lamCount       : Nat
  /-- Count of unique forall binders. -/
  forallCount    : Nat
  /-- Count of unique constants. -/
  constCount     : Nat
  /-- Count of unique metavariables. -/
  mvarCount      : Nat
  /-- Simple count of unique syntactic redexes. -/
  redexCount     : Nat
  /-- Legacy-named 64-bit structural fingerprint; collisions remain possible. -/
  shapeHash      : UInt64
  /-- Optional de Bruijn incidence digest; not computed by `computeFingerprint`. -/
  deBruijnIncidenceHash : String := ""
  /-- Optional alpha-local digest supplied by a separate postprocessor. -/
  alphaLocalHash : String := ""
deriving ToJson, FromJson, Repr, Inhabited

/- Compute expression statistics and a constructor-aware 64-bit structural hash.

The hash includes constructor tags, ordered child hashes, and relevant
constructor payloads. It does not use Lean's cached `Expr.hash`, which is only 32 effective
bits in the pinned toolchain. `ExprStructEq` ensures that a hash collision does
not merge distinct nodes in the memo table. The result itself is still a
finite hash and is only a search key, never an identity certificate. Metadata
payloads (`Expr.mdata`) are intentionally erased; the constructor and body
remain represented. -/
def computeFingerprint (e : Expr) : ExprFingerprint := Id.run do
  let mut computed : Std.HashMap ExprStructEq UInt64 := {}
  let mut stack : List (Expr × Bool) := [(e, false)]
  let mut hist : Array Nat := #[]
  let mut nc := 0
  let mut ac := 0
  let mut lc := 0
  let mut fc := 0
  let mut cc := 0
  let mut mc := 0
  let mut rc := 0

  while !stack.isEmpty do
    let (curr, expanded) := stack.head!
    stack := stack.tail!

    let key : ExprStructEq := ⟨curr⟩
    if !expanded then
      if computed.contains key then continue
      stack := (curr, true) :: stack
      match curr with
      | .app f a => stack := (f, false) :: (a, false) :: stack
      | .lam _ ty body _ => stack := (ty, false) :: (body, false) :: stack
      | .forallE _ ty body _ => stack := (ty, false) :: (body, false) :: stack
      | .letE _ ty val body _ =>
          stack := (ty, false) :: (val, false) :: (body, false) :: stack
      | .mdata _ body => stack := (body, false) :: stack
      | .proj _ _ body => stack := (body, false) :: stack
      | _ => pure ()
      continue

    if computed.contains key then continue
    nc := nc + 1
    let childHash := fun child : Expr =>
      computed.getD (⟨child⟩ : ExprStructEq) 0
    let mut h := 0
    match curr with
    | .bvar n =>
        h := mixHash (hash (0 : Nat)) (hash n)
        if n < hist.size then
          hist := hist.modify n (· + 1)
        else
          let extra := Array.replicate (n - hist.size + 1) 0
          hist := (hist ++ extra).modify n (· + 1)
    | .fvar id => h := mixHash (hash (1 : Nat)) (hash id)
    | .mvar id =>
        h := mixHash (hash (2 : Nat)) (hash id)
        mc := mc + 1
    | .sort level => h := mixHash (hash (3 : Nat)) (hash level)
    | .const name levels =>
        h := mixHash (hash (4 : Nat)) (hash name)
        h := mixHash h (hash levels)
        cc := cc + 1
    | .app f a =>
        h := mixHash (hash (5 : Nat)) (childHash f)
        h := mixHash h (childHash a)
        ac := ac + 1
        if f.isLambda then rc := rc + 1
    | .lam name ty body binderInfo =>
        h := mixHash (hash (6 : Nat)) (hash name)
        h := mixHash h (hash binderInfo)
        h := mixHash h (childHash ty)
        h := mixHash h (childHash body)
        lc := lc + 1
    | .forallE name ty body binderInfo =>
        h := mixHash (hash (7 : Nat)) (hash name)
        h := mixHash h (hash binderInfo)
        h := mixHash h (childHash ty)
        h := mixHash h (childHash body)
        fc := fc + 1
    | .letE name ty val body binderInfo =>
        h := mixHash (hash (8 : Nat)) (hash name)
        h := mixHash h (hash binderInfo)
        h := mixHash h (childHash ty)
        h := mixHash h (childHash val)
        h := mixHash h (childHash body)
    | .lit literal => h := mixHash (hash (9 : Nat)) (hash literal)
    | .mdata _ body =>
        h := mixHash (hash (10 : Nat)) (childHash body)
    | .proj structureName index body =>
        h := mixHash (hash (11 : Nat)) (hash structureName)
        h := mixHash h (hash index)
        h := mixHash h (childHash body)
    computed := computed.insert key h

  let rootHash := computed.getD (⟨e⟩ : ExprStructEq) 0

  return {
    algorithmVersion := "lean-expr-structural-v3"
    shapeHash      := rootHash
    depthHistogram := hist
    nodeCount      := nc
    appCount       := ac
    lamCount       := lc
    forallCount    := fc
    constCount     := cc
    mvarCount      := mc
    redexCount     := rc
  }

end DAG
