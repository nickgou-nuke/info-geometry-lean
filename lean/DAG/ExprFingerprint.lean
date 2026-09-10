import Lean
import Std

open Lean

namespace DAG

/-- Spectral fingerprint of a Lean expression.

    Captures structural and de Bruijn binding information for
    alpha-equivalence clustering and incidence graph analysis.
-/
structure ExprFingerprint where
  /-- Version of the content-preserving canonical fingerprint algorithm. -/
  algorithmVersion : String := "lean-expr-canonical-v2"
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
  /-- Hash of the expression's structural shape. -/
  shapeHash      : UInt64
  /-- SHA-256 of the de Bruijn incidence pattern (computed in post-processing). -/
  deBruijnIncidenceHash : String := ""
  /-- Alpha-local hash: structural hash invariant under alpha-renaming. -/
  alphaLocalHash : String := ""
deriving ToJson, FromJson, Repr, Inhabited

/-- Efficiently compute the ExprFingerprint for a given expression.
    Uses an iterative worklist and sharing-aware hashing to avoid timeouts. -/
def computeFingerprint (e : Expr) : ExprFingerprint := Id.run do
  let mut visited : Std.HashSet UInt64 := {}
  let mut stack : List Expr := [e]
  
  let mut h : UInt64 := 0
  let mut hist : Array Nat := #[]
  let mut nc := 0
  let mut ac := 0
  let mut lc := 0
  let mut fc := 0
  let mut cc := 0
  let mut mc := 0
  let mut rc := 0

  while !stack.isEmpty do
    let curr := stack.head!
    stack := stack.tail!
    
    let eh := curr.hash
    if visited.contains eh then continue
    visited := visited.insert eh
    
    nc := nc + 1
    
    match curr with
    | .bvar n =>
        h := mixHash h (hash n)
        if n < hist.size then
          hist := hist.modify n (· + 1)
        else
          let extra := Array.replicate (n - hist.size + 1) 0
          hist := (hist ++ extra).modify n (· + 1)
    | .fvar id =>
        h := mixHash h (hash (1 : Nat))
        h := mixHash h (hash id)
    | .mvar id =>
        h := mixHash h (hash (2 : Nat))
        h := mixHash h (hash id)
        mc := mc + 1
    | .sort level =>
        h := mixHash h (hash (3 : Nat))
        h := mixHash h (hash level)
    | .const name levels =>
        h := mixHash h (hash (4 : Nat))
        h := mixHash h (hash name)
        for level in levels do
          h := mixHash h (hash level)
        cc := cc + 1
    | .app f a =>
        h := mixHash h (hash (5 : Nat))
        ac := ac + 1
        if f.isLambda then rc := rc + 1
        stack := f :: a :: stack
    | .lam _ ty body binderInfo =>
        h := mixHash h (hash (6 : Nat))
        h := mixHash h (hash binderInfo)
        lc := lc + 1
        stack := ty :: body :: stack
    | .forallE _ ty body binderInfo =>
        h := mixHash h (hash (7 : Nat))
        h := mixHash h (hash binderInfo)
        fc := fc + 1
        stack := ty :: body :: stack
    | .letE _ ty val body binderInfo =>
        h := mixHash h (hash (8 : Nat))
        h := mixHash h (hash binderInfo)
        stack := ty :: val :: body :: stack
    | .lit literal =>
        h := mixHash h (hash (9 : Nat))
        h := mixHash h (hash literal)
    | .mdata data body =>
        h := mixHash h (hash (10 : Nat))
        h := mixHash h (hash (toString data))
        stack := body :: stack
    | .proj structureName index body =>
        h := mixHash h (hash (11 : Nat))
        h := mixHash h (hash structureName)
        h := mixHash h (hash index)
        stack := body :: stack

  return {
    algorithmVersion := "lean-expr-canonical-v2"
    shapeHash      := h
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
