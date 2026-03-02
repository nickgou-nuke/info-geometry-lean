import Std
import DAG.Basic
import DAG.Util

namespace DAG

/-- Component-level path counts on condensed SCC DAG. -/
private def componentPathCounts
  (dag : Array (Array Nat))
  (topo : Array Nat)
  (src : Nat)
  : Array Nat :=
  Id.run do
    let n := dag.size
    let mut counts := arrayReplicate n 0
    counts := counts.set! src 1

    for ti in [:topo.size] do
      let u := topo[ti]!
      let cu := counts[u]!
      if cu != 0 then
        for ei in [:dag[u]!.size] do
          let v := dag[u]![ei]!
          counts := counts.modify v (fun x => x + cu)

    counts


/-- Path counts lifted back to original nodes. -/
def pathCountFrom
  {α} [BEq α] [Hashable α] [Inhabited α]
  (h : HydratedGraph α)
  (src : α)
  : Std.HashMap α Nat :=
  match h.toGraph.nodeToIdx.get? src with
  | none => Std.HashMap.ofList []
  | some u =>
    let srcScc := h.sccOf[u]!
    let compCounts := componentPathCounts h.dag h.topo srcScc

    Id.run do
      let mut out : Std.HashMap α Nat := Std.HashMap.ofList []
      for si in [:h.sccs.size] do
        let comp := h.sccs[si]!
        let c := compCounts[si]!
        for vi in [:comp.size] do
          let v := comp[vi]!
          let name := h.toGraph.nodes[v]!
          out := out.insert name c
      out


/-- Component-level BFS distances. -/
private def componentDistances
  (dag : Array (Array Nat))
  (src : Nat)
  : Array (Option Nat) :=
  Id.run do
    let n := dag.size
    let mut dist := arrayReplicate n none
    dist := dist.set! src (some 0)

    let mut queue : List Nat := [src]

    while true do
      match queue with
      | [] => break
      | u :: rest =>
        queue := rest
        match dist[u]! with
        | none => pure ()
        | some du =>
          for ei in [:dag[u]!.size] do
            let v := dag[u]![ei]!
            if dist[v]! == none then
              dist := dist.set! v (some (du + 1))
              queue := v :: queue

    dist


/-- Distance map lifted to original nodes. -/
def distanceMap
  {α} [BEq α] [Hashable α] [Inhabited α]
  (h : HydratedGraph α)
  (src : α)
  : Std.HashMap α Nat :=
  match h.toGraph.nodeToIdx.get? src with
  | none => Std.HashMap.ofList []
  | some u =>
    let srcScc := h.sccOf[u]!
    let compDist := componentDistances h.dag srcScc

    Id.run do
      let mut out : Std.HashMap α Nat := Std.HashMap.ofList []
      for si in [:h.sccs.size] do
        match compDist[si]! with
        | none => pure ()
        | some d =>
          let comp := h.sccs[si]!
          for vi in [:comp.size] do
            let v := comp[vi]!
            let name := h.toGraph.nodes[v]!
            out := out.insert name d
      out


/-- Influence summary. -/
def influenceFrom
  {α} [BEq α] [Hashable α] [Inhabited α]
  (h : HydratedGraph α)
  (src : α)
  : Nat × Nat :=
  let pc := pathCountFrom h src
  pc.fold
    (init := (0, 0))
    (fun (sumPaths, reachCount) _ n =>
      if n == 0 then
        (sumPaths, reachCount)
      else
        (sumPaths + n, reachCount + 1))


/-- Vulnerability summary (reverse accumulation). -/
def vulnerabilityOf
  {α} [BEq α] [Hashable α] [Inhabited α]
  (h : HydratedGraph α)
  (dst : α)
  : Nat × Nat :=
  match h.toGraph.nodeToIdx.get? dst with
  | none => (0, 0)
  | some u =>
    let dstScc := h.sccOf[u]!

    Id.run do
      let n := h.dag.size
      let mut counts := arrayReplicate n 0
      counts := counts.set! dstScc 1

      for ti in [:h.topo.size] do
        let u := h.topo[h.topo.size - 1 - ti]!
        let cu := counts[u]!
        if cu != 0 then
          for pi in [:h.preds[u]!.size] do
            let p := h.preds[u]![pi]!
            counts := counts.modify p (fun x => x + cu)

      let mut sumPaths := 0
      let mut srcCount := 0

      for si in [:h.sccs.size] do
        let comp := h.sccs[si]!
        let c := counts[si]!
        if c != 0 then
          sumPaths := sumPaths + (c * comp.size)
          srcCount := srcCount + comp.size

      (sumPaths, srcCount)

/--
Extract the 'True Skeleton' of the theory.
Filters out auxiliary lemmas (`_aux`, `match_`, `proof_`, `injEq`),
and ranks remaining nodes by a heuristic of their structural importance
(e.g., in-degree, vulnerability, or simply being a hub).
Returns an array of names sorted by importance.
-/
def extractTheorySkeleton
  (h : HydratedGraph Lean.Name)
  (minVulnerability : Nat := 1) : Array (Lean.Name × Nat × Nat) :=
  Id.run do
    let mut skeleton : Array (Lean.Name × Nat × Nat) := #[]
    for i in [:h.toGraph.nodes.size] do
      let n := h.toGraph.nodes[i]!
      let s := n.toString
      -- Filter out obvious generated/auxiliary declarations
      let isAux :=
        s.contains "._" ||
        s.endsWith "match_" ||
        s.endsWith "proof_" ||
        s.endsWith "injEq" ||
        s.endsWith "brecOn" ||
        s.endsWith "below" ||
        s.endsWith "ibelow" ||
        s.endsWith "sizeOf_spec"

      if !isAux then
        let (vulPaths, vulSrcs) := vulnerabilityOf h n
        -- Heuristic: If it is used by at least `minVulnerability` other concepts, it is part of the skeleton
        if vulSrcs >= minVulnerability then
          skeleton := skeleton.push (n, vulPaths, vulSrcs)

    -- Sort by structural importance (number of sources that depend on it) descending
    return skeleton.qsort (fun a b => a.2.2 > b.2.2)

end DAG
