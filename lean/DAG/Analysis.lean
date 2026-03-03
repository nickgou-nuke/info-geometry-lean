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
          let old := counts[v]!
          counts := counts.set! v (old + cu)

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


/-- Component-level BFS distances (true FIFO). -/
private def componentDistances
  (dag : Array (Array Nat))
  (src : Nat)
  : Array (Option Nat) :=
  Id.run do
    let n := dag.size
    let mut dist := arrayReplicate n none
    dist := dist.set! src (some 0)

    let mut q : Array Nat := #[src]
    let mut head : Nat := 0

    while head < q.size do
      let u := q[head]!
      head := head + 1
      let some du := dist[u]! | continue
      for v in dag[u]! do
        if dist[v]!.isNone then
          dist := dist.set! v (some (du + 1))
          q := q.push v

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
            let old := counts[p]!
            counts := counts.set! p (old + cu)

      let sccSize : Array Nat := h.sccs.map (·.size)
      let mut sumPaths := 0
      let mut srcCount := 0

      for si in [:h.sccs.size] do
        let c := counts[si]!
        if c != 0 then
          let size_si := sccSize[si]!
          sumPaths := sumPaths + (c * size_si)
          srcCount := srcCount + size_si

      -- Subtract the destination itself from the vulnerability totals
      if srcCount > 0 then
        let size_dst := sccSize[dstScc]!
        srcCount := srcCount - size_dst
        sumPaths := sumPaths - size_dst

      (sumPaths, srcCount)



/--
Extract the 'True Skeleton' of the theory.
Filters out auxiliary lemmas (`_aux`, `match_`, `proof_`, `injEq`),
and ranks remaining concepts by a heuristic of their structural importance
(e.g., in-degree, vulnerability, or simply being a hub).
Emits one representative node per SCC to avoid mutual-recursion duplication.
Returns an array of names sorted by importance.
-/
def extractTheorySkeleton
  (h : HydratedGraph Lean.Name)
  (minVulnerability : Nat := 1) : Array (Lean.Name × Nat × Nat) :=
  Id.run do
    let mut candidates : Array (Lean.Name × Nat) := #[]

    for si in [:h.sccs.size] do
      let comp := h.sccs[si]!

      -- Find a representative node in the SCC that is not auxiliary
      let mut rep? : Option Lean.Name := none
      for vi in [:comp.size] do
        let v := comp[vi]!
        let n := h.toGraph.nodes[v]!
        if !isGeneratedOrUnstableName n then
          rep? := some n
          break

      if let some n := rep? then
        -- Fast heuristic: immediate reverse dependencies * SCC size
        let score := h.preds[si]!.size * comp.size
        candidates := candidates.push (n, score)

    -- Sort candidates by the fast heuristic
    let sortedCandidates := candidates.qsort (fun a b => a.2 > b.2)

    let mut skeleton : Array (Lean.Name × Nat × Nat) := #[]
    let mut count := 0
    let topK := 500 -- Only compute exact path counts for the top K

    for (n, _) in sortedCandidates do
      if count >= topK then
        break
      let (vulPaths, vulSrcs) := vulnerabilityOf h n
      if vulSrcs >= minVulnerability then
        skeleton := skeleton.push (n, vulPaths, vulSrcs)
        count := count + 1

    -- Sort the final skeleton by the exact vulnerability sources in descending order
    return skeleton.qsort (fun a b => a.2.2 > b.2.2)

end DAG
