import Std
import DAG.Basic
import DAG.Util

namespace DAG

/-- Component-level path counts along an adjacency array in a given traversal order.
    Unified implementation for both forward (dag + topo) and reverse (preds + reverse-topo) directions. -/
def componentPathCountsAlong
  (adj : Array (Array Nat))
  (order : Array Nat)
  (src : Nat)
  : Array Nat :=
  Id.run do
    let n := adj.size
    let mut counts := arrayReplicate n 0
    counts := counts.set! src 1

    for ti in [:order.size] do
      let u := order[ti]!
      let cu := counts[u]!
      if cu != 0 then
        for ei in [:adj[u]!.size] do
          let v := adj[u]![ei]!
          let old := counts[v]!
          counts := counts.set! v (old + cu)

    counts

/-- Component-level path counts on condensed SCC DAG (forward direction). -/
def componentPathCounts
  (dag : Array (Array Nat))
  (topo : Array Nat)
  (src : Nat)
  : Array Nat :=
  componentPathCountsAlong dag topo src

/-- Component-level path counts on the reversed condensed SCC DAG (upward direction). -/
def componentPathCountsUpward
  (preds : Array (Array Nat))
  (orderFromRoots : Array Nat)
  (src : Nat)
  : Array Nat :=
  componentPathCountsAlong preds orderFromRoots src

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

      if srcCount > 0 then
        let size_dst := sccSize[dstScc]!
        srcCount := srcCount - size_dst
        sumPaths := sumPaths - size_dst

      (sumPaths, srcCount)

/-- True dependency roots on the condensed SCC DAG. -/
def rootSet
  {α} [BEq α] [Hashable α]
  (h : HydratedGraph α) : Array Nat :=
  Id.run do
    let mut roots := #[]
    for i in [:h.dag.size] do
      if h.dag[i]!.isEmpty then
        roots := roots.push i
    roots

/-- Capstones in the dependency geometry: SCCs with no reverse dependents. -/
def capstoneSet
  {α} [BEq α] [Hashable α]
  (h : HydratedGraph α) : Array Nat :=
  Id.run do
    let mut out := #[]
    for i in [:h.preds.size] do
      if h.preds[i]!.isEmpty then
        out := out.push i
    out

/-- Minimal depth from the true dependency roots. -/
def depthMinFromRoots
  {α} [BEq α] [Hashable α]
  (h : HydratedGraph α) : Array (Option Nat) :=
  Id.run do
    let n := h.dag.size
    let roots := rootSet h
    let mut depth := arrayReplicate n none
    let mut q : Array Nat := #[]

    for r in roots do
      depth := depth.set! r (some 0)
      q := q.push r

    let mut head : Nat := 0
    while head < q.size do
      let u := q[head]!
      head := head + 1
      let some du := depth[u]! | continue
      for v in h.preds[u]! do
        match depth[v]! with
        | none =>
            depth := depth.set! v (some (du + 1))
            q := q.push v
        | some _ => pure ()

    depth

/-- Maximal depth from the true dependency roots, with one witness predecessor. -/
private def depthMaxCore
  {α} [BEq α] [Hashable α]
  (h : HydratedGraph α) : Array (Option Nat) × Array (Option Nat) :=
  Id.run do
    let n := h.dag.size
    let roots := rootSet h
    let orderFromRoots := h.topo.reverse
    let mut depth := arrayReplicate n none
    let mut pred : Array (Option Nat) := arrayReplicate n none

    for r in roots do
      depth := depth.set! r (some 0)

    for u in orderFromRoots do
      let some du := depth[u]! | continue
      for v in h.preds[u]! do
        let cand := du + 1
        match depth[v]! with
        | none =>
            depth := depth.set! v (some cand)
            pred := pred.set! v (some u)
        | some dv =>
            if cand > dv then
              depth := depth.set! v (some cand)
              pred := pred.set! v (some u)

    (depth, pred)

/-- Maximal depth from the true dependency roots. -/
def depthMaxFromRoots
  {α} [BEq α] [Hashable α]
  (h : HydratedGraph α) : Array (Option Nat) :=
  (depthMaxCore h).1

/-- Topological layers grouped by minimal root depth. -/
def topologicalLayersFromRoots
  {α} [BEq α] [Hashable α]
  (h : HydratedGraph α) : Array (Array Nat) :=
  Id.run do
    let depthMin := depthMinFromRoots h
    let mut maxDepth := 0
    for i in [:depthMin.size] do
      match depthMin[i]! with
      | none => pure ()
      | some d =>
          if d > maxDepth then
            maxDepth := d

    let mut layers : Array (Array Nat) := arrayReplicate (maxDepth + 1) #[]
    for i in [:depthMin.size] do
      match depthMin[i]! with
      | none => pure ()
      | some d =>
          layers := layers.modify d (·.push i)
    layers

/-- Difference between maximal and minimal root depth. -/
def depthSpreadFromRoots
  {α} [BEq α] [Hashable α]
  (h : HydratedGraph α) : Array (Option Nat) :=
  let dMin := depthMinFromRoots h
  let dMax := depthMaxFromRoots h
  Id.run do
    let mut out : Array (Option Nat) := arrayReplicate h.dag.size none
    for i in [:h.dag.size] do
      match dMin[i]!, dMax[i]! with
      | some a, some b =>
          out := out.set! i (some (b - a))
      | _, _ => pure ()
    out

/-- Root contribution path counts for a given component in the upward dependency geometry. -/
def rootContributionCounts
  {α} [BEq α] [Hashable α]
  (h : HydratedGraph α)
  (dstComp : Nat) : Array (Nat × Nat) :=
  Id.run do
    let roots := rootSet h
    let orderFromRoots := h.topo.reverse
    let mut out : Array (Nat × Nat) := #[]
    for r in roots do
      let counts := componentPathCountsUpward h.preds orderFromRoots r
      let c := counts[dstComp]!
      if c != 0 then
        out := out.push (r, c)
    out.qsort (fun a b => a.2 > b.2)

/-- Representative maximal chains from true roots to maximally deep nodes. -/
def deepestRootChains
  {α} [BEq α] [Hashable α]
  (h : HydratedGraph α) : Array (Array Nat) :=
  Id.run do
    let (depth, pred) := depthMaxCore h
    let mut deepest := 0
    for i in [:depth.size] do
      match depth[i]! with
      | none => pure ()
      | some d =>
          if d > deepest then
            deepest := d

    let mut chains : Array (Array Nat) := #[]
    for i in [:depth.size] do
      if depth[i]! == some deepest then
        let mut chain : Array Nat := #[]
        let mut cur : Option Nat := some i
        while cur.isSome do
          let u := cur.get!
          chain := chain.push u
          cur := pred[u]!
        chains := chains.push chain.reverse
    chains

/-- Pick one stable representative name for an SCC when available. -/
def componentRepresentative?
  (h : HydratedGraph Lean.Name)
  (compIdx : Nat) : Option Lean.Name :=
  Id.run do
    let comp := h.sccs[compIdx]!
    for vi in [:comp.size] do
      let v := comp[vi]!
      let n := h.toGraph.nodes[v]!
      if !isGeneratedOrUnstableName n then
        return some n
    if h.sccs[compIdx]!.isEmpty then
      return none
    let v := h.sccs[compIdx]![0]!
    return some h.toGraph.nodes[v]!

/--
Extract the 'True Skeleton' of the theory.
Filters out auxiliary lemmas (`_aux`, `match_`, `proof_`, `injEq`),
and ranks remaining concepts by a heuristic of their structural importance
(e.g., in-degree, vulnerability, or simply being a hub).
Emits one representative node per SCC to avoid mutual-recursion duplication.
Returns an array of names sorted by importance.
-/
private def pickTheoryRepresentative?
  (h : HydratedGraph Lean.Name)
  (comp : Array Nat)
  (preferred? : Option (Std.HashSet Lean.Name)) : Option Lean.Name :=
  Id.run do
    if let some preferred := preferred? then
      for vi in [:comp.size] do
        let v := comp[vi]!
        let n := h.toGraph.nodes[v]!
        if preferred.contains n then
          return some n

    for vi in [:comp.size] do
      let v := comp[vi]!
      let n := h.toGraph.nodes[v]!
      if !isGeneratedOrUnstableName n then
        return some n

    return none

private def extractTheorySkeletonCore
  (h : HydratedGraph Lean.Name)
  (preferred? : Option (Std.HashSet Lean.Name))
  (minVulnerability : Nat := 1) : Array (Lean.Name × Nat × Nat) :=
  Id.run do
    let mut candidates : Array (Lean.Name × Nat) := #[]

    for si in [:h.sccs.size] do
      let comp := h.sccs[si]!
      let rep? := pickTheoryRepresentative? h comp preferred?

      if let some n := rep? then
        let score := h.preds[si]!.size * comp.size
        candidates := candidates.push (n, score)

    let sortedCandidates := candidates.qsort (fun a b => a.2 > b.2)

    let mut skeleton : Array (Lean.Name × Nat × Nat) := #[]
    let mut count := 0
    let topK := 500

    for (n, _) in sortedCandidates do
      if count >= topK then
        break
      let (vulPaths, vulSrcs) := vulnerabilityOf h n
      if vulSrcs >= minVulnerability then
        skeleton := skeleton.push (n, vulPaths, vulSrcs)
        count := count + 1

    return skeleton.qsort (fun a b => a.2.2 > b.2.2)

/--
Extract the 'True Skeleton' of the theory, preferring representatives from a
caller-supplied semantic set and falling back to the legacy non-generated-name
heuristic when no preferred declaration is present in an SCC.
-/
def extractTheorySkeletonWithPreferred
  (h : HydratedGraph Lean.Name)
  (preferred : Std.HashSet Lean.Name)
  (minVulnerability : Nat := 1) : Array (Lean.Name × Nat × Nat) :=
  extractTheorySkeletonCore h (some preferred) minVulnerability

/--
Extract the 'True Skeleton' of the theory using the legacy representative
selection heuristic.
-/
def extractTheorySkeleton
  (h : HydratedGraph Lean.Name)
  (minVulnerability : Nat := 1) : Array (Lean.Name × Nat × Nat) :=
  extractTheorySkeletonCore h none minVulnerability

end DAG
