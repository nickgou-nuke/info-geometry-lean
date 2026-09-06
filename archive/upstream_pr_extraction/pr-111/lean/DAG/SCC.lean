import DAG.Basic
import DAG.Util

namespace DAG

structure TState where
  next    : Nat
  idx     : Array (Option Nat)
  low     : Array Nat
  stack   : Array Nat
  onStack : Array Bool
  comps   : Array (Array Nat)

private structure Frame where
  node        : Nat
  nextEdgeIdx : Nat
  parent?     : Option Nat
deriving Inhabited

private def discover (u : Nat) (st : TState) : TState :=
  let i := st.next
  { st with
    next := i + 1,
    idx := st.idx.set! u (some i),
    low := st.low.set! u i,
    stack := st.stack.push u,
    onStack := st.onStack.set! u true }

private def popComponent (u : Nat) (st : TState) : TState := Id.run do
  let mut stack := st.stack
  let mut onStack := st.onStack
  let mut comp : Array Nat := #[]
  while stack.size > 0 do
    let x := stack.back!
    stack := stack.pop
    onStack := onStack.set! x false
    comp := comp.push x
    if x == u then
      return { st with stack := stack, onStack := onStack, comps := st.comps.push comp }
  { st with stack := stack, onStack := onStack, comps := st.comps.push comp }

/--
Iterative Tarjan DFS.
The previous recursive walk could overflow the runtime stack on the full repo
graph once refresh reached SCC hydration.
-/
private def dfsIter (g : Array (Array (Nat × EdgeKind))) (start : Nat) (st0 : TState) : TState := Id.run do
  let mut st := discover start st0
  let mut work : Array Frame := #[{ node := start, nextEdgeIdx := 0, parent? := none }]

  while work.size > 0 do
    let top := work.size - 1
    let frame := work.back!
    let u := frame.node
    let adj := g[u]!

    if frame.nextEdgeIdx < adj.size then
      match adj[frame.nextEdgeIdx]? with
      | some (v, _) =>
          work := work.set! top { frame with nextEdgeIdx := frame.nextEdgeIdx + 1 }
          match st.idx[v]! with
          | none =>
              st := discover v st
              work := work.push { node := v, nextEdgeIdx := 0, parent? := some u }
          | some j =>
              if st.onStack[v]! then
                st := { st with low := st.low.set! u (Nat.min st.low[u]! j) }
      | none =>
          pure ()
    else
      let idxU :=
        match st.idx[u]! with
        | some idxU => idxU
        | none => st.low[u]!
      if st.low[u]! == idxU then
        st := popComponent u st
      work := work.pop
      match frame.parent? with
      | some parent =>
          st := { st with low := st.low.set! parent (Nat.min st.low[parent]! st.low[u]!) }
      | none =>
          pure ()
  st

def tarjan (g : Array (Array (Nat × EdgeKind))) : Array (Array Nat) := Id.run do
  let n := g.size
  let mut st : TState := {
    next := 0,
    idx := arrayReplicate n none,
    low := arrayReplicate n 0,
    stack := #[],
    onStack := arrayReplicate n false,
    comps := #[]
  }
  for u in [:n] do
    if st.idx[u]! == none then
      st := dfsIter g u st
  st.comps

end DAG
