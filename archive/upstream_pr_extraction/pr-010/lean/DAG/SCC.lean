import DAG.Basic
import DAG.Util

namespace DAG

structure TState where
  next    : Nat
  idx     : Array (Option Nat)
  low     : Array Nat
  stack   : List Nat
  onStack : Array Bool
  comps   : Array (Array Nat)


private partial def dfs (g : Array (Array (Nat × EdgeKind))) (u : Nat) (st : TState) : TState := Id.run do
  let i := st.next
  let mut st := { st with
    next := i + 1,
    idx := st.idx.set! u (some i),
    low := st.low.set! u i,
    stack := u :: st.stack,
    onStack := st.onStack.set! u true }

  for (v, _) in g[u]! do
    match st.idx[v]! with
    | none =>
        st := dfs g v st
        st := { st with low := st.low.set! u (Nat.min st.low[u]! st.low[v]!) }
    | some j =>
        if st.onStack[v]! then
          st := { st with low := st.low.set! u (Nat.min st.low[u]! j) }

  let lowU := st.low[u]!
  let idxU := st.idx[u]!
  let isRoot := match idxU with | some idxVal => lowU == idxVal | none => false
  if isRoot then
    let rec pop (stk : List Nat) (acc : Array Nat) (on : Array Bool) :=
      match stk with
      | [] => ([], acc, on)
      | x :: xs =>
        let on := on.set! x false
        let acc := acc.push x
        if x == u then (xs, acc, on)
        else pop xs acc on
    let (stk, comp, on) := pop st.stack #[] st.onStack
    st := { st with stack := stk, onStack := on, comps := st.comps.push comp }
  st

def tarjan (g : Array (Array (Nat × EdgeKind))) : Array (Array Nat) := Id.run do
  let n := g.size
  let mut st : TState := {
    next := 0,
    idx := arrayReplicate n none,
    low := arrayReplicate n 0,
    stack := [],
    onStack := arrayReplicate n false,
    comps := #[]
  }
  for u in [:n] do
    if st.idx[u]! == none then
      st := dfs g u st
  st.comps

end DAG
