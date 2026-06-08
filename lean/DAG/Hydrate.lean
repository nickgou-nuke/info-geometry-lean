import DAG.Basic
import DAG.SCC
import DAG.Topo
import DAG.Dominators

namespace DAG

def hydrate {α} [BEq α] [Hashable α] (g : Graph α) : HydratedGraph α := Id.run do
  let sccs := tarjan g.forward
  let k := sccs.size

  let mut sccOf := arrayReplicate g.nodes.size 0
  for i in [:k] do
    for v in sccs[i]! do
      sccOf := sccOf.set! v i

  let mut dag := arrayReplicate k #[]
  let mut preds := arrayReplicate k #[]
  let mut seen : Std.HashSet (Nat × Nat) := {}

  for i in [:k] do
    for u in sccs[i]! do
      for (v, _) in g.forward[u]! do
        let j := sccOf[v]!
        if i != j && !seen.contains (i,j) then
          dag := dag.modify i (·.push j)
          preds := preds.modify j (·.push i)
          seen := seen.insert (i,j)

  let order := topo dag preds
  let doms := Dominators.dominators preds order

  {
    toGraph := g,
    sccs := sccs,
    sccOf := sccOf,
    dag := dag,
    preds := preds,
    topo := order,
    doms := doms
  }

end DAG
