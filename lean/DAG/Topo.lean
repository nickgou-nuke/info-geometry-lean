namespace DAG

def topo (dag preds : Array (Array Nat)) : Array Nat := Id.run do
  let mut indeg := preds.map (·.size)
  let mut q : List Nat := []
  for i in [:dag.size] do
    if indeg[i]! == 0 then q := i :: q

  let mut out := #[]
  while true do
    match q with
    | [] => break
    | u :: r =>
        q := r
        out := out.push u
        for v in dag[u]! do
          let d := indeg[v]! - 1
          indeg := indeg.set! v d
          if d == 0 then
            q := v :: q
  out

end DAG
