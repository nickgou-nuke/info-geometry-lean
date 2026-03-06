import Lean
import DAG.Betti

open Lean
open DAG

-- Test on Nat.add
#eval show MetaM Unit from do
  let env ← getEnv
  if let some ci := env.find? ``Nat.add then
    if let some val := ci.value? then
      IO.println "Analyzing Nat.add..."
      DAG.computeExprHomology val
