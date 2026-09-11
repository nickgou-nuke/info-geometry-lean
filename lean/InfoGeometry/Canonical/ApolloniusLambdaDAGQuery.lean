import Lean
import InfoGeometry.Algebra.FiniteSpinAlgebra
import DAG.Basic
import DAG.Hydrate
import DAG.Impact
import DAG.Analysis
import InfoGeometry.Canonical.ApolloniusLambdaDAGClosure

/-!
# Native declaration-DAG query for the Apollonius lambda closure

`DAG.buildGraphFromEnv` reads constants occurring in declaration types and
values, i.e. the actual Lean lambda/application dependency surface.  This file
provides a focused query over the new closure namespace and its direct theorem
owners.
-/

open Lean Elab Command

namespace InfoGeometry.Canonical.ApolloniusLambdaDAGQuery

/-- Namespace-local declaration graph for the lambda-DAG closure owner. -/
def closureGraph (env : Environment) : DAG.Graph Name :=
  DAG.buildGraphFromEnv env
    (some "InfoGeometry.Canonical.ApolloniusLambdaDAGClosure")

/-- Hydrated SCC/topological representation of the closure declaration graph. -/
def closureHydratedGraph (env : Environment) : DAG.HydratedGraph Name :=
  DAG.hydrate (closureGraph env)

/-- Actual declaration dependencies reachable from a closure declaration. -/
def declarationDependencies (env : Environment) (n : Name) : Array Name :=
  DAG.impact (closureHydratedGraph env) n

/-- Actual declarations which reverse-depend on a closure declaration. -/
def declarationDependents (env : Environment) (n : Name) : Array Name :=
  DAG.reverseImpact (closureHydratedGraph env) n

/-- Path-count data from one declaration in the namespace-local SCC DAG. -/
def declarationPathCounts (env : Environment) (n : Name) : Std.HashMap Name Nat :=
  DAG.pathCountFrom (closureHydratedGraph env) n

/-- Distance data from one declaration in the namespace-local SCC DAG. -/
def declarationDistances (env : Environment) (n : Name) : Std.HashMap Name Nat :=
  DAG.distanceMap (closureHydratedGraph env) n

/-- Print the actual namespace-local dependency closure of the capstone theorem. -/
elab "#apollonius_lambda_dag" : command => do
  let env ← getEnv
  let h := closureHydratedGraph env
  let root := ``InfoGeometry.Canonical.ApolloniusLambdaDAGClosure.current_topological_closure
  let deps := DAG.impact h root
  let rev := DAG.reverseImpact h root
  let influence := DAG.influenceFrom h root
  logInfo m!"Apollonius lambda DAG nodes: {h.toGraph.nodes.size}"
  logInfo m!"SCCs: {h.sccs.size}; topological components: {h.topo.size}"
  logInfo m!"current_topological_closure dependency impact: {deps.size} declarations"
  logInfo m!"current_topological_closure reverse impact: {rev.size} declarations"
  logInfo m!"path influence (sumPaths, reachCount): {influence}"

/-- Audit that the capstone declaration is visible to the actual Lean DAG. -/
elab "#audit_apollonius_lambda_dag" : command => do
  let env ← getEnv
  let h := closureHydratedGraph env
  let root := ``InfoGeometry.Canonical.ApolloniusLambdaDAGClosure.current_topological_closure
  match h.toGraph.nodeToIdx.get? root with
  | none => throwError "current_topological_closure missing from native declaration DAG"
  | some _ =>
      let deps := DAG.impact h root
      if deps.isEmpty then
        throwError "native declaration DAG returned an empty impact set"
      else
        logInfo m!"Apollonius native declaration DAG audit PASS: {deps.size} reachable declarations."

end InfoGeometry.Canonical.ApolloniusLambdaDAGQuery


