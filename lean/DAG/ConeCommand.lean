import Lean
import Lean.Data.Json
import Std
import DAG.Basic
import DAG.DeclIndex
import DAG.JsonInstances

/-!
# DAG.ConeCommand

Lean-native declaration dependency cone commands.

Layering:

```text
Lean Environment
  → DAG.DeclDepIndex
  → bounded cone traversal over cached deps/users maps
  → DOT/JSON command output
```

Orientation used by emitted cone edges:

```text
dependency -> user
```

Thus, if theorem `T` uses lemma `L`, the emitted edge is `L -> T`.

These commands inspect the syntactic/kernel dependency graph.  They do not
compute a minimal logical dependency graph and they do not prove any theorem.
-/

open Lean Elab Command

namespace DAG.ConeCommand

abbrev Edge := Name × Name

private partial def backwardEdgesLoop
    (idx : DAG.DeclDepIndex)
    (seen : Std.HashSet Name)
    (todo : List Name)
    (edges : Array Edge) : Array Edge :=
  match todo with
  | [] => edges
  | n :: rest =>
      if seen.contains n then
        backwardEdgesLoop idx seen rest edges
      else
        let seen := seen.insert n
        let deps := idx.directDepsOf n
        let edges := deps.foldl (init := edges) fun es d => es.push (d, n)
        backwardEdgesLoop idx seen (deps.toList ++ rest) edges

/-- Transitive backward dependency edges for root declaration `root`. -/
def backwardEdges (idx : DAG.DeclDepIndex) (root : Name) : Array Edge :=
  backwardEdgesLoop idx {} [root] #[]

private partial def forwardEdgesLoop
    (idx : DAG.DeclDepIndex)
    (seen : Std.HashSet Name)
    (todo : List Name)
    (edges : Array Edge) : Array Edge :=
  match todo with
  | [] => edges
  | n :: rest =>
      if seen.contains n then
        forwardEdgesLoop idx seen rest edges
      else
        let seen := seen.insert n
        let users := idx.directUsersOf n
        let edges := users.foldl (init := edges) fun es u => es.push (n, u)
        forwardEdgesLoop idx seen (users.toList ++ rest) edges

/-- Transitive forward usage edges for root declaration `root` in the current index. -/
def forwardEdges (idx : DAG.DeclDepIndex) (root : Name) : Array Edge :=
  forwardEdgesLoop idx {} [root] #[]

private partial def backwardEdgesBoundedLoop
    (idx : DAG.DeclDepIndex)
    (maxDepth maxEdges : Nat)
    (seen : Std.HashSet Name)
    (todo : List (Name × Nat))
    (edges : Array Edge) : Array Edge :=
  if edges.size >= maxEdges then
    edges
  else
    match todo with
    | [] => edges
    | (n, depth) :: rest =>
        if seen.contains n || depth >= maxDepth then
          backwardEdgesBoundedLoop idx maxDepth maxEdges seen rest edges
        else
          let seen := seen.insert n
          let deps := idx.directDepsOf n
          let room := maxEdges - edges.size
          let depsLimited := deps.extract 0 (min deps.size room)
          let edges := depsLimited.foldl (init := edges) fun es d => es.push (d, n)
          let rest := depsLimited.toList.map (fun d => (d, depth + 1)) ++ rest
          backwardEdgesBoundedLoop idx maxDepth maxEdges seen rest edges

/-- Depth/edge-limited backward dependency edges for root declaration `root`. -/
def backwardEdgesBounded (idx : DAG.DeclDepIndex) (root : Name) (maxDepth maxEdges : Nat) :
    Array Edge :=
  backwardEdgesBoundedLoop idx maxDepth maxEdges {} [(root, 0)] #[]

private partial def forwardEdgesBoundedLoop
    (idx : DAG.DeclDepIndex)
    (maxDepth maxEdges : Nat)
    (seen : Std.HashSet Name)
    (todo : List (Name × Nat))
    (edges : Array Edge) : Array Edge :=
  if edges.size >= maxEdges then
    edges
  else
    match todo with
    | [] => edges
    | (n, depth) :: rest =>
        if seen.contains n || depth >= maxDepth then
          forwardEdgesBoundedLoop idx maxDepth maxEdges seen rest edges
        else
          let seen := seen.insert n
          let room := maxEdges - edges.size
          let users := idx.directUsersOf n
          let usersLimited := users.extract 0 (min users.size room)
          let edges := usersLimited.foldl (init := edges) fun es u => es.push (n, u)
          let rest := usersLimited.toList.map (fun u => (u, depth + 1)) ++ rest
          forwardEdgesBoundedLoop idx maxDepth maxEdges seen rest edges

/-- Depth/edge-limited forward usage edges for root declaration `root`. -/
def forwardEdgesBounded (idx : DAG.DeclDepIndex) (root : Name) (maxDepth maxEdges : Nat) :
    Array Edge :=
  forwardEdgesBoundedLoop idx maxDepth maxEdges {} [(root, 0)] #[]

private def dotName (n : Name) : String :=
  "\"" ++ toString n ++ "\""

private def edgeToDot : Edge → String
  | (a, b) => "  " ++ dotName a ++ " -> " ++ dotName b ++ ";\n"

/-- Render dependency/user edges as a DOT graph. -/
def edgesToDot (graphName : String) (edges : Array Edge) : String :=
  let body := edges.foldl (init := "") fun acc e => acc ++ edgeToDot e
  "digraph " ++ graphName ++ " {\n" ++ body ++ "}\n"

private def edgeToJson (e : Edge) : Json :=
  Json.mkObj
    [ ("source", Json.str (toString e.1))
    , ("target", Json.str (toString e.2)) ]

/-- Render dependency/user edges as a compact JSON object. -/
def edgesToJson (root : Name) (orientation : String) (edges : Array Edge) : Json :=
  Json.mkObj
    [ ("root", Json.str (toString root))
    , ("edge_orientation", Json.str "dependency -> user")
    , ("cone_orientation", Json.str orientation)
    , ("edge_count", Json.num edges.size)
    , ("edges", Json.arr (edges.map edgeToJson)) ]

/-- Render the bidirectional causal diamond around `root` as JSON. -/
def coneToJsonBounded
    (idx : DAG.DeclDepIndex) (root : Name)
    (backwardDepth forwardDepth edgeLimit : Nat) : Json :=
  let back := backwardEdgesBounded idx root backwardDepth edgeLimit
  let fwd := forwardEdgesBounded idx root forwardDepth edgeLimit
  Json.mkObj
    [ ("root", Json.str (toString root))
    , ("edge_orientation", Json.str "dependency -> user")
    , ("bounded", Json.bool true)
    , ("backward_depth", Json.num backwardDepth)
    , ("forward_depth", Json.num forwardDepth)
    , ("edge_limit_per_cone", Json.num edgeLimit)
    , ("backward_cone", edgesToJson root "backward_dependencies" back)
    , ("forward_cone", edgesToJson root "forward_users_in_current_environment" fwd)
    , ("warning",
        Json.str
          "This is the syntactic/kernel declaration graph, not proof closure. Lean remains proof authority.") ]

/-- Render the full bidirectional causal diamond around `root` as JSON. -/
def coneToJson (idx : DAG.DeclDepIndex) (root : Name) : Json :=
  let back := backwardEdges idx root
  let fwd := forwardEdges idx root
  Json.mkObj
    [ ("root", Json.str (toString root))
    , ("edge_orientation", Json.str "dependency -> user")
    , ("bounded", Json.bool false)
    , ("backward_cone", edgesToJson root "backward_dependencies" back)
    , ("forward_cone", edgesToJson root "forward_users_in_current_environment" fwd)
    , ("warning",
        Json.str
          "This is the syntactic/kernel declaration graph, not proof closure. Lean remains proof authority.") ]

/--
Print a bounded backward dependency cone of a declaration as DOT.

For interactive safety this command emits:

```text
backward depth = 4
edge limit     = 500
```
-/
syntax "#deps_dot" ident : command

elab "#deps_dot" id:ident : command => do
  let root ← resolveGlobalConstNoOverload id
  let env ← getEnv
  let idx := DAG.DeclDepIndex.buildBackwardSlice env root 4 500
  logInfo (edgesToDot "lean_backward_deps" (backwardEdgesBounded idx root 4 500))

/--
Print a bounded backward dependency cone of a declaration as JSON.

For interactive safety this command emits:

```text
backward depth = 4
edge limit     = 500
```
-/
syntax "#deps_json" ident : command

elab "#deps_json" id:ident : command => do
  let root ← resolveGlobalConstNoOverload id
  let env ← getEnv
  let idx := DAG.DeclDepIndex.buildBackwardSlice env root 4 500
  let edges := backwardEdgesBounded idx root 4 500
  let json :=
    Json.mkObj
      [ ("root", Json.str (toString root))
      , ("edge_orientation", Json.str "dependency -> user")
      , ("cone_orientation", Json.str "backward_dependencies")
      , ("bounded", Json.bool true)
      , ("backward_depth", Json.num 4)
      , ("edge_limit", Json.num 500)
      , ("edge_count", Json.num edges.size)
      , ("edges", Json.arr (edges.map edgeToJson)) ]
  logInfo (toString json)

/--
Print the bidirectional declaration cone of a declaration as JSON.

The backward cone follows dependencies.  The forward cone uses the cached
reverse-user index from `DeclDepIndex`.

For interactive safety this command emits a bounded diamond:

```text
backward depth = 4
forward depth  = 1
edge limit     = 500 per cone
```
-/
syntax "#cone_json" ident : command

elab "#cone_json" id:ident : command => do
  let root ← resolveGlobalConstNoOverload id
  let env ← getEnv
  let idx := DAG.DeclDepIndex.buildBoundedCone env root 4 1 500
  logInfo (toString (coneToJsonBounded idx root 4 1 500))

end DAG.ConeCommand
