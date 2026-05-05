import Lean
import Std
import DAG.Basic

/-!
# DAG.DeclIndex

One-shot declaration dependency indexing.

`DAG.Basic` owns extraction from Lean declarations.  This file regularizes that
raw extraction into two maps:

* `deps  : declaration -> direct dependencies`
* `users : declaration -> direct users`

Forward cone algorithms should use this reverse index rather than rescanning
the full `Environment` at every expansion step.
-/

open Lean

namespace DAG

private def uniqueSortedNames (xs : Array Name) : Array Name :=
  Id.run do
    let mut seen : Std.HashSet Name := {}
    let mut out : Array Name := #[]
    for x in xs do
      if !seen.contains x then
        seen := seen.insert x
        out := out.push x
    out.qsort Name.lt

private def normalizeNameArrayMap
    (m : Std.HashMap Name (Array Name)) :
    Std.HashMap Name (Array Name) :=
  m.fold
    (init := ({} : Std.HashMap Name (Array Name)))
    (fun acc k vs => acc.insert k (uniqueSortedNames vs))

/-- Cached declaration dependency and reverse-user index. -/
structure DeclDepIndex where
  deps : Std.HashMap Name (Array Name)
  users : Std.HashMap Name (Array Name)

namespace DeclDepIndex

/-- Direct dependencies of a declaration in the cached index. -/
def directDepsOf (idx : DeclDepIndex) (n : Name) : Array Name :=
  idx.deps.getD n #[]

/-- Direct users of a declaration in the cached reverse index. -/
def directUsersOf (idx : DeclDepIndex) (n : Name) : Array Name :=
  idx.users.getD n #[]

/-- Build both dependency directions from the current Lean environment once. -/
def build (env : Environment) : DeclDepIndex :=
  Id.run do
    let mut depsMap : Std.HashMap Name (Array Name) := {}
    let mut usersMap : Std.HashMap Name (Array Name) := {}

    for (n, ci) in env.constants.toList do
      let deps :=
        uniqueSortedNames <|
          (DAG.edgesFromConstantInfo ci).map (fun (dep, _kind) => dep)
            |>.filter (fun dep => dep != n)

      depsMap := depsMap.insert n deps

      for dep in deps do
        let old := usersMap.getD dep #[]
        usersMap := usersMap.insert dep (old.push n)

    { deps := normalizeNameArrayMap depsMap
      users := normalizeNameArrayMap usersMap }

/--
Build only the bounded backward dependency slice from `root`.

This is useful for interactive dependency commands.  It is still an indexed
graph layer, but it avoids indexing unrelated declarations.
-/
def buildBackwardSlice
    (env : Environment) (root : Name) (maxDepth maxEdges : Nat) : DeclDepIndex :=
  Id.run do
    let mut depsMap : Std.HashMap Name (Array Name) := {}
    let mut usersMap : Std.HashMap Name (Array Name) := {}
    let mut seen : Std.HashSet Name := {}
    let mut edgeCount : Nat := 0
    let mut todo : List (Name × Nat) := [(root, 0)]

    while !todo.isEmpty && edgeCount < maxEdges do
      let (n, depth) := todo.head!
      todo := todo.tail!
      if !seen.contains n && depth < maxDepth then
        seen := seen.insert n
        let deps : Array Name :=
          match env.find? n with
          | none => #[]
          | some ci =>
              uniqueSortedNames <|
                (DAG.edgesFromConstantInfo ci).map (fun (dep, _kind) => dep)
                  |>.filter (fun dep => dep != n)
        let room := maxEdges - edgeCount
        let depsLimited := deps.extract 0 (min deps.size room)
        depsMap := depsMap.insert n depsLimited
        edgeCount := edgeCount + depsLimited.size
        for dep in depsLimited do
          let old := usersMap.getD dep #[]
          usersMap := usersMap.insert dep (old.push n)
        todo := depsLimited.toList.map (fun dep => (dep, depth + 1)) ++ todo

    { deps := normalizeNameArrayMap depsMap
      users := normalizeNameArrayMap usersMap }

/--
Build a bounded cone index around `root`.

The backward side is expanded by following dependencies.  The forward side is
expanded by scanning the environment once per frontier layer and adding users
of the current frontier.  This is intended for command-level bounded cones; the
full repo/index export path should use `DeclDepIndex.build`.
-/
def buildBoundedCone
    (env : Environment) (root : Name)
    (backwardDepth forwardDepth maxEdges : Nat) : DeclDepIndex :=
  Id.run do
    let mut idx := buildBackwardSlice env root backwardDepth maxEdges
    let mut seenForward : Std.HashSet Name := {}
    let mut frontier : Array Name := #[root]
    let mut edgeCount : Nat := 0

    for _ in [:forwardDepth] do
      if edgeCount < maxEdges then
        let current := frontier
        frontier := #[]
        let mut wanted : Std.HashSet Name := {}
        for n in current do
          if !seenForward.contains n then
            seenForward := seenForward.insert n
            wanted := wanted.insert n

        for (n, ci) in env.constants.toList do
          if edgeCount < maxEdges then
            let deps : Array Name :=
              uniqueSortedNames <|
                (DAG.edgesFromConstantInfo ci).map (fun (dep, _kind) => dep)
                  |>.filter (fun dep => dep != n)
            let mut hitsCurrent := false
            for dep in deps do
              if edgeCount < maxEdges && wanted.contains dep then
                hitsCurrent := true
                let oldUsers := idx.users.getD dep #[]
                idx := { idx with users := idx.users.insert dep (oldUsers.push n) }
                edgeCount := edgeCount + 1
            if hitsCurrent then
              idx := { idx with deps := idx.deps.insert n deps }
              frontier := frontier.push n

    { deps := normalizeNameArrayMap idx.deps
      users := normalizeNameArrayMap idx.users }

end DeclDepIndex

end DAG
