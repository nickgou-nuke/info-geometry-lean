  import Lean

open Lean

namespace Graph



/-- simple helper to create an array filled with `x` repeated `n` times. -/
def arrayReplicate {α} (n : Nat) (x : α) : Array α :=
  Id.run do
    let mut a : Array α := #[]
    for _ in [:n] do
      a := a.push x
    a


/-- A very small graph representation used for export and analysis.

Each node is a declaration name, and edges represent direct dependencies
extracted from the type or value of the declaration.  The graph is intentionally
minimal; higher‑level utilities can wrap it in a richer structure as needed.

**IMPORTANT:** the namespace is `InfoGeometry.Analysis.Graph`.  *nothing* in
this namespace may be called `Graph` or Lean will collapse the namespace, and
all subsequent declarations will be hoisted into `InfoGeometry.Analysis`.
To avoid that we call the structure `SimpleGraph`.
-/
structure SimpleGraph where
  nodes : List Name
  edges : List (Name × Name)  -- from → to

/-- richer edge classification. -/
inductive EdgeKind
  | type
  | value
  deriving Repr, DecidableEq, BEq, Hashable

/-- adjacency representation with index mapping, similar to DAG.Basic. -/
structure IndexedGraph where
  nodes     : Array Name
  nodeToIdx : Std.HashMap Name Nat
  forward   : Array (Array (Nat × EdgeKind))

/-- collect constant names appearing in an expression (including projection heads)
    this mirrors `DAG.KernelExtract.consts`. -/
def collectConsts (e : Expr) : NameSet :=
  let fromConsts :=
    e.foldConsts (init := NameSet.empty) (fun n acc => acc.insert n)
  let rec proj (e : Expr) (acc : NameSet) : NameSet :=
    match e with
    | .proj s _ body => proj body (acc.insert s)
    | .app f a       => proj f (proj a acc)
    | .lam _ ty body _ => proj ty (proj body acc)
    | .forallE _ ty body _ => proj ty (proj body acc)
    | .letE _ ty val body _ => proj ty (proj val (proj body acc))
    | .mdata _ body  => proj body acc
    | _              => acc
  fromConsts.union (proj e NameSet.empty)

/-- extract a list of unique constant names from an expression. -/
def collectDeps (e : Expr) : List Name :=
  (collectConsts e).toList

/-- Build an indexed graph from an environment.  Nodes are all constants in
    `env`; edges are typed/value dependencies between them.  External names
    (not present in `env`) are ignored.  This is essentially the same logic
    found in `DAG.KernelExtract.buildGraphFromEnv`. -/
def envToIndexedGraph (env : Environment) (nsPrefix? : Option String := none) : IndexedGraph :=
  Id.run do
    -- collect all constant names and sort them to ensure deterministic
    -- ordering.  the `Environment.constants` hashmap does not guarantee
    -- any particular iteration order, so we sort by `Name`'s `Ord`.
    let consts := env.constants
    let allNames : Array Name := 
      match nsPrefix? with
      | none => consts.fold (init := #[]) (fun acc n _ => acc.push n)
      | some p => consts.fold (init := #[]) (fun acc n _ => 
          if (toString n).startsWith p then acc.push n else acc)
    
    let constList : Array Name := allNames.qsort Name.lt

    let mut nodeToIdx : Std.HashMap Name Nat := {}
    for i in [:constList.size] do
      nodeToIdx := nodeToIdx.insert constList[i]! i
    let mut forward : Array (Array (Nat × EdgeKind)) :=
      arrayReplicate constList.size #[]
    for i in [:constList.size] do
      let name := constList[i]!
      match env.find? name with
      | none => pure ()
      | some ci =>
          let typeDeps :=
            (collectConsts ci.type).toList.toArray.map (fun d => (d, EdgeKind.type))
          let valDeps :=
            match ci.value? with
            | some v => (collectConsts v).toList.toArray.map (fun d => (d, EdgeKind.value))
            | none   => #[]
          for (dep, k) in (typeDeps ++ valDeps) do
            match nodeToIdx.get? dep with
            | none => pure ()
            | some j =>
                forward := forward.modify i (fun arr => arr.push (j, k))
    { nodes := constList, nodeToIdx := nodeToIdx, forward := forward }

/-- convert an `IndexedGraph` back to the simple `Graph`. -/
def indexedToGraph (g : IndexedGraph) : SimpleGraph :=
  let edges := Id.run do
    let mut out : List (Name × Name) := []
    for i in [:g.forward.size] do
      for (j, _) in g.forward[i]! do
        out := (g.nodes[i]!, g.nodes[j]!) :: out
    out.reverse
  { nodes := g.nodes.toList, edges := edges }

/-- old flat graph from environment -/
def envToGraph (env : Environment) (nsPrefix? : Option String := none) : SimpleGraph :=
  indexedToGraph (envToIndexedGraph env nsPrefix?)

end Graph

-- bring the useful names out of the subnamespace into the parent so that
-- `import InfoGeometry.Analysis.Graph` gives you everything directly.
namespace InfoGeometry.Analysis

open InfoGeometry.Analysis.Graph

/-- compatibility alias for the old name.  placed in the parent namespace so it
    does *not* collapse `InfoGeometry.Analysis.Graph`. -/
abbrev Graph := SimpleGraph

export InfoGeometry.Analysis.Graph
  (SimpleGraph EdgeKind IndexedGraph arrayReplicate collectConsts collectDeps envToIndexedGraph
   indexedToGraph envToGraph)

end InfoGeometry.Analysis

  -- when the module path and namespace coincide we don't need additional aliases
  -- inside `InfoGeometry.Analysis.Graph` – the declarations above already live
  -- in that namespace automatically (because the file lives there).  no further
  -- abbreviation is necessary.
