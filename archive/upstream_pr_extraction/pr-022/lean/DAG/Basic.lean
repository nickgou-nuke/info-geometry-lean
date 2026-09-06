import Lean
import Std

namespace DAG

inductive EdgeKind | type | value
  deriving Repr, DecidableEq, BEq, Hashable

structure Graph (α) [BEq α] [Hashable α] where
  nodes     : Array α
  nodeToIdx : Std.HashMap α Nat
  forward   : Array (Array (Nat × EdgeKind))

structure HydratedGraph (α) [BEq α] [Hashable α]
  extends Graph α where
  sccs  : Array (Array Nat)
  sccOf : Array Nat
  dag   : Array (Array Nat)
  preds : Array (Array Nat)
  topo  : Array Nat
  doms  : Array ByteArray

instance [Repr α] [BEq α] [Hashable α] :
  Repr (HydratedGraph α) where
  reprPrec h _ :=
    s!"HydratedGraph ⟨nodes := {repr h.toGraph.nodes}, sccs := {repr h.sccs}, topo := {repr h.topo}⟩"

/-- Collect projection head names in an expression. -/
partial def projHeads (e : Lean.Expr) : Lean.NameSet :=
  let rec go (todo : List Lean.Expr) (seen : Std.HashSet Lean.Expr) (out : Lean.NameSet) :=
    match todo with
    | [] => out
    | x :: xs =>
      if seen.contains x then
        go xs seen out
      else
        let seen := seen.insert x
        match x with
        | .proj s _ body =>
            go (body :: xs) seen (out.insert s)
        | .app f a =>
            go (f :: a :: xs) seen out
        | .lam _ ty body _ =>
            go (ty :: body :: xs) seen out
        | .forallE _ ty body _ =>
            go (ty :: body :: xs) seen out
        | .letE _ ty val body _ =>
            go (ty :: val :: body :: xs) seen out
        | .mdata _ body =>
            go (body :: xs) seen out
        | _ =>
            go xs seen out
  go [e] {} Lean.NameSet.empty

/-- Collect constant names appearing in an expression. -/
def collectExprConsts (e : Lean.Expr) : Lean.NameSet :=
  let fromConsts :=
    e.foldConsts (init := Lean.NameSet.empty) fun n acc =>
      acc.insert n
  fromConsts.union (projHeads e)

/-- Immediate outgoing edges extracted from a constant. -/
def edgesFromConstantInfo (ci : Lean.ConstantInfo)
    : Array (Lean.Name × EdgeKind) :=
  let typeEdges :=
    (collectExprConsts ci.type).toList.toArray.map
      (fun n => (n, EdgeKind.type))

  let valueEdges :=
    match ci.value? with
    | none => #[]
    | some v =>
        (collectExprConsts v).toList.toArray.map
          (fun n => (n, EdgeKind.value))

  typeEdges ++ valueEdges

/-- Build a `Graph Name` from an environment, with optional namespace filtering. -/
def buildGraphFromEnv (env : Lean.Environment) (nsPrefix? : Option String := none) : Graph Lean.Name :=
  Id.run do
    let consts := env.constants
    let allNames : Array Lean.Name := 
      match nsPrefix? with
      | none => consts.fold (init := #[]) (fun acc n _ => acc.push n)
      | some p => consts.fold (init := #[]) (fun acc n _ => 
          if (toString n).startsWith p then acc.push n else acc)
    
    let constList : Array Lean.Name := allNames.qsort Lean.Name.lt

    let mut nodeToIdx : Std.HashMap Lean.Name Nat := {}
    for i in [:constList.size] do
      nodeToIdx := nodeToIdx.insert constList[i]! i

    let mut forward : Array (Array (Nat × EdgeKind)) :=
      Array.replicate constList.size #[]

    for i in [:constList.size] do
      let name := constList[i]!
      match env.find? name with
      | none => pure ()
      | some ci =>
          let edges := edgesFromConstantInfo ci
          for (dep, k) in edges do
            match nodeToIdx.get? dep with
            | none => pure ()
            | some j =>
                forward := forward.modify i (fun arr => arr.push (j, k))
    { nodes := constList, nodeToIdx := nodeToIdx, forward := forward }

end DAG
