import Lean
import Std
import DAG.Basic

open Lean

namespace DAG

/- JSON helpers for Lean core types -/

instance : ToJson Name where
  toJson n := Json.str n.toString

instance : FromJson Name where
  fromJson? j := j.getStr?.map (·.toName)

instance : ToJson String.Pos.Raw where
  toJson p := Json.num p.byteIdx

instance : FromJson String.Pos.Raw where
  fromJson? j := j.getNat?.map (⟨·⟩)

instance : ToJson Position where
  toJson p := Json.mkObj [("line", toJson p.line), ("column", toJson p.column)]

instance : FromJson Position where
  fromJson? j := do
    let line ← j.getObjValAs? Nat "line"
    let column ← j.getObjValAs? Nat "column"
    return { line := line, column := column }

/- JSON helpers for DAG types (if not already defined) -/

instance : ToJson DAG.EdgeKind where
  toJson
    | .type  => Json.str "type"
    | .value => Json.str "value"

instance : FromJson DAG.EdgeKind where
  fromJson? j := match j.getStr? with
    | .ok "type"  => .ok .type
    | .ok "value" => .ok .value
    | .ok s       => .error s!"unknown EdgeKind: {s}"
    | .error e    => .error e

instance {α} [BEq α] [Hashable α] [ToJson α] : ToJson (DAG.Graph α) where
  toJson g :=
    Json.mkObj
      [ ("nodes", Json.arr (g.nodes.map toJson))
      , ("forward",
          Json.arr <|
            g.forward.map (fun row =>
              Json.arr <|
                row.map (fun (t, k) => Json.arr #[toJson t, toJson k])))
      ]

instance {α} [BEq α] [Hashable α] [Inhabited α] [FromJson α] : FromJson (DAG.Graph α) where
  fromJson? j := do
    let nodes ← j.getObjValAs? (Array α) "nodes"
    let forwardRaw ← j.getObjValAs? (Array (Array (Nat × DAG.EdgeKind))) "forward"
    -- reconstruct nodeToIdx
    let mut nodeToIdx : Std.HashMap α Nat := {}
    for i in [:nodes.size] do
      nodeToIdx := nodeToIdx.insert nodes[i]! i
    return { nodes := nodes, nodeToIdx := nodeToIdx, forward := forwardRaw }

end DAG
