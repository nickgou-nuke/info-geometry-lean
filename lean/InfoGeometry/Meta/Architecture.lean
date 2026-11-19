/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Lean

open Lean

namespace InfoGeometry.Meta

/-- Representation-depth ladder for the stable information-geometry spine. -/
inductive RepDepth where
  | count
  | projective
  | operator
  | krein
  | transport
  | thermo
  deriving DecidableEq, Repr, Inhabited

/-- Numeric depth index used by the architecture auditor. -/
def RepDepth.toNat : RepDepth → Nat
  | .count => 0
  | .projective => 1
  | .operator => 2
  | .krein => 3
  | .transport => 4
  | .thermo => 5

/-- Stable short slug used in exported metadata. -/
def RepDepth.slug : RepDepth → String
  | .count => "count"
  | .projective => "projective"
  | .operator => "operator"
  | .krein => "krein"
  | .transport => "transport"
  | .thermo => "thermo"

/--
Canonical L0-L5 layer label.

These labels give the existing `@[rep_depth ...]` tags a stable
machine-readable ontology for Arango and agent retrieval without changing the
existing attribute grammar used across the repo.
-/
def RepDepth.layerLabel : RepDepth → String
  | .count => "L0_Count"
  | .projective => "L1_Projective"
  | .operator => "L2_Operator"
  | .krein => "L3_Krein"
  | .transport => "L4_ModularTransport"
  | .thermo => "L5_ThermodynamicClosure"

/-- Human description of the representation layer. -/
def RepDepth.layerDescription : RepDepth → String
  | .count => "counting/combinatorial substrate"
  | .projective => "projection/support/compression substrate"
  | .operator => "operator-algebraic bridge substrate"
  | .krein => "Krein/doubled-geometry substrate"
  | .transport => "modular/transport/flow substrate"
  | .thermo => "thermodynamic/free-energy/closure substrate"

/-- Exportable metadata strings attached to DAG declaration rows. -/
def RepDepth.exportTags (depth : RepDepth) : Array String :=
  #[ s!"rep_depth:{depth.slug}"
   , s!"rep_depth_nat:{depth.toNat}"
   , s!"rep_layer:{depth.layerLabel}"
   , s!"rep_layer_description:{depth.layerDescription}" ]

/-- Parse attribute syntax into the internal representation depth. -/
def parseRepDepth? (n : Name) : Option RepDepth :=
  match n.eraseMacroScopes with
  | `count => some .count
  | `projective => some .projective
  | `operator => some .operator
  | `krein => some .krein
  | `transport => some .transport
  | `thermo => some .thermo
  | _ => none

syntax (name := rep_depth) "rep_depth " ident : attr

/-- Attach a representation depth to a declaration participating in the stable spine. -/
initialize repDepthAttr : ParametricAttribute RepDepth ←
  registerParametricAttribute {
    name := `rep_depth
    descr := "Assign a representation depth to a declaration in the stable spine."
    getParam := fun _ stx => do
      match stx with
      | `(attr| rep_depth $id:ident) =>
          match parseRepDepth? id.getId with
          | some d => pure d
          | none =>
              throwError "invalid `rep_depth` value `{id.getId}`; expected count, projective, operator, krein, transport, or thermo"
      | _ => Lean.Elab.throwUnsupportedSyntax
  }

/-- Mark a theorem as a composite capstone exempt from strict adjacency. -/
initialize capstoneAttr : TagAttribute ←
  registerTagAttribute `capstone
    "Mark a theorem as a capstone composition exempt from adjacency policing."

/-- Look up the representation depth attached to a declaration, if any. -/
def repDepth? (env : Environment) (declName : Name) : Option RepDepth :=
  repDepthAttr.getParam? env declName

/-- Collect representation-depth tags attached to a declaration as strings. -/
def repDepthTagStringsOf (env : Environment) (declName : Name) : Array String :=
  match repDepth? env declName with
  | some depth => depth.exportTags
  | none => #[]

/-- True iff the constant info describes a theorem. -/
def isTheoremInfo : ConstantInfo → Bool
  | .thmInfo _ => true
  | _ => false

/-- True iff the constant info describes a theorem or a definition. -/
def isDefOrTheoremInfo : ConstantInfo → Bool
  | .thmInfo _ => true
  | .defnInfo _ => true
  | _ => false

end InfoGeometry.Meta
