import Lean
import Lean.Util.FoldConsts

open Lean

namespace AuditAxiomsReport

structure CacheState where
  memo : Std.HashMap Name NameSet := {}
  active : NameSet := {}

def leafNameString (n : Name) : String :=
  match (toString n).splitOn "." |>.reverse with
  | x :: _ => x
  | [] => ""

def containsPrivateMarker (s : String) : Bool :=
  (s.splitOn "._private.").length > 1 || s.startsWith "_private."

def isGeneratedName (n : Name) : Bool :=
  let s := toString n
  let leaf := leafNameString n
  containsPrivateMarker s ||
    leaf.startsWith "match_" ||
    leaf.startsWith "proof_" ||
    leaf.startsWith "_aux" ||
    leaf.endsWith "brecOn" ||
    leaf.endsWith "below" ||
    leaf.endsWith "ibelow" ||
    leaf.endsWith "injEq" ||
    leaf.endsWith "sizeOf_spec"

def constKind? (ci : ConstantInfo) : Option String :=
  match ci with
  | .axiomInfo _ => some "axiom"
  | .defnInfo _ => none
  | .thmInfo _ => some "theorem"
  | .opaqueInfo _ => some "opaque"
  | .inductInfo _ => none
  | .ctorInfo _ => none
  | .recInfo _ => none
  | .quotInfo _ => none

def nameSetToSortedStrings (s : NameSet) : List String :=
  let names := s.fold (init := #[]) fun acc n => acc.push n.toString
  (names.qsort (· < ·)).toList

partial def collectConstAxioms (env : Environment) (c : Name) : StateM CacheState NameSet := do
  let st ← get
  if let some axioms := st.memo[c]? then
    return axioms
  if st.active.contains c then
    return {}
  modify fun st => { st with active := st.active.insert c }
  let axioms ←
    match env.find? c with
    | some ci => do
        let depNames := ci.getUsedConstantsAsSet.fold (init := #[]) fun acc dep => acc.push dep
        let mut acc : NameSet := {}
        for dep in depNames do
          let depAxioms ← collectConstAxioms env dep
          acc := acc ++ depAxioms
        match ci with
        | .axiomInfo _ =>
            pure <| acc.insert c
        | _ =>
            pure acc
    | none =>
        pure {}
  modify fun st =>
    { st with
        active := st.active.erase c
        memo := st.memo.insert c axioms }
  pure axioms

def shouldIncludeName (prefixes : Array String) (s : String) : Bool :=
  prefixes.isEmpty || prefixes.any fun prefix => s.startsWith prefix

def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `InfoGeometry }, { module := `SelfReference }] {}
  let modules := env.header.moduleNames
  let prefixes := args.toArray
  let names :=
    env.constants.fold (init := #[]) fun acc name _ =>
      let s := name.toString
      if (s.startsWith "InfoGeometry" || s.startsWith "SelfReference") &&
          !isGeneratedName name &&
          shouldIncludeName prefixes s then
        acc.push name
      else
        acc
  let names := names.qsort Name.lt
  for name in names do
    match env.find? name, env.getModuleIdxFor? name with
    | some ci, some modIdx =>
        match constKind? ci with
        | some kind =>
            let (axioms, _) := (collectConstAxioms env name).run {}
            let axioms := nameSetToSortedStrings axioms
            let moduleName := (modules[modIdx.toNat]!).toString
            IO.println s!"{moduleName}\t{kind}\t{name}\t{String.intercalate ";" axioms}"
        | none =>
            pure ()
    | _, _ =>
        pure ()
  return 0

end AuditAxiomsReport

def main (args : List String) : IO UInt32 :=
  AuditAxiomsReport.main args
