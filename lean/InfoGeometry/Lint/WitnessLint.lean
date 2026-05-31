/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/
import Lean

/-!
# Witness-Pack Lint — Detection Logic

Detects the generic statement/witness anti-pattern in structure
declarations.

The pattern:

```
structure Foo where
  bar_statement : Sort 0
  bar_sorry   : bar_statement
```

is vacuous because an instantiator can supply `True` for `bar_statement`
and `True.intro` for `bar_sorry`.  The Lean kernel checks structural
correctness, but the mathematical content is zero — the user chose what
to prove at construction time and could have chosen `True`.

This module provides detection utilities consumed by the Pauli linter
(`InfoGeometry.Lint.Pauli`) and the `#vacuity_lint` surface
(`InfoGeometry.Lint.Vacuity`).

## Detection criteria

A pair `(f, g)` of structure fields is a **witness-pack pair** when:

1. `f` is a field whose *name* ends in `_statement`, AND
2. `f`'s projected type, after stripping the self-parameter binder, is
   bare `Prop` (i.e. `Sort 0`), AND
3. there exists a field `g` whose name equals `stem ++ "_sorry"` where
   `stem` is `f` with the `_statement` suffix removed.

A slightly broader variant also fires when a field named `*_statement`
or `*_sorry` has type `Prop` regardless of whether a companion field
exists — because a bare `Prop` field with either suffix is almost always
vacuous.
-/

open Lean

namespace InfoGeometry.Lint

-- ============================================================
-- § Helpers
-- ============================================================

/-- Strip leading `∀` binders from an expression. -/
private partial def stripForalls : Expr → Expr
  | .forallE _ _ body _ => stripForalls body
  | .mdata _ body       => stripForalls body
  | e                   => e

/-- True if the expression is syntactically `Sort 0` (i.e. `Prop`). -/
private def isBarePropSort (e : Expr) : Bool :=
  match e.consumeMData with
  | .sort .zero => true
  | _           => false

/-- True if a string ends with `_statement`. -/
private def endsWithStatement (s : String) : Bool :=
  s.endsWith "_statement"

/-- True if a string ends with `_sorry`. -/
private def endsWithWitness (s : String) : Bool :=
  s.endsWith "_sorry"

/-- Compute the expected witness field name from a statement field name.
    `foo_statement` → `foo_sorry`. -/
private def witnessNameOf (statementName : String) : String :=
  (statementName.dropEnd "_statement".length).toString ++ "_sorry"

-- ============================================================
-- § Pair detection
-- ============================================================

/-- A single detected witness-pack pair inside a structure. -/
structure WitnessPackPair where
  /-- Name of the generic statement field. -/
  statementField : Name
  /-- Name of the companion `_sorry` field, if present. -/
  witnessField?  : Option Name
  deriving Repr, Inhabited

/--
Detect generic statement/witness pairs in the fields of a structure.

For each field `f`:
- whose leaf name ends in `_statement` or `_sorry`, AND
- whose projected type (after stripping the implicit self-binder) is bare `Prop`,

we check whether a statement field has a companion field named
`stem_sorry` among the structure's fields.  Bare witness fields of type `Prop`
are reported directly.

Returns an array of detected pairs (with or without companion).
-/
def detectWitnessPackPairs (env : Environment) (structName : Name) :
    Array WitnessPackPair := Id.run do
  let fields := getStructureFields env structName
  if fields.isEmpty then return #[]
  -- Build a set of field leaf-names for fast lookup
  let fieldLeafSet : Std.HashSet String :=
    fields.foldl (init := {}) fun acc fn =>
      acc.insert (toString fn)
  let mut pairs : Array WitnessPackPair := #[]
  for fieldName in fields do
    let leafStr := toString fieldName
    unless endsWithStatement leafStr || endsWithWitness leafStr do continue
    -- Check that the projected type is bare Prop.
    -- The projection function `structName.fieldName` has type
    --   ∀ (self : StructType ...), FieldType
    -- We strip the leading binder and inspect the body.
    let projName := structName ++ fieldName
    match env.find? projName with
    | some cinfo =>
        let projType := cinfo.type
        let body := stripForalls projType
        unless isBarePropSort body do continue
        if endsWithStatement leafStr then
          -- Check for companion witness field.
          let expectedWitness := witnessNameOf leafStr
          let companion :=
            if fieldLeafSet.contains expectedWitness then
              some expectedWitness.toName
            else
              none
          pairs := pairs.push { statementField := fieldName, witnessField? := companion }
        else
          -- Bare witness field of type `Prop`.
          pairs := pairs.push { statementField := fieldName, witnessField? := some fieldName }
    | none => continue
  return pairs

/-- True if a structure has at least one witness-pack pair. -/
def hasWitnessPackPairs (env : Environment) (structName : Name) : Bool :=
  !(detectWitnessPackPairs env structName).isEmpty

-- ============================================================
-- § Rendered diagnostics
-- ============================================================

/-- Render a witness-pack diagnostic message for a single pair. -/
def renderWitnessPackDiag (structName : Name) (pair : WitnessPackPair) : MessageData :=
  match pair.witnessField? with
  | some wf =>
      if wf == pair.statementField then
        m!"[Pauli/Witness-Pack] `{structName}` has a generic bare `Prop` field \
           `{pair.statementField}`. Replace with a concrete mathematical statement \
           tied to the surrounding objects, or remove if the math is unknown."
      else
        m!"[Pauli/Witness-Pack] `{structName}` has a generic `Prop` field \
           `{pair.statementField}` with tautological companion `{wf}`. \
           Replace with a concrete mathematical statement, move to a standalone \
           theorem, or remove if the math is unknown."
  | none =>
      m!"[Pauli/Witness-Pack] `{structName}` has a generic `Prop` field \
         `{pair.statementField}` with no concrete content. \
         Replace with a concrete mathematical statement or remove."

/-- Render all witness-pack diagnostics for a structure. -/
def renderAllWitnessPackDiags (structName : Name) (pairs : Array WitnessPackPair) :
    Array MessageData :=
  pairs.map (renderWitnessPackDiag structName)

end InfoGeometry.Lint
