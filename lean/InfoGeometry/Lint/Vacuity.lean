/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/
import Lean
import DAG.Basic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.Vacuity

/-!
# Vacuity Linter — Declaration-Local Checks

Layer A of the three-layer vacuity enforcement system.

This module provides:
- Role-annotation attributes (`@[infrastructure]`, `@[terminal]`, `@[expository]`)
- Declaration-local proof-shape and statement-shape classification
- A `#vacuity_lint` command for batch checking

It deliberately does **not** perform graph-level analysis. That belongs in
`tools/theorem_significance.py` (Layer B). The CI policy gate
(`tools/check_vacuity_policy.py`) combines both layers (Layer C).

## Violation classes checked here

- **V0 (syntactic vacuity)**: proof is `rfl`, `trivial`, single-const forwarding, or
  trivial `simpa`/`rw`, and statement is a projection/abbreviation/coercion exposure.
  Warns unless `@[infrastructure]` or `@[expository]`.

- **V1 (public wrapper inflation)**: proof forwards to a single prior theorem and
  statement adds no new mathematical content. Warns; errors in bridge/canonical files
  (enforced at CI layer).

- **V5 (certification wash)**: certified naming surface only aliases or transports
  an uncertified twin. Warns unless explicitly role-tagged.

## Attributes

| Attribute        | Meaning                                  |
|------------------|------------------------------------------|
| `infrastructure` | Support lemma; not theorem-level content  |
| `terminal`       | Public declaration with no expected reuse |
| `expository`     | Wrapper/restatement kept for readability  |

Note: `@[capstone]` already exists in `InfoGeometry.Meta.Architecture`.
-/

open Lean Meta Elab Command InfoGeometry.Meta

namespace InfoGeometry.Lint

-- ============================================================
-- § Proof-shape analysis
-- ============================================================

/-- Classification of a declaration value/proof term shape. -/
inductive ProofShape where
  | exactConst (target : Name)
  | exactApp (head : Name) (nargs : Nat)
  | rfl
  | trivial
  | lambda
  | other
  deriving Repr, Inhabited

/-- Classify the value/proof term of a theorem or definition declaration. -/
def classifyProofShape (env : Environment) (declName : Name) : ProofShape :=
  match env.find? declName with
  | some (.thmInfo info) =>
      let v := info.value
      if v.isConst then
        .exactConst v.constName!
      else if v.isAppOfArity ``Eq.refl 2 then
        .rfl
      else if v.isAppOfArity ``rfl 2 then
        .rfl
      else if v.isApp then
        let f := v.getAppFn
        if f.isConst then
          .exactApp f.constName! v.getAppNumArgs
        else
          .other
      else if v.isLambda then
        .lambda
      else
        .other
  | some (.defnInfo info) =>
      let v := info.value
      if v.isConst then
        .exactConst v.constName!
      else if v.isAppOfArity ``Eq.refl 2 then
        .rfl
      else if v.isAppOfArity ``rfl 2 then
        .rfl
      else if v.isApp then
        let f := v.getAppFn
        if f.isConst then
          .exactApp f.constName! v.getAppNumArgs
        else
          .other
      else if v.isLambda then
        .lambda
      else
        .other
  | _ => .other

/-- True if the proof shape looks like a thin forwarding wrapper. -/
def ProofShape.isForwarding : ProofShape → Bool
  | .exactConst _ => true
  | .exactApp _ nargs => nargs ≤ 4
  | .rfl => true
  | .trivial => true
  | _ => false

/-- Extract the single head target of a forwarding declaration shape, if present. -/
def ProofShape.forwardTarget? : ProofShape → Option Name
  | .exactConst target => some target
  | .exactApp head _ => some head
  | _ => none

-- ============================================================
-- § Statement-shape analysis
-- ============================================================

/-- Classification of a theorem's statement shape. -/
inductive StatementShape where
  | eq
  | iff
  | forallEq
  | forallIff
  | exists_
  | existsUnique
  | prop
  | other
  deriving Repr, Inhabited

/-- Classify the outermost shape of a theorem's statement type. -/
def classifyStatementShape (env : Environment) (declName : Name) : StatementShape :=
  match env.find? declName with
  | some (.thmInfo info) =>
      let t := info.type
      -- unwrap leading foralls
      let body := t.consumeMData
      let rec stripForall (e : Expr) : Expr :=
        match e with
        | .forallE _ _ b _ => stripForall b
        | _ => e
      let inner := stripForall body
      if inner.isAppOfArity ``Eq 3 then
        if t.isForall then .forallEq else .eq
      else if inner.isAppOfArity ``Iff 2 then
        if t.isForall then .forallIff else .iff
      else if inner.isAppOfArity ``Exists 2 then
        -- Check if it's ∃! (ExistsUnique is sugar for ∃ x, p x ∧ ∀ y, p y → y = x)
        .exists_
      else
        .prop
  | _ => .other

-- ============================================================
-- § Lint logic
-- ============================================================

/-- Check whether a declaration has any of the vacuity-exempting role tags. -/
def hasRoleTag (env : Environment) (declName : Name) : Bool :=
  isVacuityRoleTagged env declName

/-- Combined role-tag check including all exempt annotations. -/
def isExempt (env : Environment) (declName : Name) : Bool :=
  hasRoleTag env declName || capstoneAttr.hasTag env declName

/-- Case-insensitive test for `certified` anywhere in a declaration name. -/
def containsCertifiedMarker (declName : Name) : Bool :=
  (toString declName).toLower.contains "certified"

/-- Lower-cased final dotted component of a declaration name. -/
def declNameLeaf (declName : Name) : String :=
  match (toString declName).toLower.splitOn "." |>.reverse with
  | leaf :: _ => leaf
  | [] => (toString declName).toLower

/-- Lower-cased declaration name with every `certified` marker erased. -/
def eraseCertifiedMarker (declName : Name) : String :=
  (toString declName).toLower.replace "certified" ""

/-- Lower-cased final dotted component with every `certified` marker erased. -/
def eraseCertifiedMarkerLeaf (declName : Name) : String :=
  (declNameLeaf declName).replace "certified" ""

/-- Detect names of the form `certifiedFoo_eq_foo` or `certifiedFoo_iff_foo`. -/
def isCertifiedTransportName (declName : Name) : Bool :=
  let nameStr := declNameLeaf declName
  let parts :=
    if nameStr.contains "_eq_" then
      nameStr.splitOn "_eq_"
    else if nameStr.contains "_iff_" then
      nameStr.splitOn "_iff_"
    else
      []
  match parts with
  | [lhs, rhs] =>
      lhs.contains "certified" &&
        !rhs.contains "certified" &&
        lhs.replace "certified" "" = rhs
  | _ => false

/-- Detect forwarding from a certified surface directly to an uncertified twin. -/
def isCertifiedTwinForward (declName : Name) (pshape : ProofShape) : Bool :=
  match pshape.forwardTarget? with
  | some target =>
      containsCertifiedMarker declName &&
        !containsCertifiedMarker target &&
        eraseCertifiedMarkerLeaf declName = eraseCertifiedMarkerLeaf target
  | none => false

/-- Lint a single declaration for vacuity issues. Returns warning messages. -/
def lintDecl (env : Environment) (declName : Name) : Array MessageData := Id.run do
  let mut msgs : Array MessageData := #[]

  -- Only lint theorems and definitions.
  match env.find? declName with
  | some (.thmInfo _) => pure ()
  | some (.defnInfo _) => pure ()
  | _ => return msgs

  -- Skip internal/auxiliary names
  if declName.isInternal then return msgs
  if declName.hasMacroScopes then return msgs

  let exempt := isExempt env declName
  let pshape := classifyProofShape env declName
  let sshape :=
    match env.find? declName with
    | some (.thmInfo _) => classifyStatementShape env declName
    | _ => .other

  -- V0: syntactically trivial proof on a low-load statement
  if !exempt && pshape.isForwarding then
    match sshape with
    | .eq | .forallEq =>
        msgs := msgs.push
          m!"[V0/syntactic-vacuity] {declName}: trivial proof on equality statement. \
             Consider @[infrastructure] or @[expository]."
    | .prop =>
        msgs := msgs.push
          m!"[V0/syntactic-vacuity] {declName}: trivial forwarding proof. \
             Consider @[infrastructure] or @[expository]."
    | _ => pure ()

  -- V1: forwarding wrapper (exact-const with no new content)
  if !exempt then
    match pshape with
    | .exactConst target =>
        msgs := msgs.push
          m!"[V1/public-wrapper-inflation] {declName}: proof forwards entirely to `{target}`. \
             Mark @[infrastructure], @[expository], or prove non-trivially."
    | _ => pure ()

  -- V5: certified naming surface only transports or aliases an uncertified twin
  if !exempt && (isCertifiedTransportName declName || isCertifiedTwinForward declName pshape) then
    match pshape.forwardTarget? with
    | some target =>
        msgs := msgs.push
          m!"[V5/certification-wash] {declName}: certified surface forwards to uncertified twin `{target}`. \
             Mark @[infrastructure]/@[expository] or add proof-bearing certified content."
    | none =>
        msgs := msgs.push
          m!"[V5/certification-wash] {declName}: certified transport surface only forgets certification in its public API. \
             Mark @[infrastructure]/@[expository] or add proof-bearing certified content."

  return msgs

-- ============================================================
-- § Command interface
-- ============================================================

/-- `#vacuity_lint` — run vacuity checks on all declarations in the current environment. -/
syntax (name := vacuityLintCmd) "#vacuity_lint" : command

@[command_elab vacuityLintCmd]
def elabVacuityLint : CommandElab := fun _stx => do
  let env ← getEnv
  let countsRef ← IO.mkRef (0, 0)  -- (count, warnCount)
  env.constants.forM fun declName _ => do
    let msgs := lintDecl env declName
    for msg in msgs do
      logWarning msg
      countsRef.modify fun (c, w) => (c, w + 1)
    countsRef.modify fun (c, w) => (c + 1, w)
  let (count, warnCount) ← countsRef.get
  logInfo m!"Vacuity lint checked {count} declarations, found {warnCount} warnings."

/-- `#vacuity_lint_file` — run vacuity checks only on declarations from the current module. -/
syntax (name := vacuityLintFileCmd) "#vacuity_lint_file" : command

@[command_elab vacuityLintFileCmd]
def elabVacuityLintFile : CommandElab := fun _stx => do
  let env ← getEnv
  let countsRef ← IO.mkRef (0, 0)
  env.constants.forM fun declName _ => do
    match env.getModuleIdxFor? declName with
    | some _ => pure ()
    | none =>
        let msgs := lintDecl env declName
        for msg in msgs do
          logWarning msg
          countsRef.modify fun (c, w) => (c, w + 1)
        countsRef.modify fun (c, w) => (c + 1, w)
  let (count, warnCount) ← countsRef.get
  logInfo m!"Vacuity lint (file) checked {count} declarations, found {warnCount} warnings."

/-- `#lint_vacuity_decl Foo.bar` — run vacuity checks on a single declaration. -/
syntax (name := vacuityLintDeclCmd) "#lint_vacuity_decl " ident : command

@[command_elab vacuityLintDeclCmd]
def elabVacuityLintDecl : CommandElab := fun stx => do
  let env ← getEnv
  let declName := stx[1].getId.eraseMacroScopes
  if env.find? declName |>.isNone then
    logError m!"Unknown declaration `{declName}`."
    return
  let msgs := lintDecl env declName
  if msgs.isEmpty then
    logInfo m!"Vacuity lint: {declName} has no warnings."
  else
    for msg in msgs do
      logWarning msg

end InfoGeometry.Lint
