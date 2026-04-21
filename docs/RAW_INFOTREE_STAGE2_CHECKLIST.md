# Raw InfoTree Stage 2 Checklist

Machine-usable checklist for the `fusion/upstream-intake-20260419` worktree.

Purpose:
- map real Lean 4.28 `InfoTree`/`Info`/context fields to exporter status
- distinguish easy captures from hard structured shadows
- standardize leakage row labels
- guide Stage 2 expansion without heuristic guessing

Scope:
- based on Lean 4.28 source, especially:
  - `Lean/Elab/InfoTree/Types.lean`
  - `Lean/Elab/InfoTree/Main.lean`
- applies to:
  - `lean/DAG/RawInfoTreeExport.lean`
  - `docs/RAW_INFOTREE_EXPORT_CONTRACT.md`

## Status vocabulary

- `exported`: field is already exported in a meaningful form
- `partial`: shallow export exists, but not the full structural object
- `missing`: no meaningful export yet

## Priority vocabulary

- `easy`: stable names/ids/counts/text can be added now
- `medium`: structured rows are feasible without full compiler-object serialization
- `hard`: requires object-graph or near-lossless structural serialization

## Checklist

| area | lean source owner | field / object | current status | priority | next action | recommended leakage label |
|---|---|---|---|---|---|---|
| context | `PartialContextInfo.parentDeclCtx` | `parentDecl : Name` | exported | easy | keep exact context field, add/use decl-link row when branch is exercised | n/a |
| context | `PartialContextInfo.autoImplicitCtx` | `autoImplicits : Array Expr` | partial | medium | export count, text, const-name links, optional per-expr rows | `auto_implicit_expr_graph` |
| context | `CommandContextInfo` | `currNamespace : Name` | exported | easy | keep exact string export | n/a |
| context | `CommandContextInfo` | `openDecls : List OpenDecl` | partial | medium | add structured open-decl rows instead of only count/text | `command_context_open_decls_structured` |
| context | `CommandContextInfo` | `options : Options` | partial | medium | add per-option structured rows; keep raw text as redundant surface | `command_context_options_structured` |
| context | `CommandContextInfo` | `ngen : NameGenerator` | partial | easy | keep prefix/index, add clearer provenance fields if useful | `command_context_name_generator_full` |
| context | `CommandContextInfo` | `env : Environment` | partial | hard | do not guess; design structural environment join/export plan | `command_context_env_snapshot` |
| context | `CommandContextInfo` | `cmdEnv? : Option Environment` | partial | hard | do not guess; design final command environment join/export plan | `command_context_final_env_snapshot` |
| context | `CommandContextInfo` | `mctx : MetavarContext` | partial | hard | preserve current refs/decl rows, expand graph only with explicit structure | `command_context_mctx_graph` |
| info | `TermInfo` | `expr : Expr` | partial | hard | keep text/const links, plan expression-graph export | `term_expr_graph` |
| info | `TermInfo` | `expectedType? : Option Expr` | partial | hard | keep text/const links, plan expression-graph export | `term_expected_type_expr_graph` |
| info | `TermInfo` | `lctx : LocalContext` | partial | hard | add local-context graph plan, avoid fake counts as completeness claims | `term_local_context_graph` |
| info | `PartialTermInfo` | `expectedType? : Option Expr` | partial | hard | same as `TermInfo.expectedType?` | `partial_term_expected_type_expr_graph` |
| info | `PartialTermInfo` | `lctx : LocalContext` | partial | hard | same as `TermInfo.lctx` | `partial_term_local_context_graph` |
| info | `CommandInfo` | syntax/elaborator only | exported | easy | keep; enrich only if stable additional fields exist upstream | n/a |
| info | `TacticInfo` | `goalsBefore : List MVarId` | partial | easy | export exact goal ids, not only counts | `tactic_goals_before_full` |
| info | `TacticInfo` | `goalsAfter : List MVarId` | partial | easy | export exact goal ids, not only counts | `tactic_goals_after_full` |
| info | `TacticInfo` | `mctxBefore : MetavarContext` | missing/partial | medium-hard | add mctx refs first, then decl rows, then deeper graph only if real | `tactic_mctx_before_graph` |
| info | `TacticInfo` | `mctxAfter : MetavarContext` | missing/partial | medium-hard | add mctx refs first, then decl rows, then deeper graph only if real | `tactic_mctx_after_graph` |
| info | `MacroExpansionInfo` | `output : Syntax` | partial | hard | keep syntax text, plan syntax-object fidelity separately | `macro_expansion_output_syntax_graph` |
| info | `MacroExpansionInfo` | `lctx : LocalContext` | partial | hard | same local-context debt as term/field info | `macro_expansion_local_context_graph` |
| info | `OptionInfo` | `optionName`, `declName` | exported | easy | keep exact names and decl links | n/a |
| info | `ErrorNameInfo` | `errorName` | exported | easy | keep exact name and decl link when meaningful | n/a |
| info | `FieldInfo` | `projName`, `fieldName` | exported | easy | keep exact names, keep decl link to `projName` | n/a |
| info | `FieldInfo` | `val : Expr` | partial | hard | keep text/const links, plan expr graph export | `field_value_expr_graph` |
| info | `FieldInfo` | `lctx : LocalContext` | partial | hard | same local-context debt | `field_info_local_context_graph` |
| info | `CompletionInfo` | constructor-specific stable names/ids | partial | easy-medium | extend per constructor with stable ids and rows | `completion_constructor_payload_gap` |
| info | `UserWidgetInfo` | widget instance payload | missing/partial | hard | preserve explicit leakage until a true widget serializer exists | `user_widget_instance_payload` |
| info | `CustomInfo` | `value : Dynamic` | missing/partial | hard | preserve explicit leakage; no fake serialization | `custom_dynamic_payload` |
| info | `FVarAliasInfo` | `userName`, `id`, `baseId` | exported | easy | keep exact alias identity rows | n/a |
| info | `FieldRedeclInfo` | syntax only | partial | easy-medium | extend only if Lean exposes a stable owner relation | `field_redecl_owner_relation` |
| info | `DelabTermInfo` | `location? : Option DeclarationLocation` | missing/partial | easy-medium | export exact location override when stable | `delab_term_location_override` |
| info | `DelabTermInfo` | `docString? : Option String` | partial | easy | export exact override text if present | `delab_term_docstring_override` |
| info | `ChoiceInfo` | failed-alternative structure | partial | medium | preserve child topology, add explicit payload note if needed | `choice_failed_alternatives_payload` |
| info | `DocInfo` | basic elaboration fact | exported | easy | keep exact syntax/elaborator export | n/a |
| info | `DocElabInfo` | `name`, `kind` | exported | easy | keep exact name/kind and decl link | n/a |
| tree | `InfoTree.hole` | `hole : MVarId` | partial | medium | export exact hole id, add assignment relation if available | `infotree_hole_assignment` |
| tree | `InfoState.lazyAssignment` | lazy hole assignments | missing/partial | hard | add explicit leakage unless real task/assignment capture is implemented | `infotree_hole_lazy_assignment` |

## mctx bridge assessment

## Reclaimed already

The current `raw_infotree_mctx_refs` + `raw_infotree_mctx_decls` surfaces reclaim a nontrivial portion of compiler shadow for `CommandContextInfo.mctx`:

- mctx identity/count/depth layer
- declaration id inventory
- user-name inventory
- assignment presence
- delayed assignment presence
- type text/hash
- assignment text/hash where exposed

This means the command-context mctx is no longer a total black box.

## Still dark

What remains unexported for true mctx losslessness:

- full expression graph for types and assignments
- full local-context graph per metavariable declaration
- exact dependency graph among metavariables
- full level-expression structure
- full delayed-assignment payload graph
- tactic-local before/after mctx structural capture unless added separately

## Recommended next order

1. export exact `TacticInfo` goal ids before/after
2. add `TacticInfo` mctx ref rows before/after
3. add `TacticInfo` mctx decl rows before/after
4. add auto-implicit const-name / decl-link surface
5. export `DelabTermInfo.location?`
6. add structured `OpenDecl` rows
7. design real expr-graph export boundary

## Hard rule

Never remove a leakage class because the field is inconvenient.
Remove it only when the corresponding artifact is actually serialized in a stable, queryable form.
