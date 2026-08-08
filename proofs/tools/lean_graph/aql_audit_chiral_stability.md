# AQL Audit: Chiral τ-Ideal Stability Certificate

Machine-generated proof-topology audit of the 4-cell τ-ideal matrix
and its dependency spine. Run in ArangoDB web UI or via python-arango.

**Database**: `info_geometry` | **Graph**: `LeanUniverseGraph`

## 1. 4-Cell τ-Ideal Matrix — Verify All Four Cells

```aql
FOR decl IN lean_decls
  FILTER decl.name IN [
    "ChiralTLDescent.chiral_left_tau_ideal",
    "ChiralTLDescent.chiral_kernel_is_left_tau_ideal",
    "ChiralTLDescent.chiral_right_tau_ideal",
    "ChiralTLDescent.chiral_right_kernel_tau_ideal"
  ]
  LET inbound = LENGTH(FOR e IN references FILTER e._to == decl._id RETURN 1)
  LET outbound = LENGTH(FOR e IN references FILTER e._from == decl._id RETURN 1)
  RETURN {cell: decl.name, referenced_by: inbound, depends_on: outbound}
```

Expected: all 4 cells present, depends_on ≥ 8 (each pulls the full tauL/tauR + qCrossMap chain).

## 2. Dependency Spine — What Does Each Cell Pull In?

```aql
FOR v, e IN 1..5 OUTBOUND "lean_decls/ChiralTLDescent_chiral_left_tau_ideal" references
  COLLECT name = v.name, depth = MIN(LENGTH(e))
  SORT depth, name
  RETURN {name, depth}
```

Key expected nodes at each depth:
- depth 1: `e_tmul_eta_mem_leftTarget`, `tauL_qCrossMap_on_e`, `R_chiral_tensor`
- depth 2: `tauL_qCrossMap_on_pure_tmul`, `e`, `M2C`, `SpinPair`
- depth 3: `qCrossMap`, `tauL`, `IsLeftTauIdeal`, `X`, `Y`, `Z`
- depth 4: `σPlus`, `σMinus`, `σ3c`, `CrossMap`

## 3. Socket Scan — Declarations With Zero Incoming References

```aql
FOR decl IN lean_decls
  FILTER decl.kind IN ["def", "structure", "axiom", "opaque"]
  LET refs = LENGTH(FOR e IN references FILTER e._to == decl._id RETURN 1)
  FILTER refs == 0
  SORT decl.module, decl.name
  RETURN {module: decl.module, name: decl.name, kind: decl.kind}
```

Interpretation:
- `def` with 0 refs and `_proof_` in name: auto-generated, safe to ignore
- `structure` with 0 refs: likely a genuine socket (unproven interface)
- `axiom`/`opaque` with 0 refs: foundational assumption, verify intentional

## 4. Transitive Closure — Which Proofs Depend on τ-Stability?

```aql
FOR v IN 1..10 INBOUND "lean_decls/ChiralTLDescent_chiral_left_tau_ideal" references
  COLLECT name = v.name
  SORT name
  RETURN name
```

Shows all declarations that transitively depend on the left span τ-ideal theorem.
If this set is empty, no downstream proof uses the stability certificate yet.

## 5. AST Depth — Proof Complexity by Cell

```aql
FOR decl IN lean_decls
  FILTER decl.name IN [
    "ChiralTLDescent.chiral_left_tau_ideal",
    "ChiralTLDescent.chiral_kernel_is_left_tau_ideal",
    "ChiralTLDescent.chiral_right_tau_ideal",
    "ChiralTLDescent.chiral_right_kernel_tau_ideal"
  ]
  LET root = FIRST(FOR e IN has_syntax FILTER e._from == decl._id RETURN DOCUMENT(e._to))
  LET nodeCount = LENGTH(FOR v IN 1..50 OUTBOUND root ast_child RETURN 1)
  RETURN {cell: decl.name, ast_nodes: nodeCount}
```

Lower AST node counts indicate simpler proofs (kernel versions should be smaller than span versions).

## 6. Cross-Module Coupling — BraidIdealDescent ↔ ChiralTLDescent

```aql
FOR a IN lean_decls
  FILTER a.module == "ChiralTLDescent"
  FOR b IN lean_decls
    FILTER b.module == "BraidIdealDescent"
    FOR v, e IN 1..5 OUTBOUND a._id references
      FILTER v._id == b._id
      RETURN {from: a.name, to: b.name, path_length: LENGTH(e)}
```

All paths from ChiralTLDescent to BraidIdealDescent should go through the τ-stability spine.

## 7. Most-Referenced Atoms — Identify Core Lemmas

```aql
FOR edge IN references
  COLLECT target = edge._to WITH COUNT INTO c
  SORT c DESC LIMIT 20
  LET doc = DOCUMENT(target)
  RETURN {name: doc.name, module: doc.module, used_by: c}
```

Top hits (verified 2026-06-16):
| Lemma | Module | Used By |
|---|---|---|
| `M2C` | ChiralCausalCone | 81 |
| `σPlus` | ChiralCausalCone | 40 |
| `σMinus` | ChiralCausalCone | 40 |
| `σ3c` | ChiralCausalCone | 36 |
| `SpinPair` | ChiralTensorRecoupling | 23 |

## 8. Vacuity Scan — AST Text Search for Suspicious Patterns

```aql
FOR node IN syntax_nodes
  FILTER node.kind == "atom"
  FILTER node.value IN ["sorry", "admit", "trivial"]
  LET decl = FIRST(FOR e IN has_syntax FILTER e._to == node._id RETURN DOCUMENT(e._from))
  RETURN {decl: decl.name, suspicious: node.value, syntaxKind: node.syntaxKind}
```

Expected result: **0 records** — the codebase is zero-sorry.

## 9. Module-Level Proof Inventory

```aql
FOR decl IN lean_decls
  COLLECT module = decl.module INTO group
  LET theorems = LENGTH(FOR d IN group FILTER d.decl.kind == "theorem" RETURN 1)
  LET defs = LENGTH(FOR d IN group FILTER d.decl.kind == "def" RETURN 1)
  LET axioms = LENGTH(FOR d IN group FILTER d.decl.kind == "axiom" RETURN 1)
  SORT module
  RETURN {module, theorems, defs, axioms, total: LENGTH(group)}
```

## 10. Full Chiral Stability Certificate (Single Query)

```aql
LET stability_cells = ["chiral_left_tau_ideal","chiral_kernel_is_left_tau_ideal",
                        "chiral_right_tau_ideal","chiral_right_kernel_tau_ideal"]
FOR cell_name IN stability_cells
  LET decl = FIRST(FOR d IN lean_decls FILTER d.name == CONCAT("ChiralTLDescent.", cell_name) RETURN d)
  LET deps = LENGTH(FOR v IN 1..5 OUTBOUND decl._id references RETURN 1)
  LET users = LENGTH(FOR v IN 1..5 INBOUND decl._id references RETURN 1)
  RETURN {
    cell: cell_name,
    kind: decl.kind,
    exists: decl != null,
    transitive_deps: deps,
    transitive_users: users
  }
```

Expected: all 4 cells exist, transitive_deps ≥ 15, kind = "theorem".

## Import Statistics (2026-06-16, full repo)

```
bridge_records:     4,898
lean_decls:           334
syntax_nodes:      14,325
references:         1,702
ast_child:         13,991
has_syntax:           334
sockets (0 refs):      8
```

Chiral Pauli basis (`M2C`, `σPlus`, `σMinus`, `σ3c`) accounts for 197 of 1,702 reference edges (11.6%).
The τ-stability 4-cell matrix is complete with 9-10 direct dependencies each.
