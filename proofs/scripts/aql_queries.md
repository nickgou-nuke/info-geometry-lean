# AQL Query Arsenal for the Lean Proof Graph

Run queries from `/home/goutev/auto/proofs` with the dependency-light HTTP runner:

```bash
source /home/goutev/.config/arango/env.sh
python3 tools/lean_graph/aql_query.py <<'AQL'
RETURN LENGTH(FOR d IN syntax_decls RETURN 1)
AQL
```

You can also run queries in the ArangoDB web UI using the endpoint from
`/home/goutev/.config/arango/env.sh` (currently `http://127.0.0.1:8530`) or via
`python-arango` when it is installed.

## 0. Current syntax-only graph health and search

The currently loaded lightweight AST graph uses:

- `syntax_decls`
- `syntax_nodes`
- `ast_child`
- `decl_root`

Use this before writing code:

```aql
RETURN {
  syntax_decls: LENGTH(FOR x IN syntax_decls RETURN 1),
  syntax_nodes: LENGTH(FOR x IN syntax_nodes RETURN 1),
  ast_child: LENGTH(FOR x IN ast_child RETURN 1),
  decl_root: LENGTH(FOR x IN decl_root RETURN 1)
}
```

Declaration search:

```aql
FOR d IN syntax_decls
  FILTER CONTAINS(d.name, 'Cuntz')
     OR CONTAINS(d.name, 'Super')
     OR CONTAINS(d.name, 'Poincare')
     OR CONTAINS(d.name, 'Lorentz')
  SORT d.name
  LIMIT 100
  RETURN {name: d.name, keyword: d.keyword, range: d.range}
```

AST identifier/doc search:

```aql
LET terms = ['affineSuperBracket', 'supercharge', 'pauliMomentum', 'boostX']
FOR n IN syntax_nodes
  LET txt = HAS(n,'raw') ? n.raw : (HAS(n,'value') ? n.value : '')
  FILTER txt != ''
  LET hits = (FOR t IN terms FILTER CONTAINS(txt, t) RETURN t)
  FILTER LENGTH(hits) > 0
  COLLECT decl = n.declName INTO group = {txt, range:n.range, hits:hits}
  SORT decl
  LIMIT 80
  RETURN {decl, hits: UNIQUE(FLATTEN(group[*].hits)), samples: SLICE(group,0,3)}
```

## 1. Anti-pattern: theorems using `ring` on Matrix/Tensor types

```aql
FOR decl IN declarations
  FILTER decl.name LIKE "%_sq" OR decl.name LIKE "%idempotent%"
  FOR v IN 1..1 OUTBOUND decl depends_on
    FILTER v.name LIKE "%Matrix%" OR v.name LIKE "%Tensor%"
    OR v.name LIKE "%SpinPair%"
    RETURN { theorem: decl.name, depends_on_matrix: v.name }
```

## 2. Top 20 most-depended-on lemmas (reuse analysis)

```aql
FOR dep IN depends_on
  COLLECT target = dep._to WITH COUNT INTO freq
  SORT freq DESC
  LIMIT 20
  RETURN { name: DOCUMENT(target).name, used_by: freq }
```

## 3. Full dependency tree of e_sq (depth 5)

```aql
FOR v, e, p IN 1..5 OUTBOUND "declarations/ChiralTensorRecoupling_e_sq" depends_on
  RETURN { name: v.name, depth: LENGTH(p.edges[*]) }
```

## 4. Find all socketed (unproved) declarations

```aql
FOR decl IN declarations
  FILTER decl.kind == "def"
  LET uses = (FOR v IN 1..1 INBOUND decl depends_on RETURN 1)
  FILTER LENGTH(uses) > 5  -- likely a structure with many fields
  FILTER decl.name LIKE "%Socket%" OR decl.name LIKE "%Target%"
  RETURN { name: decl.name, module: decl.module }
```

## 5. Tactic profiling by module

Note: requires tactic extraction (Phase 2 of pipeline).
Shown here as a target query.

```aql
FOR tactic IN tactics
  COLLECT name = tactic.name WITH COUNT INTO freq
  SORT freq DESC
  LIMIT 20
  RETURN { tactic: name, frequency: freq }
```

## 6. Dependency depth distribution

```aql
FOR decl IN declarations
  LET deps = LENGTH(FOR v IN 1..10 OUTBOUND decl depends_on RETURN v)
  COLLECT depth = deps WITH COUNT INTO count
  SORT depth ASC
  RETURN { depth, count }
```

## 7. Find circular dependencies

```aql
FOR v, e IN 2..10 OUTBOUND "declarations/ChiralTensorRecoupling_e_sq" depends_on
  FILTER v._id == "declarations/ChiralTensorRecoupling_e_sq"
  RETURN { cycle_length: LENGTH(e) }
```

## 8. Module-level: what does each module export?

```aql
FOR decl IN declarations
  COLLECT module = decl.module INTO group
  RETURN {
    module,
    theorem_count: LENGTH(FOR d IN group FILTER d.decl.kind == "theorem" RETURN 1),
    def_count: LENGTH(FOR d IN group FILTER d.decl.kind == "def" RETURN 1)
  }
```

## 9. Dependency bridge: what connects module A to module B?

```aql
FOR a IN declarations
  FILTER a.module == "ChiralCausalCone"
  FOR b IN declarations
    FILTER b.module == "TLChain"
    FOR v, e IN 1..5 OUTBOUND a depends_on
      FILTER v._id == b._id
      RETURN { from: a.name, to: b.name, path_length: LENGTH(e) }
```

## 10. Isolation check: declarations with NO dependencies

```aql
FOR decl IN declarations
  LET deps = (FOR v IN 1..1 OUTBOUND decl depends_on RETURN 1)
  FILTER LENGTH(deps) == 0
  RETURN decl.name
```

## 11. Syntax → Environment bridge coverage

Requires `tools/lean_graph/ingest_bridge_to_arango.py --execute`.

```aql
LET total = LENGTH(FOR s IN syntax_decls RETURN 1)
LET bridged = LENGTH(FOR e IN syntax_elaborates_to RETURN 1)
RETURN { syntax_decls: total, bridged, missing: total - bridged }
```

## 12. KMS declarations with source ranges and dependencies

```aql
FOR s IN syntax_decls
  FILTER s.name LIKE "SupergradedCuntzBdG.%KMS%"
  FOR env IN 1..1 OUTBOUND s syntax_elaborates_to
    RETURN {
      name: s.name,
      keyword: s.keyword,
      range: s.range,
      env_kind: env.kind,
      deps: (
        FOR dep IN 1..1 OUTBOUND env depends_on
          RETURN dep.name
      )
    }
```

## 13. GEPA universe: tactics under declarations depending on KMS

Requires `tools/lean_graph/import_arango.py --execute`.

```aql
FOR kms IN lean_decls
  FILTER kms.name == "SupergradedCuntzBdG.KMSStateSocket"
  FOR thm IN 1..2 INBOUND kms references
    FOR ast_root IN 1..1 OUTBOUND thm has_syntax
      FOR ast_node IN 1..15 OUTBOUND ast_root ast_child
        FILTER ast_node.syntaxKind LIKE "%Tactic%"
           OR ast_node.ident IN ["simp", "rw", "exact", "simpa", "unfold", "dsimp"]
           OR ast_node.atom IN ["simp", "rw", "exact", "simpa", "unfold", "dsimp"]
        RETURN {
          theorem: thm.name,
          syntaxKind: ast_node.syntaxKind,
          tactic: HAS(ast_node, "ident") ? ast_node.ident : ast_node.atom,
          range: ast_node.range
        }
```

## 14. GEPA universe: `sorry` scan through AST

```aql
FOR decl IN lean_decls
  FOR ast_root IN 1..1 OUTBOUND decl has_syntax
    FOR ast_node IN 1..25 OUTBOUND ast_root ast_child
      FILTER ast_node.atom == "sorry" OR ast_node.ident == "sorry"
      RETURN { declaration: decl.name, range: ast_node.range }
```
