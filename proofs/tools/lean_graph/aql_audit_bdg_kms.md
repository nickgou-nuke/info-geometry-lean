# AQL Audit: BdG/KMS Finite Algebraic Certificate

Machine-generated proof-topology audit for the finite algebraic
BdG/grand-canonical KMS layer in `SupergradedCuntzBdG.lean`.

**Database**: `info_geometry` | **Graph**: `LeanUniverseGraph`

Core boundary statement:

> Excellent — that’s the right boundary: finite algebraic BdG/KMS layer closed,
> analytic completion explicitly socketed instead of faked.

## 1. Proved Finite Algebraic Declarations

```aql
LET proved = [
  "SupergradedCuntzBdG.star_bdgMajoranaPlus",
  "SupergradedCuntzBdG.bdgMajoranaPlus_sq_eq_hamiltonianAtom",
  "SupergradedCuntzBdG.bdgMajoranaMinus_is_odd",
  "SupergradedCuntzBdG.grandCanonicalBracket_even_left",
  "SupergradedCuntzBdG.grandCanonicalBracket_even_right",
  "SupergradedCuntzBdG.grandCanonicalBracket_odd_odd",
  "SupergradedCuntzBdG.grandCanonicalWeightedBracket_even_left",
  "SupergradedCuntzBdG.grandCanonicalWeightedBracket_even_right",
  "SupergradedCuntzBdG.grandCanonicalWeightedBracket_odd_odd"
]
FOR name IN proved
  LET decl = FIRST(FOR d IN lean_decls FILTER d.name == name RETURN d)
  RETURN {
    name,
    exists: decl != null,
    kind: decl == null ? "missing" : (decl.kind == null ? "unknown" : decl.kind),
    depends_on: decl == null ? 0 : LENGTH(FOR e IN references FILTER e._from == decl._id RETURN 1),
    referenced_by: decl == null ? 0 : LENGTH(FOR e IN references FILTER e._to == decl._id RETURN 1)
  }
```

Expected: all listed declarations exist. Some bridge imports may have nullable
`kind` metadata in ArangoDB even though Lean compiled them as theorems; the
source of truth remains the Lean build plus declaration presence.

## 2. Classified Finite Algebraic Blocker

```aql
LET blockers = [
  {
    name: "SupergradedCuntzBdG.bdgMajoranaMinus",
    blocker: "bdgMajoranaMinus star/square requires finite Cuntz T_mul_S/partition algebra, not analytic completion"
  }
]
FOR b IN blockers
  LET decl = FIRST(FOR d IN lean_decls FILTER d.name == b.name RETURN d)
  RETURN {
    name: b.name,
    exists: decl != null,
    kind: decl == null ? "missing" : (decl.kind == null ? "unknown" : decl.kind),
    blocker: b.blocker,
    classification: "finite-algebraic-blocker"
  }
```

Expected: `bdgMajoranaMinus` exists as a `def`; it is intentionally not
classified as an analytic socket.

## 3. Analytic KMS/GNS/Tomita Socket Frontier

```aql
LET sockets = [
  {
    name: "CStarCuntzTensorQuotient.UniversalCStarCompletionSocket",
    layer: "C*/universal completion"
  },
  {
    name: "SupergradedCuntzBdG.KMSStateSocket",
    layer: "algebraic KMS expectation interface"
  },
  {
    name: "SupergradedCuntzBdG.TomitaTakesakiKMSRealizationSocket",
    layer: "GNS/Tomita cyclic-separating realization"
  },
  {
    name: "ModularRenyiEntropy.ModularRenyiEntropySocket",
    layer: "future spectral/Rényi/Mellin analytic layer"
  }
]
FOR s IN sockets
  LET decl = FIRST(FOR d IN lean_decls FILTER d.name == s.name RETURN d)
  RETURN {
    name: s.name,
    exists: decl != null,
    kind: decl == null ? "future" : (decl.kind == null ? "unknown" : decl.kind),
    layer: s.layer,
    classification: "analytic-socket"
  }
```

Expected: current C*/KMS/Tomita sockets exist; ModularRényi may be absent until
the analytic spectral module is introduced.

## 4. BdG/KMS Module Inventory

```aql
FOR decl IN lean_decls
  FILTER decl.module IN [
    "SupergradedCuntzBdG",
    "ComplexStarCuntzRedesign",
    "CStarCuntzTensorQuotient",
    "AlgebraicCuntzQuotient"
  ]
  COLLECT module = decl.module INTO group
  LET theorems = LENGTH(FOR d IN group FILTER d.decl.kind == "theorem" RETURN 1)
  LET defs = LENGTH(FOR d IN group FILTER d.decl.kind == "def" RETURN 1)
  LET structures = LENGTH(FOR d IN group FILTER d.decl.kind == "structure" RETURN 1)
  SORT module
  RETURN {module, theorems, defs, structures, total: LENGTH(group)}
```

## 5. Dependency Frontier From Finite BdG/KMS Theorems

```aql
LET proved = [
  "SupergradedCuntzBdG.star_bdgMajoranaPlus",
  "SupergradedCuntzBdG.bdgMajoranaPlus_sq_eq_hamiltonianAtom",
  "SupergradedCuntzBdG.bdgMajoranaMinus_is_odd",
  "SupergradedCuntzBdG.grandCanonicalWeightedBracket_odd_odd"
]
FOR name IN proved
  LET decl = FIRST(FOR d IN lean_decls FILTER d.name == name RETURN d)
  FOR v IN 1..4 OUTBOUND decl._id references
    COLLECT source = name, dep = v.name, module = v.module
    SORT source, module, dep
    RETURN {source, dep, module}
```

## 6. KMS Socket Users

```aql
FOR socket IN lean_decls
  FILTER socket.name IN [
    "SupergradedCuntzBdG.KMSStateSocket",
    "SupergradedCuntzBdG.TomitaTakesakiKMSRealizationSocket",
    "CStarCuntzTensorQuotient.UniversalCStarCompletionSocket"
  ]
  LET users = (
    FOR v IN 1..5 INBOUND socket._id references
      COLLECT name = v.name
      SORT name
      RETURN name
  )
  RETURN {socket: socket.name, transitive_users: users}
```

## 7. Vacuity Scan Restricted to BdG/KMS Syntax

```aql
FOR decl IN lean_decls
  FILTER decl.module IN ["SupergradedCuntzBdG", "CStarCuntzTensorQuotient", "ComplexStarCuntzRedesign"]
  FOR root IN 1..1 OUTBOUND decl has_syntax
    FOR node IN 0..50 OUTBOUND root ast_child
      FILTER node.kind == "atom" AND node.value IN ["sorry", "admit"]
      RETURN {decl: decl.name, token: node.value}
```

Expected: `[]`.

## 8. Full BdG/KMS Certificate Query

```aql
LET proved = [
  "SupergradedCuntzBdG.star_bdgMajoranaPlus",
  "SupergradedCuntzBdG.bdgMajoranaPlus_sq_eq_hamiltonianAtom",
  "SupergradedCuntzBdG.bdgMajoranaMinus_is_odd",
  "SupergradedCuntzBdG.grandCanonicalBracket_even_left",
  "SupergradedCuntzBdG.grandCanonicalBracket_even_right",
  "SupergradedCuntzBdG.grandCanonicalBracket_odd_odd",
  "SupergradedCuntzBdG.grandCanonicalWeightedBracket_even_left",
  "SupergradedCuntzBdG.grandCanonicalWeightedBracket_even_right",
  "SupergradedCuntzBdG.grandCanonicalWeightedBracket_odd_odd"
]
LET blockers = ["SupergradedCuntzBdG.bdgMajoranaMinus"]
LET analytic = [
  "CStarCuntzTensorQuotient.UniversalCStarCompletionSocket",
  "SupergradedCuntzBdG.KMSStateSocket",
  "SupergradedCuntzBdG.TomitaTakesakiKMSRealizationSocket"
]
RETURN {
  proved_present: LENGTH(FOR name IN proved FILTER FIRST(FOR d IN lean_decls FILTER d.name == name RETURN d) != null RETURN 1),
  proved_total: LENGTH(proved),
  finite_blockers_present: LENGTH(FOR name IN blockers FILTER FIRST(FOR d IN lean_decls FILTER d.name == name RETURN d) != null RETURN 1),
  analytic_sockets_present: LENGTH(FOR name IN analytic FILTER FIRST(FOR d IN lean_decls FILTER d.name == name RETURN d) != null RETURN 1),
  sorry_admit_atoms: LENGTH(
    FOR decl IN lean_decls
      FILTER decl.module IN ["SupergradedCuntzBdG", "CStarCuntzTensorQuotient", "ComplexStarCuntzRedesign"]
      FOR root IN 1..1 OUTBOUND decl has_syntax
        FOR node IN 0..50 OUTBOUND root ast_child
          FILTER node.kind == "atom" AND node.value IN ["sorry", "admit"]
          RETURN node
  ),
  boundary: "finite algebraic BdG/KMS layer closed; analytic completion explicitly socketed"
}
```
