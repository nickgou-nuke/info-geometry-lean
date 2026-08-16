# Complete Python Code Property Graph (CPG) + ArangoDB Analysis Methodology

## 1. Architectural Status & Purpose

This HOWTO documents the repository-owned **Python Code Property Graph (CPG) and Discrete Graph Operator Analysis System** in ArangoDB, serving as the static code analysis counterpart to Lean's `ASTAQLHASH-HOWTO.md` and `InfoTree` framework.

The authoritative implementation surfaces are:
- `tools/infra/python_ast_dag_ingest.py`: CPython ASDL AST extraction, de Bruijn $\alpha$-hash and $\pi_{\text{shape}}$ factorization, dynamic dispatch annotation, and bulk streaming into ArangoDB.
- `tools/infra/python_dag_dependency_oracle.py`: High-speed inverted token dependency graph and discrete reachability analyzer.
- `tools/quality/check_python_cpg_gate.py`: CI gatekeeper enforcing zero cache-destructive hazards, reachability safety, and machine telemetry emission.
- `tools/quality/test_python_cpg_oracle_adversarial.py`: Curated 10-case adversarial fixture suite testing precision, recall, and mutation sensitivity.
- `reports/python_cpg_manifest.json`: Machine-generated telemetry block containing commit SHA, scope fingerprint, and verified metrics.

---

## 2. Epistemic Foundations & Complexity Bounds

### 2.1. Asymptotic Computational Complexity
The global graph construction and reachability analysis eliminates the naive $O(N \cdot M)$ cross-product search via an inverted token index:
$$T_{\mathrm{scan}} = O(\text{input size} + |V| + |E|)$$
with expected $O(1)$ set/hash lookups per token match and single-pass multi-source BFS from authoritative entrypoints.

### 2.2. Model-Bounded Semantic Guarantees
1. **`CPG_ORPHAN_CANDIDATE`:**  
   $$m \in \operatorname{ker}(\partial_{\mathrm{in}}) \setminus \mathcal{R}_{\mathrm{entry}} \quad \Longleftrightarrow \quad d_{\mathrm{in}}^{\mathrm{import}}(m) = 0 \ \land \ d_{\mathrm{in}}^{\mathrm{call}}(m) = 0 \ \land \ d_{\mathrm{in}}^{\mathrm{shell}}(m) = 0 \ \land \ \operatorname{Ref}_{\mathrm{docs}}(m) = 0$$
   *Definition:* A script with no detected incoming dependency or reference within the declared analysis scope and modeled CPG universe. This is a model-relative safety certificate, not an unconditioned semantic proof over arbitrary unmodeled dynamic Python runtimes.
2. **Hazard Predicate:**  
   PASS on the hazard gate proves that **no forbidden executable path to cache-destructive operations (`lake clean`, `.lake/` deletion) exists in the modeled call/system AST graph**. Pure docstrings or comments mentioning forbidden commands are recognized as documentation and immunized against false positives.

---

## 3. Three-Layer Hybrid CPG Architecture in ArangoDB

```text
Database: `infogeometry` (http://127.0.0.1:8530)

📦 Document Collections:
├── python_modules      (Relative path, line count, module AST hash, compiler root flag)
└── python_ast_nodes    (AST node type, line/col, shape_hash, alpha_hash, metrics, hazard_markers)

🔗 Edge Collections:
├── python_ast_edges    (Parent -> Child syntactic hierarchy)
├── python_call_edges   (Caller -> Callee inter-procedural calls with is_dynamic flag and confidence weights)
└── python_import_edges (Module -> Module dependencies with symbol payload)
```

---

## 4. Discrete Graph Operators & AQL Query Recipes

### 4.1. Exact Structural Clone Clustering via $\pi_{\mathrm{shape}}$
Groups functions and classes sharing identical control-flow and expression structures:
```aql
FOR doc IN python_ast_nodes
  FILTER doc.node_type IN ['FunctionDef', 'ClassDef']
  COLLECT shape = doc.shape_hash INTO group
  FILTER LENGTH(group) > 1
  SORT LENGTH(group) DESC
  RETURN {
    shape_hash: shape,
    duplicate_count: LENGTH(group),
    instances: group[*].doc.file
  }
```

### 4.2. Causal Cones & Hazard Paths ($\mathcal{C}^+$)
Traverses the call graph to detect whether any function execution path reaches forbidden operations:
```aql
FOR v, e, p IN 1..6 OUTBOUND 'python_ast_nodes/node_root' python_call_edges
  FILTER LENGTH(v.hazard_markers) > 0
  RETURN {
    caller_path: p.vertices[*].name,
    files: p.vertices[*].file,
    hazards: v.hazard_markers
  }
```

### 4.3. Discrete In-Degree Boundary Operator ($d_{\mathrm{in}}$) & Orphan Identification
```aql
FOR mod IN python_modules
  FILTER mod.is_compiler_root == false
  LET in_imports = (
    FOR e IN python_import_edges
      FILTER e._to == CONCAT('python_modules/', mod._key)
      RETURN e
  )
  LET in_calls = (
    FOR e IN python_call_edges
      FILTER e._to == CONCAT('python_ast_nodes/', mod._key)
      RETURN e
  )
  FILTER LENGTH(in_imports) == 0 AND LENGTH(in_calls) == 0
  RETURN {
    orphan_candidate: mod.file,
    lines: mod.num_lines,
    in_degree: 0
  }
```

---

## 5. Adversarial Validation Suite & Telemetry

### Running the Adversarial Completeness Test Suite
```bash
python3 tools/quality/test_python_cpg_oracle_adversarial.py
```
*Evaluates 10 curated test fixtures covering direct imports, dynamic dispatch, shell wrappers, AST subprocess hazards, concatenation hazards, docstring false-positive immunity, genuine orphans, registered plugins, cyclic imports, and mutation sensitivity.*

### Running the CI Quality Gate & Telemetry Manifest
```bash
python3 tools/quality/check_python_cpg_gate.py
```
*Emits the machine-readable manifest to `reports/python_cpg_manifest.json`.*
