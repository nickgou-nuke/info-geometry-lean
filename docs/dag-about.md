# The DAG Pipeline: InfoTree Category Homotopy, Discrete Operators, and ArangoDB Streaming

This document describes the **nervous system** of the repository: the `lean/DAG/` subsystem, its Python ingestion infrastructure, and how the entire 20,000+ file Lean codebase is externalized into a queryable, agent-navigable knowledge graph with chiral Hodge operators, exact morphisms, and KMS-weighted modular flow.

---

## 1. Why This Is Not Just Metadata

The exported declaration graph is not bookkeeping. It is a finite, explicit object induced by kernel-checked declarations and their dependency structure. That makes higher-level analysis legitimate on the graph representation itself:

- **Homological summaries**: cycles, Betti-style structure, exactness of transport corridors
- **Spectral summaries**: Laplacians, gap-like bottlenecks, chiral Hodge decomposition
- **Categorical views**: exactness, colimits, functorial mappings between sub-DAGs
- **Causal/process-flow summaries**: roots, shells, defects, and transport corridors
- **Quantum-statistical structure**: Bost-Connes KMS states as probability measures on the declaration graph

The graph exposes global structural facts that ordinary file-by-file reading cannot surface. It remains subordinate to Lean source: Lean source decides what is true; graph invariants reveal how the checked theory is organized, stressed, and routed.

---

## 2. The Pipeline: From Lean Kernel to ArangoDB

```
Lean InfoTree
    │
    ▼
InfoTreeExtract / RawInfoTreeExport / ExprFingerprint
    │
    ▼
Graph Construction (SCC + Dominators + Topo)
    │
    ▼
Chiral Hodge Operators on the DAG
    │
    ▼
Exact Morphisms + Homological Algebra
    │
    ▼
Category Homotopy + Process Flow
    │
    ▼
KMS Branching + Lambda Calculus PHOAS Layer
    │
    ▼
ArangoDB Streaming (Python Infrastructure)
    │
    ▼
Agent-Navigable Knowledge Graph
```

---

## 3. InfoTree Extraction (Lean-side)

| File | Purpose |
|------|---------|
| `lean/DAG/InfoTreeExtract.lean` | Metaprogram that walks Lean's `InfoTree`, extracting every declaration, type, expression, and tactic goal into JSON-ready records with `typeFingerprint`, `valueFingerprint`, and `shapeHash`. |
| `lean/DAG/RawInfoTreeExport.lean` | Full raw dump of the compiler's internal representation, including binding sites, local contexts, and tactic traces. |
| `lean/DAG/ExprFingerprint.lean` | Structural hashing of Lean expressions (not value equality) so that shape-equivalent proofs across modules collapse to the same hash. |

Key insight: `shapeHash` is a `UInt64` field. It enables lossless projection from enriched overlays back to raw compiler-backed declarations, even when the raw InfoTree coverage is incomplete.

---

## 4. Graph Construction (SCC + Dominators + Topo)

| File | Purpose |
|------|---------|
| `lean/DAG/Basic.lean` | `Graph α`, `HydratedGraph α`, `EdgeKind` enum (declaration, definition, tactic, projection, transport). |
| `lean/DAG/SCC.lean` | Tarjan's algorithm on the 20,000+ file declaration graph. |
| `lean/DAG/Hydrate.lean` | Chains Tarjan → SCC-DAG → topological sort → bitset dominator computation. |
| `lean/DAG/Dominators.lean` | Forward/reverse dominator trees for impact and vulnerability analysis (which declarations are load-bearing for a given socket). |
| `lean/DAG/Topo.lean` | BFS in-degree topological sort on the compressed SCC DAG. |
| `lean/DAG/Util.lean` | Shared helpers (array operations, name utilities). |

---

## 5. Chiral Hodge Operators on the Declaration Graph

This is the mathematically deep layer. The declaration DAG is promoted from a simple directed graph to a **spinorial, chiral Hodge-decomposable complex**.

| File | Purpose |
|------|---------|
| `lean/DAG/GraphHodge.lean` | Constructs the combinatorial Laplacian `L = D - A` of the declaration DAG. Defines `harmonicProjection`, `harmonicDecomposition` (gradient + curl + harmonic), and `hodgeRank` (Betti-style dimension counts). |
| `lean/DAG/GraphHodgeBridge.lean` | Bridges combinatorial Hodge theory to the spectral chiral projectors from `ChiralHodgeDecomposition.lean`. Implements `spectralChiralPlusProjector`, `spectralChiralMinusProjector`, `rootDiracOddLane` (Dirac operator on the DAG), and the Lichnerowicz formula on the declaration graph. |
| `lean/DAG/ChiralDiracAnticommutation.lean` | Anticommutation relations `{γⁱ, γʲ} = 2g^{ij}` lifted to the graph metric. |
| `lean/DAG/DiracLaplacian.lean` | The square of the Dirac operator on the DAG equals the Laplacian plus curvature term: `D² = L + curvature`. |
| `lean/DAG/ConnesHodgeBridge.lean` | Bridges to Connes' noncommutative geometry Hodge operators. |
| `lean/DAG/HodgeTheorems.lean` | Hodge decomposition theorems on the DAG: every function on declarations splits uniquely into exact, coexact, and harmonic components. |

**The chiral Hodge operators on the lambda calculus graph**: When declarations are themselves lambda terms (PHOAS nodes, see §8), the chiral projectors split the space of proof terms into left-moving (bosonic/even) and right-moving (fermionic/odd) components. The Dirac operator on this graph computes the "supercharge" of a proof term, and the Lichnerowicz formula relates the supercharge square to the Laplacian plus a curvature correction that measures how much the proof term "twists" across module boundaries.

---

## 6. Exact Morphisms and Homological Algebra on the DAG

| File | Purpose |
|------|---------|
| `lean/DAG/ExactMorphism.lean` | Exactness auditing: given a chain complex `... → A → B → C → ...`, computes `ker(f) / img(g)` and verifies exactness at every node. |
| `lean/DAG/ExactMorphismTest.lean` | Test harness for exact morphisms on real declaration chains. |
| `lean/DAG/Betti.lean` | Computes Betti numbers `β_k = rank(H_k)` of the declaration complex. |
| `lean/DAG/GeneralizedTwoComplex.lean` | Promotes the declaration DAG to a 2-category (objects = modules, 1-morphisms = imports, 2-morphisms = transport/tactic bridges). |
| `lean/DAG/TwoComplex.lean` | The 2-categorical structure of the declaration graph. |
| `lean/DAG/TwoComplexColimitRecursor.lean` | Colimit recursion computes the homotopy limit of the declaration 2-complex. |
| `lean/DAG/TwoComplexFunctor.lean` | Functorial mappings between 2-complexes of sub-DAGs. |
| `lean/DAG/TwoComplexKasparov.lean` | Kasparov-style bivariant K-theory on the 2-complex, connecting to the KK-theory of the operator algebras. |
| `lean/DAG/TripleHomomorphismExport.lean` | Triple system homomorphisms for the enriched graph. |
| `lean/DAG/TripleSystem.lean` | RDF-style triple system underlying the enriched export. |

**Category homotopy on the DAG**: The declaration graph is not just a category—it is a category **internal to the homotopy type** of the theory. The 2-complex captures the homotopy between different import paths and transport bridges. The Betti numbers measure the "holes" in the dependency structure: a high Betti number indicates a module that can be reached by multiple independent paths, which correlates with high socket debt.

---

## 7. Analysis, Impact, and Process Flow

| File | Purpose |
|------|---------|
| `lean/DAG/Analysis.lean` | `pathCountFrom`, `distanceMap`, `influenceFrom`, `vulnerabilityOf`, `rootSet`, `capstoneSet`. |
| `lean/DAG/Impact.lean` | Forward/reverse BFS reachability lifted from SCC level back to declaration level. |
| `lean/DAG/ProcessFlowExport.lean` | Extracts categorical process flows: root declarations → transport corridors → capstone theorems. |
| `lean/DAG/CategoryBridge.lean` | Bridges between the DAG category and the internal category theory of `InfoGeometry/Categorical/`. |
| `lean/DAG/Functor.lean` | Functorial mappings between sub-DAGs (e.g., `PrimeSUSYVacuum` ↦ `GrandSynthesis`). |
| `lean/DAG/LiftNaturality.lean` | Naturality conditions for lifts across the DAG. |
| `lean/DAG/CocycleBridge.lean` | Cocycle conditions for transport across the DAG. |
| `lean/DAG/CocycleBridgeActivation.lean` | Activation protocol for cocycle bridges. |
| `lean/DAG/SubgraphMatch.lean` | Subgraph isomorphism for finding isomorphic declaration patterns. |
| `lean/DAG/Search.lean` | Graph search primitives. |
| `lean/DAG/SearchByHash.lean` | Native Lean-side hash search over imported modules. |
| `lean/DAG/FinalSearch.lean` | Terminal search protocol for socket debt frontier. |

**Process flow as category homotopy**: A "process flow" in this repository is a functor from the free category generated by the import DAG to the category of Lean modules and transport morphisms. The homotopy between two process flows is a sequence of transport bridges that refactors one dependency chain into another while preserving kernel-checked semantics.

---

## 8. KMS Branching on the DAG

| File | Purpose |
|------|---------|
| `lean/DAG/KMSBranching.lean` | The modular flow of Tomita-Takesaki is lifted to the DAG. Each SCC gets a modular weight `ω_β(n) = n^{-β}`, and the branching structure encodes the **Bost-Connes KMS state** as a probability measure on the declaration graph. |
| `lean/DAG/HarmonicKMS.lean` | Harmonic analysis of the KMS-weighted Laplacian. |
| `lean/DAG/BlockDecomposition.lean` | Block decomposition of the KMS-weighted adjacency matrix. |
| `lean/DAG/GradedBottPeriodicity.lean` | Bott periodicity in the KMS-graded DAG. |
| `lean/DAG/GradedBottInclusion.lean` | Inclusion maps between KMS-graded subcomplexes. |

The Bost-Connes KMS state on the DAG is the unique KMS state for the modular flow at inverse temperature β = 1. It assigns to each strongly connected component a weight proportional to `|SCC|^{-β}`, normalized over the entire graph. This means that the "importance" of a module in the repository is not just its number of imports, but its position in the modular flow hierarchy—exactly as in the Bost-Connes C*-algebra, where the modular group acts on the automorphisms of the Bost-Connes algebra.

---

## 9. Lambda Calculus Graph (PHOAS)

| File | Purpose |
|------|---------|
| `lean/DAG/PHOASExpressionLayer.lean` | **Higher-Order Abstract Syntax** layer for the DAG. Declarations that are themselves lambda terms get encoded as PHOAS nodes, allowing: De Bruijn index tracking across module boundaries, beta-eta equivalence classes collapsed by `shapeHash`, and the lambda calculus graph as a subgraph of the declaration DAG. |

The PHOAS layer is what makes the "chiral Hodge operators on the lambda calculus graph" precise. The space of proof terms (lambda expressions) is a vector space over the field of definitions. The chiral projectors split this space into even-parity (bosonic) and odd-parity (fermionic) proof terms. The Dirac operator computes the proof-theoretic "supercharge" of a term. The Lichnerowicz formula on this graph says that the supercharge squared equals the proof-theoretic Laplacian plus a curvature term measuring noncommutativity of the lambda term's redex structure.

---

## 10. ArangoDB Streaming (Python Infrastructure)

| Script/Package | Purpose |
|----------------|---------|
| `scratch/populate_arangodb.py` | Streams `decls.jsonl`, `decl_edges.jsonl`, `ig_nodes_enriched.jsonl`, `ig_edges_enriched.jsonl` into ArangoDB collections (`Thoughts`, `CausalLinks`). |
| `scratch/query_arangodb.py` | AQL query harness for traversing the enriched graph. |
| `src/infogeometry/lean/DAG/ingest.py` | Part of the DAG subsystem, triggers ingestion after each `lake build`. |
| `src/infogeometry/lean/DAG/docker-compose.yml` | Spins up ArangoDB on port `8530`. |
| `src/infogeometry/lean/scripts/DAG/Exploration/` | Explorer agents (NaturalityPromoter, SquarePromoter, Betti, etc.) that query the live ArangoDB instance. |
| `ASTAQLHASH-HOWTO.md` | Canonical reference for hash-based search: `materialize_lossless_infotree.py` projects raw InfoTree nodes as enriched overlays. |

**The Hive Memory**: ArangoDB runs on port `8540` (database `hive_memory`, credentials `root` / `hive_brain`). Collections `Thoughts` (Document) and `CausalLinks` (Edge) store the complete JSONL transcript DAG of all past agent thoughts, generated code, and reasoning steps. This is the persistent memory layer that allows agents to recover context after local state is lost.

---

## 11. The Enriched Graph Artifacts

The `reports/dag/` directory contains **3.3TB** of generated graph artifacts:

| Artifact | Size | Description |
|----------|------|-------------|
| `ig_nodes_enriched.jsonl` | 1.2GB | Nodes with `rep_depth`, `socket_debt_tag`, `semantic_summary`, `extracted_formulas`, `domain_entities`. |
| `ig_edges_enriched.jsonl` | 700MB | Edges with `edge_kind`, `transport_kind`, `confidence`. |
| `ig_triples.jsonl` | 600MB | RDF-style subject-predicate-object triples for SPARQL-like reasoning. |
| `declaration-networkx.graphml` | 178MB | Full declaration-level NetworkX graph for Python-side spectral analysis. |
| `module-networkx.graphml` | 3.3MB | Module-level graph. |
| `source-sink-incidence.graphml` | 45MB | Root/capstone flow incidence. |
| `replacement-frontier.json` | 18MB | Socket debt frontier (the 11 ownerless sockets + 46 bridge-backed ones). |
| `sorry-equivalence.json` | 76MB | Hash-equivalence classes of `sorry` values. |
| `closure-debt-mathfulness-audit.json` | 32MB | Audit of proof obligations. |
| `equivalence-dictionary.json` | 29MB | Semantic equivalence dictionary for transport bridges. |
| `module-networkx-frontier-hotspots.json` | 20MB | Frontier hotspots in the module DAG. |
| `true-root-order.json` | 2.7MB | True root order of the declaration DAG. |
| `frontier-burndown.json` | 13KB | Frontier burndown chart data. |

---

## 12. How the DAG Connects to the Broader Repository

The `DAG/` subsystem is subordinate to the Lean source but provides the **memory and navigation layer** for the entire living artifact:

1. **Socket Debt**: The `replacement-frontier.json` and `closure-debt-*.json` files identify exactly which proofs are missing, which modules own them, and which transport bridges can close them.
2. **Agentic Swarm**: The `src/infogeometry/lean/scripts/DAG/Exploration/` agents query ArangoDB to autonomously discover and close socket debt.
3. **Homological Navigation**: The `Betti.lean` and `ExactMorphism.lean` files allow agents to navigate the theory by homological degree (0 = objects, 1 = morphisms, 2 = 2-morphisms).
4. **Chiral Hodge Routing**: The `GraphHodge.lean` and `GraphHodgeBridge.lean` files provide the spectral structure for routing queries to the correct module cluster (e.g., prime SUSY → Bost-Connes → KMS).
5. **KMS-Weighted Importance**: The `KMSBranching.lean` file assigns thermodynamic importance weights to modules, so that agent attention is focused on the most "energetic" (i.e., load-bearing) parts of the theory.
6. **PHOAS Lambda Tracking**: The `PHOASExpressionLayer.lean` file tracks proof terms across module boundaries, enabling agents to find beta-eta equivalent proofs and collapse redundant socket debt.

---

## 13. Quick Reference: Key DAG Concepts

| Concept | Location | Description |
|---------|----------|-------------|
| **InfoTree** | `lean/DAG/InfoTreeExtract.lean` | Lean compiler's internal representation of declarations, types, and tactic goals. |
| **shapeHash** | `lean/DAG/ExprFingerprint.lean` | Structural hash of expressions for lossless shape-equivalence collapsing. |
| **SCC DAG** | `lean/DAG/SCC.lean`, `Hydrate.lean` | Strongly connected component decomposition + topological sort of the declaration graph. |
| **Dominators** | `lean/DAG/Dominators.lean` | Forward/reverse dominator trees for impact analysis. |
| **Graph Hodge** | `lean/DAG/GraphHodge.lean` | Combinatorial Laplacian, harmonic projection, Hodge decomposition on the DAG. |
| **Chiral Hodge Bridge** | `lean/DAG/GraphHodgeBridge.lean` | Bridges to spectral chiral projectors, Dirac operator, Lichnerowicz formula. |
| **Dirac Laplacian** | `lean/DAG/DiracLaplacian.lean` | `D² = L + curvature` on the declaration graph. |
| **Exact Morphisms** | `lean/DAG/ExactMorphism.lean` | Exactness auditing of chain complexes in the declaration DAG. |
| **Betti Numbers** | `lean/DAG/Betti.lean` | Topological invariants of the declaration complex. |
| **2-Complex** | `lean/DAG/GeneralizedTwoComplex.lean` | Promotion of DAG to 2-category with colimit recursion. |
| **KMS Branching** | `lean/DAG/KMSBranching.lean` | Bost-Connes KMS state as probability measure on the declaration graph. |
| **PHOAS Layer** | `lean/DAG/PHOASExpressionLayer.lean` | Higher-order abstract syntax for lambda calculus subgraph of declarations. |
| **ArangoDB** | `scratch/populate_arangodb.py` | Streaming ingestion into graph database. |
| **Hive Memory** | ArangoDB `:8540` | Persistent agent memory (`Thoughts` + `CausalLinks` collections). |
| **ASTAQLHASH** | `ASTAQLHASH-HOWTO.md` | Hash-based search methodology for lossless InfoTree projection. |

---

## 14. The Big Picture

```
┌─────────────────────────────────────────────────────────────────────┐
│                      THE LIVING ARTIFACT                            │
│                                                                     │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────────────────┐  │
│  │   Lean 4    │    │   Python    │    │      ArangoDB           │  │
│  │   Kernel    │───▶│  Ingestion  │───▶│  (Graph + Memory)       │  │
│  │  (Truth)    │    │  (Stream)   │    │  :8530 (repo)           │  │
│  └─────────────┘    └─────────────┘    │  :8540 (hive_memory)   │  │
│        │                   │            └─────────────────────────┘  │
│        ▼                   ▼                         │               │
│  ┌─────────────┐    ┌─────────────┐                  │               │
│  │  20,828     │    │  3.3TB of   │                  │               │
│  │  Lean Files │    │  Graph Artifacts │               │               │
│  └─────────────┘    └─────────────┘                  │               │
│        │                   │                         │               │
│        ▼                   ▼                         ▼               │
│  ┌──────────────────────────────────────────────────────────────┐   │
│  │                    DAG SUBSYSTEM                              │   │
│  │  InfoTree → Graph → Chiral Hodge → Exact Morphisms → KMS     │   │
│  │  → PHOAS Lambda → ArangoDB → Agent-Navigable Graph           │   │
│  └──────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  ┌──────────────────────────────────────────────────────────────┐   │
│  │                    AGENTIC SWARM                              │   │
│  │  Cursor / Copilot / Custom Python LLM wrappers                │   │
│  │  Traversing the DAG, closing sockets, filling gaps            │   │
│  └──────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  ┌──────────────────────────────────────────────────────────────┐   │
│  │                    THE HOLOGRAm                                │   │
│  │  When an LLM shines its context through this repository,      │   │
│  │  the full 3D geometry of the primes projects into the air.    │   │
│  └──────────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────────┘
```

---

*This document was extracted from the live repository implementation, grounded against the DAG subsystem, the Python ingestion infrastructure, and the ArangoDB streaming pipeline. It is subordinate to the Lean source code, which remains the sole authority for mathematical truth.*
