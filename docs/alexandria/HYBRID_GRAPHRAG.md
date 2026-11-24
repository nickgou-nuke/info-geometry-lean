# Alexandria Hybrid GraphRAG Architecture

Alexandria combines deterministic structural parsing, mathematical-archetype entity extraction, strictly acyclic theorem/citation DAGs, BM25 ArangoSearch indexing, and Personalized PageRank over a multi-document concept graph. All outputs remain `"sourceAuthority": "retrieval_context_only"` and never substitute for kernel-checked Lean proofs.

---

## 1. Two-Tier Ingestion Spine

| Tier | Primary Tool | Structural Unit | Output Collections |
|---|---|---|---|
| **PDF Corpus DAG Brain** | `tools/alexandria/pdf_corpus_ingest.py` | Page-tracked PDF blocks (`abstract`, `theorem`, `proof`, `definition`, `equation`, `remark`, `bibliography`, `prose`) | All 4 doc collections + 6 edge collections (including `alexandria_dag_edges`) |
| **LaTeX / Math Paper** | `tools/alexandria/math_paper_graphrag_ingest.py` | Unbroken `\section` and `\begin{theorem|proof|equation|align}` blocks | Doc collections + entity/relation edges (compatible with `arango_ingest.py`) |
| **Markdown / Repo Prose** | `tools/alexandria/semantic_ingest.py` | Markdown heading hierarchy + identifier tokenization | Doc collections + adjacent/entity edges |

---

## 2. Deterministic Entity, Relation & Archetype Layer

Each ingested PDF chunk undergoes deterministic extraction before any optional LLM enrichment:

1. **Structural & Symbolic Entities (`alexandria_entities`):**
   - `theorem_result`, `definition_term`, `symbolic_expr`, `unicode_math`, `domain_term`, `math_archetype`, plus local structural anchors (`math_label`, `math_reference`, `bib_entry`).
2. **10 Mathematical Archetypes (`MATH_ARCHETYPE_PATTERNS`):**
   - `z2_graded_polarization` — $\mathbb{Z}/2$-grading, chiral grading, Peirce decomposition, isotropic nullcone, $\gamma_5$, Krein involution
   - `curved_dga_differential` — curved DG, Maurer–Cartan, Bianchi identity, Cartan curvature, soldering
   - `clifford_spinor_tower` — Clifford algebras, $\mathrm{Cl}(p,q)$, spinors, Dirac–Hestenes, Jordan–Wigner, $\mathrm{Pin}$
   - `krein_indefinite_metric` — Krein space, fundamental symmetry, indefinite inner product, Pontryagin space, $J$-self-adjoint
   - `drazin_riesz_spectral` — Drazin inverse, Riesz projector/decomposition, Moore–Penrose, Fredholm, generalized inverse
   - `souriau_metriplectic_thermo` — Souriau thermodynamics, coadjoint orbits, moment map, Massieu potential, Gibbs/Casimir/Onsager/metriplectic
   - `modular_kms_monodromy` — Tomita–Takesaki modular flow, KMS state, Bost–Connes, thermal time, monodromy, de Rham
   - `categorical_colimit_tower` — direct limit, colimit, inductive limit, functor, natural transformation, adjunction, topos, sheaf
   - `noncommutative_k_theory` — $C^*$-algebra, $KK$-theory, Kasparov, spectral triple, cyclic cohomology, Cuntz, Toeplitz
   - `yang_mills_gauge_holonomy` — Yang–Mills, gauge connection, Wilson loop, holonomy, Berry curvature, principal bundle, Chern–Simons
3. **Cross-Document `canonicalKey` Discipline:**
   - Global concepts (including all `math_archetype` nodes and domain/symbolic entities) receive `canonicalKey = stable_key("concept", entity_type, normalized.lower())` and are indexed on `alexandria_entities.canonicalKey`.
   - Local numbering artifacts in `NON_CROSS_DOC_ENTITY_TYPES` (`math_label`, `math_reference`, `bib_entry`) keep an empty `canonicalKey` so generic `Lemma 2.1` or `[1]` strings do not link unrelated papers.
4. **Optional Bounded LLM Enrichment (`--enrich-ollama`):**
   - Supports OpenAI-compatible `/v1/chat/completions` (e.g., vLLM Qwen3.8 27B NVFP4 with default `enable_thinking: false` unless `--allow-thinking` is passed) and Ollama `/api/chat`.
   - Adds structured summaries, `assumed_definitions`, `mathematical_entities`, `symbolic_terms`, and validated `[subject, predicate, object]` `alexandria_entity_relation_edges` without mutating the source excerpt.

---

## 3. Strictly Acyclic Mathematical DAG (`alexandria_dag_edges`)

`pdf_corpus_ingest.py` constructs directed edges across 6 semantic relations in fixed priority order (`DAG_EDGE_PRIORITY`):

1. `section_precedes_section`
2. `proof_proves_theorem`
3. `chunk_cites_entry`
4. `chunk_uses_definition`
5. `chunk_references_result`
6. `document_cites_document` (arXiv ID / DOI citation resolution across the corpus)

Before writing JSONL artifacts, `verify_and_prune_dag` drops self-loops and any lower-priority edge that closes a cycle, then runs an independent Kahn topological sort check so `alexandria_dag_edges` is guaranteed strictly acyclic.

---

## 4. Hybrid BM25 + Cross-Document Personalized PageRank

Retrieval (`retrieve_context.py`) and graph ranking (`graph_context_rank.py`) execute a multi-stage hybrid loop:

1. **Seed Selection (`ARANGO_SEED_AQL` / lexical overlap):**
   - Queries `alexandria_chunks_search` using `TOKENS(@q, "text_en")` (text + `2.0x` boosted title) plus exact `c.searchTerms IN @terms` (`safe_search_terms` preserves letter-digit boundaries like `Cl11` or `gamma5`).
   - Collects 1-hop `alexandria_chunk_adjacent_edges` (`LIMIT 4` per seed) and `1..@hops` BFS `alexandria_dag_edges` (`LIMIT 6` in ranker, `LIMIT 8` in retriever; `@hops` clamped to `[1, 3]`).
2. **Subgraph Expansion (`ARANGO_SUBGRAPH_AQL` & `build_graph`):**
   - Bounded to at most `200` chunk nodes in `rank_arango_context`, plus up to `600` chunk-entity links and `200` `alexandria_entity_relation_edges`.
   - Adds directed edges from adjacent chunks (`next`/`prev`), de Bruijn token conductivity, `alexandria_dag_edges`, `entity_relation`, and bidirectional `shared_entity` edges across chunks sharing an entity or matching `canonicalKey` (skipping `NON_CROSS_DOC_ENTITY_TYPES`).
3. **Personalized PageRank & Optional GPU Backend:**
   - Runs `personalized_scores` (`steps=12`, `alpha=0.85`, teleporting to BM25/lexical seed weights) over the weighted directed graph, optionally preferring NetworkX `cugraph` dispatch via `--use-gpu` (`NETWORKX_FALLBACK_TO_NX=true`).
   - Also provides `scc_quotient_scores` (`nx.condensation`) and entity-connected component clustering for downstream analysis.
