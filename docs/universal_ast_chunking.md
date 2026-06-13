# Universal AST Chunking and Local Qwen Purification

`tools/infra/universal_ast_chunker.py` is the repo-native entry point for
AST-aware code chunking into Alexandria/Arango JSONL.

It is a context layer only.  Lean source and `lake env lean` remain proof
authority.  Local LLM output is retrieval metadata, never a proof and never a
source rewrite.

## Lanes

- Lean 4: declaration-span chunks with imports, scope, symbols, and optional
  `lake env lean <file>` compile-gate metadata.
- Python/SymPy: stdlib `ast` chunks for imports, functions, classes, calls, and
  scope chains.
- LeanDojo: normalized theorem/tactic trace JSON via `--json-mode leandojo`.
- Markdown theory notes: structural heading chunks for paper/textbook fragments,
  with deterministic extraction of LaTeX/equation lines and domain entities
  such as quaternion curvature, spin connection, Riemannian curvature, and
  soldering forms.
- Native Lean CST/AST: compatible with the existing
  `external_refs/ast_export` package; use that when full Lean `Syntax` JSON is
  needed for a narrower formal-AST audit.

## Local Qwen

Run Qwen through a local OpenAI-compatible server, for example vLLM:

```bash
vllm serve Qwen/Qwen2.5-Math-7B-Instruct \
  --served-model-name qwen-math \
  --host 127.0.0.1 \
  --port 8000
```

On this machine there are two useful endpoint shapes:

- live smoke-test endpoint: `http://127.0.0.1:18889/v1`, currently backed by
  the `leanstral-api` llama.cpp container;
- Qwen production endpoint from
  `/home/goutev/repos/dgx-spark-qwen3-coder-next-compose/docker-compose.yml`:
  `http://127.0.0.1:30000/v1`;
- Qwen production endpoint from
  `/home/goutev/repos/spark-vllm-docker/recipes/qwen3-coder-next-int4-minimal.yaml`:
  `http://127.0.0.1:8000/v1`.

Then run the chunker:

```bash
python3 tools/infra/universal_ast_chunker.py \
  --input lean/InfoGeometry/Algebra/Det2.lean \
  --input tools/sympy/formal_theory_quantum/chapter3_yang_baxter.py \
  --input path/to/section9_quaternion_curvature.md \
  --output artifacts/ast_chunker_probe \
  --lean-compile-check \
  --max-compile-files 1 \
  --purify-with-local-llm \
  --local-llm-base-url http://127.0.0.1:8000/v1 \
  --local-llm-model qwen-math \
  --local-llm-temperature 0.1
```

For a safe first test:

```bash
python3 tools/infra/universal_ast_chunker.py \
  --input lean/InfoGeometry/Algebra/Det2.lean \
  --output artifacts/ast_chunker_qwen_probe \
  --lean-compile-check \
  --max-compile-files 1 \
  --purify-with-local-llm \
  --local-llm-base-url http://127.0.0.1:8000/v1 \
  --local-llm-model qwen-math \
  --local-llm-limit 1 \
  --local-llm-timeout 10
```

The local LLM result is validated before it is accepted.  Responses that omit
required fields, change `raw_content_unchanged`, or replace the fixed
`ast_context_only_not_proof_authority` sentinel are written with
`ok: false` and `validationErrors` for later retry or prompt tuning.

## Outputs

The output directory contains Alexandria-compatible JSONL:

- `alexandria_documents.jsonl`
- `alexandria_sections.jsonl`
- `alexandria_chunks.jsonl`
- `alexandria_entities.jsonl`
- `alexandria_document_section_edges.jsonl`
- `alexandria_section_chunk_edges.jsonl`
- `alexandria_chunk_entity_edges.jsonl`
- `alexandria_chunk_adjacent_edges.jsonl`
- `alexandria_entity_relation_edges.jsonl`
- `code_purification_requests.jsonl`
- `code_purifications.jsonl`
- `manifest.json`

Markdown chunks add formula entities through `CONTAINS_FORMULA` edges and
domain-term entities through `MENTIONS_DOMAIN_ENTITY` edges.  This provides a
deterministic graph seed before any local Qwen purification runs.

Load with:

```bash
python3 tools/alexandria/arango_ingest.py \
  --input-dir artifacts/ast_chunker_probe
```

## Authority Boundary

Qwen is used for:

- two-sentence mathematical summaries,
- dependency hints,
- normalized variable aliases for search,
- extra retrieval terms.

Qwen is not used for:

- proving Lean theorems,
- changing source files,
- replacing `lake env lean`,
- promoting graph proximity into mathematical authority.

If a future pass asks Qwen to propose rewritten Lean code, that proposal must be
written to a scratch file outside the source tree and compiled independently
before it can become anything more than retrieval metadata.
