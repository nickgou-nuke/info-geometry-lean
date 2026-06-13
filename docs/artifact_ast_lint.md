# Artifact AST Digest and Lint

`tools/alexandria/artifact_ast_lint.py` is the front-end for digesting raw
mathematical artifacts from papers and textbooks.

It is a context-builder and hygiene gate, not a proof oracle.

## Pipeline

```text
PDF / TeX / Markdown / text
  -> layout/structural extraction
  -> LaTeX-aware math chunks
  -> embedded Lean/Python candidate extraction
  -> deterministic lint findings
  -> optional Lean candidate compile gate
  -> Qwen purification requests
  -> Alexandria/Arango JSONL
```

For PDFs that contain no embedded source archive, use the coordinate/font
recovery stage first:

```bash
python3 tools/alexandria/recover_pdf_source_fragments.py \
  --pdf path/to/paper.pdf \
  --output artifacts/alexandria/paper_pdf_recovery
```

This stage runs `pdftohtml -xml`, identifies monospaced/code fonts such as
`JuliaMono`, reconstructs side-by-side code columns from coordinates, and emits
candidate `.lean` and `.py` files under the output directory.

To validate recovered Lean candidates in generated batches:

```bash
python3 tools/alexandria/batch_check_recovered_lean.py \
  --input artifacts/alexandria/paper_pdf_recovery/recovered_pdf_code_blocks.jsonl \
  --output artifacts/alexandria/paper_pdf_recovery/lean_batch_check \
  --preamble "import Std" \
  --batch-size 16
```

Use `--isolate-failures` when you need per-fragment failure attribution. Without
it, failed batches are reported as `batch_failed`, which is faster for broad
triage.

For targeted checks:

```bash
python3 tools/alexandria/batch_check_recovered_lean.py \
  --input artifacts/alexandria/paper_pdf_recovery/recovered_pdf_code_blocks.jsonl \
  --output artifacts/alexandria/paper_pdf_recovery/lean_batch_check_p40_45 \
  --min-page 40 \
  --max-page 45 \
  --isolate-failures
```

## Authority Boundary

- PDF/OCR/Markdown extraction is evidence, not authority.
- PDF coordinate/font recovery is reconstruction, not the original TeX source.
- Embedded Lean code from a paper is candidate text only.
- Tree-sitter or Python AST parsing is structural evidence only.
- Lean authority begins only after `lake env lean` or `lake build` accepts the
  candidate.
- Local LLM/Qwen output is retrieval metadata only and must keep raw content
  unchanged.

## Usage

```bash
python3 tools/alexandria/artifact_ast_lint.py \
  --input path/to/paper.tex \
  --output artifacts/alexandria/artifact_digest_probe \
  --max-chars 2400
```

For PDF input, pass a layout-aware parser:

```bash
python3 tools/alexandria/artifact_ast_lint.py \
  --input path/to/paper.pdf \
  --pdf-parser marker \
  --output artifacts/alexandria/artifact_digest_probe
```

To kernel-check extracted Lean-looking blocks:

```bash
python3 tools/alexandria/artifact_ast_lint.py \
  --input path/to/paper.md \
  --output artifacts/alexandria/artifact_digest_probe \
  --check-lean-candidates \
  --lean-preamble "import Mathlib" \
  --fail-on error
```

## Outputs

The output directory contains Alexandria-compatible JSONL plus artifact hygiene
sidecars:

- `alexandria_documents.jsonl`
- `alexandria_sections.jsonl`
- `alexandria_chunks.jsonl`
- `alexandria_entities.jsonl`
- `alexandria_*_edges.jsonl`
- `artifact_digests.jsonl`
- `artifact_lint_findings.jsonl`
- `artifact_code_candidates.jsonl`
- `artifact_purification_requests.jsonl`
- `manifest.json`

The PDF source-recovery stage writes:

- `recovered_text.md`
- `recovered_text.tex`
- `recovered_pdf_lines.jsonl`
- `recovered_pdf_code_lines.jsonl`
- `recovered_pdf_code_blocks.jsonl`
- `recovered_lean/*.lean`
- `recovered_python/*.py`
- `manifest.json`

The recovered Lean batch-check stage writes:

- `lean_batch_results.jsonl`
- `lean_batch_sources/*.lean`
- `manifest.json`

Load the Alexandria collections with:

```bash
python3 tools/alexandria/arango_ingest.py \
  --input-dir artifacts/alexandria/artifact_digest_probe
```

## Lint Findings

The linter currently detects:

- unclosed, unmatched, or mismatched LaTeX environments;
- unbalanced inline/display dollar math delimiters;
- oversized structural chunks;
- proof blocks not adjacent to theorem-like blocks;
- prose claims such as `kernel-verified`, `zero sorries`, or `axiom-free`
  without an explicit Lean evidence link;
- embedded Python candidates that fail `ast.parse`;
- embedded Lean candidates that were not checked or failed `lake env lean`.

## Qwen Purification

`artifact_purification_requests.jsonl` is a sidecar for local Qwen/vLLM
processing. The prompt asks for retrieval metadata only:

- summary;
- assumed definitions;
- mathematical entities;
- candidate formalizations;
- claims requiring evidence;
- normalized notation;
- lint awareness.

The response must not rewrite the artifact, and it must not promote paper prose
or LLM summaries into Lean proof authority.
