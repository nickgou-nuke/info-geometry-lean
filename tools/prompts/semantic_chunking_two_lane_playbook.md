# Semantic Chunking Two-Lane Playbook (Frontier + Local)

Goal: use large-context model once for boundary mapping, then do local Leanstral-only refinement and deterministic validation.

## 0) JSON contract (shared by all lanes)

```json
{
  "document_id": "string",
  "source_path": "string",
  "chunks": [
    {
      "id": "string",
      "type": "section|definition|lemma|theorem|proof|remark|equation|paragraph|appendix",
      "title": "string",
      "start_line": 1,
      "end_line": 1,
      "anchors": {
        "section": "string|null",
        "label": "string|null",
        "equation": "string|null"
      },
      "context_header": "string",
      "math_symbols": ["\\alpha", "\\beta"],
      "dependencies": ["chunk_id"]
    }
  ]
}
```

Hard rules:
- Line ranges are inclusive and monotonically increasing.
- No overlaps.
- No gaps unless blank lines/comments-only spans.
- Never split inside `$$...$$`, `\\[...\\]`, `\\(...\\)`, or `\\begin{env}...\\end{env}`.

## 1) Frontier lane prompt (OpenRouter owl-alpha)

Use with entire source when possible.

```text
You are a mathematical document segmenter.
Task: produce a semantic chunk boundary map for the input LaTeX/Markdown document.

Output format: STRICT JSON only, exactly matching the provided schema keys.
No prose, no markdown fences.

Constraints:
1) Preserve mathematical integrity:
   - Never split inside math mode or LaTeX environments.
   - Treat theorem-like environments as indivisible unless they exceed max lines.
2) Semantic boundaries:
   - Prefer boundaries at section/subsection, definition/theorem/proof transitions, and numbered equation blocks.
3) Context preservation:
   - Add `context_header` explaining local dependency in <= 20 words.
4) Anchors:
   - Extract section labels and \label{} anchors when present.
5) Safety:
   - If uncertain, choose fewer/larger chunks instead of risky splits.

Chunk size policy:
- Target: 80-220 lines per chunk.
- Hard max: 320 lines per chunk.
- If a single indivisible environment exceeds hard max, keep it intact and mark type accordingly.

Return strict JSON only.
```

## 2) Frontier lane prompt (Gemini CLI variant)

Run guard first from repo root:

```bash
python3 tools/infra/gemini_cli_guard.py --check --json
```

Then use prompt:

```text
You are the irregular sidecar boundary mapper for long mathematical text.
Return only strict JSON using the provided schema.

Mission:
- Identify robust semantic chunk boundaries for theorem-heavy LaTeX/Markdown.
- Keep Definition/Theorem/Proof units coherent.
- Never cut through formulas or begin/end environments.

Policy:
- This output is non-canonical preprocessing metadata.
- Do not invent claims about mathematical truth.
- Prefer conservative boundaries over aggressive splitting.

Line-range constraints:
- start_line/end_line must be valid source lines.
- no overlap; monotone ordering.
- if uncertain on boundary, expand outward to nearest safe anchor.

Return JSON only.
```

## 3) Local lane prompt (Leanstral refinement)

Use after frontier output; pass the source plus preliminary JSON.

```text
You are a local chunk-refiner.
Input A: source document.
Input B: preliminary chunk map JSON.

Task:
1) Keep chunk ids stable unless invalid.
2) Repair invalid boundaries (overlap, out-of-range, split-inside-math).
3) Normalize chunk `type` to allowed enum.
4) Improve `context_header` to concise dependency hints (<= 16 words).
5) Extract `math_symbols` only from local chunk text.

Do not rewrite source text. Do not add theorem claims.
Return strict JSON only in the same schema.
```

## 4) Deterministic validator rules (local, non-LLM)

Required checks:
1) Schema validity (required keys/types).
2) Range validity (`1 <= start_line <= end_line <= N`).
3) Order and overlap (sorted, non-overlapping).
4) Coverage report (covered lines %, uncovered non-empty lines list).
5) Environment integrity:
   - chunk must not start inside open env/math mode.
   - chunk must not end before closing currently-open env/math mode.
6) Anchor sanity:
   - if `anchors.label` is set, corresponding `\\label{...}` must appear in chunk lines.
7) Size policy:
   - warn if < 40 lines unless type in {equation, remark}.
   - warn if > 320 lines.
8) Dependency sanity:
   - all `dependencies` ids must exist and point to earlier chunks.

Suggested verdict levels:
- FAIL: schema/range/overlap/env-integrity violations.
- WARN: size/coverage/anchor/dependency quality issues.
- PASS: no FAIL; WARN optional.

## 5) Minimal execution recipe

```bash
# A) Frontier map (choose one)
# openrouter/owl-alpha -> save JSON to /tmp/chunks.frontier.json
# or gemini-cli (after guard) -> /tmp/chunks.frontier.json

# B) Local refinement with Leanstral -> /tmp/chunks.refined.json

# C) Deterministic validation
python3 tools/infra/semantic_chunking_validator.py \
  --source path/to/document.md \
  --chunks /tmp/chunks.refined.json
```

## 6) Notes for this repository

- Treat all frontier outputs as retrieval-only sidecars until certified by local checks.
- Keep owner-proof authority in Lean modules; chunk maps are navigation metadata.
