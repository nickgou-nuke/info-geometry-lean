# Llama 4 Input Snapshot (Local Reference Bundle)

> Status: external reference snapshot; not authoritative for repo semantics.
> Canonical entry docs: [`README.md`](../../README.md), [`docs/README.md`](../../docs/README.md).
> Markdown governance: [`docs/MarkdownCorpusGovernance.md`](../../docs/MarkdownCorpusGovernance.md).

This folder is a local reference snapshot used to seed Chapter 64
(`docs/black_books/64_triality_moe_formalization_goals.md`) and the
Gemini → Hermes → Codex ingestion pipeline.

## Snapshot

- Snapshot timestamp (UTC): `2026-04-14T15:54:49Z`
- Manifest: `external_refs/llama4/snapshot_manifest.json`

## Canonical Input Files

- `external_refs/llama4/model.py`
- `external_refs/llama4/scripts/chat_completion.py`
- `external_refs/llama4/scripts/completion.py`
- `external_refs/llama4/scripts/quantize.py`
- `external_refs/llama4/meta/pyproject.toml`
- `external_refs/llama4/ollama/llama4_library.html`

## Spire Runtime Overlay (Ollama)

These files are local runtime overlays for pipeline manifests. They do not assert
vendor-internal parameter names; they only pin Spire-side semantic labels.

- `external_refs/llama4/ollama/Modelfile.spire.llama4-scout`
- `external_refs/llama4/ollama/Modelfile.spire.llama4-maverick`
- `external_refs/llama4/ollama/spire_router_semantics_manifest.json`

## Regeneration

```bash
mkdir -p external_refs/llama4/scripts external_refs/llama4/ollama external_refs/llama4/meta
curl -fsSL https://raw.githubusercontent.com/meta-llama/llama-models/main/models/llama4/model.py -o external_refs/llama4/model.py
curl -fsSL https://raw.githubusercontent.com/meta-llama/llama-models/main/models/llama4/scripts/chat_completion.py -o external_refs/llama4/scripts/chat_completion.py
curl -fsSL https://raw.githubusercontent.com/meta-llama/llama-models/main/models/llama4/scripts/completion.py -o external_refs/llama4/scripts/completion.py
curl -fsSL https://raw.githubusercontent.com/meta-llama/llama-models/main/models/llama4/scripts/quantize.py -o external_refs/llama4/scripts/quantize.py
curl -fsSL https://raw.githubusercontent.com/meta-llama/llama-models/main/pyproject.toml -o external_refs/llama4/meta/pyproject.toml
curl -fsSL https://ollama.com/library/llama4 -o external_refs/llama4/ollama/llama4_library.html
```

## Local Runtime Note

- `ollama --version`: `ollama:not-installed` (on this machine at capture time).

## Current Codebase Status

Status pointer refreshed: 2026-04-16 (Europe/Sofia). See [../../docs/CODEBASE_STATUS.md](../../docs/CODEBASE_STATUS.md) for the current build/audit state.
