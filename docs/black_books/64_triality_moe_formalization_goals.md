# 64. Triality-MoE Formalization Goals (Operator-First)

*Date: April 14, 2026*
*Context: Precognitive architecture notes (2025) translated into Lean-safe objectives*

## Executive Intention

We formalize LLM MoE routing as an operator-first decomposition pipeline,
without promoting external model narratives directly into canonical theorems.

The core objective is to encode a **structural bridge**:

- `attention / background transport` (reactive lane),
- `router-induced inactive mass` (defect lane),
- `canonical sourced generator` via the existing
  `ObserverDefect -> ModularSourceBridge` owner stack.

## Non-Negotiable Guardrails

1. No external product claims as theorem premises.
2. No direct ontological claims (`Majorana`, `Kramers`, `CCC`) as Lean facts unless already owner-certified.
3. Use only repo-native symbols for canonical closures:
   - `CertifiedInverseKernel`,
   - `ObserverDefect.ObserverL5`,
   - `ObserverDefect.observerDefectResidual`,
   - `ModularSourceBridge.BackgroundModularFlow`,
   - `ModularSourceBridge.sourcedModularGenerator`.
4. Keep external architecture descriptions in docs as interpretation layers, never as proof kernel assumptions.

## Formalization Program

### Phase P0: Vocabulary Lock

Create an LLM-side structural vocabulary for sparse routing that is independent from any specific vendor model:

- sparse router weights,
- active vs defect gates,
- decomposition identity per expert and after summation.

### Phase P1: Algebraic MoE Split

Prove in Lean:

- per-expert weight decomposition (`weight = active + defect`),
- total output decomposition (`total = active + defect`).

This is purely algebraic and must compile without introducing new operator axioms.

### Phase P2: Canonical Bridge Contract

Define a bridge structure asserting that a router residual is identified with
`observerDefectResidual`. From this, derive:

- sourced generator equality with canonical source bridge,
- preservation of Drazin cut as a direct corollary.

### Phase P3: Triality/GQA Interpretation Layer

Add theorem-neutral documentation mapping:

- QKV coupling to triality language,
- active/excluded experts to regular/defect lanes,
- sourced transport as defect-aware update.

This phase remains interpretive unless and until owner theorem surfaces exist.

## Deliverables

1. `lean/InfoGeometry/LLM/TrialityMoE.lean`
2. Import in `lean/InfoGeometry/LLM.lean`
3. Targeted build gates:
   - `lake build InfoGeometry.LLM.TrialityMoE`
   - `lake build InfoGeometry.LLM`

## Acceptance Criteria

- The new LLM module builds cleanly.
- No new `sorry`/axioms introduced by the module.
- The bridge theorem uses canonical symbols exactly as owned in current `main`.
- Interpretive claims remain in Black Book prose, not in theorem statements.

## Forward Candidate Theorem Family

- `router_weight_split`
- `moe_output_split`
- `sourcedGenerator_eq_canonical`
- `sourcedGenerator_respects_cut`

These are sufficient as a first stable surface.

## Input Snapshot Configuration (Llama 4 / Ollama)

This chapter now uses a fixed local input snapshot for LLM formalization seeding.

- Snapshot timestamp (UTC): `2026-04-14T15:54:49Z`
- Manifest: `external_refs/llama4/snapshot_manifest.json`
- Source bundle:
- `external_refs/llama4/args.py` (sha256 `e10bfccad9e73344…`, bytes `3458`)
- `external_refs/llama4/datatypes.py` (sha256 `b3d4687569c847d2…`, bytes `1721`)
- `external_refs/llama4/ffn.py` (sha256 `39382be23ac75f24…`, bytes `1995`)
- `external_refs/llama4/model.py` (sha256 `a3b50fac19b702c5…`, bytes `16309`)
- `external_refs/llama4/moe.py` (sha256 `a0338e75fcb6bfb3…`, bytes `6928`)
- `external_refs/llama4/scripts/chat_completion.py` (sha256 `f7c7b540f262e8ea…`, bytes `4004`)
- `external_refs/llama4/scripts/completion.py` (sha256 `25a0ea91ad5061c2…`, bytes `2085`)
- `external_refs/llama4/scripts/quantize.py` (sha256 `b121ab2d928a9577…`, bytes `8544`)
- `external_refs/llama4/meta/pyproject.toml` (sha256 `d7f4e80bd68f218f…`, bytes `1421`)
- `external_refs/llama4/ollama/llama4_library.html` (sha256 `756ed48be841f6da…`, bytes `87885`)

### Regeneration Command

```bash
mkdir -p external_refs/llama4/scripts external_refs/llama4/ollama external_refs/llama4/meta
curl -fsSL https://raw.githubusercontent.com/meta-llama/llama-models/main/models/llama4/args.py -o external_refs/llama4/args.py
curl -fsSL https://raw.githubusercontent.com/meta-llama/llama-models/main/models/llama4/datatypes.py -o external_refs/llama4/datatypes.py
curl -fsSL https://raw.githubusercontent.com/meta-llama/llama-models/main/models/llama4/ffn.py -o external_refs/llama4/ffn.py
curl -fsSL https://raw.githubusercontent.com/meta-llama/llama-models/main/models/llama4/model.py -o external_refs/llama4/model.py
curl -fsSL https://raw.githubusercontent.com/meta-llama/llama-models/main/models/llama4/moe.py -o external_refs/llama4/moe.py
curl -fsSL https://raw.githubusercontent.com/meta-llama/llama-models/main/models/llama4/scripts/chat_completion.py -o external_refs/llama4/scripts/chat_completion.py
curl -fsSL https://raw.githubusercontent.com/meta-llama/llama-models/main/models/llama4/scripts/completion.py -o external_refs/llama4/scripts/completion.py
curl -fsSL https://raw.githubusercontent.com/meta-llama/llama-models/main/models/llama4/scripts/quantize.py -o external_refs/llama4/scripts/quantize.py
curl -fsSL https://raw.githubusercontent.com/meta-llama/llama-models/main/pyproject.toml -o external_refs/llama4/meta/pyproject.toml
curl -fsSL https://ollama.com/library/llama4 -o external_refs/llama4/ollama/llama4_library.html
```

### Pipeline Role

- Gemini creative pass consumes `seed_text` segments derived from this snapshot.
- Hermes verification pass enriches each segment with literature evidence.
- Codex translation pass maps validated segments into repo-native theorem targets.
