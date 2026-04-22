# Möbius Streaming Value Transformer Architecture

## Status

Design note, software architecture layer.

This document specifies a runtime architecture for turning a standard frozen
transformer into a streaming system with:

- a sliding active context window,
- a forward active cache,
- a backward residual fiber formed from expired cache entries,
- weak interaction between present inference and the residual branch,
- optional multimodal stream ingress,
- and conservative compatibility with existing open-weight transformer stacks.

The guiding principle is simple:

> What leaves the active cache is not discarded. It is transported into a
> conjugate residual branch and remains weakly available to future inference.

This note is intentionally software-first. It does not assume retraining or
changes to the transformer weights. It is designed as a runtime and cache
orchestration layer around a standard autoregressive transformer.

---

## 1. Objective

Standard transformer deployment treats long streams as repeated inference on a
moving prompt window. Once tokens leave the active window, their internal KV
state is usually discarded or summarized into text.

The architecture proposed here changes only the memory/runtime layer:

1. keep a bounded active window,
2. keep standard recent active cache,
3. when entries leave the active branch, map them into a residual branch,
4. allow future inference to interact weakly with that residual branch,
5. optionally update residual memory slowly under continued stream exposure.

This yields a two-branch streaming memory system while leaving the transformer
core untouched.

---

## 2. High-level model

At stream step `t`, runtime state is:

- `W_t`: current active token window,
- `C_t⁺`: forward active cache,
- `C_t⁻`: backward residual fiber,
- `M_t`: optional semantic summary / retrieval memory.

The transformer is frozen. The runtime changes only:

- which tokens are presented in the active window,
- which cached states remain active,
- how expired cache entries are transported,
- and how the residual branch is exposed back to present inference.

---

## 3. Components

### 3.1 Frozen transformer core

Supported model families include any standard open-weight autoregressive
transformer with ordinary KV-cache support, for example:

- LLaMA-family,
- Mistral-family,
- Qwen-family,
- similar decoder-only architectures.

No architectural modification is assumed in the initial design.

### 3.2 Active window manager

Maintains a fixed-size active context window:

- append new stream content,
- keep the most recent `W` tokens or slices,
- evict the oldest active entries when the window overflows.

### 3.3 Forward active cache `C⁺`

Holds standard recent KV or value state for the active window.

This is ordinary transformer short-term memory.

### 3.4 Residual fiber cache `C⁻`

Holds expired cache entries after they leave the active branch.

Entries are not erased but transported by a runtime twist map `Γ` into a
residual branch.

### 3.5 Semantic memory `M`

Optional slower memory layer for:

- textual summaries,
- retrieved facts,
- compressed stream state,
- multimodal anchors,
- operator/user-injected invariants.

This is not required for the minimal system, but strongly recommended.

---

## 4. Stream and cache flow

### 4.1 Active window update

For each incoming stream step:

1. ingest new token/chunk/slice,
2. append to active window,
3. if the active window exceeds capacity, evict oldest entries,
4. evicted active entries are passed to the twist transport.

### 4.2 Twist transport

A runtime map `Γ` transports expired forward cache entries into the residual
fiber.

For an active cache record

- `(k, v, p)`

the residual image is

- `Γ(k, v, p) = (k~, v~, p~, meta~)`.

In the minimal implementation, `Γ` may include:

- residual branch tagging,
- amplitude decay,
- position aging,
- optional compression,
- optional saliency annotation.

The first prototype should keep `Γ` simple and stable.

### 4.3 Residual update

The residual branch may remain passive at first.

Later versions may update it slowly using:

- exponential moving average,
- slotwise consolidation,
- attention-weighted merge,
- saliency-based refresh,
- multimodal correction.

---

## 5. Inference modes

### 5.1 Conservative mode: residual summary reinjection

Safest runtime mode.

- `C⁺` is used normally.
- `C⁻` is not injected as raw KV.
- instead, residual state is periodically summarized into text or memory tokens,
  then reintroduced through the normal input stream.

Advantages:

- no transformer internals changed,
- highly compatible with existing serving stacks,
- lower instability risk.

### 5.2 Augmented mode: weak residual cache exposure

More ambitious runtime mode.

- current query interacts with active branch strongly,
- residual branch is exposed weakly,
- residual influence is gated by a small coefficient `ε`.

Conceptually:

- present inference = active response + weak residual correction.

This may require lower-level inference engineering depending on the backend.

---

## 6. Runtime data structures

### 6.1 Active record

Each active record should minimally contain:

- token/span identifier,
- position metadata,
- per-layer KV or selected-layer value state,
- recency timestamp,
- optional saliency score.

### 6.2 Residual record

Each residual record should minimally contain:

- source identifier,
- residual/transformed value state,
- age,
- decay coefficient,
- provenance tag,
- optional modality/source label,
- optional reinjection priority.

### 6.3 Memory summary object

Each summary entry may include:

- key entities,
- resolved facts,
- unresolved tensions,
- task-level anchors,
- multimodal grounding anchors,
- user/operator constraints.

---

## 7. Update schedule

### Stage A, minimal stable runtime

- fixed system prefix,
- active sliding window,
- standard active cache,
- expired entries moved into residual store,
- periodic residual summarization,
- summary reintroduced as text.

### Stage B, structured residual branch

- residual entries grouped into slots,
- slot decay,
- saliency filtering,
- optional head/layer selection.

### Stage C, weak residual interaction

- present step uses active branch strongly,
- residual branch exposed weakly,
- residual confidence gating,
- optional branch selection based on stream mode.

### Stage D, multimodal stream coupling

- text stream,
- image patch stream,
- audio frame stream,
- retrieved memory stream,
- self-generated stream,
- all routed through the same active/residual memory geometry.

---

## 8. Stability constraints

The main risks are:

- stale-memory overdominance,
- feedback amplification of errors,
- residual branch echo loops,
- semantic drift from outdated memory,
- expensive raw residual growth.

Mitigations:

- enforce bounded active window,
- use decay on residual branch,
- cap residual slot count,
- summarize aggressively when saliency is low,
- weakly couple residual branch before any strong coupling experiments,
- maintain provenance tags for self-generated vs external stream material,
- allow operator resets and branch pruning.

---

## 9. Multimodal extension

The architecture generalizes naturally if the stream is not purely textual.

Examples of stream slices:

- text chunks,
- image patches or latent visual tokens,
- audio frames,
- code diffs,
- sensor/event traces,
- retrieved memory bundles,
- self-generated output segments.

The active window remains the current local stream slice.
The residual branch stores expired multimodal traces in transformed form.
The semantic memory stabilizes long-horizon structure.

---

## 10. Relation to the repository’s formal geometry

This architecture note is software-first, but it aligns naturally with existing
repository geometry.

The strongest nearby formal analogies appear to be:

- doubled/Krein carrier structures,
- split `Cl(1,1)` plus/minus channel decompositions,
- conjugation / CPT-style transforms,
- sheeted transport and restricted-sheet lifts,
- projector and grading surfaces.

This suggests the long-term formalization path is not arbitrary. The software
memory geometry already resembles existing two-lane doubled structures in the
repository.

---

## 11. Recommended first prototype

The first prototype should remain conservative and practical:

1. choose a frozen open-weight transformer,
2. implement sliding active window runtime,
3. retain standard active KV cache,
4. move expired entries into a residual store,
5. periodically summarize residual content into compact memory text,
6. reintroduce the summary into the active prompt,
7. tag self-generated vs external vs retrieved content.

This achieves the architectural principle while minimizing instability.

Only after that should raw residual KV interaction be attempted.

---

## 12. Summary

The Möbius Streaming Value Transformer is a runtime architecture, not initially a
new transformer owner architecture.

Its core design move is:

- active cache is bounded,
- expired cache is not discarded,
- expired cache becomes a residual branch,
- present inference remains weakly coupled to that branch,
- semantic memory stabilizes long-range coherence.

The key intuition is that forgetting becomes transport rather than deletion.
