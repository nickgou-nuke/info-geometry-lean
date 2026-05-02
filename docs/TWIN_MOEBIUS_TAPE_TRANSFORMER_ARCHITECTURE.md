# Twin Möbius Tape Transformer Architecture

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

## Status

Design note, software architecture layer.

This document specifies a runtime architecture for a twin-transformer streaming
system built around a Möbius-tape memory geometry.

The central idea is not a primary stream plus an auxiliary correction stream.
Instead, there are:

- two equal streams,
- two equal cache lanes,
- two equal transformer branches,
- and a pair of transport maps that move information from one branch into the
  other.

The image is intentionally geometric:

> the system has two locally distinct orientations of one circulating tape,
> like the two sides of a Möbius strip, so that what exits one branch does not
> disappear but re-enters the other in transformed form.

This architecture is software-first and runtime-oriented. It does not require
changing the transformer weights in the first implementation.

---

## 1. Objective

Standard transformer streaming treats the sequence as a one-way causal stream.
Even when sliding windows and memory summaries are used, there is still an
implicit asymmetry:

- one active forward stream,
- and everything else is either forgotten, summarized, or weakly recalled.

The twin Möbius tape architecture removes that asymmetry.

It treats the stream as a closed symbolic process with two equal
presentations/orientations:

- a forward-oriented branch,
- a backward/conjugate branch.

Both branches are active, both maintain memory, and both constrain current
inference.

---

## 2. Core principle

At stream step `t`, there are two equal live branches:

- `S_t⁺`: forward-oriented stream state,
- `S_t⁻`: backward/conjugate stream state.

They are not independent corpora. They are two presentations of one evolving
symbolic tape.

The essential closure law is:

- what leaves one branch is not discarded,
- it is transported into the other branch,
- so the process is self-closing rather than linearly forgetting.

This is the runtime meaning of the Möbius tape metaphor.

---

## 3. System state

At step `t`, the runtime state is:

- `W_t⁺`: active forward window,
- `W_t⁻`: active backward/conjugate window,
- `C_t⁺`: forward active cache,
- `C_t⁻`: backward active cache,
- `M_t`: optional semantic/shared memory layer.

where:

- `W_t⁺` and `W_t⁻` are equal-status active windows,
- `C_t⁺` and `C_t⁻` are equal-status memory structures,
- `M_t` is optional slower shared stabilization memory.

---

## 4. Twin transformer branches

The runtime uses two transformer instances or two equal runtime roles of the
same frozen transformer family:

- `T⁺`: forward transformer branch,
- `T⁻`: backward transformer branch.

Possible implementation choices:

1. same architecture, same weights, different stream orientation,
2. same architecture, same weights, different runtime role,
3. same main architecture with one lighter auxiliary twin,
4. eventual trained specialization after the runtime concept is validated.

The first design note assumes the branches are equal at the software level.

---

## 5. Branch update law

At each stream step:

1. ingest new stream content into the forward presentation,
2. update the conjugate/backward presentation,
3. run each branch on its own current window and cache,
4. transport expired states across branches,
5. fuse branch outputs into present inference/output.

This yields a symmetric two-branch online process.

---

## 6. Cross-branch transport maps

Let the inter-branch transport maps be:

- `Γ₊₋`: forward branch to backward branch,
- `Γ₋₊`: backward branch to forward branch.

These are the key runtime objects.

When an item exits the active forward branch, it is mapped into the backward
branch:

- expired forward state -> `Γ₊₋(state)` -> backward branch insertion.

Likewise, when an item exits the backward branch, it is mapped into the forward
branch:

- expired backward state -> `Γ₋₊(state)` -> forward branch insertion.

These maps may include:

- branch tagging,
- decay,
- reindexing,
- conjugation,
- parity/orientation transform,
- compression,
- modality-aware transport.

---

## 7. Möbius closure condition

The branch transport is Möbius-like if a double transport approximately returns
to the original orientation:

- `Γ₋₊ ∘ Γ₊₋ ≈ Id`,
- `Γ₊₋ ∘ Γ₋₊ ≈ Id`,

up to:

- attenuation,
- compression,
- phase shift,
- branch-specific filtering.

This means the two branches are not merely connected. They are two orientations
of one closed process.

---

## 8. Per-branch inference

Each branch processes its own active window and cache, while optionally receiving
weak input from the opposite branch.

### Forward branch

- active input: `W_t⁺`, `C_t⁺`
- weak cross-branch input: transformed `C_t⁻`

### Backward branch

- active input: `W_t⁻`, `C_t⁻`
- weak cross-branch input: transformed `C_t⁺`

This preserves equality of status while allowing controlled interaction.

---

## 9. Two-lane attention law

A clean first attention law is branchwise attention followed by linear fusion.

### Forward branch attention

- `A_t⁺ = Attn(Q_t⁺, K_t⁺, V_t⁺)` plus optional weak transformed contribution
  from the opposite branch.

### Backward branch attention

- `A_t⁻ = Attn(Q_t⁻, K_t⁻, V_t⁻)` plus optional weak transformed contribution
  from the opposite branch.

### Branch fusion

The present step output is fused from both branches:

- `A_t = α A_t⁺ + β A_t⁻`

with:

- `α + β = 1`,
- usually `α ≈ β` in the equal-branch ideal,
- but runtime gating may temporarily skew this for stability.

This is the safest first design. It keeps branches interpretable and separate.

---

## 10. Cross-branch cache coupling

There are three implementation levels.

### Level 1: output-only fusion

- branches run independently,
- only outputs are fused.

Safest and easiest.

### Level 2: weak cache coupling

- branch queries may weakly attend to transformed opposite-branch cache.

More expressive and closer to the Möbius-tape concept.

### Level 3: shared intermediate memory

- both branches read/write a slower shared memory layer `M_t`.

Most powerful, but introduces additional stability concerns.

---

## 11. Window geometry

Each branch has its own active window.

### Forward branch window

Tracks the ordinary stream orientation:

- recent input,
- active recent outputs,
- most recent local stream state.

### Backward branch window

Tracks the conjugate/reversed/transported orientation:

- transformed expired content,
- residual branch state,
- future-constraint-like or anti-causal-like organization,
- optional reversed ordering.

The architecture does not force a single implementation of the backward window.
That choice is a design axis to be explored.

---

## 12. Memory policy

### Forward cache `C⁺`

Use ordinary recent KV/value cache semantics.

### Backward cache `C⁻`

Use transported cache states received from the opposite branch.

Possible storage policies:

- exact residual slots,
- decayed residual slots,
- compressed residual slots,
- saliency-selected residual slots,
- multimodal residual slots.

### Shared memory `M`

Optional slower shared memory can contain:

- textual summaries,
- retrieved facts,
- multimodal anchors,
- operator goals,
- branch agreements,
- stabilized symbolic motifs.

---

## 13. Stability constraints

Main risks:

- echo loops between branches,
- self-amplification of hallucinated content,
- unstable oscillation between mutually reinforcing branch states,
- overdominance of one branch,
- cache blowup in both directions.

Mitigations:

- bounded branch windows,
- bounded cache sizes,
- decayed transport,
- weak cross-branch coupling at first,
- confidence/saliency gating,
- provenance tags for self-generated vs external content,
- periodic semantic stabilization through `M_t`,
- operator-level reset/prune hooks.

---

## 14. Multimodal extension

The architecture extends naturally if stream slices include:

- text chunks,
- image tokens,
- audio frames,
- retrieved memory bundles,
- code states,
- self-generated segments,
- external event traces.

The Möbius-tape idea does not depend on text-only data. It requires only:

- a branchable stream representation,
- a transport map,
- branchwise cache persistence,
- and cross-branch fusion.

---

## 15. Relation to existing repository geometry

This architecture appears strongly aligned with existing formal surfaces in the
repository.

The most relevant analogies are likely:

- doubled/Krein carrier structures,
- split `Cl(1,1)` plus/minus channel decompositions,
- projector/equivariance surfaces,
- restricted-sheet transport,
- CPT/conjugation operators,
- hyperbolic/boost transport laws.

In software terms, the architecture reads like a two-branch memory runtime.
In geometric terms, it resembles a doubled carrier with transport between two
orientations.

That is a strong sign that the runtime architecture and the repository’s formal
language may be made compatible later.

---

## 16. Prototype roadmap

### Phase A: symmetric runtime wrapper

- one frozen transformer family,
- two equal branch runtimes,
- two active windows,
- two bounded caches,
- no cross-branch raw attention yet,
- output fusion only.

### Phase B: transport-enabled branches

- define `Γ₊₋`, `Γ₋₊`,
- move expired cache entries across branches,
- add branch-specific decay and transport tags.

### Phase C: weak cross-branch interaction

- expose transformed opposite-branch cache weakly,
- gated branch fusion,
- monitor resonance and failure modes.

### Phase D: shared semantic stabilization layer

- shared summary memory,
- motif stabilization,
- multimodal grounding,
- operator goal alignment.

### Phase E: later formalization

Once the runtime behavior is validated, formalize:

- branch transport laws,
- closure properties,
- projector-based branch decomposition,
- doubled-space dictionary,
- and eventual link to existing Krein / split-lane formal surfaces.

---

## 17. Appendix: Two-Lane Weak-Value Attention

This appendix records a weak-measurement-inspired attention law for the twin
Möbius tape architecture.

The goal is not to literally swap query and key roles. The correct import from
weak-measurement intuition is instead:

- a pre-selected branch,
- a post-selected/conjugate branch,
- weak cross-branch influence,
- and low-disturbance memory update.

### 17.1 Branch roles

Interpret the two branches as:

- forward branch = pre-selected lane,
- backward/conjugate branch = post-selected lane.

At the current step, each branch contributes a conditioned readout.

### 17.2 Forward branch attention

Let:

- `Q⁺` be the current forward query state,
- `(K⁺, V⁺)` be the forward branch key/value state.

Then the forward branch attention is:

- `A⁺ = softmax((Q⁺ (K⁺)^T) / sqrt(d) + B⁺) V⁺`

where `B⁺` is the usual branch-local positional or structural bias.

### 17.3 Backward branch attention

Let:

- `Q⁻` be the current conjugate/backward query state,
- `(K⁻, V⁻)` be the backward branch key/value state.

Then the backward branch attention is:

- `A⁻ = softmax((Q⁻ (K⁻)^T) / sqrt(d) + B⁻) V⁻`

where `B⁻` may include:

- residual penalties,
- orientation tags,
- decay terms,
- conjugate branch position rules.

### 17.4 Weak-value style fusion

The simplest two-lane weak-value fusion is a weighted combination:

- `A = α A⁺ + β A⁻`

with:

- `α + β = 1`,
- typically `α >= β`,
- and `β` small in the first implementation.

This is the safest branchwise fusion law.

### 17.5 Compatibility-gated weak fusion

A stronger variant uses a compatibility gate between the two branches:

- `A = A⁺ + ε G(A⁺, A⁻) ⊙ A⁻`

where:

- `ε` is weak coupling strength,
- `G(A⁺, A⁻)` is a branch agreement or compatibility gate,
- `⊙` is headwise or componentwise gating.

This encodes the idea that the conjugate branch should influence the present
weakly unless it is compatible with the forward branch.

### 17.6 Query/key role clarification

The weak-measurement analogy should not be implemented as a naive query-key
swap.

The recommended role interpretation is:

- query = present interrogation,
- key = branch-specific address structure,
- value = recoverable branch content.

If a stronger asymmetric version is desired later, use a transformed or twisted
query on the conjugate branch rather than swapping query and key outright.

### 17.7 Conjugate-query variant

A future extension may define:

- `Q⁻ = Θ(Q⁺)`

where `Θ` is a branch-twist/conjugation map.

Then the backward branch attention becomes:

- `A⁻ = softmax((Θ(Q⁺) (K⁻)^T) / sqrt(d) + B⁻) V⁻`

This is a better analog of two-state / pre-post-selected conditioning than a
literal key-query exchange.

### 17.8 Low-disturbance residual update

The weak-measurement analogy is strongest in the memory update law.

Residual memory should be updated weakly:

- `V⁻_{t+1} = (1 - α_mem) V⁻_t + α_mem Φ(W_t, V⁻_t)`

with:

- `α_mem << 1`

so that the conjugate branch is influenced gradually rather than overwritten.

This is the runtime analogue of low-information-gain / low-disturbance update.

### 17.9 Recommended implementation order

The recommended progression is:

1. branchwise independent attention,
2. weighted two-lane fusion,
3. compatibility-gated weak fusion,
4. conjugate-query branch,
5. slow residual memory update.

This preserves stability while keeping the weak-value interpretation meaningful.

## 18. Summary

The Twin Möbius Tape Transformer is a symmetric two-branch streaming runtime.

Its central claims are:

- there are two equal streams,
- there are two equal cache branches,
- what exits one branch is transported into the other,
- present inference is fused from both,
- the process is closed and recirculating rather than one-way and forgetful.

The architecture is therefore not merely bidirectional attention.
It is a closed-loop twin-transformer memory geometry in which forgetting becomes
cross-branch transport and memory becomes a recirculating tape.
