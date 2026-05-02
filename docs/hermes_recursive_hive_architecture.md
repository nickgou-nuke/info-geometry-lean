# Recursive Hermes Hive Architecture

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

Status: design doctrine
Date: 2026-04-23
Scope: Hermes-wrapped backend workers inside the packetized Hive.

## 1. Core ontology

Hermes is not one backend.

Hermes is the doctrinal wrapper:
- memory discipline,
- skills,
- packet protocol,
- lineage law,
- authority boundaries,
- repo-local role identity.

A backend is an embodiment:
- Codex CLI,
- Gemini CLI,
- Copilot CLI,
- local OpenAI-compatible model,
- provider-mediated model when explicitly allowed.

Therefore:

```text
Hermes[backend] = Hermes wrapper + backend embodiment + role discipline
```

The Hive is not a raw model swarm. It is a recursive ecology of
Hermes-wrapped backend workers:

```text
HermesHive
  -> Hermes[CodexCLI]
  -> Hermes[GeminiCLI]
  -> Hermes[CopilotCLI]
  -> Hermes[LocalProver]
  -> Hermes[LocalAuditor]
```

The model/CLI is the embodiment. Hermes is the operational soul.

## 2. HermesHive

HermesHive is the meta-shell above individual Hermes workers.

Responsibilities:
- task routing,
- packet classification,
- backend selection,
- memory discipline,
- skill loading,
- lineage enforcement,
- retry/backoff policy,
- authority-boundary enforcement.

HermesHive does not certify theorem truth.

It governs passage.

## 3. Backend specializations

### Hermes[CodexCLI]

Role:
- condenser,
- reviewer,
- formalizer-adjacent worker,
- strict coder,
- code-aware compressor.

Temperature:
- low.

Strength:
- local consistency,
- patch hygiene,
- executable narrowing,
- import/module discipline,
- code review,
- build-facing repair.

Risk:
- over-condensation,
- premature deletion of weak but fertile prima materia.

Default use:
- code edits,
- review,
- refactor compression,
- proof-surface narrowing,
- build/gate preparation.

### Hermes[GeminiCLI]

Role:
- high-pressure symbolic dreamer,
- bridge ideator,
- future-pass expander.

Temperature:
- high.

Strength:
- motif generation,
- strange bridge hypotheses,
- symbolic expansion,
- broad analogy search.

Risk:
- inflation,
- fake repo claims,
- drift from executable surfaces.

Default use:
- guarded symbolic expansion only,
- never automatic polling,
- explicit-operator-use sidecar.

### Hermes[CopilotCLI]

Role:
- medium-hot code-shaped symbolic interpolator,
- generative coder,
- pattern expander.

Temperature:
- medium-high.

Strength:
- candidate code forms,
- rapid symbolic completion,
- alternate theorem formulations,
- bridge sketching.

Risk:
- implementation confabulation,
- invented imports/declarations,
- plausible but false local details.

Default use:
- candidate packet expansion,
- preliminary code-shaped formulations,
- inputs to Codex condensation.

### Hermes[LocalProver]

Role:
- Lean proof-specialist lane.

Embodiments:
- DeepSeek-Prover,
- LeanDojo/ReProver,
- other local proof models.

Authority:
- proposal only.

Lean remains the proof authority.

### Hermes[LocalAuditor]

Role:
- conservative critique and audit-prep lane.

Embodiments:
- Goedel-Prover,
- local audit models,
- deterministic audit scripts.

Authority:
- proposal/audit-prep only unless routed through AuditBee.

## 4. Shared inheritance

Every Hermes worker inherits:
- core repo doctrine,
- packet schemas,
- authority lattice,
- representation metadata rules,
- owner/shadow discipline,
- no-fake-closure law,
- Black Book intake law,
- negative-antiproof law.

Every Hermes worker may additionally have:
- backend-local preferences,
- role-local skills,
- model-specific prompting,
- temperature/pressure profile,
- transport policy.

The point is sameness of doctrine with diversity of embodiment.

## 5. Packet law

Hermes workers may emit:
- `TheoremCandidatePacket`,
- `RetrievalHypothesisPacket`,
- `ProposalPacket`,
- `CritiquePacket`,
- `ExecutionIntentPacket` only after critique/freeze policy,
- deadend/residue/negative-antiproof packets.

Hermes workers may not directly emit:
- `LeanVerificationPacket`,
- `BuildPacket`,
- `AuditPacket`,
- `PromotionDecisionPacket`.

Those are authority-gate packets.

## 6. Authority law

No Hermes wrapper is final truth.

Even Hermes[CodexCLI] remains below authority.

Truth and integration still pass through:

```text
Lean
  -> BuildBee
  -> AuditBee
  -> PromotionBee
```

Hermes may dream, compress, critique, refactor, and route.

Logos gates decide what survives.

## 7. Transport law

Default provider contact should flow through one persistent Codex CLI-backed
worker when possible.

Do not fan out many cold direct provider/API connections.

If provider contact fails:
- classify as `provider_unavailable`,
- mark `environment_blocked`,
- set `failure_kind = retryable_transport_failure`,
- do not treat it as theorem failure,
- restart or resume one canonical Codex CLI-backed session.

## 8. Thermodynamic reading

The recursive Hermes Hive is a heat engine:

```text
Hermes[GeminiCLI] / Hermes[CopilotCLI]
  -> heat / symbolic expansion / candidate gas

Hermes[CodexCLI]
  -> condensation / compression / executable narrowing

Lean/build/audit/promotion
  -> phase-stability and authority gates

deadends / Black Book / future-pass
  -> vapor capture and negative expertise
```

The system is healthy only if it preserves both:
- positive condensates,
- non-condensed residue.

## 9. Relation to NemoClaw/OpenShell

NemoClaw/OpenShell provide the secure runtime envelope.

They are not the theorem authority and not the mathematical planner.

They host the assistant/runtime substrate in which Hermes workers and Codex CLI
operate under policy.

The canonical layering is:

```text
NemoClaw/OpenShell
  -> HermesHive
  -> Hermes[backend] workers
  -> Lean/build/audit/promotion gates
```

## 10. Doctrine

The Hive is not a collection of unrelated model backends.

It is a recursive Hermes ecology:

```text
a packet-governed metahive whose bees are Hermes-wrapped backend embodiments,
each carrying memory, skills, role discipline, lineage law, and authority limits.
```

Codex specializes in condensation/formalization.

Gemini and Copilot specialize in symbolic expansion and creative interpolation.

HermesHive governs passage.

Lean/build/audit/promotion remain the Logos gates.
