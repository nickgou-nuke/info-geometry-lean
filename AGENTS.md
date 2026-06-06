# Repository Agent Routing

> Canonical pipeline: read `docs/CANONICAL_AGENT_PIPELINE.md` first for the
> current repo path, tool routing, aiClaw queue discipline, Pi extension stack,
> GEPA flow, and forbidden legacy routes. If a generated transcript or archived
> routing note conflicts with it, `docs/CANONICAL_AGENT_PIPELINE.md` wins.

For DAG/Arango/LeanTrail/Hodge/de Bruijn/WL redundancy cleanup, namespace
deduplication, stale dropin removal, pure forwarding module collapse, or
compatibility-shim refactors, use:

```text
skills/lean-dag-wire-refactor/SKILL.md
```

> ⚠️ **CRITICAL: CATEGORICAL INFRASTRUCTURE EXISTS BEFORE YOU REWRITE**
> Read `docs/CATEGORICAL_INFRASTRUCTURE_MAP.md` first.
> The categorical layer (`Algebra/Grothendieck.lean`,
> `Canonical/TensorTowerColimit.lean`, `Categorical/FibonacciBraiding.lean`)
> is the owner. Matrix-level code is an *instance*, never a replacement.
> Do not rebuild what already exists.

For categorical-infrastructure-projection tasks, see the central
skill library at:

```text
skills/lean-skill-library/
```

The skill is `categorical-infrastructure-projection` in the local catalog.
GEPA: `tools/infra/gepa_categorical_projection.py --evolve --generations 10`

Core law:

```text
Graph tools identify candidate wires.
Lean owner files decide truth.
Only kernel-checked source edits count.
```

For aiClaw/ChatGPT-assisted proof repair, use:

```text
skills/socratic-oracle-proof-repair/SKILL.md
docs/AICLAW_CHATGPT_REVIEW_RUNBOOK.md
```

ChatGPT is a Socratic auditor and repair suggester only. Do not stack prompts;
poll aiClaw status, send the complete owner file plus all relevant build errors
in one prompt, wait/read the final visible answer, then use the answer as a
full-file replacement candidate only if it survives Lean checking. Keep the
corrected file small and mathlib-style. Do not claim hidden chain-of-thought
recovery. Prefer
`tools/infra/socratic_clawbot.py --dry-run --json` for Lean owner-file oracle
prompts; it delegates transport safety to `tools/infra/aiclaw_chat.py`.

The aiClaw lane is single-flight per platform. Check
`python3 tools/infra/aiclaw_chat.py queue-status --platform chatgpt` before
sending. If a prompt returns `Thinking`, times out after send, or otherwise
needs browser readback, do not send another prompt until the final visible
answer is recorded and the lane is released with `queue-release`.

All repo-owned ChatGPT browser senders must use this same lane. Do not call the
old port-1956 WebSocket bridge directly, do not use raw browser-harness DOM
injection without `tools/infra/chatgpt_lane_guard.py`, and do not press Enter as
a fallback when ChatGPT has not exposed an enabled send button.

For the external formal precedent, read:

```text
docs/DEBATE_ORACLE_CONVERGENCE_MAP.md
```

`external_refs/deepmind-debate` is an adversarial stochastic debate correctness
source, not a blanket chatbot-convergence theorem.

Keep graph evidence as navigation evidence only. Do not edit dirty external
submodules unless explicitly requested.
