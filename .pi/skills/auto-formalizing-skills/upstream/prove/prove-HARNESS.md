# prove-HARNESS.md — verified harness mechanics for the 3-tier /prove orchestration

Field-verified facts about how the LEADER → ORCHESTRATOR → WORKER tiers actually behave on
this harness. `prove-PROTOCOL.md` (orchestrator manual) and the `/prove` leader command point
here. When a mechanic is re-verified or changes, update THIS canonical home + the pointers.

## ⭐ Worker dispatch: FOREGROUND-concurrent (DEFAULT) vs run_in_background (resume-only)

The orchestrator dispatches workers via the Agent tool. Two modes, with a REAL tradeoff —
choosing wrong is what caused the "bubble bug" pain:

- ⭐ **FOREGROUND concurrent — the DEFAULT for parallel / bulk work.** Issue MULTIPLE `Agent`
  calls in ONE assistant turn: they run CONCURRENTLY and their returns come back **DIRECTLY to
  the orchestrator** as that turn's tool results. **No bubble — the orchestrator processes its
  own worker returns in place.** This is the right mode for fan-out: a wave of independent
  leaves, each on its OWN file, fired together and collected together. Cadence: dispatch a
  batch → collect the batch → audit/commit → dispatch the next. Costs: (a) the orchestrator
  blocks until the batch returns (fine for dispatch→collect→next); (b) all returns land in the
  orchestrator's context (compaction pressure — see Auto-compaction below).

- **`run_in_background: true` — RESERVE for the FEW hard nodes that need RESUME.** A background
  worker can be RESUMED by its `agentId` later, with the orchestrator's ruling, context intact
  (the return-then-resume pattern for a hard node the orchestrator must adjudicate before the
  worker continues). BUT: ⚠ **THE BUBBLE BUG** — a background worker's COMPLETION NOTIFICATION
  routes to the TOP-LEVEL main session (the **LEADER**), NOT to the spawning orchestrator
  (SubagentStop hooks fire in the main session; no documented config reroutes a nested
  grandchild's completion to its immediate parent — claude-code-guide verified against the docs;
  GH issues open). So a bg worker's result reaches the orchestrator only via a LEADER FORWARD.

**RULE.** DEFAULT to FOREGROUND-concurrent dispatch (direct returns, no bubble, no forwarding).
Use `run_in_background` ONLY when you genuinely need agentId-resume on a specific hard node —
and then expect the LEADER to forward that worker's return digest to you.

## Leader-forward SOP (only for the run_in_background case)

When a `run_in_background` worker's completion bubbles to the LEADER (main), the leader extracts
a FAITHFUL DIGEST (the worker's actual findings — NOT the leader's own re-ruling) and SendMessages
it to the orchestrator, which ground-truths it (M1: glue-compiles ≠ leaf-true; #print axioms before
trusting "proven") and acts. With foreground-concurrent dispatch this whole channel is unnecessary.

## Auto-compaction (subagents) — CONFIRMED WORKING

- Official docs: subagents auto-compact with the SAME logic as the main conversation. This works
  out of the box — no special configuration is required for the long-lived orchestrator to compact
  and recover in place.
- ✅ **GROUND-TRUTHED (grep `"type":"system","subtype":"compact_boundary"` in the subagent
  transcripts at `<project>/<sessionUUID>/subagents/agent-<agentId>.jsonl`):** an orchestrator subagent
  DOES auto-compact and SURVIVE. One /prove orchestrator (146 worker dispatches) auto-compacted **3×**
  (`trigger:auto`, `compactMetadata.preTokens` ≈1.0M each) and KEPT WORKING to a 14M transcript; the
  leader/main compacted at ≈787K. ⚠ An earlier "subagent auto-compaction
  doesn't fire" belief was WRONG — a pure artifact of orchestrators that were TOLD to clean-quiesce below
  the threshold (they bowed out before reaching it); "0 compactions" meant "never got the chance", NOT "broken".
- A subagent CANNOT manually self-trigger `/compact` (Agent-SDK-only), and does NOT need to: auto-compaction
  fires for it automatically BETWEEN turns while it keeps working. (Ending a turn merely to AWAIT async worker
  results is normal and fine — that is NOT "exiting"; the parent resumes it when the results arrive.)
- ⟹ **THE ORCHESTRATOR WORKS CONTINUOUSLY AND NEVER VOLUNTARILY EXITS** (directive: never let the
  orchestrator exit — do not exit even if you might die mid-task). Let auto-compaction fire at the threshold and recover IN PLACE
  via M10 (re-read PROTOCOL + PLAN.md + disk). Do NOT clean-quiesce, do NOT ask to be re-spawned, do NOT bow
  out to "avoid a hard death". If an involuntary death ever comes, the disk (commits + `PLAN.md` = the M10
  anchor) makes it fully recoverable and the LEADER re-spawns from there — but the orchestrator's job is to
  RIDE THROUGH, never retreat. **There is NO "clean-quiesce fallback" — that guidance is DELETED.** The only
  non-death re-spawn is a USER-initiated cross-conversation `/handoff`.

## agentId-resume + the message hierarchy (parent→child / child→parent)

- A parent (orchestrator) RESUMES a background child by its `agentId` with a follow-up message,
  context intact. A child CANNOT live-SendMessage its spawning orchestrator (a child only knows
  the recipient `"main"`); a worker's ONLY up-channel is its RETURN VALUE.
- orchestrator(background) → LEADER: SendMessage to `"main"` works (route-reports).
- LEADER → orchestrator: agentId-resume (SendMessage the orchestrator's `agentId`).
- Trust model (UNIVERSAL, both directions, every tier): any claim — returned, resumed, forwarded,
  or messaged — is a SUGGESTION the RECIPIENT ground-truths (compiler + disk: `#print axioms`,
  `lake build`, grep, the on-disk decl body) BEFORE acting. Reading ≠ proving.
