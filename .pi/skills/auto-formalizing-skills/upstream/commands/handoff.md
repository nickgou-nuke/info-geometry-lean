---
description: Gracefully WIND DOWN an active /prove run for a CROSS-CONVERSATION handover — the LEADER tells its background ORCHESTRATOR to STOP dispatching, DRAIN the in-flight workers (integrate their work, never waste it), flush PLAN.md + commit a clean build-green checkpoint, return a final digest; then the leader writes a COMPLETE self-contained HANDOFF.md (incorporating its own LEADER.md strategic model) so a FRESH conversation's /prove resumes with ZERO context loss. A bounded wind-down, not an autonomous build; does NOT run under /goal and never spins. This is the ONLY routine re-spawn path — NOT for the orchestrator's own context recycling (that is auto-compact + M10 in place).
argument-hint: <optional — a note on WHY you are stopping / what to emphasise in the handoff>
---

`/handoff` is the graceful cross-conversation stop protocol for a long autonomous
`/prove` run. It is invoked in the LEADER conversation (the `/prove` main loop). It exists
because a `/prove` run is a three-tier live system — LEADER (you) → one long-lived
background ORCHESTRATOR → WORKERS — and the background orchestrator + its workers DIE when
this conversation ends. So to resume in a NEW conversation you must, in order:
**(1) tell the orchestrator to STOP dispatching — now; (2) DRAIN the in-flight workers
cleanly and integrate their work; (3) flush the tactical state to `PLAN.md` + commit a
clean green checkpoint; (4) write a COMPLETE, self-contained `HANDOFF.md` (folding in your
own `LEADER.md` strategic model)** — so the next conversation picks the run up without
losing a single verified finding.

It is a **bounded** wind-down. It is NOT `/goal`, does NOT `ScheduleWakeup`, and never
spins: drive the orchestrator's drain via SendMessage + the harness's completion
notifications, integrate, then terminate once `HANDOFF.md` is written and the checkpoint is
committed. The terminal condition is **"handoff committed + written + in-flight drained"**
— NOT the headline being sorry-free. `$ARGUMENTS`, if present, is a free-text note on why
you are stopping / what to foreground in the handoff.

**This is the ONLY routine re-spawn path.** Do NOT use `/handoff` for the orchestrator's
own context recycling — that is plain auto-compaction + M10 in place (the orchestrator
rides through it; re-spawning for context would shift the absorption burden onto you). Use
`/handoff` only to stop the WHOLE run for a different conversation / a different day.

---

## §1. STOP dispatching — immediately (tell the orchestrator, now)

The instant `/handoff` is invoked, SendMessage the background orchestrator: **"WIND DOWN
NOW — stop ALL new dispatch this instant; do not start a next wave / round-2 / a re-fix /
a scoping researcher; drain your in-flight workers, flush PLAN.md, commit a green
checkpoint, and send me your final state digest."** Every "just one more agent" is the
NEXT conversation's job; it gets captured in `HANDOFF.md §7`, not dispatched now. The stop
is immediate at the dispatch level even though draining the already-running workers (§2)
takes a few more turns.

(If the orchestrator is already DEAD / unreachable — the harness killed it on context-full
instead of auto-compacting — skip the delegation and reconstruct directly from `PLAN.md` +
`LEADER.md` + a fresh build/trace yourself; note the death in the handoff. Foreground
build/trace/axiom-check commands the leader runs are NOT "new agents" — run them.)

---

## §2. DRAIN the in-flight workers — don't kill, don't waste (the orchestrator does this; you confirm)

Workers already running have **already been paid for**, and killing one risks leaving a
**half-written file on disk** (a broken partial that poisons the next build). So the
orchestrator's default is **DRAIN**: let each in-flight worker finish via its completion
notification, then integrate it. On **each** return the orchestrator (per
prove-PROTOCOL.md §3 / §0dec):

1. **Quality-evals it** (in the user's language) — a one-line honest assessment of what it delivered.
2. **Audits, then decides** — the fill-as-certifier rule governs (*a non-compiling proof is
   WORSE than a `sorry`; only a built file is trusted*):
   - **LANDED** (its module builds by name; sorry-free, or an honest precise posited-child
     per §0ter ASSUME-AND-RECURSE): **keep on disk**.
   - **NON-COMPILING / BLOCKED / half-edited**: **REVERT clean** — `git checkout
     <base-commit> -- <its file>` and `rm` any new file it added — and record the precise
     diagnosis (the exact blocking error / the route it found false) into `PLAN.md` + the
     handoff so the next session re-dispatches from a known state. Never carry a broken
     file into the checkpoint.

**HARD-ABORT variant** (use ONLY if the user explicitly wants in-flight work abandoned, or
a worker is visibly hung / producing clearly-wrong output): stop it (`TaskStop`), revert
ALL its on-disk files to the committed base, and note it as "killed mid-run — re-dispatch
next session". Default to DRAIN; hard-abort is the exception.

While the orchestrator drains, neither tier idle-spins: use the interval to write the
stable parts of `HANDOFF.md` (§4) and to confirm `LEADER.md` is current — they don't
depend on the last worker's return.

---

## §3. Reconcile + commit a CLEAN checkpoint (at quiescence)

Once every in-flight worker has drained, the orchestrator integrates to a single green
checkpoint and flushes the tactical state, so the next conversation gets a **committed**
base + a current `PLAN.md` instead of an uncommitted pile:

1. **Root-register** every LANDED new file in the project's root aggregate module
   (the orchestrator owns the root file — workers were told not to touch it).
2. **ONE full build** — `lake build` and confirm by
   `grep -c "Build completed successfully"` on a **captured log** (a piped `| tail` returns
   exit 0 even on failure — the pipe exit code LIES).
3. **Trace the frontier** (§5 tracer) — record the on-path sorry count + the exact leaves
   into `PLAN.md` (frontier + `N_sorry` + REQUIRED READING refreshed).
4. **Headline `#print axioms`** — confirm no junk axioms entered and the frozen headline
   statement(s) are byte-unchanged.
5. **COMMIT** the checkpoint with a message describing the MATH that landed (NO
   task-numbering like "Wave 12"/"round-1"/"T1.x"; NO `Co-Authored-By: Claude` / "Generated
   with Claude Code" footer; NO reference to `LEADER.md`/`PLAN.md`/`HANDOFF.md`).
6. **Final digest UP** — the orchestrator SendMessages the leader its final state digest
   (HEAD hash, frontier count, what landed/reverted this drain, the current crux + route,
   anything the next session must know). Then the orchestrator stops.

**Green-or-documented, never broken-committed.** If the integrated state cannot be made
build-green (a landed file breaks something un-revertably), revert to the last green
commit, commit nothing broken, and document the broken work + its diagnosis in `PLAN.md` +
the handoff. A clean committed base is worth more than salvaging one half-landed file.

(If NO workers were in flight when `/handoff` fired, skip the drain — the orchestrator just
checkpoints current green work + flushes PLAN.md + digests up. If the orchestrator is dead,
YOU the leader do steps 2–5 yourself from disk.)

**You (the leader) VERIFY the checkpoint yourself** before writing the handoff — re-run the
full build + `#print axioms` + `git status` (Law 6 / §0dec: a digest is a SUGGESTION, not a
fact). Do not write "GREEN" into HANDOFF.md on the orchestrator's say-so.

---

## §4. Write the COMPLETE handoff — `HANDOFF.md`

Write `HANDOFF.md` at the worktree root (gitignored durable scratch — confirm with
`git check-ignore`). It MUST be **self-contained**: a fresh conversation that reads ONLY
`HANDOFF.md` + `LEADER.md` + `PLAN.md` resumes with zero context loss. Then **update
`PLAN.md`'s RESUME POINTER and `LEADER.md`'s direction line to point at `HANDOFF.md`** (so a
bare `/prove` is routed to it).

The template — every section, in order:

- **§0 HOW TO RESUME (first).** The literal restart steps: `cd` to the worktree (note any
  wrong-dir trap); read this + `LEADER.md` (strategic model + DEAD ROUTES) + `PLAN.md`
  (frontier + REQUIRED READING); `git log --oneline`; recreate `/tmp/trace_sorries.lean`
  from §9 and run it; reconcile anything the handoff flags as uncommitted/in-flight; then
  re-invoke `/prove <goal>` — which makes you the LEADER again and **spawns a FRESH
  background orchestrator** (`agentType: prove-orchestrator`, `run_in_background: true`)
  seeded by "read prove-PROTOCOL.md + PLAN.md + LEADER.md + HANDOFF.md, resume the
  descent/glue/fill loop".
- **§1 TASK & TERMINAL CONDITION.** The headline theorem(s); the EXACT terminal (`#print
  axioms <headline>` = EXACTLY `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no
  "modulo"/deferred-baseline); the BYTE-FROZEN headline statements with their `file:line`.
- **§2 CURRENT COMMITTED STATE.** HEAD short-hash, full-build job count + GREEN, the
  frontier count (`N_sorry`), the recent commit chain.
- **§3 THE FRONTIER.** Every on-path `sorry` leaf — full decl name + `file:line` + the
  `sorry` line — clustered by sub-theory. Tell the reader to re-run the tracer for the live
  list. (This mirrors `PLAN.md`'s frontier; HANDOFF.md is the self-contained snapshot.)
- **§4 STRATEGY & ROUTE MODEL.** The global route architecture + the cluster → plan table
  (which leaves, which approach, status) — **lifted from your `LEADER.md` model zone** (the
  strategic mind that was never compacted). Include the DEAD ROUTES summary + MOTHBALLED
  list so the next session does not re-tread them.
- **§5 DEEP RESEARCH FINDINGS — the highest-value section (see §5 below).** Every verified
  research result so the next session does NOT re-research.
- **§6 THIS SESSION'S AGENTS / IN-FLIGHT STATUS.** Each notable worker: role, target file,
  return verdict, key finding (star the ones that change the plan). Plus the reconcile
  procedure for anything left uncommitted, and whether the orchestrator drained cleanly or
  died.
- **§7 NEXT-STEPS PLAN.** Exactly what to dispatch next, with **dependencies** and **target
  `file:line`**, in streaming order; include every deeper posited child surfaced this
  session (the recurse targets).
- **§8 CONVENTIONS & DISCIPLINE.** Everything that keeps the run sound — build-by-module-
  name, fill-as-certifier (REVERT non-compiling), §0ter ASSUME-AND-RECURSE, root-
  registration-by-orchestrator, the subagent `agentType` model/effort pin, commit-message
  rules, the soundness traps (no hypothesis-packaging, no vacuous predicate, the banned
  predicates, comment-free library), the three-tier + SendMessage architecture, the
  two-file state model (LEADER.md strategic / PLAN.md tactical) — distilled from CLAUDE.md +
  prove-PROTOCOL.md + the run's lessons.
- **§9 TOOLS.** The frontier tracer **source embedded verbatim** (NOT a `/tmp` path — `/tmp`
  may be cleared between conversations), the headline axiom-check snippet, and the full-build
  command with the `grep` success-check.

---

## §5. Capture the research — the thing most easily lost

The single biggest waste in a handover is **re-running research the prior session already
did**. Before writing HANDOFF §5, sweep this session for EVERY verified finding (yours +
the orchestrator's final digest + what `PLAN.md` already records) and record it WITH its
verified location:

- researcher returns — existence checks (does lemma X exist? where?), citation `file:line`
  confirmations, route GO/NO-GO verdicts, scope decompositions, counterexample /
  false-as-stated results (these belong in `LEADER.md`'s DEAD ROUTES too);
- every worker's incidental corrections — "this lemma is at `X:line` not `Y`", "this
  citation is stale in the index — grep source", "this sub-claim is FALSE for arbitrary
  inputs, true only for …", "the deep node bottoms at <baseline>";
- the dependency structure discovered (what unblocks what; which posited children are the
  genuine recurse targets).

A finding recorded without its `file:line` is half-lost — the next session pays to
re-derive it. Verified-location-or-it-didn't-happen.

---

## §6. Prohibitions / conventions

- **STOP NEW DISPATCH is absolute.** After `/handoff`, the orchestrator spawns zero new
  workers — not even a "quick scoping researcher." Foreground build/trace/axiom-check
  commands (leader or orchestrator) are fine — they are not new agent work.
- **Drain, don't waste; never carry broken.** Default to letting in-flight workers finish
  and integrating; REVERT any non-compiling/half-edited file; never commit a red build
  (green-or-documented).
- **Verify, don't relay.** The orchestrator's drain/checkpoint digest is a SUGGESTION — YOU
  (the leader) re-run the build + `#print axioms` + `git status` before writing "GREEN" /
  "committed" into the handoff (Law 6 / §0dec).
- **The handoff is OPERATIONAL, not a narrative.** A resume document: exact decl names,
  `file:line`, the embedded tracer, the next-dispatch plan, the route model. Self-contained
  — assume the reader has NO prior context (it is a NEW conversation).
- **Headlines stay byte-frozen;** the handoff records the terminal condition but `/handoff`
  itself does NOT reach it (a pause for handover, not a completion — do not fake progress).
- **Commit messages** describe the math; no task/wave/phase numbering; **never** a Claude
  co-author / "Generated with Claude Code" footer; never name `LEADER.md`/`PLAN.md`/
  `HANDOFF.md`.
- Communicate in **the user's language**; give a one-line quality evaluation of each notable in-flight
  worker as it drains. If you create/update/delete any durable MEMORY, do so per the project
  rule (the LEADER owns memory currency, §0dec(5)).
- **Terminate cleanly.** End with a tight wind-down summary: the committed hash, the
  frontier count (`N_sorry`), where `HANDOFF.md` is, and the one-line "next conversation
  does X". Then STOP — no `/goal`, no `ScheduleWakeup`, no further dispatch.
