# Local adaptation for info-geometry-lean

This repository adaptation keeps the useful mathematical discipline from
`auto-formalizing-skills` while overriding its Claude-specific harness rules.
The local authorities are, in order:

1. `AGENTS.md`
2. `docs/CANONICAL_AGENT_PIPELINE.md`
3. `docs/HIVE_AGENT_COMMANDMENTS.md`
4. the protected-baseline skill at `.pi/skills/protected-baseline-formalization/`
5. the owner Lean source and kernel output

The upstream Markdown is retained under `../upstream/` for reference only. Do
not follow instructions there that conflict with the authorities above.

## Local execution model

Pi uses this skill as a single local agent workflow. The upstream three-tier
Leader/Orchestrator/Worker design is a planning model, not a license to spawn
unavailable subagents or concurrent compiler jobs. Execute the roles
sequentially in the current session:

- **Researcher:** read-only repository and Mathlib search; report exact paths and
  signatures, never guessed identifiers.
- **Refuter:** read-only statement audit and runnable `/tmp` counterexample;
  absence of a counterexample is not a proof.
- **Formalist:** edit the smallest owner file and close the theorem with a real
  proof.
- **Critic:** inspect the diff, theorem axioms, and fake-closure markers.
- **Archivist:** record only durable task state when explicitly requested.

Do not claim that a multi-agent race or background worker occurred. If a task
needs parallel research, parallelize only read-only searches and never builds.

## Protected Lean loop

1. Read the routing documents and inspect `git status`; preserve unrelated work.
2. State the exact mathematical proposition and identify its owner.
3. Search the whole repository by symbol, type shape, namespace, imports, and
   dependents before adding an abstraction.
4. Audit signs, carriers, bases, quantifiers, and hypotheses against existing
   owners. Prefer reusable lemmas over duplicate bridges.
5. Keep source complete: no `sorry`, `admit`, custom `axiom`, proxy certificate,
   hypothesis-packaging, vacuous theorem, or unsupported physical claim. The
   upstream “posit a `sorry` child” mechanism is translated locally into a
   non-source research note or an explicit user-facing mathematical fork; never
   land a temporary sorry in Lean.
6. Edit only the owner surface, then immediately stage with `git add -A` (use
   `git add -f` for this ignored local skill directory).
7. Before any build/check command, inspect compiler processes. Never run concurrent
   Lake/Lean/test commands, never kill a running task, and never run `lake clean`
   or delete any `.lake` cache. Use
   `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock <module>`
   for module builds.
8. Treat warnings as actionable. A narrow green check is not repository closure;
   distinguish it from a fresh full build and axiom audit.

## `/check` adaptation

`check` is read-only. Pin the on-disk statement, search the trap catalog, and
run any counterexample only in `/tmp`. Re-run every claimed counterexample
locally. Report `FALSE`, `CONDITIONAL`, `NO-COUNTEREXAMPLE-FOUND`, or `UNCERTAIN`;
never report `PROVEN` from a search.

## `/prove` adaptation

`prove` means a close-first proof attempt with explicit owner-file edits. Use the
upstream protocol and contracts as checklists, but replace their `sorry`-based
frontier with a truthful local status: proven, transitively blocked by an
existing debt, or a precise mathematical stop. Do not manufacture a proof tree
or a new file merely to satisfy the workflow. Every accepted theorem must pass
kernel checking and the repository's axiom/proxy/vacuity gates.

## `/handoff` adaptation

There is no live Claude orchestrator to stop. A handoff is a bounded snapshot of
actual on-disk state: changed files, exact build command/results, remaining
errors, next owner theorem, and unresolved mathematical choices. Do not claim a
clean or committed checkpoint unless independently verified. Do not revert or
clean unrelated concurrent work.

## Persistent state

Use the repository's existing `.runtime/`, `PLAN.md`, `LEADER.md`, or artifact
conventions only when the task explicitly calls for them. Do not commit generated
runtime artifacts, reports, or scratch files. Keep Lean/CAS witnesses in their
mandated locations and treat CAS, graph, transcript, and model output as
navigation evidence rather than proof authority.
