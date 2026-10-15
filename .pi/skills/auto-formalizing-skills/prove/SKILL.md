---
name: auto-formalizing-prove
description: Apply the adapted top-down Lean formalization workflow to a precise theorem or owner file in info-geometry-lean. Use for proof repair, theorem completion, dependency search, and honest kernel-checked closure.
---

<!-- repository-context-rule -->
## Repository context rule

For repository work, the current checked-out codebase is the context. Search
existing implementation and trace actual carriers, definitions, imports,
instances, theorem statements, and uses before claiming a structure is missing
or incorrect. A local absence is not a repository-wide absence. Names,
heuristics, summaries, and documentation guide discovery but do not override
source. Follow `docs/REPO_DEEP_SEARCH_PROTOCOL.md` before repo-wide gap claims.


# Adapted prove workflow

Read `../shared/local-flow.md` first. Then read the relevant portions of:

- `../upstream/prove/prove-PROTOCOL.md`
- `../upstream/prove/prove-CONTRACTS.md`
- `../upstream/prove/prove-TRAPS.md`

The upstream protocol supplies useful adversarial and consumer-minimal proof
engineering. Its Claude Workflow, pinned models, background workers, and
`sorry`-frontier instructions are not operative here; the local flow above wins.

## Procedure

1. Pin the headline or target declaration from Lean source. If the request is
   informal, state the quantifiers, carrier, hypotheses, and intended owner
   before editing.
2. Search all Lean, scripts, tests, and imports for the declaration and its
   dependents. Check existing categorical and algebraic owners before creating a
   bridge. For this repository, graph/CAS/oracle results are navigation only.
3. Run a narrow baseline check when safe. Before the command, inspect
   `ps -C lake -C lean -o pid,stat,etime,args`; wait for any active compiler job.
   Use the locked runner for Lake module builds and never use `lake clean`.
4. Attempt the smallest complete proof first. Add private helpers with genuine
   proofs when they belong to the same owner. Do not add a hypothesis matching
   the conclusion, and do not hide missing mathematics behind `sorry`, `admit`,
   an axiom, `unsafe`, or a proxy structure.
5. If the statement is false or over-strong, stop editing the owner and report a
   precise correction with a runnable `/tmp` witness when possible. If a genuine
   prerequisite is absent, report the exact missing proposition as a research
   boundary rather than landing a temporary sorry.
6. Stage every source/document change immediately. Re-run the owner check after
   each edit, then inspect warnings, `#print axioms`, and fake-closure markers.
7. Report facts separately: changed paths, exact command and exit status, kernel
   evidence, remaining debt, and whether a full repository build was performed.

## Required closure checks

For a completed target, verify the actual declaration body and run the applicable
axiom audit. A narrow successful module build does not establish repository-wide
closure. Do not claim completion while unrelated active writers or compiler jobs
make the result stale.

## Useful entrypoint semantics

When invoked with an argument, interpret it as a theorem statement, an owner-file
path, or a task plan. For a read-only truth question, use
`/skill:auto-formalizing-check` instead. For cross-session state capture, use
`/skill:auto-formalizing-handoff` instead.
