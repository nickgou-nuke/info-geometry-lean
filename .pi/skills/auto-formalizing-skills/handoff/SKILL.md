---
name: auto-formalizing-handoff
description: Capture a truthful cross-session handoff for an info-geometry-lean proof task, preserving exact files, build evidence, errors, and next mathematical decisions without pretending unfinished work is complete.
---

<!-- repository-context-rule -->
## Repository context rule

For repository work, the current checked-out codebase is the context. Search
existing implementation and trace actual carriers, definitions, imports,
instances, theorem statements, and uses before claiming a structure is missing
or incorrect. A local absence is not a repository-wide absence. Names,
heuristics, summaries, and documentation guide discovery but do not override
source. Follow `docs/REPO_DEEP_SEARCH_PROTOCOL.md` before repo-wide gap claims.


# Adapted handoff workflow

Read `../shared/local-flow.md` first, then read:

- `../upstream/commands/handoff.md`
- `../upstream/prove/prove-HARNESS.md`

The upstream handoff assumes a Claude Leader/Orchestrator process. This local
adapter has no live orchestrator to stop or drain. It therefore records actual
repository state only and never kills processes, reverts unrelated work, or
claims a clean checkpoint without evidence.

## Procedure

1. Inspect `git status --short`, recent commits, active compiler processes, and
   the exact owner files involved. Preserve unrelated staged or modified work.
2. Gather command evidence: narrow owner checks, locked module-build output,
   full-build output when it has actually run, and any axiom/proxy scans. Record
   failures verbatim enough for the next session to reproduce them.
3. Write or update a handoff document only when requested. Include:
   - repository path and wrong-directory warning;
   - task and precise terminal condition;
   - changed/staged files and whether they are independently verified;
   - current theorem/error frontier;
   - mathematical route, rejected routes, and unresolved choices;
   - exact next commands, with the shared build lock requirement;
   - explicit distinction between kernel evidence, search evidence, and claims.
4. Stage the handoff source immediately. Do not commit unless the user explicitly
   requests a commit. Do not include generated runtime artifacts or scratch
   files unless the repository's protocol requires them.

A handoff is complete when it is a reproducible snapshot, not when the theorem is
finished. Say plainly if a build is blocked by an active external task or if
unrelated writers make the worktree non-quiescent.
