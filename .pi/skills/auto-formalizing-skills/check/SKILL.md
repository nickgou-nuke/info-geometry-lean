---
name: auto-formalizing-check
description: Adversarially check one Lean or mathematical statement in info-geometry-lean using repository definitions, trap analysis, and runnable scratch counterexamples without modifying project source.
---

<!-- repository-context-rule -->
## Repository context rule

For repository work, the current checked-out codebase is the context. Search
existing implementation and trace actual carriers, definitions, imports,
instances, theorem statements, and uses before claiming a structure is missing
or incorrect. A local absence is not a repository-wide absence. Names,
heuristics, summaries, and documentation guide discovery but do not override
source. Follow `docs/REPO_DEEP_SEARCH_PROTOCOL.md` before repo-wide gap claims.


# Adapted check workflow

Read `../shared/local-flow.md` first, then read:

- `../upstream/commands/check.md`
- `../upstream/prove/prove-TRAPS.md`

This is read-only with respect to repository source. Scratch files belong in
`/tmp`; do not create project files, commit, or change theorem declarations.
The upstream multi-agent Workflow is translated into sequential local roles:
researcher, refuter, then critic. Never claim that a search proves a theorem.

## Procedure

1. Pin the exact on-disk declaration if the request gives `file:identifier`.
   Otherwise make the informal quantifier order, domains, carrier, typeclasses,
   and conventions explicit. Ask a question only when two readings disagree on
   truth.
2. Search project definitions and Mathlib APIs by name and type shape. Check the
   recurring traps: free-family quantifiers, vacuous or packaged hypotheses,
   existential degeneracy, domain overreach, per-fibre versus joint claims,
   chart-coordinate extraction, sign/orientation, and degenerate dimensions.
3. For an alleged counterexample, write a self-contained `/tmp/*.lean` scratch
   and run it in the foreground only after checking compiler processes. Re-run
   any decisive scratch yourself; pasted output is not evidence.
4. Return exactly one headline status:
   - `FALSE`: a Lean-confirmed counterexample;
   - `CONDITIONAL`: the minimal missing hypothesis or restricted domain;
   - `NO-COUNTEREXAMPLE-FOUND`: survived the checked lenses, not a proof;
   - `UNCERTAIN`: the search could not settle the required theorem.
5. Include the pinned statement, lenses checked, exact witness or correction,
   scratch path/command, and the limitation that only kernel proof establishes
   truth.

Do not edit the owner file as part of `/check`. If the user wants the corrected
statement formalized, switch explicitly to `auto-formalizing-prove`.
