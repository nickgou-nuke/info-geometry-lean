# Collected Lean Skills

This file records the concrete capabilities available from the vendored public
repositories and how they line up with the local repo skill stack.

## Skill pack: `cameronfreer/lean4-skills`

Workflow commands:
- `draft`
- `formalize`
- `autoformalize`
- `prove`
- `autoprove`
- `checkpoint`
- `review`
- `refactor`
- `golf`

Use this pack when you want a host-agnostic Lean workflow loop with explicit
stop budgets and proof cleanup.

## Other vendored Lean tools

| Repo | Capability |
| --- | --- |
| `ulamai/ulamai` | Agent-facing Lean theorem proving and formalization |
| `lean-dojo/LeanDojo` | Lean data extraction and programmatic interaction |
| `lean-dojo/LeanCopilot` | Lean proof copilot / inference tooling |
| `leanprover-community/aesop` | White-box automated proof search |
| `Paper-Proof/paperproof` | Proof-state visualization and inspection |
| `project-numina/numina-lean-agent` | Lean agent workflow tooling |
| `leanprover-community/repl` | Lean REPL for errors and sorries |

## Local repo alignment

The repo-local skills that already cover most of the same surfaces are:
- `lean4`
- `lean-proof`
- `proof-only-mandate`
- `lean-bisect`
- `mathlib-build`
- `mathlib-review`
- `paperproof-validator`
- `lean-dag-wire-refactor`
- `mission-loop`
- `closure-mission-loop`
- `closure-debt-proof`
- `categorical-infrastructure-projection` — project categorical infrastructure onto concrete matrix computations (GEPA: `tools/infra/gepa_categorical_projection.py --evolve`)
- `virasoro-finite-to-infinite-transition` — finite-to-infinite bridge work
- `sympy-lean-handoff` — verify exact algebraic/group identities in SymPy and translate them into Lean 4 owner theorems
