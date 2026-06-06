# Lean Skill Library Catalog

This catalog groups the repo-local skills and the public external skills that
are relevant to Lean 4 theorem proving and this codebase.

## Local repo skills

| Skill | Use |
| --- | --- |
| `lean4` | Lean edits, builds, diagnostics, mathlib search |
| `lean-proof` | Proof search, `sorry` filling, proof cleanup |
| `proof-only-mandate` | No-cheat policy and theorem-honesty checks |
| `lean-mwe` | Minimal reproductions and reduction |
| `lean-bisect` | Regression isolation |
| `mathlib-build` | Build and compile gates |
| `mathlib-review` | Proof/code review |
| `paperproof-validator` | Proof-state visualization and validation |
| `lean-dag-wire-refactor` | Wrapper/wire cleanup and duplicate surface reduction |
| `categorical-infrastructure-projection` | Category-to-matrix projection work |
| `virasoro-finite-to-infinite-transition` | Finite-to-infinite bridge work |
| `sympy-lean-handoff` | SymPy-verified algebra and group facts translated into Lean 4 |
| `mission-loop` | Persistent closure-debt burn-down |
| `closure-mission-loop` | Closure-debt mission orchestration |
| `closure-debt-proof` | Proof debt closure workflow |
| `lean-setup` | Lean environment bootstrap |
| `lean-sandbox` | Isolated Lean execution |

## Public external Lean/proof tooling

| Project | Why it matters |
| --- | --- |
| `cameronfreer/lean4-skills` | Lean 4 workflow pack with `prove`, `autoprove`, `formalize`, `review`, `refactor`, `golf` |
| `ulamai/ulamai` | Lean theorem prover/formalizer that plugs into agent workflows |
| `lean-dojo/LeanDojo` | Lean theorem-proving data/execution tooling |
| `lean-dojo/LeanCopilot` | Lean proof copilot/inference tooling |
| `leanprover-community/aesop` | White-box proof automation tactic library |
| `Paper-Proof/paperproof` | Proof-state visualization and trace inspection |
| `project-numina/numina-lean-agent` | Lean agent workflow/tooling |
| `leanprover-community/repl` | Lean REPL for errors and sorries |

## Vendored local checkouts

These repositories now live under `external_refs/` in this repo.

| Repo | Local path | Lean toolchain |
| --- | --- | --- |
| `cameronfreer/lean4-skills` | `external_refs/lean4-skills` | n/a |
| `ulamai/ulamai` | `external_refs/ulamai` | n/a |
| `lean-dojo/LeanDojo` | `external_refs/LeanDojo` | `leanprover/lean4:v4.28.0` |
| `lean-dojo/LeanCopilot` | `external_refs/LeanCopilot` | `leanprover/lean4:v4.28.0` |
| `project-numina/numina-lean-agent` | `external_refs/numina-lean-agent` | `external_refs/numina-lean-agent/leanproblems/lean-toolchain` |
| `leanprover-community/aesop` | `external_refs/aesop` | `leanprover/lean4:v4.28.0` |
| `Paper-Proof/paperproof` | `external_refs/paperproof` | `leanprover/lean4:v4.28.0` |
| `leanprover-community/repl` | `external_refs/repl` | `leanprover/lean4:v4.28.0` |

## Selection rule

Use the smallest combination that covers the task:

1. Local repo skill first.
2. Add a public external skill only if the local stack lacks a needed
   capability.
3. Keep the library descriptive; Lean proofs remain kernel authority.
