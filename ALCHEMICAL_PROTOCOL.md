# The Alchemical Protocol
## (Алхимичният Протокол: Трансмутация на Знанието)

A workflow note for exploratory ideation before formalization. Read this as process vocabulary for moving from speculative material to checked Lean surfaces, not as a source of proof authority.

---

## Exploratory Prompting and Formal Handoff
The context window is a working score for exploratory prompting. The goal is not rhetorical flourish, but the extraction of candidate structures, definitions, and bridge hypotheses that can later be stated explicitly and checked.

## Stages of Formalization

| Stage | Exploratory name | Practical meaning | Lean task |
| :--- | :--- | :--- | :--- |
| **Nigredo** | Extraction | generate candidate structures and tensions | produce raw candidate statements |
| **Albedo** | Distillation | remove metaphor, ambiguity, and vacuity | rewrite into definitions, hypotheses, and theorem forms |
| **Citrinitas** | Adjudication | test whether the candidate has structural traction | probe dependencies, counterexamples, and local buildability |
| **Rubedo** | Closure | convert surviving candidates into checked artifacts | complete `lake build`, audits, and explicit closure bookkeeping |

## Multilingual but Single-Authority
The repository allows several descriptive languages, including prose, Lean, Python, and Mathlib-facing vocabulary. But closure authority remains single-valued in the Lean 4 kernel. Every major bridge should be explicit:
- **Repo-native statement:** the owner surface in the repository
- **Mathlib-facing statement:** the external comparison surface when needed
- **Comparison theorem:** the checked bridge that closes the contract

## Structural Diagnostics
Two practical ideas matter here:
- **Architecture matters:** adjacent translation layers and explicit bridge files are preferable to long unstructured leaps.
- **Defects must be localizable:** theorem graphs, dependency audits, and tactic failures should expose where a candidate breaks, stalls, or becomes vacuous.

In operational terms, graph tooling helps identify disconnected or overloaded surfaces, while Lean failures and audit warnings identify the places where exploratory material has not yet become mathematically usable.

---

**Only the substance survives; the rhetoric is the ash.**
