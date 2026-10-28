---
name: epistemic-compilation
description: Convert informal or confabulated mathematical intake into repository-grounded, kernel-checked Lean theorems.
---

# Epistemic Compilation Skill

Use this skill whenever the input mixes mathematical notation, physical
interpretation, metaphor, generated code, or claims of verification.

## Authority

The authority order is:

1. Lean source in the current checkout and its imported owners;
2. kernel-checked `lake env lean` or locked Lake output;
3. Mathlib declarations actually available through the import graph;
4. navigation evidence such as AST, Arango, CAS, transcripts, and search;
5. prose, prompts, and physical interpretation.

Only the first three levels can promote a theorem claim.

## Required compilation sequence

1. **Freeze intake.** Preserve the source text and provenance. Do not silently
   delete narrative, assumptions, or unsupported interpretation.
2. **Extract atoms.** Split the intake into definitions, equations, hypotheses,
   conclusions, dependencies, and interpretation claims.
3. **Classify scope.** Mark each atom as theorem-backed, locally provable,
   conditional, computational evidence, conjectural, or open debt.
4. **Search owners.** Search the whole repository before judging absence or
   inventing a carrier. Read definitions, imports, instances, theorem bodies,
   and dependents of every relevant owner.
5. **Write a ground-truth contract.** Record the exact carrier, operations,
   conventions, owner declarations, imports, smallest missing statement, and
   adjacent claims that remain unproved.
6. **Normalize causally.** Order only proved dependencies in a causal DAG. A
   conceptual analogy is not an edge, and graph proximity is not equivalence.
7. **Choose the smallest theorem.** Use existing owners and native Mathlib
   structures. Do not create wrappers, witness packets, aliases, scalar toys,
   or duplicate APIs.
8. **Prove explicitly.** Use complete Lean proofs with no `sorry`, `admit`,
   custom axioms, `unsafe`, `: True`, or hidden proof fields.
9. **Verify independently.** Run the narrow Lean check, locked Lake build,
   placeholder scan, semantic-vacuity gate, and axiom inspection. Generation,
   audit, and acceptance must be separate roles.
10. **Report honestly.** State the exact theorem, file, commit, commands,
    axiom footprint, warnings, and remaining open debt.

## Repository-specific graph grounding

This repository has several related, separately owned structures. Search and
cite their actual interfaces rather than merging their names into one presumed
object:

- `lean/DAG/LambdaReductionPreorder.lean` owns a preorder on the repository's
  de Bruijn lambda terms via beta-reduction reachability.
- `lean/DAG/TermDigest.lean` owns the versioned `lean-expr-debruijn-v4`
  structural digest of Lean `Expr`; constants encode their names and universe
  levels, so this is not recursively content-addressed dependency closure.
- `lean/InfoGeometry/NCG/CausalPoset.lean` and
  `lean/InfoGeometry/NCG/AnomalyGradeGeneration.lean` own distinct Zorn-sector
  causal and Peirce-component results.
- Declaration DAG, InfoTree, Hodge/Dirac, and Arango tooling are separate
  navigation or graph constructions unless an owner proves a connecting map.

Do not call these collectively a formalized “noncommutative lambda-calculus
DG” without locating a declaration that defines that combined carrier and
proves the required compatibility maps. A topological-extension proposal may
be recorded as a candidate archetype, but its edges must come from explicit
maps and proved laws; similarity of vocabulary or graph proximity is not a
mathematical morphism.

When the prompt refers to the repo's causal/Darwinian pipeline, use
`skills/darwinian-codebase-epistemology/SKILL.md` for the graph-evidence and
coverage checks. When a classical identity fails on an owner carrier, use
`skills/anomaly-resolution/SKILL.md` to normalize the defect and prove its
component readouts.

## Scope barriers

Finite algebra does not imply topology, a quotient manifold, a colimit,
completion, a physical interpretation, or a classification theorem. A
presentation relation is not a quotient-space construction. A periodic scalar
coefficient is not operator periodicity until the operator carrier is named.
An Euler number is not a surface invariant unless a genuine finite complex or
homological owner is constructed.

When the owner surface is missing, downgrade the claim to explicit open debt
and formalize only the strongest source-confirmed fragment.

## Required result labels

Use one of:

- `[kernel_verified]` — the stated Lean theorem compiled;
- `[accepted_limited_scope]` — a smaller theorem was proved and its boundary is explicit;
- `[bucket_2_conditional]` — the result depends on named hypotheses;
- `[bucket_3_open_debt]` — the requested claim exceeds current owners;
- `[countermodel_found]` — the requested statement is false or overstrong.

Never report “verified” for a stronger narrative claim than the Lean type
actually proves.
