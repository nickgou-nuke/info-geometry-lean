---
name: erlangen-2-0-synthesis-workflow
description: Ground speculative Erlangen, Cuntz, exceptional-algebra, and Lax-flow claims in existing Lean owners before proposing a proved bridge.
metadata:
  short-description: Repository-grounded synthesis for speculative operator-geometry claims
---

# Repository-grounded synthesis workflow

Use this skill when an intake links split-octonions, exceptional symmetries,
Cuntz systems, Cantor addresses, categorical limits, Lax equations, or mass-gap
language and asks for a unified Lean formalization. Treat “Erlangen 2.0” as an
intake label, not as an existing mathematical structure.

## Route and authority

Apply these repository skills together:

- [`epistemic-compilation`](../epistemic-compilation/SKILL.md) for claim
  extraction, theorem contracts, causal order, and verification status;
- [`anomaly-resolution`](../anomaly-resolution/SKILL.md) when a failed identity
  has a concrete defect operator;
- [`darwinian-codebase-epistemology`](../darwinian-codebase-epistemology/SKILL.md)
  when declaration fingerprints, commit ancestry, or Arango graphs are used.

The Lean owner and its kernel-checked theorem are the evidence. Search results,
skill inventories, comments, generated prose, Arango edges, AST/hash matches,
and CAS output only help locate candidates. Follow
`docs/REPO_DEEP_SEARCH_PROTOCOL.md` before making repository-wide absence or
novelty claims. For colimit or categorical-limit claims, read
`docs/CATEGORICAL_INFRASTRUCTURE_MAP.md` and extend the categorical owner; do
not replace it with a finite matrix model.

## Candidate owners to inspect

These paths are search seeds, not guarantees that a requested theorem exists:

- Günaydin–Gürsey algebra: `lean/InfoGeometry/Canonical/`,
  `lean/InfoGeometry/Superalgebra/`, and
  `lean/InfoGeometry/Lie/CanonicalZornDerivationDimension.lean`;
- split-octonion derivations:
  `lean/InfoGeometry/Synthesis/G2SplitSedenionDerivationBridge.lean` and its
  imported carrier/equivalence owners;
- Cuntz systems and canonical shift:
  `lean/InfoGeometry/NCG/CuntzColimitKMSTiltGNS.lean`;
- Cantor words and address operations:
  `lean/InfoGeometry/Canonical/TypeIIIModularCantorSystem.lean` and the actual
  Cantor hopping owners under `lean/InfoGeometry/Tessellation/`;
- Zorn Peirce, commutator, and anomaly results:
  `lean/InfoGeometry/NCG/PeirceGradingOperator.lean`,
  `ZornCommutator.lean`, `AnomalyGradeGeneration.lean`, and `CausalPoset.lean`;
- Lax-related algebra:
  `lean/InfoGeometry/Canonical/ManakovZornSolitonLaxBridge.lean` and any
  exact matrix-operator owners found by repository search.

Read the carrier, multiplication, parameter spaces, hypotheses, theorem proof,
and consumers. Do not infer a Lie group, representation, dimension, topology,
flow, or mass gap from a name or a matching equation.

## Boundaries established by the current NCG intake

These are scope guards; recheck the current source before relying on them:

- The current `CuntzSystem` owner bundles the Cuntz relations and proves
  algebraic properties of `Φ(X) = Σᵢ Sᵢ X Sᵢ*`. A finite-word prefix function
  is separate data. No Cuntz representation on Cantor addresses follows until
  an action/representation map and its compatibility laws are constructed.
- A predicate `D(e) = 0` on the existing 14-parameter Zorn-derivation family
  is a stabilizer condition. It does not establish that the solution space is
  an 8-dimensional Lie algebra, isomorphic to `su(3)`, or carries triplet and
  antitriplet representations. Those require a kernel/subalgebra dimension
  proof and explicit action/intertwining theorems on the named carrier.
- `tr([P,L]) = 0` and `tr(L^k [P,L]) = 0` are algebraic trace identities.
  They do not alone define or prove a differentiable Lax flow, isospectrality,
  a positive spectral gap, or a Yang–Mills mass gap. A determinant/kernel
  criterion is not a gap criterion.
- A Cuntz relation, split-octonion identity, or finite-stage calculation does
  not imply an `E₈` lattice closure, fractal topology, categorical colimit,
  type-III factor result, or continuum/mass-gap theorem. Require the precise
  carrier, maps, compatibility, and universal property in the relevant owner.

If an existing source contradicts one of these guards, inspect and cite that
source; the guard itself is not proof authority.

## Workflow

1. Preserve the original intake and provenance. Split it into atomic
   definitions, equations, assumptions, conclusions, and interpretation.
2. Classify each atom as already proved, locally provable, conditional,
   computational evidence, conjecture, or unsupported scope.
3. Search repository-owned Lean sources with `rg`/`rg --files`; trace imports,
   namespaces, consumers, and alternate carriers. Use Arango/Darwin tools only
   when they materially help locate dependencies or lineage. Inspect each
   tool's current CLI and configuration first; never embed credentials in the
   skill or report.
4. Write the ground-truth theorem contract required by
   `docs/CANONICAL_AGENT_PIPELINE.md`: exact claim; carrier and operations;
   owner statements and hypotheses; imports/consumers; smallest gap; adjacent
   unproved claims.
5. Draw a causal DAG only from actual dependencies or proved maps. A conceptual
   analogy or shared fingerprint is not a morphism. If extending a graph or
   complex, define its cells, boundary maps, and chain laws explicitly.
6. State the smallest owner-aligned theorem. For a false identity, define the
   ordered defect and prove its exact component formula before interpreting
   it as a grade generator. Prove nonvanishing separately when claimed.
7. Make the smallest modular Lean change. Preserve the noncommutative or
   nonassociative carrier when that is the subject; do not substitute a scalar
   or diagonal toy for the requested operator theorem.
8. Stage each edit immediately. Before compiling, inspect running compiler
   processes and use the repository's shared locked Lake build. Never run
   concurrent builds or `lake clean`.
9. Run applicable placeholder, semantic-vacuity, and axiom checks. Report the
   exact kernel-verified statement, command, warnings, and open debt. Do not
   claim independent QA unless a separate reviewer actually performed it.

## Acceptance boundary

Promote only the theorem's Lean type and proof scope. Mark unproved bridges as
open debt. A successful compile verifies the proposition Lean was given; it
does not verify that the proposition captures the surrounding narrative.
