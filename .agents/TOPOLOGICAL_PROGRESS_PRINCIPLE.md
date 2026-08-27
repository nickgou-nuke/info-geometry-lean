# The Topological Progress Principle for Formal Development

## Prime Directive

> A missing proof or dependency is not a blocker; it is a topological void defining the next development frontier. Do not bridge the void by claiming the impossible or inserting assumptions. Instead, continuously expand the verifiable boundary by proving the exact nearest theorem that locally covers the dependency cone toward the goal.

**Refine missing edges; prove the nearest reachable node; iterate to the goal.**

## Verified Computational Pipeline

External computational systems are discovery and witness-generation engines, not proof authorities.

```text
External computation
  -> explicit witness data
  -> small Lean propositions
  -> distributed kernel proofs
  -> structural assembly
```

GAP, SageMath, Singular, SymPy, Macaulay2, D-module packages, or other CAS tools may propose finite words, matrices, coefficients, normal forms, Groebner reductions, syzygies, decompositions, or other explicit witnesses. They must not supply an imported proposition asserting that the mathematical result is true. Lean verifies the supplied witness on the native carrier.

## Nearest-Provable-Theorem Rule

When a requested target theorem `T` is not derivable from the current verified state:

1. Identify the exact missing premise, construction, or transport edge.
2. Decompose that edge into the smallest natural intermediate dependency sub-DAG.
3. Select the node `Q` closest to the target whose immediate prerequisites are already available.
4. Implement and prove `Q` in Lean with no new unproved assumptions.
5. Add the explicit bridge from `Q` to the next node toward `T`.
6. Repeat in topological order until `T` is closed.

A missing abstraction is therefore a development frontier. It is not grounds for declaring the target impossible when a smaller mathematically meaningful predecessor can still be formalized.

## Topological Closure Invariant

For a fixed target `T`, let `R_T(S)` denote the portion of the target's prerequisite region that is already represented in the current verified state `S`. A successful development step must either close the target or strictly enlarge this verified target-directed frontier:

```text
R_T(S) ⊂ R_T(S')
```

This is intentionally a verified-state notion. It must not be confused with the graph-theoretic `forwardCone` of a single declaration in `ProofDAGRepresentation`, whose order orientation is prerequisite-to-dependent.

Every iteration has one of three valid outcomes:

- **CLOSED**: the requested target theorem is proved.
- **ADVANCED**: a new nearest predecessor theorem is proved and the verified frontier toward the target strictly advances.
- **EXTERNALLY DATA-LIMITED**: the next proof requires genuinely unavailable external witness data. The pipeline may pause to generate that data, but no theorem is assumed in its place.

"Cannot be proved right now" is not a terminal development state if there remains a nearer theorem with available prerequisites.

## Prohibited Shortcuts

Do not replace dependency closure by any of the following:

- `sorry`, `admit`, new axioms, or equivalent unproved assumptions;
- a structure field whose only purpose is to carry the theorem currently missing;
- a guessed orientation, carrier identification, or canonical equivalence;
- treating CAS output as proof authority;
- existential finite search when an external certificate already supplies the exact witness;
- a monolithic global `decide` used in place of distributed certificate verification;
- presenting quotient-level evidence as an exact group equality;
- presenting cardinality arithmetic as a carrier-level bijection or isomorphism;
- promoting a generated table's default branch to a universal theorem.

**Never assume across a missing edge. Refine it until a provable edge is exposed.**

## Distributed Certificate Discipline

For large finite computations, external tools supply data and Lean proves each local claim separately.

```text
CAS/GAP data
  -> fixed witness rows
  -> closed native equalities
  -> cell/subsystem assembly
  -> structural transport
  -> global theorem
```

A row proof should verify the exact exported witness. For example, if GAP exports a PC exponent `e`, Lean should prove a closed native equality involving `pcWord e`; it should not discard `e` and search the finite carrier for some replacement witness.

The finite-group G2 Bruhat corridor is the model example:

```text
189 explicit witness rows
  -> cell-scoped soundness
  -> quotient-row witnesses
  -> orbit membership
  -> Bruhat covering
  -> quotient injectivity/surjectivity corridor
  -> Fin 189 ≃ CarrierQuotient
  -> quotient cardinality 189
  -> ambient order theorem
```

Each edge remains independently visible and independently auditable.

## Relationship to the Repository's Causal and Categorical Layers

The repository already distinguishes proof-theoretic dependency from physical causality through `InfoGeometry.Causal.ProofDAGRepresentation`. Its relation points from prerequisite to dependent declaration. `InfoGeometry.Canonical.PenrosePosetCategoryFoundation` supplies the corresponding preorder/category, cocone, and colimit interfaces.

These owners provide the structural language for dependency cones and compatible assembly. They do not make every development pipeline literally a spectral sequence or a homotopy theory. Such identifications require explicit bridges and coherence theorems.

The engineering invariant is therefore deliberately narrower and fully operational:

```text
missing dependency
  -> refine dependency graph
  -> prove nearest reachable theorem
  -> kernel-check
  -> connect by explicit transport
  -> iterate
```

## Repository Development Criterion

A proof-oriented change counts as genuine DAG progress only if it does at least one of the following:

1. closes an existing target node;
2. proves a previously missing predecessor node;
3. proves a new transport/coherence edge between existing nodes;
4. imports explicit external witness data and proves native soundness facts about it.

Merely renaming an unresolved theorem as a hypothesis, certificate field, or assumed equivalence is not progress.

## Canonical Form

> **Missing is a frontier, not a blocker. Compute externally when useful, export explicit witnesses, verify locally in Lean, assemble structurally, and keep refining the dependency DAG until the goal is reached.**
