# The Topological Progress Principle for Formal Development

> Status: normative development doctrine
> Scope: Lean 4 theorem proving, autonomous proof agents, external-CAS certificate pipelines, and repository closure work

## Prime Directive

> **A missing proof or dependency is not a blocker; it is a topological void defining the next development frontier. Do not bridge the void by claiming the impossible or inserting assumptions. Instead, continuously expand the verifiable boundary by proving the exact nearest theorem that locally advances the causal corridor toward the goal.**

**Refine missing edges; prove the nearest reachable node; iterate to the goal.**

This doctrine is about proof-theoretic development. It does not identify repository dependency causality with physical spacetime causality, and it does not promote categorical or homotopical analogies beyond the formal statements actually proved in Lean.

## Verified Computational Pipeline

External computational power is an untrusted discovery engine. The trust boundary is crossed only by explicit data, never by a declaration that a theorem is true.

```text
External Computation
    -> Explicit Witness Data
    -> Small Native Lean Propositions
    -> Distributed Kernel Proofs
    -> Structural Assembly
```

### Discovery layer — untrusted

GAP, SageMath, Singular, Python, SAT/SMT tools, or custom exporters may discover words, matrices, coefficients, finite enumerations, factorizations, or candidate certificates. Their output is not proof authority.

### Certificate layer — data only

External output is imported as explicit native Lean data. Data owners must not contain hidden correctness fields, proof-carrying assumptions, or proposition-valued wrappers that simply restate the desired theorem.

### Verification layer — kernel authority

Lean checks small, explicit propositions against the imported data. For large finite certificates, prefer distributed pointwise theorems whose propositions are themselves the intended native mathematical facts.

### Assembly layer — structural proof

Verified leaves are assembled using reusable theorems: finite partitions, injectivity, quotient transport, subgroup membership, cocones, colimits, orbit-stabilizer, or other genuinely proved structure. Assembly may not smuggle in the global target as an assumption.

## Nearest-Provable-Theorem Rule

When a requested theorem `T` cannot be proved from the current verified state:

1. **Identify** the exact missing premise or construction.
2. **Decompose** the missing edge into the smallest natural intermediate dependency DAG.
3. **Select** a nearest node `Q` whose prerequisites are already available.
4. **Prove** `Q` in the Lean kernel with no new unproved assumptions.
5. **Reconnect** `Q` to the original corridor through an explicit bridge or transport theorem.
6. **Iterate** in topological order until `T` is closed or genuinely external data is required.

A structure field containing exactly the theorem currently needed does not count as progress. Renaming a missing edge as an assumption leaves the mathematical frontier unchanged.

## Two Distinct Development Models

The repository already has a proof-dependency DAG interpretation in which

```text
a <= b
```

means that `a` is a prerequisite of `b`. In that theorem-node order, moving from `a` toward a later node `b` generally **shrinks** the remaining forward dependency corridor.

A growing verified theory state is a different object: it is a set of proved declarations closed under prerequisites. If `S <= S'` means that `S'` contains all verified content of `S`, then verified knowledge grows monotonically.

These two models must not be conflated:

```text
D_proof : theorem/declaration dependency order
D_state : monotone inclusion order of verified theory states
```

For a target `T`, write `R_T(S)` for the target-relevant verified region of a verified state `S`. The exact Lean representation may evolve, but `R_T(S)` must denote proved/available target-relevant content, not merely graph-theoretic reachability from one prerequisite node.

## Topological Closure Invariant

Every development iteration must end in exactly one of three valid states.

### CLOSED

The requested target theorem is kernel-checked in the intended native carrier.

### ADVANCED

A new nearest predecessor theorem is kernel-checked and strictly expands the target-relevant verified region:

```text
R_T(S) proper_subset R_T(S')
```

This is successful repository development even when `T` is not yet closed.

### EXTERNALLY DATA-LIMITED

The next proof obligation requires genuinely unavailable external mathematical data, such as an ungenerated finite CAS certificate. The process may pause for data generation, but the missing theorem must not be replaced by an assumption.

"Cannot be proven right now" is not a terminal engineering state unless the next admissible edge is genuinely external-data-limited.

## Prohibited Anti-Patterns

### Proxy-debt

Do not introduce a structure, class, witness packet, or opaque field whose sole purpose is to assume the missing theorem.

### Teleportation

Do not cross a missing edge with `sorry`, `admit`, a new unsupported `axiom`, or an equivalent disguised assumption when the edge can be refined into smaller proof obligations.

### Mislabeled arithmetic

An arithmetic identity such as

```text
64 * 189 = 12096
```

remains arithmetic until connected to the native mathematical carrier through kernel-checked equivalences, cardinality theorems, or bijections.

### Surrogate promotion

Do not present any of the following as stronger facts without an explicit bridge:

```text
A <= B                         as A = B
Nat.card A = Nat.card B        as A ≃ B
Nonempty (A ≃ B)              as a canonical equivalence
quotient equality              as group equality
matrix equality                as group equality without proved faithfulness
conditional theorem `_of_X`    as proof of X
proxy carrier                  as native carrier
finite carrier                 as real/Lie carrier
```

### Vacuous propositions

The proposition checked by `decide`/`native_decide` must itself be the intended mathematical claim. Avoid implication-shaped row certificates or existential wrappers that can become true for irrelevant reasons.

## Distributed Finite Certificate Pattern

For large finite algebraic certificates, the preferred architecture is:

```text
CAS / GAP
  -> raw witness tables
  -> exact native row predicate
  -> independent pointwise Lean theorems
  -> cell-scoped or partition-scoped assembly
  -> faithful carrier readback
  -> global theorem
```

The definition of the row predicate is the critical trust boundary. Distributing a surrogate proposition into hundreds of kernel-valid rows merely distributes semantic debt.

## Semantic Strength Discipline

Every owner must distinguish:

1. **Literal implementation** — the claimed mathematical structure is actually present in Lean.
2. **Structural reuse** — an implemented abstraction is legitimately reused in a new setting.
3. **Meta-level analogy** — a useful conceptual interpretation that is not itself a theorem of the repository.

Names, docstrings, commit messages, and reports must not silently promote category 2 or 3 into category 1.

## Operational Rule for Autonomous Agents

An autonomous theorem-proving agent should optimize for **frontier movement**, not line count, theorem count, or superficial proximity to the requested name.

A useful small theorem that unlocks multiple admissible downstream morphisms is greater progress than a large proxy API that leaves the reachable mathematical region unchanged.

The standing rule is therefore:

> **Never assume across a missing edge. Refine it until a provable edge is exposed.**

## Relation to Existing Repository Foundations

The repository already contains literal foundations for parts of this doctrine:

- `InfoGeometry.Causal.ProofDAGRepresentation`: proof-theoretic dependency order and forward/backward cones;
- `InfoGeometry.Canonical.PenrosePosetCategoryFoundation`: preorder/category transport, upper-bound cocones, and LUB colimit cocones;
- the spectral subsystem: genuine spectral and stabilization mathematics in its own algebraic domain.

The interpretation of repository development itself as a directed filtered homotopy theory remains a meta-level program unless and until explicit development-state and higher-path structures are formalized. The doctrine must preserve that boundary.
