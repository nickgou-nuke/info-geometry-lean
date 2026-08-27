# Distributed Certificate Closure for Finite G₂ Constructions

## Purpose

Large finite algebraic gaps should be decomposed into small, independently
checkable certificates. The decomposition is an implementation strategy, not
an additional axiom: every leaf is a proposition proved by Lean's kernel.

## Method

```text
native data → certificate rows → kernel readback → cell assembly
             → structural transport → global theorem
```

CAS, GAP, or a generator supplies finite data only. It does not supply an
equality proof, soundness proposition, surjectivity witness, or classification
theorem. Lean evaluates each witness on the native carrier and proves the
resulting proposition.

## Distributed divide and conquer

For a finite index space, split by the mathematical partition already owned by
the development. For the G₂ flag problem:

```text
Fin 12 cells
  → certified orbitCells membership
  → 189 closed row theorems, one for each valid pair
  → cell-scoped assembly
  → quotient-row witness
  → Bruhat covering
```

This is not the rejected global tactic `revert k i hi; decide`. The finite
computation is distributed into explicit row owners, each with a fixed witness
and a fixed native matrix equality. The assembly eliminates only the already
proved cell-membership proposition; invalid pairs are discharged by proving
that their membership premise is impossible. It is a selector over closed row
theorems, not another evaluator.

## Trust boundary

```text
GAP words
  ↓ data only
gapLeftWitness / gapRightWitness
  ↓ native evaluation
gapWitnessMatrixSound
  ↓ 189 closed row proofs
cell-scoped assembly
  ↓ autMatrix_injective
gapWitness_group_factorization
  ↓ quotient transport
QuotientRowWitness
```

The matrix representation is used only through its proved faithfulness,
`autMatrix_injective`. Orientation is fixed in the imported carrier-aligned
data; it is never inferred by a heuristic or hidden in a Boolean validity
flag. A CAS assertion is not imported as a Lean proof.

## Current G₂ owners

The following names describe the local/staged implementation currently being
developed. They are not remote-certified owner names until the corresponding
commits are published and independently audited.

* `G2GAPFlagWitnessData.lean`: exported witness payload.
* `G2GAPFlagWitnessRows.lean`: 189 closed pointwise matrix proofs.
* `G2GAPFlagWitnessAssembly.lean`: cell-scoped selector and quotient assembly.
* `G2GAPFlagWitnessReadback.lean`: matrix-to-group and quotient transport.
* `G2ConcreteBruhatOrbitCertificate.lean`: conditional covering interface.

The resulting theorem is conditional exactly where the mathematics is
conditional:

```lean
∀ k i, i ∈ orbitCells k → QuotientRowWitness k i
```

An enumeration equivalence of the quotient is a separate obligation and must
not be smuggled into certificate assembly.

The lower bridge remains explicit:

```text
all_gapWitnessMatrixSound
  → all_gapWitnessFactorization
  → fin189_orbit_membership
  → covering_eq_univ enum orbitWeyl orbitCells
```

The final covering theorem still requires
`enum : Fin 189 ≃ CarrierQuotient` together with the explicit alignment

```lean
henum : ∀ i : Fin 189, enum i = orbitEnum i
```

or an equivalence whose `toFun` is definitionally `orbitEnum`. A cardinality
equivalence unrelated to the verified representatives is not sufficient.
Coverage does not prove quotient bijectivity.

## Prohibited shortcuts

Certificate closure must not be replaced by:

* `sorry`, `admit`, axioms, or opaque soundness fields;
* a global `decide` over a large dependent proposition;
* a guessed orientation normalizer;
* existential witness search inside a row proof;
* presenting a quotient witness as exact group factorization;
* presenting cardinality equality as a canonical equivalence;
* promoting a table's default branch to a universal theorem;
* treating CAS output as proof authority.

For every valid row, the exporter supplies the exact PC witness and Lean
checks that witness on the native matrix carrier. A row proof should have the
form

```lean
autMatrix (flagRepresentative i) =
  autMatrix (pcWord (gapLeftWitness k i) *
    weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
    pcWord (gapRightWitness k i))
```

or the equivalent residual/readback equality. The row does not assert that a
flag representative is itself a PC word. It verifies the exact exported left
and right witnesses, not an existential proposition followed by a finite
search for a replacement witness.

## Why the method closes old gaps

Each valid row either compiles or exposes a concrete carrier-level
counterexample. There are 189 valid cell/index pairs, not 2268 arbitrary
`Fin 12 × Fin 189` pairs. Once all rows pass, assembly is a short structural
selector; quotient, covering, cardinality, and order owners consume it without
repeating the computation.
The expensive finite verification is therefore distributed and auditable,
while the mathematical interfaces remain small, native, and reusable.

## Development invariant: missing edges are opportunities

A missing edge in the dependency DAG is not a reason to promote an assumption
or stop the development. It identifies the next theorem to formalize:

```text
fixed goal
  → inspect immediate predecessors
  → select the nearest node whose prerequisites are closed
  → prove that node natively
  → add its consumer bridge
  → repeat
```

For the current finite Bruhat corridor:

```text
row certificates
  → quotient row membership
  → concreteBruhatCovering = Set.univ
  → quotient injectivity / surjectivity
  → Fin 189 ≃ CarrierQuotient
```

The covering edge may require an explicit enumeration alignment, while the
quotient-equivalence branch may require native PC-coordinate readback. These
are separate next nodes, not reasons to weaken either theorem.

## Topological Closure Invariant

For a target theorem `T`, a missing immediate dependency edge is not a
blocker. Refine that edge into its natural mathematical sub-DAG until the
nearest node `Q` is reached whose immediate prerequisites are already proved.
Prove `Q` in Lean, connect it explicitly to the existing owner graph, and
repeat until `T` is closed.

```text
missing edge ≠ blocker
missing edge = next theorem frontier
```

Never assume across a missing edge. A structure field containing the desired
conclusion is not progress: it merely renames the unresolved edge as an
assumption. Every development commit must therefore either close its stated
target node or add a kernel-checked theorem edge that strictly reduces the
remaining dependency distance to that target.

The rule is operational:

```text
target T
  → expose unresolved prerequisites
  → choose nearest reachable node Q
  → prove Q natively
  → wire Q to its consumer
  → repeat
```

For the Fin-189 corridor, row readback and quotient-row assembly are already
closed edges. Quotient enumeration, residual alignment, and representative
injectivity remain separate theorem frontiers; none may be silently promoted
from conditional interfaces to unconditional classification.

### Topological closure rule

For a target theorem `T`, refine a missing dependency edge into its natural
mathematical sub-DAG until the nearest node `Q` whose immediate predecessors
are already proved is exposed. Prove `Q`, add the checked edge, and repeat:

```text
missing edge ≠ blocker
missing edge = next theorem frontier
```

The nearest-reachable-theorem rule is:

> Never assume across a missing edge. Refine it until a provable edge is
> exposed, prove that edge in Lean, and continue toward the target.

Every commit must either close the current target or strictly reduce the
remaining dependency distance:

```text
d(Q, T) < d(P, T)
```

An assumption-bearing structure whose field is the theorem being requested is
not progress; it only renames the missing edge. In particular,
`pure_proof_carrier` wrappers and opaque soundness fields are not certificate
verification.

```text
Every commit must close a target node or add a proved edge nearer to it.

## Verified computational mathematics pipeline

External systems are discovery and witness-generation engines, not proof
authorities. GAP, Sage, Singular, Macaulay2, SymPy, and specialised
representation or D-module software may discover finite words, matrices,
coefficients, reductions, syzygies, normal forms, or annihilating operators.
Only the resulting explicit data crosses the trust boundary:

```text
external computation
  → explicit native witness data
  → small Lean propositions
  → kernel-checked leaves
  → structural assembly
```

The Lean owner must check the supplied witness itself. It must not import a
CAS assertion, search for a replacement existential witness, or infer a
theorem from a cardinality report. For example, a finite-group export supplies
`b₁`, `w`, and `b₂`; Lean proves the corresponding native matrix equality and
then applies the existing faithful readback. A polynomial export supplies
reduction coefficients; Lean checks the displayed ideal combination. The same
rule applies to syzygies, elimination certificates, resolutions, and
annihilating operators.

Large computations are divided by their mathematical structure:

```text
finite group:
  closed row witnesses → cell assembly → quotient/covering theorem

commutative algebra:
  reduction certificates → ideal or Gröbner theorem → elimination consequence

complexes:
  differential identities → exactness lemmas → homological consequence

representations:
  generator readbacks → relations → homomorphism/faithfulness theorem
```

This is certificate checking, not brute-force theorem discovery. A pointwise
`decide` is acceptable only for a closed, explicitly supplied proposition; a
global finite evaluator is not a substitute for the row certificates. Each
failure must identify the exact witness and native carrier where the proposed
edge fails, so the dependency edge can be refined into the nearest reachable
theorem.

The project-level law is therefore:

```text
compute externally, export witnesses, verify locally, assemble structurally
```

No claim is promoted beyond the strongest theorem actually checked by Lean.
Quotient statements remain quotient statements, inclusions remain inclusions,
conditional interfaces remain conditional, and external provenance remains
evidence rather than authority.
```
