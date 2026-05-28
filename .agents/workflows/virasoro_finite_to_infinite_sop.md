# SOP: Finite-to-Infinite Algebraic Transition Pattern

## Purpose

Use the external Virasoro library as a worked exemplar for a broader rule:
finite/local algebraic laws may be lifted to infinite-indexed systems only by
building an honest infinite carrier and proving the finiteness, locality, or
convergence obligations required by that carrier.

This SOP applies to any Lean formalization that claims a finite-to-infinite or
local-to-global transition, including:

- Witt/Virasoro/Heisenberg/affine Kac--Moody/Sugawara mode algebras;
- finite N=2 supercharge closure transported to infinite mode families;
- central-charge, cocycle, or anomaly-extension corridors;
- direct sums, inductive systems, locally finite operator sums, and genuine
  topological/analytic completions.

## Core rule

Do **not** encode an infinite-dimensional theorem as a finite theorem plus an
assumed limit, law, certificate, witness, guard, or readback field.

A valid finite-to-infinite theorem must use one of these honest mechanisms:

1. **Algebraic direct sum / finite support**
   - Carrier example: `ι →₀ A` or `ℤ →₀ 𝕜`.
   - Infinite index set is allowed because each element is finitely supported.
   - Closure should preferably be an equality in the direct-sum carrier, not
     only pointwise prose.
2. **Modewise family with proved finite-support preservation**
   - Carrier example: `ι → A` plus a proved finite-support predicate.
   - Use only when a dependent/flexible family is needed; prefer `Finsupp` if
     direct-sum object equality is available.
3. **Locally finite/truncated operator sums**
   - Every vector/state/input sees finitely many nonzero summands.
   - Prove the support of the summand is finite before defining or using the
     sum.
4. **Central extension by explicit cocycle**
   - Define the structural bracket and the cocycle explicitly, then form the
     extension.
   - Central terms are cocycles/central coordinates, not stored theorem fields.
5. **Genuine analytic/topological completion**
   - Only if the topology, Cauchy/convergence notion, continuity, and limiting
     theorem are formalized and proved.
   - Otherwise leave visible debt or keep the file data-only.

If none of these mechanisms is available, the theorem must remain an honest
visible `sorry` or be refactored into definitions/data with no theorem claim.

## Reference exemplar: external Virasoro package

Use these files as the canonical model for the algebraic cases:

- `lean/InfoGeometry/External/Virasoro/WittAlgebra.lean`
- `lean/InfoGeometry/External/Virasoro/VirasoroCocycle.lean`
- `lean/InfoGeometry/External/Virasoro/VirasoroAlgebra.lean`
- `lean/InfoGeometry/External/Virasoro/HeisenbergAlgebra.lean`
- `lean/InfoGeometry/External/Virasoro/AffineKacMoody.lean`
- `lean/InfoGeometry/External/Virasoro/Sugawara.lean`
- `lean/InfoGeometry/External/Virasoro/CentralExtension.lean`
- `lean/InfoGeometry/External/Virasoro/BosonizationConstructiveCurrent.lean`

The Virasoro pattern is:

```text
finite/local generator law
→ infinite index set with finitely supported carrier (`ℤ →₀ 𝕜`)
→ basis-mode bracket/cocycle
→ bilinear extension
→ central extension
→ mode-generator bracket theorem
→ locally finite Sugawara construction, if sums are needed
```

The shared invariant shape is:

```text
closure = shifted structural term + explicit central/cocycle term
```

## General transition templates

### Template A: algebraic direct sum

Use this when the infinite object is a finite linear combination of modes.

```lean
abbrev ModeFamily (ι A : Type*) [Zero A] := ι →₀ A
```

Required proof shape:

1. Define the operation as a `Finsupp` object (`onFinset`, `mapRange`,
   `zipWith`, linear extension, or basis construction).
2. Prove support control.
3. State closure as object equality in `ι →₀ A`.
4. Derive pointwise statements only as corollaries.

Example target style:

```lean
anticommutatorMode Q R = H + Z
```

not merely:

```lean
∀ i, anticommutator (Q i) (R i) = H i + Z i
```

Pointwise theorems are acceptable, but the direct-sum equality is the stronger
Virasoro-style endpoint.

### Template B: basis + cocycle + central extension

Use this when closure has an anomaly/central-charge term and you want the full
external-Virasoro-style construction.

Required proof shape:

1. Define an explicit mode-label type.
2. Define the base algebra as a finitely supported basis carrier, typically
   `AbelianLieAlgebraOn labels 𝕜` or `labels →₀ 𝕜`.
3. Define basis generators (`qgen`, `rgen`, `hgen`, `lgen`, `jgen`, etc.).
4. Define an explicit alternating 2-cocycle on basis labels.
5. Extend the cocycle bilinearly using the basis constructor.
6. Prove skewness/self-zero and the cocycle condition.
7. Form `LieTwoCocycle.CentralExtension`.
8. Lift basis generators into the central extension.
9. Prove generator bracket laws first.
10. Prove arbitrary-element bracket readback from the central-extension
    definition.

Allowed pattern:

```lean
γ basis_m basis_n = if resonance m n then centralValue m n else 0
CentralExtension γ
```

Forbidden pattern:

```lean
central_law : Prop
central_certificate : central_law
```

### Template C: locally finite operator sums

Use this for Sugawara/normal-ordering/Fock-style constructions.

Required proof shape:

1. State local truncation as an input theorem/hypothesis about the operator
   family, not as a proof-carrying structure field.
2. Prove the summand support is finite for each vector/state.
3. Define the finite sum.
4. Prove commutator/closure from the finite-support lemma.

Typical truncation input:

```lean
∀ v, atTop.Eventually (fun l => J l v = 0)
```

Do not replace this with:

```lean
sugawara_converges_certificate : Prop
```

### Template D: finite iterates / inductive systems

Use this when a bonding/symmetry map is iterated finitely.

Required proof shape:

1. Define finite iterate as a homomorphism (`iterateEnd`, composition chain,
   functor iterate, etc.).
2. Prove the local law is preserved by one homomorphism.
3. Apply that theorem to the finite iterate.
4. If mode-indexed, combine with Template A or B.

This proves **finite-stage** transport only.  It is not an infinite colimit or
completion theorem unless the colimit/completion is separately constructed.

### Template E: genuine analytic limit/completion

Use only when the file formalizes the analytic infrastructure.

Required proof shape:

1. Specify topology/uniformity/norm/filter.
2. Define finite approximants.
3. Prove Cauchy or convergence.
4. Prove operations are continuous/closed under the limit.
5. State and prove the limiting closure theorem.

If any step is missing, do not state the infinite analytic theorem as closed.

## Implementation checklist

### 1. Classify the infinite carrier

Before writing Lean code, choose exactly one primary mechanism:

- `Finsupp`/direct sum;
- mode family plus proved support preservation;
- central extension by explicit cocycle;
- locally finite/truncated sum;
- genuine topological completion.

Record the choice in the module docstring.

### 2. Prove generator/local laws first

For mode algebras, prove basis-mode laws before arbitrary-element laws:

```lean
[J m, J n] = structuralTerm (m+n) + centralTerm m n
```

Then extend by linearity, `Finsupp` extensionality, basis construction, or the
central-extension readback theorem.

### 3. Prefer object equality over pointwise-only closure

For a direct-sum carrier, the best theorem is equality inside the carrier:

```lean
operationMode X Y = structuralMode + centralMode
```

Use pointwise statements to prove this via extensionality, not as the final
claim when object equality is feasible.

### 4. Make central/obstruction terms explicit

Central charges, anomalies, and defects must appear as:

- cocycles;
- central-extension coordinates;
- explicit mode families;
- proved structural terms.

They must not appear as opaque proof payload fields.

### 5. For sums, prove local finiteness before summing

Any expression over infinitely many modes must be justified by a finite-support
or local-truncation theorem before it is used in a proof.

### 6. Separate finite-stage from infinite-limit claims

A theorem about `φ^[n]` for every `n : ℕ` is a finite-stage theorem.  It is not
an infinite limit theorem.  Do not describe it as a completed infinite limit
unless Template E is also implemented.

### 7. Validation gates

For each touched file run:

```bash
lake env lean <file>
ulam checkpoint <file> --lean-project . --strict --no-allow-axioms
python3 tools/lean4-skills/sorry_analyzer.py lean --format=summary
```

For canonical/vacuity cleanup also run:

```bash
python3 tools/quality/proof_heartbeat.py lean/InfoGeometry/Canonical --top 30
```

Do not stage generated UlamAI JSON unless explicitly requested.

## Anti-patterns

Reject these patterns during review:

- `finite_to_infinite_limit_law : Prop` plus certificate field.
- `centrality_witness`, `closure_law`, `sugawara_certificate`,
  `convergence_guard`, or similar proof-payload fields.
- Theorems that merely re-export a structure field.
- Infinite sums without finite-support/local-truncation proofs.
- Analytic convergence claimed by a datum field.
- A finite theorem renamed as an infinite theorem without an infinite carrier.
- Pointwise-only infinite closure when a direct-sum object equality is feasible.
- Colimit/completion language for finite-iterate theorems.

## Review questions

Ask before accepting a finite-to-infinite theorem:

1. What is the infinite carrier?
2. Is finite support built into the type (`ι →₀ A`) or proved separately?
3. If direct-sum carrier is used, is closure stated as object equality?
4. Where is the basis/local bracket or anticommutator law proved?
5. Where is the cocycle/central obstruction defined?
6. Is the cocycle support/resonance explicit (`m+n=0`, residue, etc.)?
7. If a sum over modes appears, where is local truncation proved?
8. Is this only finite-stage transport, or is a real colimit/completion built?
9. Does the theorem prove closure from definitions, or re-export a stored law?
10. Would UlamAI report placeholders or axioms?
11. Does the heartbeat improve without introducing new proxy fields?

## Output standard

A compliant finite-to-infinite bridge must leave one of these outcomes:

- a kernel-checked theorem built from direct sums, finite support, local
  truncation, explicit cocycles, or proved convergence;
- a data-only structure with no theorem claim;
- or an honest visible `sorry` at the exact missing theorem.
