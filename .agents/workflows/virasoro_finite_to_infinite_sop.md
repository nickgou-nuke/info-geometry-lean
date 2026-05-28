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
5. **Algebraic direct limit / colimit**
   - Construct the actual colimit object, e.g. Mathlib `DirectLimit`, with
     explicit transition maps and canonical injections.
   - Prove the directed-system laws and canonical-image compatibility.
   - State closure on canonical images, and expose the universal compatible-cone
     lift when an external target is needed.
   - Do not call this a topological completion.
6. **Genuine analytic/topological completion**
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

The Virasoro pattern is **primarily finite-support algebra**, not a completed
colimit construction:

```text
infinite mode index set
→ finitely supported carrier (`ℤ →₀ 𝕜`, `ι →₀ 𝕜`)
→ basis generators
→ basis-level bracket/product/cocycle formulas
→ bilinear or multilinear extension by basis/Finsupp machinery
→ generator readback theorems
→ central extension, if the cocycle is an ordinary skew Lie cocycle
→ locally finite Sugawara construction, only when sums are genuinely needed
```

Use algebraic `DirectLimit` only when the object is genuinely a tower of finite
stages with bonding maps and identifications. Do not replace the simpler
Virasoro/Finsupp pattern by a staged colimit unless the mathematics calls for a
real transition system.

The shared invariant shape is:

```text
closure = shifted structural term + explicit central/cocycle term
```

Repo-owned superclosure/direct-limit exemplars:

- `lean/InfoGeometry/Algebra/InductiveSuperClosureLemmas.lean` — finite
  single and mixed superclosure induction over typed stages.
- `lean/InfoGeometry/Algebra/InfiniteSuperClosureLemmas.lean` — explicit
  target-image closure via maps `Stage n →+* Limit`.
- `lean/InfoGeometry/Algebra/DirectLimitSuperClosureLemmas.lean` — actual
  Mathlib `DirectLimit`, canonical maps, compatible-cone lift, and closure on
  canonical images.
- `lean/InfoGeometry/Algebra/FinsuppN2ModeInduction.lean` — Finsupp/direct-sum
  object-equality N=2 anticommutator closure.
- `lean/InfoGeometry/Algebra/SupergradedCocycle.lean` — symmetric odd--odd
  super-cocycle separated from ordinary skew Lie central extensions.

## Method hierarchy

Choose the lightest honest mechanism that matches the mathematics:

1. **Finsupp/direct-sum mode algebra** when elements are finite linear
   combinations of infinitely many modes. This is the default Virasoro/Witt/
   Heisenberg pattern.
2. **Supergraded Finsupp mode lane** when the mode algebra is genuinely
   super/odd and the law is a symmetric odd--odd anticommutator. Keep this
   separate from ordinary skew `LieTwoCocycle` central extensions.
3. **Locally finite operator sums** when formulas are genuinely infinite but
   each vector/state sees finitely many nonzero terms. This is the Sugawara
   pattern.
4. **Algebraic DirectLimit** when there are actual finite stages and bonding
   maps whose images must be identified.
5. **Explicit target-image theorem** when finite stages map into an external
   target but no universal colimit is needed.
6. **Analytic/topological completion** only after topology, convergence, and
   continuity are formalized.

Decision table:

| Mathematical situation | Default mechanism | Do not replace with |
| --- | --- | --- |
| Infinite modes, finite linear combinations | `ι →₀ 𝕜` / Finsupp basis API | DirectLimit or completion |
| Ordinary skew Lie anomaly | explicit `LieTwoCocycle` + `CentralExtension` | stored central law field |
| N=2/SUSY odd--odd closure | symmetric supergraded anticommutator/cocycle lane | ordinary skew `LieTwoCocycle` |
| Normal-ordered/Sugawara sum | local truncation + finite support of summand | assumed convergence certificate |
| Genuine staged inclusions/identifications | algebraic `DirectLimit` with `bondMap` | Finsupp if stages really identify |
| External target only | compatible cone / image-local theorem | global target theorem |
| Completion/convergence/spectrum/KMS/Type III | topology + continuity + convergence owner | algebraic Finsupp/DirectLimit alone |

## General transition templates

### Template A: Finsupp/direct-sum mode algebra

Use this when the infinite object is a finite linear combination of modes. This
is the default external-Virasoro method.

```lean
abbrev ModeFamily (ι A : Type*) [Zero A] := ι →₀ A
```

Required proof shape:

1. Define the carrier as a finite-support object, typically `ι →₀ 𝕜` or
   `ι →₀ A`.
2. Define named generators as basis/single elements, e.g. `gen i`.
3. Define bracket/product/cocycle formulas on basis generators.
4. Extend bilinearly/multilinearly using `Basis.constr`, Finsupp extensionality,
   or equivalent finite-support machinery.
5. Prove support control where operations are not already handled by the basis
   API.
6. Prove generator readbacks before arbitrary-element readbacks.
7. State closure as object equality in `ι →₀ A` when feasible.
8. Derive pointwise statements only as corollaries.

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

### Template B: basis + cocycle + ordinary Lie central extension

Use this when closure has an anomaly/central-charge term that is genuinely an
ordinary Lie-bracket central extension and you want the full
external-Virasoro-style construction.

This template applies to Witt/Virasoro/Heisenberg/affine Kac--Moody-style
ordinary Lie brackets. It does **not** by itself formalize an odd--odd
super-anticommutator. For N=2/SUSY odd closure, use Template C for the
anticommutator theorem and optionally use this Template B only for the ordinary
Lie central-extension skeleton/readback layer.

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

### Template C: super/odd anticommutator direct-sum closure

Use this when the finite law is an odd--odd super-anticommutator, e.g.
`{Q,R}=H+Z`, rather than an ordinary Lie bracket.

Required proof shape:

1. Define the finite anticommutator theorem in a ring or associative algebra.
2. Define the infinite carrier as a finitely supported direct sum when possible,
   e.g. `ι →₀ A`.
3. Define the anticommutator mode operation as an actual `Finsupp` object, not
   a wrapper/predicate.
4. Prove support control for the operation, e.g. support contained in
   `Q.support ∪ R.support`.
5. State closure as object equality in the direct-sum carrier:
   `anticommutatorMode Q R = H + Z`.
6. Prove finite iterate transport with `Finsupp.mapRange` or the relevant
   homomorphic transport.
7. Keep any ordinary Lie central-extension analogy in a separate layer; do not
   pretend `LieTwoCocycle.CentralExtension` is the super-anticommutator itself.

This is the correct methodology for the N=2 odd closure files. The ordinary
central-extension pipeline may still be useful as a companion skeleton, but the
SUSY anticommutator theorem lives in the direct-sum anticommutator layer.

Reusable API target for future work:

```text
Mode →₀ 𝕜 or parity-indexed Finsupp carrier
parity : Mode → ZMod 2
modeGen : Mode → carrier
oddOddCocycle : Mode → Mode → 𝕜   -- symmetric on odd/odd inputs
superBilin : carrier → carrier → 𝕜
anticommutatorMode : carrier → carrier → carrier
```

Required readbacks should include generator-level odd--odd closure, symmetry of
the odd--odd cocycle, bilinear extension, and object-equality closure in the
Finsupp carrier. Do not add this API as a proof-payload structure; prove the
laws from the definitions.

### Template D: locally finite operator sums

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

### Template E: finite iterates / inductive systems

Use this when a bonding/symmetry map is iterated finitely.

Required proof shape:

1. Define finite iterate as a homomorphism (`iterateEnd`, composition chain,
   functor iterate, etc.).
2. Prove the local law is preserved by one homomorphism.
3. Apply that theorem to the finite iterate.
4. If mode-indexed, combine with Template A, B, or C as appropriate.

This proves **finite-stage** transport only.  It is not an infinite colimit or
completion theorem unless the colimit/completion is separately constructed.

### Template F: algebraic direct limit / colimit

Use this when the infinite object is a genuine algebraic colimit of finite
stages, not merely an external target image. This is appropriate when later
stages structurally identify/enlarge earlier stages via bonding maps; it is not
the default Virasoro mode-algebra pattern.

Required proof shape:

1. Define all transition maps between finite stages, not only informal arrows.
   For a one-step chain this usually means an iterated map such as:
   `bondMap bond m n h : Stage m →+* Stage n`.
2. Instantiate the directed-system laws (`map_self`, `map_map`) for those
   transition maps.
3. Define the actual colimit object, e.g. Mathlib's algebraic `DirectLimit`.
4. Define explicit canonical maps from each stage, e.g.
   `directLimitOf bond n : Stage n →+* DirectLimit...`.
5. Prove canonical-image compatibility along every transition map and the
   one-step bonding maps.
6. If an external target is used, define a compatible cone and the universal
   lift out of the direct limit, with a readback theorem on canonical images.
7. State closure only for canonical images or elements generated/represented by
   the direct-limit construction. Do not assert arbitrary analytic completion
   or global centrality without separate owner theorems.

Repo-owned examples:

```lean
InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.bondMap
InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitOf
InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimitLift
InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.directLimit_superClosure_all
```

This proves an **algebraic colimit** theorem. It is still not a Banach/Hilbert,
KMS, spectral, Type III, or convergence theorem.

### Template G: genuine analytic limit/completion

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
- finite inductive chain only;
- explicit target-image theorem;
- algebraic `DirectLimit`/colimit;
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

A theorem about `φ^[n]` for every `n : ℕ` is a finite-stage theorem. It is not
an infinite target-image theorem, an algebraic colimit theorem, or an analytic
completion theorem.

Use the following vocabulary precisely:

- **finite-stage theorem**: proves a law for each `n` by induction;
- **target-image theorem**: maps every finite stage into an explicit target
  `L` and proves the law on `ι n (x n)`;
- **algebraic direct-limit theorem**: constructs the Mathlib direct limit,
  canonical maps, and compatible-cone lift;
- **analytic completion theorem**: adds topology/convergence/continuity and
  proves a completed limit law.

Do not describe a finite-stage theorem as a completed infinite limit. Algebraic
DirectLimit work from Template F is a colimit theorem, not an analytic
completion theorem.

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
- Treating `ι →₀ 𝕜`/`Finsupp` as a topological completion, Laurent-series
  space, distribution space, Hilbert completion, or operator closure.
- `centrality_witness`, `closure_law`, `sugawara_certificate`,
  `convergence_guard`, or similar proof-payload fields.
- Theorems that merely re-export a structure field.
- Infinite sums without finite-support/local-truncation proofs.
- Analytic convergence claimed by a datum field.
- A finite theorem renamed as an infinite theorem without an infinite carrier.
- Pointwise-only infinite closure when a direct-sum object equality is feasible.
- Colimit/completion language for finite-iterate theorems.
- Replacing a natural Finsupp mode algebra by a staged DirectLimit without a
  real mathematical transition system.

## Review questions

Ask before accepting a finite-to-infinite theorem:

1. What is the infinite carrier, and why is it the right mechanism rather than
   a simpler `Finsupp` carrier or a stronger colimit/completion claim?
2. Is finite support built into the type (`ι →₀ A`) or proved separately?
3. If direct-sum carrier is used, is closure stated as object equality?
4. Where is the basis/local bracket or anticommutator law proved?
5. Where is the cocycle/central obstruction defined?
6. Is the cocycle support/resonance explicit (`m+n=0`, residue, etc.)?
7. If a sum over modes appears, where is local truncation proved?
8. Is this finite-stage transport, target-image transport, algebraic
   DirectLimit/colimit, or genuine analytic completion?
9. Does the theorem prove closure from definitions, or re-export a stored law?
10. Would UlamAI report placeholders or axioms?
11. Does the heartbeat improve without introducing new proxy fields?

## Output standard

A compliant finite-to-infinite bridge must leave one of these outcomes:

- a kernel-checked theorem built from direct sums, finite support, local
  truncation, explicit cocycles, or proved convergence;
- a data-only structure with no theorem claim;
- or an honest visible `sorry` at the exact missing theorem.
