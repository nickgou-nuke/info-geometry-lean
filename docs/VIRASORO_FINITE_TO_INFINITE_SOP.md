# SOP: Virasoro Finite-To-Infinite Formalization

## Purpose

Use this procedure when connecting finite algebraic closure theorems in
`info-geometry-lean` to the external Virasoro, Heisenberg, Kac-Moody, or
Sugawara libraries.

The rule is: do not infer an infinite-dimensional current theorem from analogy.
Choose the correct algebraic finite-to-infinite template and prove the required
finite-support, direct-limit, or truncation facts explicitly.

## Three Templates

### A. Finsupp Mode Algebra

Use when the infinite object is an algebraic mode space: infinitely many
possible modes, but each element is a finite linear combination.

External examples:

- `WittAlgebra 𝕜 := ℤ →₀ 𝕜`;
- `AbelianLieAlgebraOn ℤ 𝕜 := ℤ →₀ 𝕜`;
- generators from `Finsupp.basisFun`;
- brackets/cocycles defined on basis generators and extended bilinearly.

Implementation pattern:

```text
ModeIndex →₀ 𝕜
→ basis generators
→ basis bracket/product/cocycle formula
→ bilinear extension
→ generator readback theorem
```

Use this before introducing topology or completion.

### B. Locally Finite Operator Sums

Use when the expression is an operator sum over infinitely many modes, but each
vector sees only finitely many nonzero summands.

External example: Sugawara.

Required shape:

```text
operator family A : ℤ → End V
truncation hypothesis heiTrunc
finite support theorem for v
∑ᶠ definition
commutator/readback theorem
```

Do not define a Sugawara-style infinite sum until the local finite-support
lemma is available.

### C. Algebraic Direct Limit

Use when the object is genuinely staged and later stages identify or enlarge
earlier stages through bonding maps.

Repo example:

- `InfoGeometry.Algebra.DirectLimitSuperClosureLemmas`

Implementation pattern:

```text
Stage : Nat → Type
bond n : Stage n →+* Stage (n+1)
bondMap bond m n h
DirectedSystem
DirectLimit Stage bondMap
directLimitOf bond n
directLimitLift bond toLimit hcone
closure/readback on canonical images
```

This is the right tool for finite inductive systems. It is still algebraic; it
does not imply analytic completion or convergence.

## Core Invariant

The invariant form is:

```text
bracket/current closure = shifted structural mode + central cocycle
```

This is the infinite-mode analogue of finite N=2 closure:

```text
{Q, R} = H + Z
```

where `H` is the noncentral structural term and `Z` is the central/cocycle term.

For N=2 or supergraded odd-odd closure, keep the parity correction explicit:
ordinary Virasoro/Heisenberg/Kac-Moody central extensions use skew
`LieTwoCocycle`; odd-odd superclosure uses a symmetric anticommutator lane
unless a true Lie-superalgebra cocycle API is installed.

## Source Modules

Use these primary sources before writing downstream bridge code:

- `lean/InfoGeometry/External/Virasoro/WittAlgebra.lean`
- `lean/InfoGeometry/External/Virasoro/VirasoroCocycle.lean`
- `lean/InfoGeometry/External/Virasoro/VirasoroAlgebra.lean`
- `lean/InfoGeometry/External/Virasoro/HeisenbergAlgebra.lean`
- `lean/InfoGeometry/External/Virasoro/AffineKacMoody.lean`
- `lean/InfoGeometry/External/Virasoro/Sugawara.lean`
- `lean/InfoGeometry/Canonical/BosonizationConstructiveCurrent.lean`
- `lean/InfoGeometry/Canonical/CurrentSugawaraBridge.lean`
- `lean/InfoGeometry/Algebra/FinsuppN2ModeInduction.lean`
- `lean/InfoGeometry/Algebra/SupergradedCocycle.lean`
- `lean/InfoGeometry/Algebra/InductiveSuperClosureLemmas.lean`
- `lean/InfoGeometry/Algebra/InfiniteSuperClosureLemmas.lean`
- `lean/InfoGeometry/Algebra/DirectLimitSuperClosureLemmas.lean`

## Implementation Discipline

Do:

- use direct `def`s and theorems for finite closure patterns;
- prefer `Finsupp`/direct-sum carriers for algebraic infinite mode spaces;
- instantiate finite closure into mode-indexed laws only through proved generator brackets;
- use central-extension theorems for centrality and cocycle readback;
- require explicit `heiTrunc` or finite-support hypotheses before using Sugawara sums;
- use `DirectLimit` only after constructing the transition maps and `DirectedSystem`;
- distinguish image-local target theorems from direct-limit universal properties;
- prove bridge lemmas by calling external theorems such as:
  - `VirasoroProject.VirasoroAlgebra.lgen_bracket`;
  - `VirasoroProject.HeisenbergAlgebra.lie_jgen`;
  - `VirasoroProject.affineCurrentGen_bracket`;
  - `VirasoroProject.commutator_sugawaraGen`;
  - `VirasoroProject.sugawaraRepresentation_cgen`.

Do not:

- assert “finite implies infinite” without a finitely-supported algebra or local truncation;
- store closure claims in witness fields or certificate packets when a direct theorem can state them;
- introduce new ontology for central charge, current, or Hodge decomposition;
- replace missing infinite-dimensional analysis with `Prop` fields;
- use ordinary skew `LieTwoCocycle` for symmetric odd-odd super-anticommutator data;
- claim Sugawara/Virasoro closure unless the Heisenberg commutator and truncation hypotheses are present.
- treat `ι →₀ 𝕜` or algebraic `DirectLimit` as a Banach/Hilbert/topological completion.

## Finite-to-Infinite Checklist

Before adding a theorem, answer these in Lean terms:

1. What are the generators?
   - finite: `Q R H Z`;
   - Heisenberg: `jgen k`, `kgen`;
   - Virasoro: `lgen n`, `cgen`;
   - Kac-Moody: `affineCurrentGen n x`, `affineCentralGen`.

2. What is the closure law?
   - finite: `anticommutator Q R = H + Z`;
   - Heisenberg: `[J_k,J_l] = k δ[k+l=0] K`;
   - Virasoro: `[L_m,L_n] = (m-n)L_{m+n} + cocycle C`;
   - Kac-Moody: `[J_m^x,J_n^y] = J_{m+n}^{[x,y]} + cocycle K`.

3. Where does finiteness enter?
   - `Finsupp` basis construction for Witt/Heisenberg;
   - loop monomials for affine Kac-Moody;
   - `heiTrunc`/finite support for Sugawara sums;
   - `bondMap`/`DirectedSystem` for staged direct limits.

4. What is preserved by the flow?
   - relation preservation, not pointwise equality of generators;
   - central line/central generator where the source theorem proves it;
   - exact/coexact/harmonic predicates only under explicit preservation hypotheses.

5. Which template is being used?
   - Finsupp mode algebra;
   - locally finite operator sum;
   - algebraic direct limit;
   - image-local external cone.

6. What is not being claimed?
   - no analytic completion without topology and continuous operations;
   - no global centrality without a generated-by-image or centrality theorem;
   - no arbitrary infinite sums without local finite support;
   - no super Lie cocycle unless the parity-specific API exists.

## Validation

For a new bridge module, run the narrowest relevant target first:

```bash
lake env lean lean/InfoGeometry/<path>/<File>.lean
```

If it is imported by an umbrella module, also run:

```bash
lake env lean lean/InfoGeometry/All.lean
```

For protected or expensive targets, prefer:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock <Lake.Target.Name>
```

Scan for hidden placeholders:

```bash
rg -n "^[[:space:]]*(sorry|admit)\b|axiom\b|Prop := True|: True|Nonempty|certificate|socket|wrapper|field" lean/InfoGeometry/<path>/<File>.lean
```

## Decision Rule

Use this order:

1. If the infinite object is finite linear combinations of modes, use
   `Finsupp`.
2. If the expression is an operator sum, prove local finite support first.
3. If the object is built from finite stages, use algebraic `DirectLimit`.
4. If the target is external, state an image-local theorem or a compatible-cone
   lift.
5. Add topology/completion only in an owner module with topology, continuous
   operations, dense image or completion maps, and convergence proofs.
