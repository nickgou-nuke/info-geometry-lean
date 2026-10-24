# Super-Grassmannian graph-chart milestone

## Ground-truth theorem contract

Work in the existing arbitrary-ring module category. For modules `U`, `W` over
an associative ring `A`, and native direct-sum gradings by submodules over a
commutative base ring `k`, construct an equivalence between degree-preserving
`A`-linear maps `U → W` and homogeneous submodules of `U × W` whose first
projection is bijective. Homogeneity means closure under the componentwise
native `DirectSum.decompose` projections. No finite dimension, characteristic,
or commutativity assumption on `A` is needed for this equivalence.

Native owners:
- `Mathlib.LinearAlgebra.Prod`: `LinearMap.graph`, with membership
  `z.2 = f z.1`; `Submodule.exists_eq_graph` from bijectivity of the first
  projection.
- `Mathlib.Algebra.DirectSum.Decomposition`: `DirectSum.Decomposition`,
  `decompose_of_mem_same`, `decompose_of_mem_ne`, and decomposition induction.
- `InfoGeometry.SuperGrassmannian.ProjectorGraphChart`: existing graph
  projector, its range equal to `f.graph`, its kernel equal to `ker fst`, and
  idempotence. This shared-tree owner is reused, not rewritten.
- Native exterior algebra is `CliffordAlgebra 0`. Its native `evenOdd` grading,
  injective generating map, and `algebraMapInv` augmentation support a genuine
  odd-coordinate regression.

For finite free left modules, coefficients act on the right:
`F(T)(x)(j) = ∑ i, x(i) * T(i,j)`. Prove that extension of a graph along any
ring homomorphism, defined as the target-module span of its coefficientwise
image, equals the graph of the mapped coefficients. Prove identity/composition
laws without assuming the homomorphism is surjective. This is explicit finite
free graph base change, not a claimed general balanced-tensor-product API.

Regression target: in the actual exterior algebra on one generator, graphs
of right multiplication by `θ` and by zero are distinct complemented graded
submodules of `A ⊕ ΠA`, but both reduce under the augmentation to the zero
coordinate graph. Prove the parity shift rather than merely label it.

Excluded: a global moduli functor, chart cover/transitions, structure-sheaf
gluing, representability, global splitting, tangent superbundle, Berezinian,
and continuum passage. These remain subsequent milestones.

## Implemented owners

All paths below are under `lean/InfoGeometry/SuperGrassmannian/`.

- `GradedGraphChart.lean`: `graphChartEquiv` classifies all transverse homogeneous
  submodules by degree-preserving maps. `graphSourceEquiv`, `graphQuotientEquiv`,
  and `chart_isCompl` prove the source/quotient identifications and complement.
- `GraphChartBaseChange.lean`: `extend_id`, `extend_comp`, `graph_eq_span`, and
  `extend_graph` prove functorial coefficient extension and its graph formula.
- `FreeSupermoduleChart.lean`: constructs `freeDecomposition` and native
  `SetLike.GradedSMul` for free supermodules; proves coefficient parity is
  necessary and sufficient. `coefficientChartEquiv` restricts Mathlib's native
  `LinearEquiv.piRing` and composes it with the graph equivalence.
  `coefficientChartEquiv_natural` proves the resulting chart commutes with every
  degree-preserving algebra map. The coefficient algebra need only be graded
  associative; supercommutative algebras are included without replacing their
  multiplication by ordinary commutative multiplication.
- `GraphChartOddRegression.lean`: uses native `ExteriorAlgebra k k` and its
  `CliffordAlgebra.evenOdd 0` grading. `oddPoint_ne_zeroPoint`, `same_reduction`,
  and `reduction_not_injective` hold over every nontrivial commutative base ring,
  including characteristic two. The first basis vector has parity zero and the
  second has parity one; this shift is used by the constructed decomposition.
- Existing `ProjectorGraphChart.lean` is reused. The only task edit to this
  shared-tree owner qualifies `LinearMap.IsIdempotentElem.ker_eq_range_one_sub`
  to fix name resolution; all other pre-existing additions were preserved.

`InfoGeometry.All` imports `GraphChartOddRegression`, reaching the complete
owner chain. The existing complex `SupergradedAlgebra` interface can supply
`GradedAlgebra` through its `graded` field; no duplicate supercommutative-algebra
carrier was introduced.

The native gradings on `U` and `W` determine product homogeneity in `IsGraded`
by componentwise decomposition. This is a local transverse chart, not a global
moduli functor or a sheaf. For finite free graphs, extension is characterized
explicitly by the mapped graph coefficients; no general noncommutative
balanced-tensor-product universal property is claimed.

## Verification (2026-10-24)

- Locked narrow build `InfoGeometry.SuperGrassmannian.GraphChartOddRegression`:
  **1,851 jobs**, exit 0; `/tmp/super-odd-chart2.log`.
- Locked umbrella build `InfoGeometry.All`: **26,985 jobs**, exit 0;
  `/tmp/super-graph-all.log`. This is the named umbrella, not every Lake target
  or every source file in the repository.
- Kernel replay and transitive all-declaration audit using
  `tools/infra/axiom_check.lean`, under the shared build lock:

  | Module | Declarations | Result |
  |---|---:|---|
  | `ProjectorGraphChart` | 14 | PASS |
  | `GradedGraphChart` | 26 | PASS |
  | `GraphChartBaseChange` | 15 | PASS |
  | `FreeSupermoduleChart` | 26 | PASS |
  | `GraphChartOddRegression` | 17 | PASS |
  | **Total** | **98** | **PASS** |

  Log: `/tmp/super-graph-axioms.log`. Only `propext`, `Classical.choice`, and
  `Quot.sound` are permitted. No unsafe/partial declarations were accepted.
- Source-aware admission/unsafe scan of all five owners: PASS.
- Staged whitespace check for task files and root import: PASS.
- The five owners are warning-free in their successful checks. Existing
  dependency/package warnings remain in the umbrella build; no globally
  warning-free baseline or repository-wide axiom audit is asserted.

### Verified source SHA-256

```text
2b1c3ef795385aea60509c7100c56e850ebec0bd4da9f5a99e5d76fb3ce73813  ProjectorGraphChart.lean
599e64d5819258480a95fa36300aea186503fe89e9de1759501aea9aebe63e8c  GradedGraphChart.lean
772745814ca63a2fbe2fad054c09b9b738c8adbece8ef7307af66287a85926d5  GraphChartBaseChange.lean
812a995df9af8ce74568d1634c62c896228da5bba43609bc8a8f9e3d8a614068  FreeSupermoduleChart.lean
4d1ecd8f539e75447410fe51a5d8b599407fa4d66ad262a17e839b5a2578d974  GraphChartOddRegression.lean
```

Follow-up completed: graph-chart overlaps, inverse and cocycle laws, graded
overlap equivalences, and coefficient-change compatibility are checked in
`docs/SUPER_GRASSMANNIAN_TRANSITION_VERIFICATION.md`. Its 184-declaration audit
includes and supersedes this 98-declaration scope. `InfoGeometry.All` now reaches
this chain through `GraphOverlapRegression`.

Remaining: the global locally free graded moduli functor, local supercoordinate
representability, chart coverage and gluing. Do not promote the local chart and
transition theorems to a global superscheme theorem.
