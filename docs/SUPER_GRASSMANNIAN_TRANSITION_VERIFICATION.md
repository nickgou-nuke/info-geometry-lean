# Super-Grassmannian graph transition milestone

## Ground-truth theorem contract

For arbitrary modules `U`, `W` over an associative ring `A`, let
`G : (U × W) ≃ₗ[A] (U × W)` and `f : U →ₗ[A] W`. Define
`D_G(f)(x) = (G(x,f(x))).1` and `N_G(f)(x) = (G(x,f(x))).2`.
The overlap condition is bijectivity of `D_G(f)`, and the transition is
`N_G(f) ∘ D_G(f)⁻¹`. This retains noncommutative composition order.

Reuse the existing `GraphChartTransition.lean` owner, in particular
`map_graph_eq_iff`, `block_map_graph` and `exists_map_graph_iff`; do not replace
its exact injective-image criterion with an assumed inverse. Reuse
`GradedGraphChart.graph_injective`, its native decomposition-based grading,
and `GraphChartBaseChange.extend`.

Targets: graph-image equality, identity and inverse transitions, exact
composable overlap domain, cocycle equality, and equivalence of overlap
subtypes. For genuine native gradings, prove evenness of transitions from
evenness of the coordinate change. Establish coefficient-change compatibility
on finite free modules without assuming surjectivity of the coefficient map.
Include inhabited regression examples and a genuine failure of overlap.

No global chart cover, localization, structure sheaf, local representability,
superscheme, Berezinian, or continuum theorem is asserted by this milestone.

## Implemented owners

Paths are under `lean/InfoGeometry/SuperGrassmannian/`.

- `GraphChartCocycle.lean`: `transition_graph`, `overlap_comp_iff`,
  `transition_cocycle`, `overlap_inverse`, `transition_inverse`, and
  `overlapEquiv`. The transition is defined on its genuine bijective-denominator
  domain, with an equivalence of overlap subtypes rather than an unrestricted
  total fractional transformation.
- `GradedGraphCocycle.lean`: product-component naturality, derived inverse
  degree preservation, even transitions, and `gradedOverlapEquiv`. No inverse
  grading condition is assumed. This reuses the shared-tree
  `GradedGraphTransition.preservesDegree_symm` owner.
- `FiniteFreeCoefficientChange.lean`: native-basis coefficient transport of
  finite free left-module maps, uniqueness, identity/composition, transported
  inverse equivalences, and naturality of the four-block ambient operator.
- `GraphTransitionScalarExtension.lean`: `denominator_map`, `numerator_map`,
  `overlap_map`, `transition_natural`, and `extend_transformed_graph`. Target
  denominator invertibility is proved by transporting its source inverse.
  Coefficient maps need not be surjective, injective, or between commutative
  rings. These finite-free results do not replace the arbitrary-module core.
- `GraphOverlapRegression.lean`: actual arbitrary-module lower-shear
  equivalences, their translation formula, a genuine exterior-algebra even
  shear taking the zero graph to the odd point, and the swap counterexample:
  an invertible ambient operator can take the zero graph outside this chart.

Shared-tree changes were preserved: the existing `GraphChartTransition` is
used unchanged. Another agent supplied the current `GradedGraphTransition`
while this task was running; its implementation is reused, with only an
unused `Decomposition GW` assumption omitted from the fractional theorem.

`InfoGeometry.All` now imports `GraphOverlapRegression`, which reaches both
the previous graph-chart chain and all transition extensions.

## Verification (2026-10-24)

- Locked narrow regression build: exit 0, **1,858 jobs**;
  `/tmp/super-overlap-regression1.log`. Its dependency warning was subsequently
  removed by omitting the unused grading assumption.
- Final locked build of `InfoGeometry.SuperGrassmannian.GraphOverlapRegression`
  and `InfoGeometry.All`: exit 0, **26,995 jobs**;
  `/tmp/super-transitions-all-final.log`.
- Final kernel replay and transitive all-declaration audit under the shared
  build lock: **184 declarations in 12 modules**, all PASS;
  `/tmp/super-transitions-axioms-final.log`.

  | Module | Declarations |
  |---|---:|
  | `ProjectorGraphChart` | 14 |
  | `GradedGraphChart` | 26 |
  | `GraphChartBaseChange` | 15 |
  | `FreeSupermoduleChart` | 26 |
  | `GraphChartOddRegression` | 17 |
  | `GraphChartTransition` | 7 |
  | `GraphChartCocycle` | 28 |
  | `GradedGraphTransition` | 2 |
  | `GradedGraphCocycle` | 16 |
  | `FiniteFreeCoefficientChange` | 13 |
  | `GraphTransitionScalarExtension` | 6 |
  | `GraphOverlapRegression` | 14 |

- Only `propext`, `Classical.choice`, and `Quot.sound` are allowed by the audit;
  no unsafe or partial declarations were accepted.
- Source-aware admission/unsafe checks for all twelve owners: PASS.
- Staged whitespace checks: PASS. Task-owner final checks are warning-free.
- The umbrella has unrelated existing warnings and reports of `native_decide`
  axioms elsewhere. Its successful build is **not** a repository-wide axiom
  certification; the clean transitive audit applies to the twelve listed owners.

### Verified source SHA-256

```text
2b1c3ef795385aea60509c7100c56e850ebec0bd4da9f5a99e5d76fb3ce73813  ProjectorGraphChart.lean
599e64d5819258480a95fa36300aea186503fe89e9de1759501aea9aebe63e8c  GradedGraphChart.lean
772745814ca63a2fbe2fad054c09b9b738c8adbece8ef7307af66287a85926d5  GraphChartBaseChange.lean
812a995df9af8ce74568d1634c62c896228da5bba43609bc8a8f9e3d8a614068  FreeSupermoduleChart.lean
4d1ecd8f539e75447410fe51a5d8b599407fa4d66ad262a17e839b5a2578d974  GraphChartOddRegression.lean
2ed4ee2e05cfc73f94113fc3e8da2affbb0f5886b7dbae978721a41d5afd0922  GraphChartTransition.lean
1783738dcba9e90ade0e82037b27edb2a048f79da58afbb354f03677df31dbbe  GraphChartCocycle.lean
d511392843fb2cc20472b460411992ef4188ca9292544cc95f49dbebabe4b7ab  GradedGraphTransition.lean
ee4f3e0d94586670c3575e21852081679377615c2530f4fa692c6df52a9ca5d1  GradedGraphCocycle.lean
cc0f14733dd6b04983c13070539a9649139ce2edb90f31591ec71804316c97fa  FiniteFreeCoefficientChange.lean
54d4f58679dd8a4232ba40bed33cf57594934bf08dabbe626fefa564f6748b43  GraphTransitionScalarExtension.lean
0d29d7064a29a349569f881e800b5eef3537fee2eeabec591d0fb9f85bc4c186  GraphOverlapRegression.lean
```

## Next boundary

The checked result is an algebraic transition system on transverse graph
charts, not a superscheme atlas. Next define the locally free graded moduli
functor, construct local supercoordinate representations, prove local chart
coverage using localization, and glue with the checked transitions. Reduced
space, tautological bundles and tangent superbundle still require their own
statements and proofs. No categorical continuum passage is part of this step.
