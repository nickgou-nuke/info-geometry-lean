# Reflexive parity/readout verification

## Delivered source

- `lean/InfoGeometry/Canonical/ReflexiveParityReadout.lean`: ten reusable
  theorems, with the existing seed predicate, ambient unit, orbit map and density.
- `lean/InfoGeometry/Canonical/ReflexiveParityRegression.lean`: seven named
  proof declarations; proper-support integral matrices, a nonzero parity defect,
  polarized trace 5, characteristic-two cancellation and the self-adjointness
  normalization counterexample.
- `lean/InfoGeometry/Canonical/All.lean` imports the regression owner, hence
  both files are included in `InfoGeometry.All`.
- `scripts/check_reflexive_parity_readout.py`: supplementary source-bound exact
  matrix checks. Run with `/home/goutev/miniforge3/envs/sage/bin/python`.

The public API includes `ambientReflection_on_support`,
`ambientReflection_swaps_seeds`, `ambientReflection_reverses_polarization`,
`odd_combination_conjugation`, `odd_combination_defect`,
`odd_combination_fixed_iff`, `polarization_mul_density`,
`tracial_polarization_density`, `pure_positive_fixed_eq_zero`, and
`pure_negative_fixed_eq_zero` in `InfoGeometry.Canonical.ReflexiveParityReadout`.

The pure-vector results hold for arbitrary left `A`-modules. They need only
reflection-fixedness and support in one pole, not a redundant hypothesis that
the opposite pole annihilates the vector. The defect criterion retains all
coefficient-annihilation cases, including characteristic two. The tracial
readout permits arbitrary weights and does not imply its value is nonzero.

No Pin membership, spinor bundle/descent, physical CP action, condensate wall,
positive normalized state, particle-production dynamics or baryogenesis was
introduced. See `docs/REFLEXIVE_PARITY_READOUT_CONTRACT.md` for the precise
mathematical and authenticated-paper boundaries.

## Checks

- Native dependency baseline: PASS (`/tmp/reflexive-parity-baseline.log`).
- Final focused owner/regression build: PASS, **8,976 jobs**
  (`/tmp/reflexive-parity-build3.log`).
- `InfoGeometry.All`: PASS, **27,059 jobs**
  (`/tmp/reflexive-parity-integrated.log`).
- New owners emit zero warnings. Existing dependency/root warnings remain.
- Strict kernel replay and transitive axiom collection: **619 declarations
  across eight owners**, all PASS; only `propext`, `Classical.choice`,
  `Quot.sound` (`/tmp/reflexive-parity-axioms.log`).
- Scoped staged-source gates: both new files PASS, stable index
  (`/tmp/reflexive-parity-source-gate.log`). No all-staged-files verdict claimed.
- Forbidden-token scans empty; selected oleans fresh; before/after/final source
  drift empty; selected working-tree and staged bytes identical.
- Exact supplementary matrix checks: **14/14 PASS**
  (`/tmp/reflexive-parity-cas.json`). Seeds are parsed from the Lean regression
  declarations; row-major storage, column-vector action, ordinary product.
  The nontrivial round trip is `U*(Q+J)*U = 2*b3`, checked also by Lean.

| Replayed owner | Generated declarations |
|---|---:|
| Canonical/ReflexiveParityReadout | 21 |
| Canonical/ReflexiveParityRegression | 25 |
| Canonical/DeBruijnRotorAlternationCycle | 164 |
| Canonical/GrassmannianBundleCyclotomicOrientability | 193 |
| Core/PeirceDensityIntertwining | 9 |
| Core/DiracSuperalgebra | 79 |
| OperatorAlgebra/TracialCARDensity | 41 |
| NCG/NoncommutativeCyclicCocycle | 87 |
| **Total** | **619** |

The two new owners contribute 46 generated declarations, not 619 new results.
Source binding: `/tmp/reflexive-parity-snapshot.json`.

```
bd061ddbc5979481b1b6503694d8139b9223adc0b5a2fec775df1c740864404e  ReflexiveParityReadout.lean
5d03dcdcdf3ecf0efdd4a4bb36a00d3220d751d7eae26a974f4d996b9cf4d566  ReflexiveParityRegression.lean
```

Builds and replay used the shared build lock and compiler-process prechecks.
No cache deletion, dependency update, process termination or source restoration.
The initial focused proof iteration failed scalar-negation normalization;
`smul_neg` repaired that proof without changing its statement.

## Remote/local provenance

Public GitHub REST readback confirmed:

- remote `main`: `73006b1342e449348fa626995ad96c6a2b48a9e6`;
- branch list: only `main`, no pagination;
- open pull requests: empty, no pagination.

This confirms current remote metadata, not every historical PR merge/ancestry
or the reported independent certification of all 38 remote modules.
The local checkout remains at `d716c2504a4cf21015982248a0860644904239ec`
with the shared staged changes. These new parity additions are staged locally,
not committed or pushed. No pull, reset, checkout or remote mutation occurred.
