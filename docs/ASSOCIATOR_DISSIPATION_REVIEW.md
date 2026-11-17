# Projected associator dissipation: source and verification record

## Intake and source identity

This change encodes a finite split-algebra instance and a general real-Hilbert
operator construction from `Pasted text(20261117-091139).txt` in three canonical
Lean owners. The input
has 36,565 bytes and SHA256
`1fef0d88c605c9d59f6590503b776362454f6b30b5022bbdec25dc1b12960e48`.
Its narrative and claims of a unique physical synthesis are not adopted as
mathematical premises. The [theorem contract](ASSOCIATOR_DISSIPATION_CONTRACT.md)
states the actual carriers, constructions, hypotheses and boundaries.

The implementation starts at upstream `main` revision
`08c34e03f610b452e03422037949196dc7d92d6d`. It does not depend on the owners
introduced by PR #371 or PR #374. The reviewed environment is unchanged:
Lean `leanprover/lean4:v4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

| Owner under `lean/InfoGeometry/` | Source declarations | SHA256 at source review |
|---|---:|---|
| `Thermo/ProjectedGramDissipation.lean` | 14 theorems, 3 definitions | `9a8b9061ba41ac29d2dde338120e8f212b340c77c29430c5dfe983a4309d4b6d` |
| `Lie/SplitOctonionScalarPotentialObstruction.lean` | 18 theorems, 3 definitions | `cfe5acf7e6f7e05a81ff3e52cac5bd2a8f946fe3158f64193aef0cf10094107f` |
| `Lie/SplitOctonionAssociatorDissipation.lean` | 16 theorems, 5 definitions | `a2b9b8841f1410aff8224e77bbd67976d3a0527e710d4e25e6bbff1661f507da` |

These are source counts, distinct from the native audit's count of all owned
declarations, including generated declarations. All three owners are imported
by `InfoGeometry.All`.

## Dependency order and reused mathematics

| Construction | Existing authority | New implication |
|---|---|---|
| Scalar conjugate sandwich | Canonical Zorn multiplication/conjugation, vector-model trace identities | Trace equals the split norm times the middle trace; a skew-conjugate middle gives zero |
| Neutral cross pairing | `ZornPolarizationMetricBridge.polarForm`, `ellLeftMul`, `ParaComplexNeutralForm` | Actual left split-axis action is an anti-isometry; the Peirce cross pairing equals half the split norm |
| Positive operator | Native `starProjection`, bounded-map composition and adjoint | Ordered projected Gram operator with derived symmetry, positivity, energy annihilation and exact kernel |
| Concrete associator channels | `SplitOctonionEllCircularPeirceBasis.rightMultiplication` from `Lie/CanonicalZornRegularOperators.lean`, native linear equivalences and finite-dimensional continuity | The actual defect `(v*a)*b - v*(a*b)` becomes a bounded operator on an explicit positive Euclidean carrier |
| Pointwise response | Existing `OnsagerMetricData` and `MetriplecticFlow` | Construct their law fields and derive energy/entropy rates under the displayed reversible hypotheses |

The bounded owner search also inspected `FiniteOnsagerGram`,
`GenericMetriplecticFlow`, `BilinearMetriplecticReduction`,
`ParaHessianMixedPotential` and the existing tensor-action bridges. The new
owners add the energy projection and actual Zorn specialization; they do not
duplicate the existing Hessian or tensor machinery. This is a bounded source
survey, not a claim that every historical file has been audited.

## Corrected implications

1. The vanishing scalar potential is a useful obstruction theorem. Scalar
   trace reassociation does not assert equality of the parenthesized Zorn
   products.
2. The symmetric cross potential is `detZ X / 2`, with value `1 / 2` at the
   identity. The positive Euclidean metric used for dissipation is separate from this
   indefinite neutral form.
3. Actual ambient associators can be nonzero on a vector in the existing
   **split-quaternion** core. The proved witness has two core arguments and
   a third argument outside it. No identification with division quaternions
   is assumed.
4. The exact dissipation criterion concerns the projected vector: production
   is positive precisely when one selected projected channel is nonzero.
   Multiplying by mobility additionally requires positive mobility for a
   strict conclusion. A nonzero ambient witness alone does not settle the
   projected question.
5. Full entropy-Casimir degeneracy is stronger than commuting with one
   Hamiltonian. The existing
   `GenericMetriplecticFlow.System.entropy_covector_eq_zero_of_injective` and
   `entropy_rate_zero_of_injective` retain the obstruction on an injective
   Poisson operator.
6. The operator identities provide no Jacobi identity, trajectory,
   Gibbs-integrability theorem, heat/erasure model, curvature theorem or
   uniqueness result. Those remain outside this contract.

## Independent source review

The generator and mathematical reviewer were separate agents. The generic
operator source and both concrete sources received hash-specific source
fidelity PASS. The reviewer checked normalization, multiplication order,
carrier transport, the actual positive metric, all structure fields and the
explicit hypotheses of the rate laws. Independent QA is a third role.

Source review established that the proposed statements match the contract.
It did not establish that Lean elaborated them. The source review receipts
have SHA256 `5b6a03c45c170e915cfaab1aa12dc581fb3b232bd6407597d1ec8d195becbf89`
and `6a6d5492530ec33ec042c4f81b811ba9bac4b0018e7f75f886ab0ba626c0ae29`.

## Verification status

Status at the initial source checkpoint, 2026-11-17 UTC:

- The actual installed pre-commit hook passed for both source commits:
  `eea6d50253257e88fb72d33ffd1d77967a1aca30` and
  `066b88578c4071ab7e1fcec2088db2cf91eed5c0`.
- The first six independent static checks passed on the unchanged source
  checkpoint. The strict placeholder scan had no hard findings and three
  soft findings; the semantic check had no errors and eleven warnings.
  Independent review found these to be legitimate coordinate readbacks,
  native dimensionality and short corollaries of the constructed pairing.
  The strict screener and refutation checks found no violations or traps.
- The first static Gate4 launch was rejected before any child process ran
  because the parent added the workflow and documentation during the QA
  snapshot. The 58 source files, integration imports, helpers, pins and index
  were unchanged. The rejection is retained; remaining checks require a new
  frozen snapshot. It is not a Gate4 or Lean failure.
- Native elaboration, selected-owner warning counts and declaration-axiom
  audit are pending. No source-only result is a kernel certificate.
- The actual push/root gate is pending and is separate from the scoped
  source-closure check. A draft PR is not a successful push-gate receipt.

### Scoped native verification route

The scoped workflow `.github/workflows/associator-dissipation.yml` invokes the
unchanged `tools/quality/check_clifford_dirac.py` with these exact targets:

```text
InfoGeometry.Thermo.ProjectedGramDissipation
InfoGeometry.Lie.SplitOctonionScalarPotentialObstruction
InfoGeometry.Lie.SplitOctonionAssociatorDissipation
```

It uses a fresh output directory, no `--incremental`, no `--skip-audit`, the
unchanged shared lock, and explicitly requires zero warnings for all three
selected owners. The native audit covers every declaration owned by these
modules and permits only `propext`, `Classical.choice` and `Quot.sound`.
Compilation of imported owners and axiom auditing of selected declarations
are different coverage statements.

The source closure contains 58 repository modules and 55 existing Mathlib
import roots. The workflow triggers on every repository source in that
closure, the integration import file, verification helpers, pins and its own
documentation/configuration. Dependency caches are permitted; repository
proof artifacts are not restored. Cache writes are restricted to manual
dispatch under the repository's trusted-event policy.

The workflow records the exact checked source revision separately from the
executing workflow revision. The live driver log is outside the maintained
checker's top-level evidence-hash set. Independent artifact acceptance must
reconcile the actual run, source/helper hashes, warnings, fresh compilation,
complete axiom records and archive bytes before declaring a native PASS.
This route does not certify `InfoGeometry.All` or the root Lake package.
