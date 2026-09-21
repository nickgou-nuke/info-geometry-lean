# Krein adjoint and diagonal Möbius transport audit

## Search scope

The September 18, 2026 search inventoried 49,631 Lean source paths using
`rg --files --hidden --no-ignore`, excluding dependency caches, Git metadata,
node modules, external reference trees, and generated report/runtime trees.
This included 23,062 paths under `lean/`, 1,061 under `proofs/`, and 24,699
under `recovered/`. These are path counts, not distinct mathematical modules.
Recovered files, temporary probes, and archives are not current proof owners.

A subsequent full-content scan of the same source scope read 49,635 Lean files
(237,340,062 bytes), with no read errors. Its sorted path/content inventory hash
was `46060d5ed79dfe5fe06b0c6220ded61c33eca35674345495034bd1fe334fef1c`.
The scan included hidden and ignored sources; it excluded `.git`, `.lake`
(including nested dependency caches), `node_modules`, `external_refs`,
`artifacts`, `reports`, and `.runtime`. The counts describe the scan snapshot,
not subsequent additions or a semantic verification of every source file.
The seven search families covered adjoint transport, Möbius/Jordan/cyclotomic
algebra, Galois/inertia, KK/tenfold, spectral/Fisher, optical/detector, and
dependency-poset declarations.

Repository-wide keyword searches covered Krein, Kasparov, tenfold,
antiunitary, adjoint definitions, and transport/equivariance declarations.
Focused follow-up searches covered `kreinConjugate`, `map_star`, metric sign
changes, normalized trace, and polar discriminant formulas. Relevant owner
bodies and their hypotheses were inspected; this is not a claim to have read
every proof in every inventoried file.

`tools/infra/context_preflight.py` was also run with external references enabled.
It reported the declaration-index, LeanSearch, and raw-InfoTree artifacts absent.
Text search and owner source therefore supplied the evidence, not graph counts.
The pipeline document names `/home/goutev/repos/info-geometry-lean`, which does
not exist in this environment; work used the user-provided actual repository
`/home/goutev/info-geometry-lean`.

## Existing owners and actual scope

| Owner under `lean/InfoGeometry/` | Content inspected |
| --- | --- |
| `Krein/TwoSheetKreinIdealBridge.lean` | Involutive conjugation, multiplicativity, principal ideals and Peirce corners |
| `Krein/KreinSpace.lean` | Bounded Hilbert operators, fundamental symmetry, genuine adjoint `J A† J` |
| `OperatorAlgebra/KreinAdjoint.lean` | Alias of that bounded-operator owner |
| `OperatorAlgebra/MetricSharpCuntz.lean` | Packaging of adjoint involution laws and metric Cuntz families |
| `Canonical/StarAlgEquivTransport.lean` | Functorial transport of star-algebra representations |
| `Canonical/FiniteKreinTomitaSixState.lean` | Finite matrix adjoints and Tomita identities |
| `Canonical/ExpectationBilinearKreinTomitaEquivariance.lean` | Finite readout/kernel equivariance |
| `Physics/Algebra/KreinBilinearCommutant.lean` | Finite matrix adjoints and commutant calculus |
| `Canonical/HestenesHermitianAdjoint.lean` | Clifford reverse-based adjoint and involution |
| `Quantum/ComplexKramersAntiunitary.lean` | Actual conjugate-linear equivalence and Kramers pairing |
| `Quantum/AltlandZirnbauerKTheoryBridge.lean` | Ten symmetry-class labels, explicitly not a classification theorem |
| `Quantum/AZTenFoldCompleteClassification.lean` | Assigned invariant labels and modular arithmetic, not a homotopy classification |
| `KK/RealSplitKreinKasparovCycle.lean` | Primitive bounded Fredholm-like carrier with compactness hypotheses; explicitly lacks a genuine right module structure |
| `KK/RealSplitKreinEquivarianceBridge.lean` | Conditional Lie-action equivariance, not construction of analytic equivariant KK classes |
| `KK/KasparovCycle.lean` | Legacy compatibility naming and index transport |
| `Algebra/MoebiusTraceInvariant.lean` | Projectively invariant trace ratio and concrete nonreal/real counterexamples |
| `Arithmetic/AmariZetaDuallyFlatGeometry.lean` | Reality locus of `s(1-s)`: real axis or critical line |
| `Physics/HarishChandraCasimirBridge.lean` | Reflection invariance and critical-line evaluation of the quadratic polynomial |
| `Arithmetic/SpectralActionConfinement.lean` | Conditional confinement from explicitly supplied reality and lower-bound hypotheses |
| `Physics/FiniteChiralSpectralSymmetry.lean` | Eigenmode sign pairing and nonzero preservation under an anticommuting involution |

## Added bridge, not replacement foundations

`Krein/StarHomAdjointTransport.lean` reuses `kreinConjugate` rather than creating
another Krein class. It supplies star-algebra homomorphism naturality of
`metric * star operator * metric`, including a metric sign change. It then
specializes this to the existing bounded `KreinSpace.kreinAdjoint` and transports
self-adjointness. A star-algebra equivalence gives an iff and a native `Equiv`
between the two self-adjoint subtypes. The square-zero
noninvertibility obstruction reuses Mathlib's `IsNilpotent.not_isUnit`.

`Algebra/MoebiusDiagonalPolar.lean` reuses the existing diagonal matrix and trace
ratio. It gives the reciprocal polar parameter, trace formula, raw discriminant
factorization, and

```
Im(traceRatio(diag(z,z⁻¹)) - 4) = (r² - (r⁻¹)²) sin(2θ).
```

The polar identity assumes `r ≠ 0`; the nonvanishing theorem assumes `r > 1`
and `sin(2θ) ≠ 0`. It is not an exhaustive conjugacy classification.

`Algebra/ParabolicAdditiveGroupBridge.lean` connects the existing `NPart` to
Mathlib's `Matrix.GeneralLinearGroup.upperRightHom`, without recreating the
group law. It exposes a native `AddChar` and `MonoidHom`, injectivity,
inverse-parameter compatibility, and the native `Matrix.IsParabolic` criterion
`t ≠ 0`. That criterion feeds the existing exact-index and non-diagonalizability
proofs. In particular, the identity at `t = 0` is not called parabolic.

## Mathematical dependency branches

The supported local dependency order is branched, not the proposed single
physical causal chain:

1. Native real matrices and `NPart` feed the Jordan results; those results and
   Mathlib's additive character feed `ParabolicAdditiveGroupBridge`.
2. Complex diagonal matrices and the projective trace ratio feed the polar
   discriminant identities and their conditional nonvanishing test.
3. Star algebra, metric conjugation, and bounded Krein operators feed adjoint
   transport; star-algebra equivalences then give the self-adjoint subtype
   equivalence.

The three branches are not asserted to imply each other. Existing
`Meta/DeclarationDependencyBridge.lean` provides a certified dependency model
for a supplied relation, while `Causal/FiniteDependencySchedule.lean` provides
topological schedules. Neither turns the proposed physical arrows into
mathematical implications merely by naming them. No full-repository causal
poset or KK/Galois/Selberg equivalence is claimed here.

The subsequent spectral branch in `Spectral/QuadraticParameterReality.lean`
reuses the Amari and Harish-Chandra owners. The real-part formula feeds the
critical-line evaluation, which feeds the lower bound and minimum criterion.
The reality-locus theorem independently feeds the nonzero-imaginary-parameter
criterion. A reflection-invariant parameter with value `3/16` demonstrates why
reflection symmetry alone does not establish a `1/4` lower bound.

The chiral branch in `Physics/ChiralEigenspaceEquivalence.lean` reuses
`FiniteChiralSpectralSymmetry` and upgrades its vector statements to native
eigenspace `LinearEquiv`s and equal `finrank`s. `KK/GradedEigenspaceBridge.lean`
specializes this to the existing `KreinGradedModule` and the odd bounded phase
of `RealSplitKreinKasparovCycle`. No replacement Krein classes are introduced.
Kernel invariance alone does not prove perturbation stability or a Fredholm
index theorem. None of these additions defines or classifies the ten AZ classes.

## Claims deliberately not encoded

- `η x η` is conjugation, not the Krein adjoint; the star is essential.
- Replacing both copies of the metric by their negatives preserves the adjoint.
- An overridable default structure field does not impose its suggested formula.
- A square-zero element is not an invertible time-reversal/particle-hole symmetry.
- An enumeration of ten labels and a list of four examples are not isomorphic
  classification theories.
- Ring identities alone supply no Hilbert C*-module, compact resolvent, Kasparov
  product, K-theory classification, mass-generation law, or Selberg bound.
- The proposed Artin–Schreier, inertia, and modular fixed-field identifications
  require separate field-theoretic hypotheses and proofs. They are not supplied
  by a real shear matrix or by the new adjoint transport theorem.

## Build integration and verification

`Krein/StarHomAdjointTransportTests.lean` includes an actual unitary sheet-exchange
matrix from `Cl11Matrix`, its Mathlib `StarAlgEquiv`, the metric sign-flip law,
and an inverse-round-trip test for the self-adjoint subtype equivalence.
It also tests noninvertibility of the existing spin-raising matrix.
`Algebra/MoebiusDiagonalPolarTests.lean` separately checks the polar branch,
including vanishing imaginary part at angle zero. Both contain axiom-print
commands. `AllExhaustive.lean` imports the tests; the existing default
`InfoGeometry` library glob also covers the files.

Initially the running `lake build -R` (PID 2255, parent 2252) held the shared
build lock. No concurrent compiler was started and no running build was stopped.
After the lock became available, the locked target build failed before checking
the new modules: Lake resolved their source paths under `tests/` instead of
`lean/`. The broad `InfoGeometryTestSuite` glob is an existing routing issue;
neither the Lake configuration nor dependency pins were changed.

Direct `lake env lean` checks, serialized with the repository's `BuildLock`,
successfully checked `Spectral/QuadraticParameterReality.lean`,
`Physics/ChiralEigenspaceEquivalence.lean`, and `KK/GradedEigenspaceBridge.lean`.
The last two also produced local `.olean` artifacts. These local checks are not a
successful default build or validation of the whole repository. The earlier
adjoint/polar/additive-group additions still require successful checks.
The intended locked target command, once target routing is corrected, is:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Krein.StarHomAdjointTransportTests
```

No `sorry`, `admit`, or new axiom declarations were added. This source-level check
is not a substitute for kernel verification.
