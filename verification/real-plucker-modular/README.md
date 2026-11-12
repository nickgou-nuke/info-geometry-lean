# Real Plücker geometry and real phase dynamics

This focused package compiles the parent repository's actual mathematical
owners, with Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` unchanged.

## Mathematical coverage

| Owner | Constructed result |
| --- | --- |
| `Projective/PluckerAffineScrew` | Direction/moment coordinates, native fixed-direction screw `LinearEquiv`, unique perpendicular axis point and pitch, covariance, native dual-number dot product. |
| `Twistor/PluckerGraphChartEquiv` | Bijection between two-by-two matrices and the existing normalized `p23 = 1` Klein chart. |
| `Geometry/PluckerPotentialBoundary` | Nonconvexity counterexample for the ambient norm pullback; a separately chosen strictly convex chart potential, its Fréchet derivative and definite Bregman expression. |
| `Algebra/RegularCentralizer` | The actual centralizer subalgebra of the left regular representation is algebra-equivalent to the opposite algebra; real star exchanges the regular sides. |
| `OperatorAlgebra/RealPhaseInnerDerivation` | The correctly signed real inner generator, native phase-centralizer endomorphism, Leibniz law, stationary kernel and star compatibility. |
| `OperatorAlgebra/RealPhaseExponentialFlow` | Actual one-parameter unitary and real star-automorphism groups, analytic derivatives and preservation of the phase centralizer. |
| `Twistor/InfinityPencilBoundary` | Exact tripotency classification of the existing four-dimensional real infinity pencil, exclusion of a nonzero third sector, and native range/kernel consequences. |

Two existing owners are amended: `PeirceSpine/TripotentDefect` receives the
generic scalar-square obstruction, and `PluckerDualFlatBridge` gets accurate
documentation of its potential-only structure. The audit also includes the
existing public declarations in these two files.

Import `InfoGeometry.Twistor.RealPluckerModularAll` to use the complete
development without audit output. `Twistor.All` exposes that aggregation to
both `InfoGeometry` and `InfoGeometry.AllExhaustive` through their existing
imports. The focused build checks this new public aggregation as well.

## Reproducible checks

From the repository root:

```sh
python3 verification/real-plucker-modular/check.py exe cache get
python3 verification/real-plucker-modular/check.py build
python3 verification/real-plucker-modular/check.py env lean \
  lean/InfoGeometry/Twistor/RealPluckerModularAudit.lean > real-plucker-axioms.log
python3 verification/real-plucker-modular/audit.py --log real-plucker-axioms.log
```

The first command is needed only when pinned Mathlib artifacts are absent.
The supplied manifest pins the same dependency revisions as the repository;
these commands do not run `lake update`. Dependencies are ordinary directories
in the parent checkout's `.lake/packages`. The wrapper holds the repository's
shared build lock throughout each Lake invocation.

`audit.py` checks source coverage and prohibited proof constructs. With
`--log`, it additionally requires actual Lean axiom records for every explicitly
declared public definition, theorem, lemma, abbreviation and structure in the
nine owners. Only `propext`, `Classical.choice`, and
`Quot.sound` are accepted. After changing a declaration inventory, regenerate
the audit with `audit.py --write`, rebuild, and rerun the log check.

The focused package builds its imported dependency closure and audits the
listed owner declarations, including their transitive axiom dependencies.
It does not audit every unused imported declaration, certify the root default
targets, or replace the root publication gate. See
[the theorem contract](../../docs/REAL_PLUCKER_MODULAR_CONTRACT.md) for exact
carrier choices and unproved physical interpretations.

The source screener runs strictly on the new mathematical owners and amended
scalar-square owner. It reports the existing `PluckerHessianGeometry` source
separately: its file-local T17 heuristic cannot see the constructive
`quadraticChartGeometry` inhabitant in the downstream owner. That original
structure and all its declarations remain included in the full axiom audit.
