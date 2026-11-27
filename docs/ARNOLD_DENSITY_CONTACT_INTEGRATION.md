# Arnold, density, contact and volume-character integration

## Intake and provenance

Continuation on 2026-11-27 of the published real Beltrami implementation,
branch `codex/arnold-beltrami-cotangent-flow-20261127`, source baseline
`a6503e601568ac49f3ef455fa3b2c4bbe78fffc0`.

The user supplied a synthesis of Arnold's volume-preserving diffeomorphism
group, Grassmannians and Plücker coordinates, contact geometry, Lie groupoids,
and Klein's Erlangen program. Its proposed connections include Euler geodesics,
Reeb/Beltrami fields, Sato Grassmannians and integrable hierarchies, projective
cotangent contact geometry, Jacobi integration, and diffeomorphism pseudogroups.
These are separate claims with different carriers and hypotheses; the table
below records the parts selected for actual integration and the remaining scope.

The operative request is to locate the existing owners and connect the real
Arnold/SDiff and Madelung constructions with Weyl scaling, entropy and Casimir
level sets, KL scale/shape decompositions, and the determinant, Berezinian,
Pfaffian and permanent constructions. In particular, the requested integration
must distinguish volume-preserving or orthogonal motion from radial scaling,
and retain the actual noncommutative operator decomposition.

The attached source is Khesin, Misiołek and Modin, *Information geometry of
diffeomorphism groups*, arXiv:2411.03265v1 (2024). Relevant sections are 3.3
(the Moser density fibration), 5.2–5.4 (information/Fisher–Rao metric), 6.3–6.4
(finite matrix and transport factorization), and 6.6 (Madelung transform).
The actual PDF was inspected as well as its extracted text. In equation 6.22
the square root covers the entire expression `rho exp(i theta)`, so the local
phase is `theta/2`. This agrees with the factor `1/4` in equation 6.25.
The present implementation remains real and does not introduce complex scalars.

## Ground-truth contracts

| Connection | Existing owners | Smallest missing statement | Boundary |
| --- | --- | --- | --- |
| Smooth symmetry and density orbit | `SmoothVolumePreservingGroup`, native `Homeomorph`, `Measure.map`, `MulAction.stabilizer` | Construct the smooth group action on native measures; identify its stabilizer with the existing volume-preserving subgroup; identify the actual orbit with its coset quotient; prove total-mass invariance and the obstruction to nontrivial finite-measure scaling | No Moser transitivity, tame Fréchet manifold, Lie groupoid or Euler geodesic theorem |
| Radial versus shape Fisher geometry | `PositiveMeasure`, `Projective/LogRatioDifferential`, `FiniteFisherRaoSquareRoot` | Actual normalization derivative, native simplex tangent, radial kernel, bilinear Fisher decomposition and equality with the existing projective Fisher energy | Radial direction is normal to constant-mass leaves; it is not generally a Shannon-entropy gradient |
| Matrix radial geometry and paired volume rates | `Architecture/MatrixSymmetricConeFisherRao`, `Analysis/FiniteMatrixJacobiDerivative`, `Quantum/OperatorTraceShapeDecomposition` | Identify radial pairing with half the actual log-absolute-determinant derivative; transport the existing native operator shape part to the full real matrix metric; identify paired logarithmic volume rates as `2d` times the existing common/relative coefficients | Arbitrary ordered real matrix products; positivity only belongs to the appropriate positive symmetric cone; path derivatives do not assert a full Fréchet Hessian construction |
| Physical contact form | `ArnoldBeltramiFlow`, `ArnoldBeltramiCotangentTransport` | Native momentum one-form, actual exterior derivative, contact volume, Reeb equations and strict derivative pullback for the existing spatial flow | Concrete real three-dimensional example; `s^2 = 1` for both the existing velocity to be its Reeb field and strict flow pullback |
| Cotangent volume versus relative character | `MobiusRealCotangentLift`, `Volume/Base`, `Volume/LogPotential` | Package the exact existing cotangent action as a native linear equivalence; compute its total determinant and its relative block determinant; compare common dilation | Ordinary volume and Berezinian-type block ratios are different characters |
| KL radial term | `Projective/GaugeReduction`, scalar expression of `TraceFormula/ItakuraSaitoMongeAmpere` | Prove the reversed mass-ratio expression `gklTerm(x,y) = x*(y/x - 1 - log(y/x))` and substitute it into the existing exact KL split | Normalized KL is not identified with Itakura–Saito; reversed ratio is essential |

All new statements use existing or native Mathlib carriers and actual operations.
No desired conclusion is added as a structure field. Candidate authors do not
run concurrent compilers; integration and exact-source checks are serialized.

## Source-backed distinctions

1. A measure-preserving smooth map need not preserve a Euclidean metric.
   The existing Beltrami shear already includes an explicit nonorthogonal
   derivative with determinant one. Orthogonal maps form a more restrictive
   class; a positive spatial dilation has a different Jacobian character.
2. Pushforward by a measurable map preserves total mass. Thus for a nonzero
   finite measure, `g_* mu = c mu` implies `c = 1`. Scaling the mass of a
   measure is an external scalar action. Infinite Lebesgue measure is outside
   that finite-mass argument.
3. The finite Fisher cone splits into total mass and normalized shape. For
   `M = sum w`, `p = w/M`, and `s(v) = sum v`, the proved bilinear identity is
   `sum u_i*v_i/w_i = s(u)*s(v)/M + M*g_p(dN(u),dN(v))`.
   Normalized Shannon entropy is constant along radial rays. Calling radial
   scaling orthogonal to all "entropy leaves" would therefore be incorrect.
4. For the actual field `u_s = (cos z, -s sin z, 0)`, the momentum form is
   `alpha_s = cos z dx - s sin z dy`. The proved exterior-calculus identity is
   `alpha_s wedge d alpha_s = s dx wedge dy wedge dz`. Contactness requires
   `s != 0`; this velocity is the Reeb field and its flow preserves the form
   under `s^2 = 1`.
5. On `E x E*`, cotangent transport uses `(g, inverse-dual(g))`. Its ordinary
   determinant is one for every invertible real `g`, whereas its relative
   block determinant is `(det g)^2`. Common scaling of both sectors has
   ordinary weight `2 dim E` and zero relative weight. Constant scaling of a
   three-dimensional contact form has weight two, not spatial Jacobian weight
   three.
6. For the existing matrix convention `g_S(X,Y) = trace(S^-1 X S^-1 Y)/2`,
   `g_S(S,X) = trace(S^-1 X)/2`. The latter trace is the actual derivative of
   `log |det S|`, obtained from Jacobi's derivative theorem. With
   `A = S^-1 X` and `B = S^-1 Y`, the full split is
   `g_S(X,Y) = trace(A)*trace(B)/(2d) + trace(shape(A)*shape(B))/2`.
   Here `shape` is the existing native endomorphism operation, transported by
   `Matrix.toLin'` and `LinearMap.toMatrix'`; no commuting assumption is used.
   For two actual matrix paths, the sum/difference of logarithmic volume rates
   is `2d` times the existing paired common/relative coefficient. This connects
   the existing operator trifactor decomposition to actual calculus. Matrix
   inversion identities require invertibility at the evaluation point, and
   dimension-normalized coefficients require `d > 0`.

## Integration surface and literature

`InfoGeometry.Canonical.ArnoldInformationGeometry` imports these bridges and
includes the existing physical one-parameter flow in the native smooth group.
It proves that the resulting measure action fixes volume, belongs to the
measure stabilizer, and fixes every externally scaled reference measure.
`InfoGeometry.All` imports this entry point, so it is available from the
repository's public root surface.

Primary sources and the scope they support:

- Arnold (1966), §10: kinetic right-invariant metric and ideal incompressible
  Euler flow: <https://www.numdam.org/article/AIF_1966__16_1_319_0.pdf>.
- Khesin, Misiołek and Modin, arXiv:2411.03265v1, §3.3 and Remark 3.10:
  pullback/right-coset and pushforward/left-coset conventions; §§5–6 for
  Fisher–Rao and Madelung geometry:
  <https://arxiv.org/html/2411.03265v1>.
- Khesin, Misiołek and Modin, *Geometry of the Madelung transform*, Definition
  2.2 and Remark 2.3: explicit half-phase and square-root convention:
  <https://arxiv.org/pdf/1807.07172>.
- Etnyre and Ghrist, Theorem 2.1: nonsingular rotational Beltrami fields and
  Reeb fields up to normalization, with the metric/volume hypotheses retained:
  <https://etnyre.math.gatech.edu/preprints/papers/hydro.pdf>.

The paper uses the radius-one square-root map. The existing finite repository
owner uses `2 sqrt p`, hence the unscaled Fisher pairing. The new derivative
proofs retain that radius-two normalization.

## Existing operator and projective pieces retained at their actual scope

- `Quantum/OperatorTraceShapeDecomposition` owns genuine real endomorphism
  scalar/traceless and paired common/relative/shape decompositions. It is a
  block-diagonal paired carrier, not an arbitrary off-diagonal supermatrix.
- `NCG/BerezinianExponentialSupertrace` proves the actual block-diagonal
  exponential character `exp(trace A - trace D)`; `SupertraceScaleKernelSplit`
  identifies the supertrace of the cotangent generator `diag(A, -A^T)` as
  `2 trace A`. Its ordinary block trace is zero. These are located pre-existing
  results retained for context; the new owners do not import or invoke them.
- `NCG/BerezinianGaussianFactorization` supplies ordered noncommutative block
  LDU algebra under an actual two-sided inverse hypothesis.
- `Projective/PluckerMatrixAction` owns the native second-compound action and
  determinant-weighted Klein quadratic form. `Canonical/PfaffianFour` and
  `Projective/PluckerLinearComplex` supply genuine four-dimensional Pfaffian
  determinant identities. Their dimensions and commutative coefficient
  hypotheses remain explicit.
- The permanent/adjugate owner
  `Canonical/CartanBhojaKrasnovXamboAharonovUnificationBridge` has ordered
  noncommutative identities. A general permanent is not a multiplicative
  replacement for the determinant.
- `Canonical/WeylGaugeGWProjectiveScaleCalibration` assumes its
  volume-to-partition calibration. It does not construct Gromov–Witten
  invariants or identify them with these measure orbits.
- `Physics/SDiffCoadjointHelicityCasimir.LocalSDiffIsometry` stores a
  pointwise inner-product preservation assumption. It is not the actual
  spatial smooth volume-preserving group. The new connections use the latter.

## Navigation provenance and open scope

Repository and pinned Mathlib source searches were performed before choosing
new owners. The local declaration index `artifacts/dag/index/decls.jsonl` is
absent. Read-only checks of the configured declaration and literature graph
endpoints both returned `URLError`; no graph was rebuilt or modified. Absence
claims from navigation are consequently qualified by the searched source scope.

The infinite-dimensional Euler–Arnold theorem, Moser transitivity on smooth
positive densities, Sato/KP hierarchy, contact/Jacobi Lie-groupoid integration,
general Gromov–Witten identification, and a general noncommutative operator
logarithm decomposition remain outside these finite/native contracts.

## Verification record

`[kernel_verified]` The combined exact 38-module source closure compiled with
Lean `4.34.1` and pinned Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. All 17 selected mathematical
owners passed with warnings treated as errors. This scope includes the original
five Beltrami owners, four reused owners whose imports were narrowed, and the
eight new mathematical owners. It is not a whole-repository build certificate.

The native `ArnoldDensityContactDeclarationAudit` accepted all 547 owned
declarations, including generated declarations: 440 theorem declarations,
101 definitions, two inductives, two constructors, and two recursors.
It inspects actual checked types and values and collects axioms transitively.
The only permitted foundational axioms are `propext`, `Classical.choice`, and
`Quot.sound`. Owner-local axioms, unsafe/partial declarations, and additional
axiom dependencies are rejected. The eight new mathematical owners account
for 227 of these audited declarations; the total is not a count of new theorems.

The existing `NoncommutativeJacobiLiouvilleFlow`, `PACKreinEquivalence`, and
`SplitPAC44KreinCarrierBridge` are included as compatibility targets. Seven
unchanged dependencies emit 25 existing warnings in total; all selected owners
and the native audit are warning-clean. The changed `InfoGeometry.All` import
line is an integration wiring change; compilation of that full umbrella remains
subject to the separate root-package gate.

Independent semantic reviews accepted the contact normalization and orientation,
actual derivative use, native carrier conversions, ordered matrix products,
paired common/relative rates, nonvacuity, and explicit scope boundaries.

Four reused owners now use specific Mathlib imports. Their mathematical
operations and formulas are retained. The Jacobi owner uses the current
`HasDerivAt.fun_finsetProd` spelling. The projective ratio owner also removes
unreachable tactics and unused nonempty hypotheses and marks its native metric
definition instance-reducible. Two pre-existing paired trace proofs now use
explicit trace and distributivity rewrites after the staged operator screener
rejected their scalar-tactic scripts. Their theorem statements are unchanged.
No linter, proof gate, dependency pin or audit condition is disabled.

To reproduce the exact check, set `ARNOLD_MATHLIB` to a clean checkout at the
repository pin and `ARNOLD_LEAN` to the pinned compiler, then run:

```bash
python3 tools/quality/check_operator_geometry.py \
  --repo . --mathlib "$ARNOLD_MATHLIB" --lean "$ARNOLD_LEAN" \
  --work-dir /tmp/arnold-density-contact-check \
  --owner InfoGeometry.Quantum.DualFlatKreinGraph \
  --owner InfoGeometry.Canonical.ArnoldBeltramiFlow \
  --owner InfoGeometry.Canonical.ArnoldBeltramiCotangentTransport \
  --owner InfoGeometry.Canonical.SmoothVolumePreservingGroup \
  --owner InfoGeometry.Canonical.ArnoldBeltramiVolume \
  --owner InfoGeometry.Canonical.FiniteFisherRaoSquareRoot \
  --owner InfoGeometry.Projective.ExpectationRatioMetric \
  --owner InfoGeometry.Analysis.FiniteMatrixJacobiDerivative \
  --owner InfoGeometry.Quantum.OperatorTraceShapeDecomposition \
  --owner InfoGeometry.Canonical.SmoothDiffeomorphismDensityOrbit \
  --owner InfoGeometry.Canonical.ArnoldBeltramiContact \
  --owner InfoGeometry.Canonical.KLScaleItakuraSaito \
  --owner InfoGeometry.Quantum.CotangentVolumeCharacters \
  --owner InfoGeometry.Canonical.ArnoldBeltramiVolumeCharacters \
  --owner InfoGeometry.Projective.FisherRaoRadialShape \
  --owner InfoGeometry.Geometry.RealMatrixFisherRadial \
  --owner InfoGeometry.Canonical.ArnoldInformationGeometry \
  --target InfoGeometry.Canonical.ArnoldInformationGeometry \
  --target InfoGeometry.Analysis.NoncommutativeJacobiLiouvilleFlow \
  --target InfoGeometry.Quantum.PACKreinEquivalence \
  --target InfoGeometry.Quantum.SplitPAC44KreinCarrierBridge \
  --owner-warnings-as-errors --audit \
  --audit-source lean/InfoGeometry/Canonical/ArnoldDensityContactDeclarationAudit.lean
```

The checker validates the compiler and all Mathlib package revisions, snapshots
actual repository sources without stubs, serializes compilation under the
maintained build lock, and records source and verification-tool hashes.
Unmodified dependency bytes are compared to the baseline separately; the
checker's pre-existing custom-owner `--base-ref` limitation is not bypassed.

### Independent execution QA

A second execution from a previously absent artifact directory, without
`--incremental` or `--base-ref`, passed the same 38-module compilation and
547-declaration audit before the two final trace-proof rewrites described
above. After those proof-only changes, the integration checker rechecked the
complete selected source closure and reran the native audit successfully,
using its maintained `--incremental` mode and source-hashed artifacts. The
scope and counts remain 38 modules, 17 owners, and 547 audited declarations.
All owner logs are empty.

All 21 unmodified nonowner dependencies and all five unchanged audited owners
byte-match baseline `a6503e601568ac49f3ef455fa3b2c4bbe78fffc0`.
The 25 dependency warnings are preserved baseline warnings. Placeholder,
bypass and required-header checks passed. Independent semantic reviews also
checked the final paired log-determinant derivative statements and the two
trace-proof rewrites. The fresh independent execution and the final
source-delta review are separate verification steps.

### Root-package and source-scan status

The extension's direct path-package preflight was executed:

```bash
python3 tools/infra/ci_bootstrap.py paths
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.All
```

Both commands exited 1. `HomotopyHypothesis` and `Atlas` have missing, untracked
path-package configurations; the pinned `GIFT` gitlink is uninitialized.
The real locked root Lake build stops at the missing
`external_refs/homotopy-hypothesis-lean4` directory. No dependency is replaced
by a stub, a moving branch, or a changed manifest. Thus the new umbrella import
is not covered by a successful root-package build.

The scoped semantic-vacuity scanner on all 14 changed Lean files exited 0
with `--fail-on error`: no errors and 19 heuristic warnings. The warnings mark
definitional application lemmas, the two explicit scalar trace consequences,
and the existing positive-probability carrier fields; semantic review checked
their actual content. This scan is distinct
from the native declaration audit and does not by itself prove nonvacuity.

The upstream review must retain draft status while root integration is
blocked. The pull-request receipt records the tracked staged and pre-push
gate outcomes for the submitted source tree; no failed gate is represented
as a pass.
