# Idempotent charts and ordered resolvent calculus

## Intake and scope

The source is the user attachment `Pasted text(6).txt`, SHA256
`7ab8a4b7a2006afa04549753c7289bd7ec539953d0d7f8308d21b9cbab9b52bc`.
Its proposed Super-Grassmannian and para-Kähler synthesis contains algebraic
identities, analytic derivative claims, interpretation, and incompatible signs.
This contract preserves those distinctions instead of treating the prose as
proof authority.

The algebraic carrier is an arbitrary unital associative ring `B`, with an
idempotent `P`. We reuse the repository's actual Peirce operators:

```text
a = conePlus P A  = P * A * (1 - P)
b = coneMinus P C = (1 - P) * C * P
Phi = genPhi P A C = a + b
V = genV P A C = a*b + b*a
Sigma = genSig P A C = a*b - b*a
```

The existing `Core.IdempotentGraphGrassmannian.idempotentGrassmannian` is an
algebraic idempotent locus. It does not supply a smooth manifold or a
supermanifold. Native `Ring.inverse` is used only with explicit unit hypotheses
when inverse laws are required. Ordered multiplication is retained throughout.

## Source-grounded claim inventory

| Intake claim | Formal scope and disposition |
|---|---|
| The binary cut gives two opposed tangent directions | Existing `PeirceSpine.Basic` supplies the two corner maps and their annihilation laws. `Core.IdempotentTangent` supplies the exact algebraic tangent equation and off-diagonal decomposition. |
| Fourfold relational anatomy | The four Peirce corners are actual ordered products. Their interpretation as conscious, projected, shadow, or ground components is not a mathematical hypothesis. |
| `P+a` and `P+b` are idempotent | Algebraic consequence of the existing corner laws; the positive-sign convention must be translated from the existing negative-sign unipotent charts. |
| The naive sum has defect `V` | Exact equation `(P+a+b)^2 - (P+a+b) = V`. Nonvanishing of `V` is a separate condition. |
| Corrected dressed projector | `(1-a)*(P+b)*(1+a) = P + Phi - Sigma - V*a`, with exact idempotency. Reuses existing unipotent orbit and defect owners. |
| Opposed round trips agree across a direction | `(a*b)^k*a = a*(b*a)^k`; this is associativity and preserves the two different products. |
| Resolvents push through the direction | Under denominator units, `inverse(1-a*b)*a = a*inverse(1-b*a)`. Peirce orthogonality relates these to `inverse(1-V)*a`. |
| One denominator hypothesis suffices in the Peirce setting | Orthogonal corner products factor `1-V` into commuting factors `1-a*b` and `1-b*a`; unit laws supply the precise implication. |
| Differential factors into an ordered sandwich | The algebraic simplification is a ring identity with inverse laws. An actual `HasFDerivAt` statement requires a normed algebra and the native inverse-function calculus. |
| Full-resolvent sandwich equals corner-resolvent sandwich | Requires the varied direction to lie in the corresponding upper or lower Peirce corner. It is not an identity for arbitrary directions. |
| The sandwich is a Hua–Bergman–Dikin metric or Amari Hessian | Open geometric identification. The ring-valued expression alone supplies no scalar pairing, nondegeneracy, positivity, connection, or Hessian potential. |
| `-log Ber(1-V) = -STr log(1-V)` | Open in the proposed supergeometric carrier. A graded matrix trace and an ordinary Schur ratio do not supply a supercommutative Berezinian or a logarithm domain. |
| Split octonions embed multiplicatively into the associative carrier | Not inferred. The existing Zorn multiplication is nonassociative; a multiplication-preserving embedding needs a valid restricted carrier and a proved map. |

## Existing owners and conventions

- `OperatorAlgebra/PeirceSpine/Basic.lean`: `conePlus`, `coneMinus`,
  `genPhi`, `genV`, `genSig`, the corner support laws, and same-corner
  annihilation. These are used with `P * P = P`.
- `OperatorAlgebra/PeirceSpine/Unipotent.lean`:
  `moebius_bruhat_idempotent_orbit_and_metric_invariance` and the existing
  single-chart identities. Its `projChartPlus` is `P - conePlus P X`;
  substituting negative coordinates is necessary for the intake's `P+a`.
- `Core/IdempotentGraphGrassmannian.lean`:
  `idempotencyDefect_idempotent_add_of_cross_sum`,
  `idempotencyDefect_conj`, and the actual algebraic idempotent locus.
- `Core/IdempotentTangent.lean`:
  `tangent_iff_diagonal_corners_zero` and `tangent_eq_offDiagonal`.
  These preserve characteristic-two distinctions.
- `OperatorAlgebra/PeirceSpine/GradedTraceMoments.lean` uses native
  `mul_pow_mul` for cyclic product powers; no commutative surrogate is needed.
- `OperatorAlgebra/PeirceSpine/Bergman.lean` defines
  `jordanTriple X Y Z = X*Y*Z + Z*Y*X`. Its diagonal value is twice the
  cubic correction in the intake.
- Mathlib `Analysis/Calculus/FDeriv/Mul.lean` supplies
  `hasFDerivAt_ringInverse` and native continuous linear multiplication maps.
  The derivative owner uses these on the unit locus of a normed algebra.
- `NCG/BerezinianExponentialSupertrace.lean` proves
  `blockBerezinian_exp_eq_exp_supertrace` and
  `neg_log_blockBerezinian_exp_eq_neg_supertrace` for finite real
  block-diagonal exponential charts. The generator is explicit; this is not
  a general matrix logarithm theorem for `1-V`.
- `SuperGrassmannian/GradedGraphTransition.lean` proves degree preservation
  for an actual ordered fractional graph-coordinate transition with a genuine
  denominator linear equivalence. Identifying this transition with the new
  resolvent coordinate is a separate, unproved bridge.
- `Canonical/SuperGrassmannianManifold.lean` supplies algebraic linear and
  bilinear carriers. Its structure definitions do not supply a graded atlas,
  nondegeneracy, or a closed differential form.
- `Canonical/StreamVIDeclarationAudit.lean` supplies the checked finite
  dependency-reachability construction. A topological rank certifies
  acyclicity; it is not substituted for the reachability relation.

## Corrected formulas and rejected implications

The attachment first uses `(1+a)*(P+b)*(1-a)` but gives a different expansion.
With its own support conventions, the actual expansion is

```text
P - a + b + a*b - b*a - a*b*a.
```

Its later corrected orientation is consistent:

```text
(1-a)*(P+b)*(1+a)
  = P + a + b - a*b + b*a - a*b*a
  = P + Phi - Sigma - V*a.
```

Both conjugations preserve idempotency; their linear and quadratic terms
are different. The earlier proposed expression `P + Phi + a*b - V*a`
does not generally preserve idempotency. The native rational `2 x 2`
matrix counterexample uses `P=E11`, `a=E12`, and `b=E21`, proves their
actual corner support laws and noncommutativity, and compares entries of
the proposed expression and its square.

The cubic correction is `a*b*a = V*a`. Under the repository's Jordan
triple convention, `jordanTriple a b a = 2 • (V*a)`. Dividing by two is
not available in an arbitrary ring.

The identity `Rplus*a = a*Rminus` is an intertwining equation at a specified
point. It does not make the nonlinear map `a ↦ inverse(1-a*b)*a` a module
homomorphism. Nor does the Peirce identity force `V` or a commutator to be
nonzero.

Left multiplication by `2*P-1` and conjugation by `2*P-1` are distinct
actions. Conjugation negates both off-diagonal corners; it is not the
claimed opposite-sign action on the two tangent directions. Distinct
`+1` and `-1` eigenvalues also require care in characteristic two.

At the base point `a=b=0`, the base values `V` and `Sigma` vanish, while
independent tangent directions can have nonzero product. Therefore the
attachment's origin formula must not identify a variation product with
the base-point expression `(V+Sigma)/2`.

The existing `OperatorLogDetDikinGeometry` identifies the scalar real-trace
log-determinant Hessian on the unit locus of complex matrices. Its positivity,
self-concordance, and Dikin-containment conclusions require strictly positive
base matrices and self-adjoint directions. These theorems do not establish
the proposed arbitrary ring-valued supertrace metric. A bosonic logdet barrier
minus a fermionic one is not automatically convex: the elementary ratio
`Ber(1,1+t)=1/(1+t)` gives the negative-log readout `log(1+t)` for `t > -1`.

## Actual dependency structure

The construction branches. Idempotency and corner laws imply single-chart
idempotency and the additive defect. Unipotent conjugation then gives the
corrected dressed idempotent. Separately, associativity gives cyclic product
intertwining; unit laws transport it through resolvents. Peirce orthogonality
relates corner denominators and full denominators. The native inverse
derivative, multiplication rule, and algebraic factorization give the
Fréchet derivative under analytic hypotheses.

There is no proved implication from dressed-projector idempotency to
invertibility, from invertibility to a Berezinian logarithm, or from these
ring identities to a supermanifold or Amari connection. Those proposed
arrows are omitted from the theorem dependency relation.

## Implementation targets

| Owner | Main declarations and exact role |
|---|---|
| `OperatorAlgebra/PeirceSpine/IdempotentChartResolvent.lean` | `conjPlusInv_lower_chart_eq`, `conjPlusInv_lower_chart_idempotent`, `add_genPhi_idempotent_iff`, `positive_chart_commutator_eq_zero_iff`, `isUnit_one_sub_genV_iff_corner_units`, and the upper/lower full-resolvent sandwich laws. |
| `OperatorAlgebra/ResolventChartDifferential.lean` | `resolventChart`, ordered inverse transport, exact `resolventChart_add_sub`, algebraic `resolvent_differential_factorization`, actual `hasFDerivAt_resolventChart`, and `fderiv_resolventChart_apply`. |
| `OperatorAlgebra/PeirceSpine/IdempotentChartDifferential.lean` | `fderiv_resolventChart_conePlus` and `fderiv_resolventChart_coneMinus` connect the actual derivative to the full-resolvent sandwich on the respective corner direction. |
| `OperatorAlgebra/PeirceSpine/ChartSignCounterexample.lean` | `matrix_units_peirce_support`, `upper_lower_noncommute`, `early_claim_not_idempotent`, and `opposite_conjugations_ne` establish the concrete matrix obstruction to the conflicting source formula. |
| `Canonical/IdempotentChartDeclarationAudit.lean` | Reuses the shared type/value audit for the new owner declarations and emits a native reachability partial order in its own namespace. |

The generic derivative quantifies over every direction. It assumes
`[NontriviallyNormedField k]`, `[NormedRing B]`, `[NormedAlgebra k B]`,
and `[HasSummableGeomSeries B]`, with both denominator units explicit.
Mathlib supplies the last typeclass from completeness. The Peirce
specializations derive both units from `IsUnit (1-genV)` and restrict the
direction to the appropriate actual corner; they do not strengthen the
generic formula to an unsupported full-resolvent identity on arbitrary
directions.

The shared audit is exposed as `auditOwners` without weakening its checked
declaration, axiom, cycle, endpoint, logged-error, or native-certificate guards.
The original Stream VI invocation remains. The supplemental-seed JSON field
is generalized from `added_inverse_declarations` to `added_seed_declarations`;
its original seed set is unchanged.

## Acceptance record

The complete selected mathematical closure and bounded audit rejection check
passed at commit `0d291ab233a01601fac703e3b80754a2ade1b555`, tree
`b6ddc968b800da9108fe5062f9776f4bf4aff0d1`, in the successful
[CI run 42198354474](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/42198354474).
Its positive step freshly checked all **71 project source modules**, including both
declaration audits, without incremental project-artifact reuse. The environment
was Lean `4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`), with Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Toolchain and dependency pins are unchanged.

The [retained verification artifact](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/42198354474/artifacts/13494142724)
contains the source snapshots, compiler/audit logs, execution fingerprints,
source and object manifests, and the negative probe's source and result.
Its ZIP SHA256 is
`cd2cef1cd16e01c1a98ec0db3d90d6a72841cc25706b7d99e6b333d622592007`.

| Audited closure | Seeds | Reachable project declarations | Theorem declarations | Dependency edges | Graph-certificate declarations |
|---|---:|---:|---:|---:|---:|
| Idempotent chart calculus | 62 | 135 | 110 | 438 | 8 |
| Preserved Stream VI | 81 | 294 | 192 | 916 | 8 |

These are closure counts, including existing, private, and generated declarations;
they are not counts of newly written public theorems. Every graph-certificate
declaration has an empty axiom list. The order constructor is shared, so the two
audits contain 15 distinct certificate declarations. The transitive axiom union
of each mathematical closure is exactly `propext`, `Classical.choice`, and
`Quot.sound`.

Independent artifact readback verified all 71 source snapshots against the exact
Git commit, checked the result/source/compile-order manifests, and matched the
71 fresh project-object hashes with the runner's preflight fingerprint. It also
checked seed ownership, exact dependency edges, endpoint bounds, acyclicity,
and certificate names. All 303 Stream VI records (294 declarations, eight
certificates, and the summary) match its earlier accepted output after only the
intended `added_inverse_declarations` to `added_seed_declarations` field rename.

The build emitted 17 lint warnings in unchanged owners, zero task-mathematics
warnings, and zero proof-hole warnings. Independent mathematical/source review
and the scoped staged-proof, strict OpenGauss, semantic-content,
semantic-vacuity, strict closure-debt, and whitespace checks passed. Nonblocking
heuristic advisories were inspected separately. Earlier normalization and
command-layout failures are preserved as failed runs; their repairs changed no
mathematical statement, hypothesis, or multiplication order.

### Bounded audit rejection check

`tools/quality/check_chart_audit_rejection.py` runs only after a complete positive
check. It replays the valid Stream VI invocation, then changes one generated
forward-edge proof to an ill-typed `Nat` term only in a new scratch namespace.
Acceptance requires one actual failing Lean invocation, no new success summary
or accepted invalid certificate, exact preservation of the valid audit and new
mathematical records, and unchanged source/index/snapshot/project-object/tool
fingerprints. An existing probe directory is refused rather than overwritten.

In run 42196321483 the probe was **BLOCKED before invoking Lean** by an overstrict
requirement that every pinned native package have a compiled library directory.
That raw result is retained and is not a rejection-test PASS. The reviewed
correction uses the positive checker's existing-directory discovery and search
order, still checks every package pin and tracked source, rejects unpinned
library directories, and records included library directories and pinned
packages without one.

The corrected runner **passed** in run 42198354474. It invoked Lean exactly
once; Lean exited 1 without a timeout. All 11 recorded acceptance criteria
passed: the valid Stream VI records and new mathematical declaration records
were preserved, the ill-typed certificate was not accepted, no new success
summary appeared, and all source/index/snapshot/project-object/tool fingerprints
remained unchanged. The generated probe source and runner were also unchanged.
This is one bounded caller-namespace regression, not an exhaustive verifier test.

Reproduce the selected check and subsequent bounded probe with the pinned
environment, using a fresh verification directory and the resolved native Lean
executable:

```sh
python3 tools/quality/check_operator_geometry.py \
  --mathlib /path/to/pinned-mathlib \
  --work-dir /path/to/fresh-verification \
  --target InfoGeometry.Canonical.IdempotentChartDeclarationAudit
python3 tools/quality/check_chart_audit_rejection.py \
  --repo . --mathlib /path/to/pinned-mathlib \
  --work-dir /path/to/fresh-verification \
  --lean /path/to/pinned-toolchain/bin/lean
```

### Integration boundary

This is selected-source acceptance, not a whole-repository build certificate.
The maintained read-only path preflight at
`0d291ab233a01601fac703e3b80754a2ade1b555` exited 1 with three
unavailable dependencies: absent, untracked HomotopyHypothesis and Atlas paths,
and the uninitialized GIFT gitlink at
`e6f3c3ac2140c2324fb2ae029c32233e73aa5e92`. Tracked `InfoGeometryCore` was available. The root
configuration, dependency/toolchain pins, lock implementation, and pre-push
hook are unchanged from the prerequisite revision. This current preflight is
an availability/provenance check, not a completed root build.

The prerequisite's maintained root Lake and clean-checkout pre-push attempts
stopped at the missing `external_refs/homotopy-hypothesis-lean4` path before
target theorem checking. The queued pre-push check for the earlier chart repair
`d1902958610c22bdb7942e4eecfa0e2aec4426de` also completed with exit 1 at that same
dependency blocker. Its four executed static audits passed. That older-revision
gate is not represented as a current-head root build.

The observed repository-wide debt workflow reports 878 forensic/fixture
findings, and the documentation workflow fails at GitHub Pages configuration
before reaching Lean. Those integration results are separate from the complete
selected mathematical build and native graph certificates. The upstream PR
remains a draft while these repository-wide gates are unresolved.
