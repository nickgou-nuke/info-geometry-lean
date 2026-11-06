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
| Full-resolvent sandwich equals corner-resolvent sandwich | Requires the varied direction to lie in the upper Peirce corner. It is not an identity for arbitrary directions. |
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

Implementation and independent validation are in progress. This section will
record the exact declarations, source closure, compiler results, axiom scope,
semantic review, and publication checks before acceptance. The root package's
existing external path-dependency blockers remain a separate integration issue.
