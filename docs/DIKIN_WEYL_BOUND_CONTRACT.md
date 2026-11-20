# Dikin and Weyl boundedness: theorem contract

## Intake and base

User follow-up to PR #424, 2026-11-20:

> lets delve deeper and replace the assumptions with boundedness by scaling the dikin elipsoid and weyl geuge scale

Base source: `9adc1482d68bdeeeaf989d70434afb0528743592`.
The intended investigation is whether constructive geometric normalization can
discharge the arithmetic growth or operator realization assumptions in the
native RH routes. A bounded normalized quantity must be accompanied by the
factor required to recover the original quantity.

## Source-grounded objects

- `Analysis/LogDetSelfConcordantBarrier.lean`, namespace `SelfConcordant`:
  `hessianQuad A_inv H = trace ((A_inv * H) * (A_inv * H))` and
  `hessianPhi A_inv H K = trace (A_inv * H * A_inv * K)` on real matrices.
  New inverse-based results instantiate `A_inv` with the actual `A⁻¹`.
  `trace_sq_eq_sum_sq` supplies positivity on symmetric normalized variations.
- `Analysis/MatrixSpectralSelfConcordantBarrier.lean`:
  `trace_inv_H_sq_eq_trace_B_sq` is a proved cyclic trace identity for a
  supplied square-root conjugation. A new consumer must construct the square
  root from the actual positive-definite matrix, not assume it as proof data.
- Native Mathlib matrix order, continuous functional calculus square roots,
  nonsingular inverse, and Frobenius norms provide that real construction.
- `InformationGeometry/BurgSteinSelfConcordance.lean`:
  `fisherScaleMetric x v = (v / x)^2` and
  `hessian_eq_fisherScaleMetric` identify the positive-ray quadratic form.
- `Parahyperkahler/AnalyticExcision.lean`:
  `InDikin x y r` is `(y-x)^2 ≤ r^2*x^2`;
  `dikin_affine_scaling` proves invariance under common nonzero scaling.
- `Geometry/BilingualAnalyticity.lean` already relates this same predicate to
  the logarithmic Hessian, the Weyl weight `exp (-log x)`, and the ordinary
  neighborhood filter. Those local topology results do not provide a uniform
  arithmetic estimate as the cutoff grows.
- `Arithmetic/ScaledEulerNN.lean` proves `scaledEuler_NN_iff` and the exact
  cutoff criterion `scaledEuler_NN_cutoff_iff`. Its objects are explicit
  derivative slots of one Euler mode, not an infinite zeta product.
- `Arithmetic/MobiusMertensRHEquivalence.lean` owns the actual native Möbius
  sum, `MertensSquareRootCancellation`, and its all-indices power bound.
- `Arithmetic/MertensMellinRiemannHypothesis.lean` consumes that bound to prove
  Mathlib's `_root_.RiemannHypothesis`.

## Proposed precise results

1. **Real matrix normalization.** For invertible real `A`, arbitrary real
   matrices `H,K`, and nonzero real `c`, prove the exact inverse and Hessian
   scaling laws. In particular, with `Q_A(H) = hessianQuad A⁻¹ H`,
   `Q_(cA)(H) = c⁻² Q_A(H)` and `Q_(cA)(cH) = Q_A(H)`.
   No commutation hypothesis is permitted. Construct the positive square root
   for `A.PosDef`, identify `Q_A(H)` with the squared Frobenius norm of the
   normalized symmetric variation, and expose the factor needed to restore
   an ordinary matrix norm. This is finite real matrix analysis, not an
   infinite-dimensional arithmetic representation.
2. **Positive-ray boundedness.** Reuse the existing Fisher scale metric to
   prove the conversion between a bounded normalized quadratic form and an
   absolute bound with the scale restored. Construct an explicit positive
   normalization for every real sequence; its existence alone must therefore
   not be advertised as arithmetic cancellation.
3. **Actual Mertens consumer.** Prove the unconditional linear bound from
   native Möbius coefficients and the resulting strict Dikin unit bound at
   scale `N+1`. Prove an exact characterization of
   `MertensSquareRootCancellation` by bounded Fisher/Dikin quadratic forms at
   the prescribed scales `(N+1)^(1/2+ε)`, and derive native RH conditionally from
   that boundedness. The equivalence must be explicit: normalization does not
   discharge the remaining uniform bound.
4. **Euler multiplier boundary.** Construct the cutoff multiplier
   `(1+q₀)^2/(4*q₀)` and prove that no single positive multiplier satisfies the
   existing Euler-mode NN slot inequality for every `0<q<1`. A point-dependent
   multiplier on derivative slots must not be described as the derivatives
   of a variable-scaled potential without accounting for product-rule terms.

## Explicit open obligations

The task does not assume or establish a new bound for the actual Mertens
function at exponents below one. The prescribed-scale boundedness is the
remaining arithmetic statement. Neither positive-cone containment nor local
self-concordance constructs a zeta-zero-to-operator-domain map. The existing
centered Mangoldt infinite interchange and Landau argument remain separate.

Common Weyl scaling preserves the normalized geometry. Scaling only the base
can force a small radius, but the scale appears again in the recovered bound.
Dimension or normalized-trace factors must likewise be retained. Alternate
`src/` intensive-logdet counterexamples are navigation evidence unless their
source lane is independently built; they must not be silently promoted.

## Validation and roles

Use the unchanged root Lean/Mathlib pins and shared compilation lock. Preserve
PR #424's initial validation record as historical evidence; record the new
source, fresh elaboration, axiom inventory, and required source gates in a
separate supplement. The root is generation/integration; `statement_audit`
may author isolated candidates; `mathematical_audit` independently reviews;
`build_audit` independently reruns decisive checks. All scope statements are
provisional until the source and recorded checks support them.
