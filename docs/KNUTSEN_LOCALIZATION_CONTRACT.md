# Projection localization, finite frames, and multiscale porosity

## Intake and source authority

The intake is `Pasted text(20261113-061747).txt`, received on 2026-11-13.
It is byte-identical to the earlier `Pasted text(20261113-060321).txt` intake.
The seven mathematical owners reuse the earlier candidate work after source
review; an independent checkout freezes this publication candidate.
Its SHA256 is
`bd31543386a90075f8bea22af36bdc630983313f5148eb6e2de6f2bfdfdb7db0`.
The implementation starts from repository commit
`a392af178af1fe2bcba2ba39eb405700c6ee103c`, with its unchanged Lean 4.34.1
and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` pins.

Primary mathematical context is Helge Knutsen,
[*A Fractal Uncertainty Principle for the Short-Time Fourier Transform and
Gabor Multipliers*, arXiv:2204.03068v1](https://arxiv.org/pdf/2204.03068v1).
The retrieved PDF identifies v1, 6 April 2022. Its equation (3.9) motivates
the real porosity recurrence. Lemma 5.2 concerns Gaussian Gabor norm estimates
through Fock-space sampling; it is not the finite Gram-square identity.

This contract specifies theorem targets and their mathematical boundaries.
Compilation and independent acceptance are recorded separately in the
verification package. The intake's claim of already complete verification is
not adopted as evidence.

## Existing owners and intended extensions

`Core.PeirceCompressionDefect` already owns polarized compression defects,
star-square factorizations, and a proper-star zero-defect criterion.
`Core.PeirceCompressionCStar` supplies the exact norm of a defect and the
commutation criterion. Projection localization specializes these owners.

`OperatorAlgebra.NoncommutativeKrausChannel` owns finite conjugation sums.
`Clifford.OperatorValuedJones` owns the native matrix generators. The intake's
skew generator is the negative of its `K_mat`; this convention is retained.
`OperatorAlgebra.CoisometricCoarseGraining` has related rectangular results
over `RCLike` coefficients. The new finite-frame algebra uses arbitrary
noncommutative star-ring coefficients, without replacing those coefficients
by scalars or introducing invalid left-module matrix actions.

Bounded searches of canonical and alternate repository source roots and the
pinned Mathlib source did not locate a metric-porosity predicate or the
Knutsen recurrence. The new analytic owners use native metric spaces, sets,
real numbers, finite sums, ordered lists, and norms.

## Projection localization and range corners

For star projections `p`, `q` and a one-sided isometry `v`, the complementary
operators `q * v * p` and `(1 - q) * v * p` have Gram operators summing to `p`.
The assumption `star v * v = 1` is an isometry condition; it does not assume
the reverse equation.

The variance of `p * q * p` is the star square of `(1 - p) * q * p` and also
the compressed star square of the Lie commutator. Positivity uses the native
star order. Equality detection and exact squared-norm formulas use C-star
hypotheses. Bare star-ring factorization alone supplies neither an order nor
faithfulness of the involution.

The map `x ↦ v * x * star v` is a native non-unital star-ring embedding and
defines an explicit ring equivalence from the coefficient algebra to the
native idempotent corner of `v * star v`. The inverse is
`x ↦ star v * x * v`. The corner unit is `v * star v`.
This construction yields intertwining, complementary partitions, power
transport, and C-star norm transport. Forward ambient power transport is
restricted to positive powers; corner powers use the correct corner unit.
Pullback power transport also holds at exponent zero.

Pullback of an ambient projection is idempotent exactly when the ambient
projection commutes with the isometry's range projection, under the stated
C-star assumptions.
No actual STFT or Bargmann integral transform is constructed by these maps.

## Finite frames and Weyl masks

For a rectangular synthesis matrix `A`, the frame and Gram operators are
`A * Aᴴ` and `Aᴴ * A`. Matrix multiplication preserves every coefficient
order. Their intertwining and power identities imply that the Gram operator
is a native star projection whenever the frame operator is the identity.
Operator-valued diagonal symbols give multipliers with explicit adjoint and
complement identities. The one-row case connects to the existing Kraus sum.

The four Jones/Weyl generators act on the Peirce window `P₊`. Their full frame
sum is `2I`; the balanced two-element mask gives `I`, while the parallel
two-element mask gives `2P₊`. The singleton gives `P₊`. These are finite
operator identities. Equal mask cardinality does not determine a strict
operator-norm contraction or geometric porosity.

The unnormalized four-term conjugation sum satisfies `E(E(M)) = 4 E(M)`.
This identity does not establish idempotence in general; a characteristic-zero
witness proves non-idempotence. Normalization by four requires invertibility
hypotheses. In characteristic three the same identity already gives
idempotence, and in characteristic two the twirl is zero. Its scalar-matrix image is not generally central when the
coefficient ring is noncommutative. Distinct labels need not give distinct
operators in characteristic two.

## Metric holes and the real recurrence

The metric predicate requires positive porosity and a nonempty positive
scale interval, with an actual ball disjoint from the localized set inside
each tested ball. A triangle-inequality theorem shrinks such holes under
native open metric thickening. It does not replace disjointness by a
measure-zero intersection. At zero thickening radius, the native open
thickening is empty. Iterated-thickening equality is not assumed in arbitrary
pseudometric spaces.

For real `ν`, define

\[
\nu_0=\nu,\qquad \nu_{j+1}=\nu_j-(\nu/3)^{j+1}.
\]

The arithmetic targets include the finite geometric-sum formula, exact closed form,
monotonicity, and the uniform bounds `ν/2 ≤ ν_j ≤ ν` for `0 ≤ ν ≤ 1`.
Consequently `1 - ν_j^(2*d) ≤ 1 - (ν/2)^(2*d)`.
For `0 < ν ≤ 1` and positive dimension, the uniform retained fraction
`q = 1 - (ν/2)^(2*d)` lies strictly between zero and one.

The metric bridge realizes `ν_j` by the single thickness `(ν - ν_j) * lower'`.
An identification of that thickness with a sum of explicitly defined geometric
radii remains a separate statement; no such radius-ladder theorem is claimed.

## Conditional multiscale estimates and open analytic obligations

An explicit one-step energy hypothesis
`E_j ≤ K * (1 - ν_j^(2*d)) * E_(j+1)` for `j < n`, with nonnegative energies
through the terminal scale `n` and nonnegative `K`,
yields `E_0 ≤ (K*q)^n * E_n`, where `q = 1 - (ν/2)^(2*d)`.
Actual decay additionally requires `K*q < 1` and an upper bound for the final
energy. Ordered operator products use `List.prod`, so this bridge does not
assume that operators at different scales commute.

The remaining analytic obligations for Knutsen's FUP are the Gaussian
STFT/Bargmann construction, Fock-space subaveraging, the connection from
Euclidean porous sets to one-step sampling/energy loss, and lattice-cell
estimates. The finite Weyl example and the recurrence do not discharge these
obligations. A conditional multiscale theorem will retain its energy or norm
estimate assumptions explicitly.

## Verification and publication

The maintained source-closure checker reads the exact canonical files under
`lean/` and checks the unchanged toolchain and Mathlib revision through the
repository build lock. Production umbrellas import mathematical owners; audit
enumeration is run as a separate verification command. It supplies no acceptance claim for unrelated root dependencies.
Independent source review and independent native QA are separate roles.
All new owner declarations, including private/generated declarations, are
subject to transitive axiom inspection with only `propext`, `Classical.choice`,
and `Quot.sound` permitted. Actual root publication hooks keep their own
coverage and result.

## Actual dependency order

- Existing polarized Peirce defects and their C-star consequences feed
  projection localization and range-corner compatibility.
- Existing Kraus sums and native rectangular matrix multiplication feed
  finite multipliers and Gram identities; existing Jones generators then
  instantiate the finite Weyl masks.
- The real recurrence yields the uniform retained fraction and the conditional
  energy iteration. Native metric thickening and the recurrence bounds yield
  the single-thickening porosity theorem.

There is no theorem edge from the numerical recurrence to the finite Weyl
example, or from the finite mask to Euclidean geometric porosity.

## Paper correspondence

| Formal content | Exact relationship to arXiv:2204.03068v1 |
| --- | --- |
| Projection complement, leakage, and commutator identities | Abstract algebra motivated by separate localization; equation (1.1) is a stronger analytic norm estimate. |
| Isometry and range-corner identities | Abstract algebra underlying section 2.1. The specific Bargmann identification also includes the reflected symbol `S(conj z)`, which is not constructed here. |
| Real geometric-loss recurrence | Equation (3.9), page 10, and the geometric-radius choice and uniform half bound, page 11. The closed interval endpoints extend the arithmetic statement. |
| Finite Gram and multiplier identities | General finite frame algebra; not Lemma 5.2's Fock sampling formula. |
| Four Weyl masks | A separate concrete matrix example, with no claimed Cantor or Euclidean porosity identification. |

Theorem 5.1 additionally requires the paper's lattice condition (H), and the
Gaussian sampling estimates. Those hypotheses are not discharged by this change.
