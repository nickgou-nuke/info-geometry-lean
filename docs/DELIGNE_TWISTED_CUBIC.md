# Deligne's concrete projective example

Owner: `lean/InfoGeometry/HodgeCohomology/TwistedCubic.lean`.
Tests: `lean/InfoGeometry/HodgeCohomology/TwistedCubicTests.lean`.

The transcript's garbled projective coordinates are interpreted as the standard
twisted cubic `[u^3 : u^2 v : u v^2 : v^3]`. The code proves this particular
example directly, independently of the transcription.

## Formal dependency order

1. Native `MvPolynomial` quadrics are homogeneous of degree two.
2. Their evaluations characterize the three quadratic equations defining the cone.
3. The cubic parametrization satisfies those equations and is nonzero for a
   nonzero parameter pair. Scaling parameters scales coordinates cubically.
4. The equations are invariant under nonzero scalar multiplication.
5. The zero and nonzero first-coordinate cases give explicit parametrizations.
6. Native `Projectivization.mk` identifies proportional representatives, yielding
   an if-and-only-if projective parametrization theorem.
7. The first two quadrics cut out, set-theoretically, the curve union the line
   `x0 = x1 = 0`. A nonzero rational point on that line fails the third equation.

All statements hold over any field unless a test explicitly specializes to
the rational or complex numbers. This is a statement about points and
homogeneous equations, not a scheme-theoretic multiplicity computation.

## Connection to the existing Hodge owners

`RationalCycleSpan.lean` already supplies rational span, linear-constraint and
surjectivity criteria. `FiniteHarmonicRepresentative.lean` supplies finite
closed/coclosed representative results. Neither constructs a Betti cycle-class
map for arbitrary smooth complex projective varieties.

The new example supplies actual polynomial geometry rather than an assumed
cycle index. It does not yet map its curve into the cohomology of an ambient
variety. That requires a geometric homology/cohomology comparison and an actual
cycle-class construction. No Hodge decomposition, smooth-projective comparison
theorem, general algebraicity assertion, motivic projector, or Hodge-conjecture
proof is added or assumed here.

## Verification status

Source proof scripts and axiom-report commands are provided without `sorry`,
`admit`, or added axioms. At implementation time another `lake build -R` held
the shared build lock, so compilation and axiom-report inspection are pending.

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.HodgeCohomology.TwistedCubicTests
```
