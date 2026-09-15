# Harmonic means and common-scale readouts

## Two separate hypotheses

`EmergentGeometry/HarmonicMeanValue.lean` uses genuine Mathlib harmonicity
and its proved circular mean-value theorem. The new
`circleAverage_radius_invariant` compares circular averages at a common
center when the field is harmonic near both closed disks. It does not
postulate the mean-value identity as a field of a structure.

`Detector/CommonScaleReadout.lean` instead studies the explicitly specified
scalar model

\[
 S=c_1s,\qquad Q=c_2s^2,\qquad
 \frac{S}{\sqrt Q}=\frac{c_1}{\sqrt{c_2}}
 \quad(s>0,\ c_2\ge0).
\]

No harmonicity or integration occurs in this cancellation proof. The
inverse-square specialization uses `s = volume / (distance + offset)^2`,
with positive volume and nonzero separation. It is a model specialization,
not a derivation of the model from a detector geometry.

For a physical quotient with a nonzero denominator, require `c₂ > 0`.
The stated algebraic theorem also covers `c₂ = 0` because Lean's real
division is totalized with division by zero equal to zero. Regression tests
make this edge case explicit rather than interpreting it as an observation.
Other tests show that dropping positivity of the scale changes the result:
zero scale gives zero, and negative scale reverses the sign of the readout.

## Derivatives and dependency order

The composition of the readout with **any** positive scale function is
constant. `hasFDerivAt_readout_comp` proves its actual Fréchet derivative is
zero; `hasDerivAt_readout_path` specializes to a real time parameter. The
scale function itself need not be continuous or differentiable. In
particular, these are stronger statements than merely writing `deriv = 0`,
which by itself could also hold at nondifferentiable points in Lean.

The explicitly declared dependency poset is:

```text
harmonicMeanValue -> concentricMeans

quadraticScale -> rootFactorization -> quotientCancellation
                                      |-> inverseSquareModel
                                      |-> constantDerivative
```

This is a finite model of the chosen mathematical dependencies, not an
automatic reflection of all Lean proof terms or a logical independence
theorem. Its partial-order laws and the stated incomparabilities are proved.
The harmonic branch does not entail the common-scale model.

## Scope boundaries

The usual harmonic mean-value theorem is a theorem about balls and spheres,
not an identity for arbitrary bounded shapes at a designated geometric
center. The implemented theorem is specifically a circular average in the
complex plane. It asserts neither a three-dimensional cylinder-volume
integral nor a focal singularity. Its center is within the harmonic domain.

An arbitrary integration functional equipped with an assumption
`integrate domain field = volume * field center` would only give conditional
scalar cancellation; it would not prove a harmonic mean-value theorem.
For this reason the proposed `HarmonicDomain`/`SatisfiesMVP` proxy is not
introduced, and the genuine harmonic owner is not replaced with rational
functions named `harmonic_flux`.

No gauge group action, differential-form complex, de Rham class, detector
transport equation, angular-correlation law, or calibration intercept is
constructed here. A constant scalar readout alone does not establish any
of those identifications or make detector-response modeling unnecessary.

## Verification

The regression target `Detector/CommonScaleReadoutTests.lean` passed, with seven
examples and twelve axiom reports (only `propext`, `Classical.choice`, and
`Quot.sound`, with no additional axioms). Checks use Lean 4.28.0, the cached Mathlib
source revision `8f9d9cff6bd728b17a24e163c9402775d9e6a365`, and isolated
outputs under the shared build lock.

The repository pins Lean 4.28.1. That compiler is installed, but a separate
import probe fails with an incompatible `.olean` header in the existing
4.28.0 Mathlib cache. These checks are not a successful pinned-toolchain or
whole-repository build. No dependency pins or cached artifacts are changed.
