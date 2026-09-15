# Operator squares, Zorn readouts, and harmonic means

These are separate mathematical statements. No identification of measured
detector counts with a differential operator or a Zorn norm is assumed.

## Symmetric-operator factorization

`EmergentGeometry/HodgeDiracFactorization.lean` uses Mathlib's
`LinearMap.IsSymmetric`, rather than defining a new self-adjointness predicate.
For an everywhere-defined symmetric real linear operator on an inner-product
space, it proves

\[
 \langle D^2u,u\rangle=\|Du\|^2,\qquad
 \ker D^2=\ker D,\qquad
 \sqrt{\langle D^2u,u\rangle}=\|Du\|.
\]

The square-root readout scales by the **absolute value** of a real scalar.
It is not a linear amplitude or an inverse recovering a spinor. Regression
tests show loss of the sign even for the identity operator on the real line.
A nonsymmetric nilpotent operator on `ℝ × ℝ` gives a counterexample to removing
the symmetry hypothesis from the kernel statement.

This is an inner-product identity, not Stokes' theorem, Gauss–Bonnet, an index
theorem, or an integration-by-parts argument on a manifold. No differential
operator domain or boundary condition is modeled here. The repository's
existing `ChiralHodgeDiracKahlerBridge` separately uses the convention
`d - delta`, whose square has a minus sign; it is not silently replaced with
this symmetric-square construction.

## Zorn positive slice

`EmergentGeometry/ZornChiralPotential.lean` reuses the existing
`Algebra.ZornMatrix`, `Vec3.dot`, and `ZornMatrix.zornNorm` definitions. It
introduces only the particular embedding

\[
 (a,v)\longmapsto\begin{pmatrix}a&v\\-v&a\end{pmatrix},
 \qquad N=a^2+v\cdot v.
\]

The spatial contribution is **added**, not subtracted, on this slice. The
formal readout theorem is

\[
 \sqrt{N-v\cdot v}=|a|,
\]

with `a` recovered only when `0 ≤ a`. This requires knowing the spatial
contribution separately. The norm alone does not determine it or the vector:
the implementation proves non-injectivity using two distinct coordinate
directions. It also exhibits a negative Zorn norm outside the positive slice.
Consequently, a general Zorn norm cannot simply be declared a nonnegative
count observable. No angular-correlation model, Gribov obstruction, or
spectral-noise mechanism is derived from these formulas.

## Actual harmonic mean-value theorem

`EmergentGeometry/HarmonicMeanValue.lean` imports Mathlib's proved
`HarmonicOnNhd.circleAverage_eq`:

\[
 f\text{ harmonic near }\overline{B(c,|r|)}
 \quad\Longrightarrow\quad
 \operatorname{circleAverage}(f,c,r)=f(c).
\]

Here `f : ℂ → ℝ`; the domain is the plane. This is not the real-variable
derivative mean-value theorem used by `Canonical.MeanValueInvariant`.
The new lemmas derive circle integrability from harmonicity, recover the
center value from a specified constant boundary, transfer a boundary upper
bound to the center, and compare center values of two harmonic functions
ordered on the boundary.

A formal counterexample uses the constant function one: harmonicity alone
does **not** imply a zero center value. A zero value follows when zero
boundary data are actually supplied. No calibration intercept or detector
boundary condition is inferred from the mean-value property.

## Dependency organization

```text
symmetric operator -> square-energy identity -> nonnegativity
                     square-energy identity -> kernel equality
                     square-energy identity -> square-root norm readout
existing Zorn algebra -> positive slice -> sum-of-squares norm
                        sum-of-squares norm -> corrected scalar readout
native harmonicity -> circle integrability -> boundary comparison
native harmonic mean value + constant boundary -> center value
```

The kernel and square-root statements are separate consequences; neither
requires the other. The Zorn branch is independent of the harmonic-mean
branch. These mathematical dependencies provide no physical identification
between the branches.

## Validation targets

`HodgeZornFactorizationTests.lean` has six examples and twelve axiom audits.
`HarmonicMeanValueTests.lean` has three examples and six audits, including the
native Mathlib mean-value theorem. Both regression targets passed with Lean
4.28.0, cached Mathlib, isolated outputs, and the shared build lock. The
repository's pinned Lean 4.28.1 is now installed, but its import probe fails
on an incompatible header in the existing 4.28.0 Mathlib `.olean` cache.
This is not a pinned-toolchain or whole-repository build.

The additional concentric-circle theorem and the separate common-scale
algebraic model are documented in `COMMON_SCALE_READOUT.md`.
