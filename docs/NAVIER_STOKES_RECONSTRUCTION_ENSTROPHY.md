# Exact two-state reconstruction and enstrophy divergence

This extension supplies an explicit spatial momentum reconstruction, a
pointwise forced Navier–Stokes equation, and a divergent regional enstrophy.
It also exhibits the singular forcing that prevents this example from
establishing a smooth-forcing global breakdown alternative.

## The actual two-state fields

Write `r=x₀`, `y=x₁`, and `d=T-t`, with momentum-to-velocity factor one. In the
native complex Euclidean two-component space, set

\[
\psi(y)=(1,e^{iy}),\qquad
\phi(d,r,y)=(d-r,r e^{iy}).
\]

`TwoStateMomentumShear` proves joint smoothness of the postselection and
smoothness of the preparation, including at `d=0`. It computes the actual
derivative and its momentum readout:

\[
-i\partial_y\psi=(0,e^{iy}),\quad
\langle\phi,\psi\rangle=d,\quad
\langle\phi,-i\partial_y\psi\rangle=r.
\]

The other two spatial derivatives of the preparation vanish. Hence the
three-dimensional reconstructed velocity, on `t≠T`, is exactly

\[
u(t,x)=\operatorname{Re}\frac{\langle\phi,-i\nabla\psi\rangle}
                                  {\langle\phi,\psi\rangle}
      =\left(0,\frac{x_0}{T-t},0\right).
\]

`TwoStateNavierStokesReconstruction.spatialMomentum` uses native `deriv`
along each coordinate line. `reconstructed_eq_velocity` proves the equality
with the independently differentiated shear. The finite matrix `diag(0,1)`
agrees with this momentum on the specified preparation family, which connects
the calculation to the existing `SarsModularWeakValue.weakValue?` guard.
`regular_readout` returns the proved quotient for `t≠T`;
`readout_guard_at_terminal_time` returns `none` at `T`.

Lean's field division is totalized. Its artificial value at zero denominator
is excluded by that guard and plays no role in the punctured limit. On the
open unit cube, both states are nonzero even at `T`, as proved by
`terminal_states_ne_zero`. No wave equation or Krein-unitary evolution is
imposed on these two fields.

## The differentiated fluid equation

`NavierStokesShearReconstruction` defines coordinate divergence, curl,
advection, and Laplacian from native derivatives. `coordDeriv_eq_fderiv`
identifies a coordinate derivative with native `fderiv` on its basis vector
whenever the scalar field is differentiable. The predicate `SatisfiesAt`
expresses the pointwise component equation and divergence zero; it does not
by itself certify smoothness or global solution conditions.

For every shear `u=(0,a(t,x₀),0)`, its proved reduction is

\[
\operatorname{div}u=0,\quad (u\cdot\nabla)u=0,\quad
\operatorname{curl}u=(0,0,a_x),\quad
\partial_tu=\nu\Delta u+f
\iff a_t=\nu a_{xx}+f_1,
\]

where pressure is zero and the force is a shear in the same direction.
For the explicit reconstructed profile, native derivative lemmas yield

\[
\Delta u=0,\qquad
f(t,x)=\left(0,\frac{x_0}{(T-t)^2},0\right).
\]

`reconstructed_satisfiesAt` proves the equation for every real viscosity and
every `t≠T`; positive viscosity is therefore included. The formula for the
force is part of the construction, not an independently prescribed regular
force. `forcing_component_tendsto_atTop` proves its divergence at a fixed point.

## Enstrophy with a genuine integral

`ReciprocalShearFlow.vorticitySq_eq_norm_sq` identifies the Cartesian sum
of squares with the native Euclidean norm squared. Enstrophy is the
nonnegative Lebesgue integral in `ℝ≥0∞`, so a divergent integral is `∞`.
For `Q=(0,1)³`, its actual Lebesgue volume is proved to be one, and

\[
\omega(t,x)=\left(0,0,(T-t)^{-1}\right),\qquad
\mathcal E_Q(t)=\int_Q|\omega|^2\,dx=(T-t)^{-2}
\longrightarrow+\infty\quad(t\uparrow T).
\]

The terminal theorem is
`TwoStateNavierStokesReconstruction.reconstructed_cube_enstrophy_tendsto_top`.
This is an integral of the curl of the reconstructed velocity, rather than a
renamed postselection barrier.

`EnstrophyDivergence` also supplies reusable sufficient conditions:

- A squared-vorticity lower bound by an unbounded uniform square on a fixed
  unit-measure region implies temporal enstrophy divergence.
- The local power-density integral on `(0,a)` is finite exactly when `s>-1`.
  A squared-vorticity lower bound by `x^s`, with `s≤-1`, forces divergence.
- The reciprocal-shear density `(-1/x²)²=x⁻⁴` has infinite integral near zero;
  Tonelli transfers this to product domains with nonzero transverse measure.

These are lower-bound arguments. A vanishing overlap, a divergent upper
gradient bound, or pointwise growth without spatial measure control would
not suffice.

## Scope relative to the external development

The source-inspected [external Comparator definitions](https://github.com/openai/NavierStokesAndEuler/blob/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538/NavierStokes/ComparatorDefinitions.lean)
use native Fréchet derivatives, trace divergence and the Euclidean Laplacian,
with additional smoothness, initial-data, forcing and energy/periodicity
requirements. This extension does not import or instantiate that solution
predicate. Its Lean toolchain differs from the owned repository's pin.

The present force is singular at `T`; the velocity grows at spatial infinity.
The construction therefore does not prove the external smooth-forcing
breakdown statement, identify its mechanism, or solve the unforced Millennium
problem. General spinor evolution projecting to prescribed Navier–Stokes
data, continuation estimates, and the proposed Andreev/self-healing evolution
remain separate proof obligations. The earlier distinction between diagonal
Krein isotropy and vanishing transition overlap still applies.

All five new modules and their 64 theorem declarations are included in the
maintained PR-wide native Lean and axiom audit. The PR records the exact
compiler version and the remaining declared-toolchain validation gate.
