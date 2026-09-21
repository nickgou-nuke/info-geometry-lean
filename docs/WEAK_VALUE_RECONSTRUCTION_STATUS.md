# Weak-value reconstruction: source scope and verification

This extension is on PR #172, branch
`codex/quantum-spin-navier-stokes-slice`. The proof terms are implementation
candidates pending the pinned Lean kernel check. No successful build is claimed.

## Mathematical content of the new sources

### Spatial reconstruction

`WeakValueSpatialReconstruction.lean` connects the existing guarded complex
operator weak ratio to a real current and nonnegative overlap weight:

\[
\operatorname{Re}(N/D)
=\frac{\operatorname{Re}N\operatorname{Re}D+
\operatorname{Im}N\operatorname{Im}D}{|D|^2}.
\]

The denominator is not assumed real or positive. Its squared norm is the
positive weight on the regular domain. Coordinate partials are actual Mathlib
derivatives. The quotient rule derives the precise incompressibility condition

\[
\rho\,\nabla\cdot j=j\cdot\nabla\rho.
\]

The module defines time derivatives, advection, pressure gradient, Laplacian,
and a forced NS residual. Its solution predicate includes time differentiability
and spatial regularity; it is not the older skew-adjoint linear closure residual.
Mass continuity transports from a current equation through the exact identity
`rho * reconstruct j rho = j` on the nonzero-density domain.

### Actual enstrophy

`WeakValueEnstrophy.lean` defines the integral of the sum of squared curl
components. It does not identify this integral with a scalar velocity square
or with the integral of the full gradient without boundary hypotheses.

For a spatially uniform overlap `d(t)`:

\[
\omega[j/d]=\omega[j]/d,\qquad
\mathcal E[j/d]=\mathcal E[j]/d^2.
\]

An integrable current with strictly positive enstrophy and `d(t)=T-t` gives
`Tendsto ... (nhdsWithin T (Iio T)) atTop`, not merely arbitrarily large values
somewhere before T. A second theorem uses an almost-everywhere spatial lower
bound with positive integrated coefficient. Integrability is explicit, avoiding
the totalized Bochner integral's zero value for nonintegrable functions.

### Explicit reconstructed forced solution

`WeakValueForcedShear.lean` supplies the manufactured solution

\[
u=(0,x_0/(T-t),0),\quad p=0,\quad
f=(0,x_0/(T-t)^2,0).
\]

It calculates the derivatives, incompressibility, vanishing advection and
Laplacian, and forced NS equation for all viscosities on `t<T`. Its velocity
component is reconstructed from the existing Pauli probe, pre-state `ket0`, and
post-state `(T-t,x_0)`. That post-state is continuous through T; the guarded
weak readout returns `none` there.

Important restrictions: the forcing is singular at T; the field is not periodic
and is not globally finite-energy on R^3. Therefore this example is not the
OpenAI admissible-forcing construction or an unforced regularity result. The
positive-enstrophy probability-measure example in the regression module is a
finite-window/normalized-measure test, not a periodic identification of shear.
The affine Pauli example and the eta-postselected null-mode theorem are separate
models; no common-state identification is asserted between them.

### Krein seam and doubled-space dynamics

`KreinSeamEvolution.lean` proves the conditional identification by deriving
`transitionAmplitude (eta psi) psi = kreinQuadratic eta psi`. Arbitrary
independent post-selection is not identified with the Krein quadratic form.
A quadratic-form-preserving evolution cannot change a globally nonnull state
into a null one; local transition amplitudes require a separate field model.

On the existing `DoubledSpace E` and `complex_i`, the source derives the actual
chain-rule identity for a trajectory satisfying

\[
\dot\Psi=\omega I\nabla F-D\nabla F,\qquad
\frac{dF}{dt}=-\langle\nabla F,D\nabla F\rangle\le0.
\]

This is open-system Hamiltonian-plus-gradient free-energy descent, not a
closed-system GENERIC energy-conservation theorem or a constructed global
trajectory. At the Onsager kernel the trajectory derivative is purely rotational.
An implicit-midpoint rotational step preserves the Hilbert quadratic norm.

The homogeneous pair `(n,d)` also has the alternative operator readout

\[
R(n,d)=\frac{d^2-n^2}{d^2+n^2}\,1+
\frac{2dn}{d^2+n^2}\,I.
\]

The source proves quadratic-norm preservation, continuity away from `(0,0)`,
and `R(n,0)=-1` for nonzero n. This is a regular rotor coordinate across the
pole of `n/d`; it does not make the original quotient finite or prove that NS
dynamics selects this readout. Exact local opposite-principal-part cancellation
also gives a continuous combined readout. Opposite residues at different points
alone would not imply that cancellation.

### Finite-to-colimit compatibility

`WeakValueCylinderTransport.lean` uses the existing `diagEmbedSucc`, `cylinder`,
and `CylinderColimit` owners. Guarded readouts commute with the embeddings;
regularity and zero-overlap fibers are preserved. Adding a bit or passing to
this algebraic cylinder carrier does not itself remove a pole. The analytic
enstrophy layer above is conditional on a supplied spatial measure and is not
an asserted identification of this colimit with physical spacetime.

## Remaining closure obligations

1. A single state dynamics connecting eta post-selection, spatial current,
   admissible NS forcing, and the proposed rotor/phase-conjugate continuation.
2. Global existence, regularity, and appropriate finite-energy/periodic boundary
   estimates for that model, including pressure/Leray compatibility.
3. Spatial coercivity deriving the enstrophy lower-bound hypothesis from that
   state dynamics, rather than a chosen uniform-denominator profile.
4. A dynamical Andreev scattering law and a proof that it selects a regular
   reconstruction; conservation of reflection probabilities alone is insufficient.
5. An explicit analytic realization of the categorical colimit and proof that
   the required differential, energy, and measure structures transport to it.
6. The connection from split-octonion/para-hyperkahler geometry to these specific
   operators and dynamics. Existing algebraic identities are not replaced by
   physical rhetoric or a new assumed theorem.

## Verification

Static checks cover imports, whitespace, and absence of new proof-debt markers.
`WeakValueReconstructionChecks.lean` contains regression proofs for cancelling
ratios, purely imaginary weak poles, zero-curl constant velocities, actual shear
enstrophy, and guarded zero-overlap readouts.

Run one sequential, locked build from the repository root on the PR branch:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.WeakValueReconstructionChecks
```

No toolchain, manifest, external submodule, or CI workflow changes are included.
The working environment has no Lean/Lake executable. Earlier PR CI was blocked
before target compilation by missing Lake/pytest, missing pinned Mathlib/Atlas
dependencies, a sandbox preflight failure, case-collision checks, and Pages setup.
Successful typechecking and imported-axiom inspection remain required before
marking the PR ready for review.
