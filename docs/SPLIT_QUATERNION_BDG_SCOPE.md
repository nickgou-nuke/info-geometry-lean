# Split-quaternion and BdG algebra: scope

`EmergentVacuum/ParahyperkahlerSpinBdG.lean` retains the requested file path,
but its declarations describe only the mathematical structures actually given.

- A `SplitQuaternionPair` contains two ring elements with squares `-1` and `1`
  which anticommute. Their product squares to `1`. It is not a manifold, metric,
  connection, or parahyperkahler integrability structure.
- The existing `Quantum.AnticommutingInvolutionCore` supplies an instance on
  native real-linear endomorphisms. The existing split-quaternion matrices are
  a concrete test instance, not a replacement for that owner layer.
- The existing `SuperMetriplectic.MetriplecticFlow` supplies the flow data.
  Dissipative equilibrium implies zero dissipative flow, zero entropy production,
  and equality of total and reversible flow. This does not assert convergence
  to equilibrium, a global minimum, a foliation, or unitary evolution.
- The existing `QuantumContext.MassAsCommutantCoupling` supplies cancellation of
  cross terms for anticommuting ring elements. When both squares are scalars,
  the square of their sum is their scalar sum. Positivity, self-adjointness,
  nonzero pairing, and a spectral gap do not follow from these assumptions.
  A zero-operator regression example records this boundary.

These are independent algebraic branches, not a proved causal chain from cooling
to spin structures, Majorana zero modes, braiding, or SU(N) gauge theory. No such
physical interpretation is installed as a theorem. See also
[YANG_MILLS_MASS_GAP_AUDIT.md](YANG_MILLS_MASS_GAP_AUDIT.md).

Kernel verification is pending the shared build lane:

```
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.EmergentVacuum.ParahyperkahlerSpinBdGTests
```
