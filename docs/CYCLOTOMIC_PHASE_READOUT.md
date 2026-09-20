# Cyclotomic phases versus spectral projectors

`Algebra/CyclotomicPhaseReadout.lean` uses Mathlib's primitive-root theorem for
`exp(2*pi*I/n)`. The root order, nontriviality, geometric-sum cancellation and
triangular identity contain no assumed exponential nonvanishing claim.

The dependency order is:

```text
positive order -> primitive root -> root order and nontriviality -> zero phase sum
primitive cubic root -> triangular polynomial identity
order-four operator -> existing Fourier projector -> projector range = eigenspace
```

The scalar `zeta^k/n` is only a weight. The module proves that the proposed
weight at `n = 3, k = 0` is not idempotent. Actual operator projectors are reused
from `FourthRootSpectralProjectors.lean`, which already proves idempotence,
orthogonality, completeness and spectral reconstruction. The new range theorem
identifies these concrete Fourier-polynomial projectors with native Mathlib
eigenspaces. The identity-operator test has an empty imaginary-root sector:
cyclicity alone does not give equally sized or nonzero copies.

No minimal-ideal classification, real-Clifford pseudoscalar/complex-scalar
identification, nuclear shape selection, spontaneous chiral symmetry breaking,
WZW integral reduction, or QCD vacuum theorem is asserted. Those require
separate structures and hypotheses. In particular, a scalar imaginary unit
cannot silently replace the real spacetime pseudoscalar when multiplying odd
Clifford elements. Nilpotent ladder operators are not idempotent projectors.

Tests and axiom commands are in `Algebra/CyclotomicPhaseReadoutTests.lean`.
Kernel checking remains pending while the existing global build holds the lock:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Algebra.CyclotomicPhaseReadoutTests
```
