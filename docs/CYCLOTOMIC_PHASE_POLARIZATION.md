# Finite cyclotomic phase polarization

`InfoGeometry.Algebra.CyclotomicPhasePolarization` reuses the exponential roots
from `Omega.Zeta.CyclotomicSectorIdentity` and Mathlib's `IsPrimitiveRoot`.
It supplies positive-order periodicity, nontrivial polygon balance, and the
degree-two identity for a primitive cube root.

Scalar phase weights are not spectral projections: the proposed weight at
order two and index zero is one half, whose square is not itself. The module
includes this counterexample rather than treating a name as an axiom.

The explicit finite model is the complex function algebra on `Fin order`.
Its coordinate indicators are mutually annihilating idempotents summing to
one. Multiplication by the coordinate phase has finite order and admits an
instance of the existing `FourierCyclotomicReadout` interface. That owner's
spectral reconstruction theorem supplies the reconstruction identity.

`CyclotomicPhaseDependencies` records a finite dependency partial order.
Polygon balance and projector construction are separate branches; the diagram
does not assert that vanishing scalar sums imply a physical symmetry breaking.
The tests also reuse the existing Peirce corner decomposition, its off-diagonal
nilpotence theorem, and the concrete complex Pauli ladder nilpotence lemmas.

## Scope

These are finite algebraic statements, not a construction of a continuum,
minimal Clifford ideals, a QCD vacuum, a WZW action, or nuclear energy minima.
The product-algebra example does not establish a Fourier resolution for every
operator. No identification of a real Clifford pseudoscalar with a commuting
complex scalar is assumed. No physical or psychological conclusions follow
from the dependency diagram.

## Verification

The source contains proof terms without placeholders. Kernel verification is
pending the repository's existing full build and shared build lock:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Algebra.CyclotomicPhasePolarizationTests
```
