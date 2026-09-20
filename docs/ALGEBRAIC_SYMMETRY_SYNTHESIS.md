# Algebraic symmetry synthesis

This translates the proposed learning and rotating-shape analogies into three
independent mathematical branches, not a physical identification theorem.

## Owners and dependency order

- `Algebra/AnticommutingBalance.lean`: real algebra and anticommutation imply
  cancellation of mixed products for arbitrary real weights. Equal squares
  imply scalar factorization. Completing the scalar square gives the unique
  minimum at one half. Nonzero self-square implies nonzero balanced square.
- `Dynamics/CyclicRotatingProfile.lean`: a periodic profile remains periodic
  under a rotating-coordinate change, becomes stationary in its moving frame,
  and has a time derivative given by the chain rule. Harmonic profiles provide
  explicit n-fold symmetry and radius bounds. Primitive roots provide distinct
  finite phases, cyclic closure, and the cubic-root equation.
- `Physics/CrankingParity.lean`: two linear operators commuting with parity
  yield a cranked operator commuting with parity. Its action preserves parity
  eigenvectors. Common energy/angular-momentum eigenvectors have eigenvalue
  `energy - speed * spin` in the rotating-frame operator.

The test module realizes the branch order as inclusion of finite dependency
contexts. The balance and rotation branches are incomparable; this does not
assert that one physical phenomenon causes the other.

## Concrete checks

`Physics/AlgebraicSymmetrySynthesisTests.lean` reuses `Cl11Matrix` and
`Cl11ZornActionSeparation` for a nonzero balanced Pauli-matrix square. It also
exhibits a positive three-fold profile that is stationary in rotating
coordinates but changes at a fixed laboratory angle. It requests axiom reports
for all named theorems introduced here.

## Scope boundaries

Anticommutation is a hypothesis, not a consequence of a balance coordinate.
The scalar coefficient minimum is not automatically an operator-order minimum.
No loss function, learning convergence, heat, superconductivity, nuclear
Hamiltonian, oxygen collision, alpha-cluster ground state, or RH implication is
constructed. Primitive-root phases do not prove a decomposition of a nuclear
configuration space, and the two roots of `x^2 + x + 1` are not all three cube
roots of unity. The orbital cyclic construction includes the root 1 as well.

Parity preservation is conditional on commutation with both input operators;
no physical parity assumption is silently inserted. Rotation and a nonzero
time derivative in laboratory coordinates are compatible with a stationary
shape in a rotating frame. No colimit or completion is claimed by these files.

## Verification

Run sequentially after the shared build lock is available:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Physics.AlgebraicSymmetrySynthesisTests
```

At authoring time the existing `lake build -R` held the shared lock. Kernel
verification and actual axiom-report inspection are pending; source proof
scripts alone are not a compilation certificate.
