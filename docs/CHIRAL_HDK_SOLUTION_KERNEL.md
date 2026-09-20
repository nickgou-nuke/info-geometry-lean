# Chiral HDK solution-kernel bridge

`lean/InfoGeometry/Synthesis/ChiralSpinNetworkHDK.lean` connects existing
algebraic owners without introducing a `ChiralHDKNetwork` class.

## Reused owners

- `CliffordWeyl/ChiralIdeals.lean`: chiral projector commutation and corner laws.
- `OperatorAlgebra/ChiralProjectorFromInvolution.lean`: constructive complementary
  projectors from a squared-identity grading.
- `Synthesis/KleinDiracKahler.lean`: covariance of the first-order equation under
  an even difference operator and odd coefficient/phase.
- `Synthesis/CuntzKleinPropagation.lean`: associative first-to-second-order identity,
  with the anticommutation hypothesis explicit.
- Mathlib: `LinearMap.mulLeft`, `LinearMap.mulRight`, composition, and kernels.

## Mathematical dependency order

Define the real-linear residual `R(state) = D * state - M * state * B`.
Its kernel is exactly the first-order solution space.

The dependencies branch:

1. A real algebra automorphism fixing `D` and negating `M` and `B` commutes
   with `R`. If the automorphism is involutive, instantiate the existing
   `ChiralInvolution` on the endomorphism algebra. Its two derived projectors
   preserve the solution kernel, and membership is equivalent to membership
   of both projected components. No fixed-state hypothesis is needed.
2. Independently, `B * B = -1` and `D * M = -(M * D)` imply that the kernel
   of `R` is contained in the kernel of left multiplication by `D² - M²`.
   This uses the existing squaring theorem rather than repeating its proof.

The projectors in the first branch are the eigenspace projectors of the
specified automorphism on algebra-valued states. Identifying them with a
different physical chirality requires an additional intertwiner.

## Scope and verification

## Concrete Cuntz and Klein instance

`Synthesis/CuntzDoubledHopping.lean` inserts the existing branch difference
`d = S 0 - S 1` into the two off-diagonal Cuntz prefix corners:

```
D = S 0 * d * T 1 + S 1 * d * T 0
M = clock
B = phase = clock * shift
```

The readout `T 0 * D * S 1 = d` records the connection to the original
propagation owner. Cuntz orthogonality derives `D * M = -(M * D)` and
commutation of `D` with `shift`; these are not new assumed fields.
This doubled operator is not identified with the raw branch difference.

`Synthesis/CuntzKleinHDKInstance.lean` lifts the **actual** `torusGlide` to
operator-valued fields by

```
kappa(field)(point) = shift * field(torusGlide point) * shift.
```

This is a specified lift combining the existing base involution with Cuntz
fibre conjugation, not a claim that base pullback alone negates constant
operators. Its involutivity, even `D`, and odd `M`/`B` are derived.

`Topology/KleinPointwiseOperatorDescent.lean` uses the existing
`quotientOperator` and `fieldEquiv` owners to descend pointwise linear
operators to the literal Klein orbit quotient. The instantiated residual
descends through this API, and quotient solutions satisfy the derived
second-order equation. This uses ordinary base-invariant fields; it does
not identify them with all sections of a twisted associated bundle.
No new colimit is introduced: this addition implements the quotient route.

## Verification status

This does not construct a Penrose spin network, a Krein inner product, a
spectral triple, a Klein quotient, or a Standard Model representation.
Nor does it identify the Cuntz branch difference with an exterior derivative,
force a nonzero mass, or derive a positive spectral gap. Existing geometric
and colimit owners are not replaced by this algebraic kernel construction.

The test module includes a unit solution using the existing real boundary
clock, shift, and phase, plus second-order and zero-solution checks.
Lean compilation is pending: the shared build lock is held by the existing
`lake build -R` process. No concurrent verification was started.

After that build finishes, the narrow verification target is:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Synthesis.ChiralSpinNetworkHDKTests
```
