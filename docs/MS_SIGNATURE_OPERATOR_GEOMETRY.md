# MS signature operator geometry

## Scope and acceptance

This is a new additive PR stacked on the checked finite-absorption PR #223,
head f9a5c6d5a7e5bc9d1ae6b6f0f3e8c77ff67a5d6e. Parent branches, main, prior
owners, dependency pins and umbrella imports are not modified. The new scoped
workflow must succeed before any kernel-verification claim applies. It compiles
the exact import closure against the repository pins and audits every declaration
owned by these seven modules with transitive axiom collection. It is not a root
package build, nor an inventory audit of all unused declarations in dependencies.

## Constructed dependency chain

- Strict fragmentation support gives transient K^N=0 through #223.
- The existing completion T has T^N=Pi. The new Drazin witnesses distinguish
  K^D=0, T^D=Pi, and the group inverse of 1-T. Exponents are bounds, not minimality.
- The centered sum Z=sum_(k<N)(T^k-Pi) satisfies (1-T)Z=Z(1-T)=1-Pi.
  The finite compatibility alternative is (1-T)x=b solvable iff Pi b=0.
- A specified linear readout produces the finite time/channel signature
  O_N x=(C K^t x)_(t<N). Its matrix Gram equals the existing finiteStein polynomial
  sum_(t<N) (K^transpose)^t C^transpose C K^t and uniquely solves
  W-K^transpose W K=C^transpose C when K^N=0.
- The native Euclidean realization explicitly transports transpose to adjoint
  and matrix Gram to the Hilbert-space Gram O*O. Kernel(O*O)=kernel(O).
- The native quotient E/kernel(O) is linearly equivalent to range(O).
  The finite Fredholm alternative and finite index balance are proved without
  asserting an infinite-dimensional Fredholm determinant or compactness theorem.
- Finite dimensionality supplies closed range, so the pre-existing Hilbert MP
  construction supplies O^+; no inverse-existence field is postulated.
  P=O^+ O is self-adjoint, idempotent, preserves signatures and detects exactly
  Gram-null directions. The Gram's MP inverse is also a Drazin witness at 1;
  no such claim is made for arbitrary nonnormal transition kernels.
- P determines doubled corners d=[[0,P],[0,0]], b=[[0,0],[P,0]]. Their actual MP
  laws allow reuse of PeirceWeylUnits for Phi3/Phi4/Phi6 active-corner equations
  and an ambient Weyl unit with fourth power one.
- The final synthesis instantiates all these maps on the same grammar/readout.
  Chemical identifiability transfers through equality of signature fibers; it
  remains a supplied separation statement about the chosen candidate encoding.

## Essential distinctions

The projected/doubled cyclotomic action is a constructed algebraic representation,
not a measured periodicity or a transformation that turns K into a root of unity.
A nilpotent cannot itself be a unit in a nontrivial ring. Polynomial constants
on the active corner are Delta, not ambient 1; Phi4's ambient residual is 1-Delta.
Fourth/sixth power laws are not claims of exact order in degenerate cases.
Gamma^2=Delta would be an involution law, not the polynomial Phi2(t)=t+1.

Autocorrelation Grams are positive; cross-Grams need not be positive, symmetric,
or invertible. The absorption projection can be oblique and is not automatically
the observable metric support. Time-resolved and aggregate readouts are different:
a concrete two-state example shows that aggregation loses a direction retained
by time-resolved observations. The source/candidate differences may be signed.

The chosen column-vector readout is C K^t x. Forward row-distribution propagation
would require a transpose convention. No physical detector model, chemical
relabeling theorem, normalization of raw spectral intensities, empirical
covariance estimator, calibration, learned predictor or statistical confidence
is supplied. Complete field and metric choices are explicit in the types.
The Fredholm statements here are finite compatibility/range-kernel results,
not analytic continuation, a Fredholm determinant or an infinite-dimensional
spectral identification. Numerical implementation/physical model error still
uses #221/#223's explicit evidence contracts.

## Verification

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.MassSpectrometry.SignatureOperatorAudit
```

The successful or failed exact revision and artifact are recorded in the PR.
No custom axiom, admitted proof, unsafe computation, native_decide or dependency
stripping is permitted for the new theorem verification.
