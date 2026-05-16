# Open Mathematical Problems

Generated: 2026-05-16

This file lists only sockets that are not closed by current Lean code, mathlib, or a direct repository theorem.

## D14: Multivariate Lee-Yang Stability

Socket:
`InfoGeometry.Canonical.PrimePartitionPolynomials.LeeYangPolydiscWitness.inner_zero_free`
and
`InfoGeometry.Canonical.PrimePartitionPolynomials.LeeYangPolydiscWitness.outer_zero_free`

Premises:
- `N` finite.
- `D : FinitePrimeChainData N`.
- `lambda > 0`.
- Couplings are ferromagnetic.
- `D.multiPartition lambda y` is the finite multi-affine local fugacity partition function.

Known owner:
Lee-Yang circle theorem, Asano contraction, Ruelle stable-polynomial machinery.
Not currently formalized in this repo or mathlib.

To prove:
If `forall i, Complex.abs (y i) < 1`, then `D.multiPartition lambda y != 0`.
If `forall i, 1 < Complex.abs (y i)`, then `D.multiPartition lambda y != 0`.

Downstream unlock:
`zero_implies_field_re_zero`, `zero_implies_critical_line`.

Risk:
Formalizable literature, not RH-equivalent by itself.

## D16: Hurwitz Zero-Free Domain Transfer

Socket:
`InfoGeometry.Canonical.PrimeHurwitzLimit.ZeroFreeDomainTransfer`

Premises:
- `F_N -> F` locally uniformly on compact subsets of each connected zero-free component.
- Each `F_N` is zero-free on the component.
- `F` is not identically zero on that component.

Known owner:
Hurwitz theorem.  Exact mathlib availability must be checked before replacing the witness.

To prove:
The limit is zero-free in `{z | Complex.abs z < 1}` and `{z | 1 < Complex.abs z}`; therefore every zero of the limit lies on the unit circle.

Downstream unlock:
`CorrectHurwitzZeroTransferWitness` can stop carrying zero-free transfer as a field.

Risk:
Likely formalizable, but not yet closed in this repository.

## D17: Prime Lee-Yang Convergence to Completed Xi

Socket:
`InfoGeometry.Canonical.PrimeLeeYangConvergence.PrimeLeeYangConvergenceSocket`

Premises:
- Finite Lee-Yang-stable prime approximants `Z_N`.
- Nonvanishing renormalizations `R_N`.
- Cayley inverse `s = z / (1 + z)`.
- Completed xi zero predicate.

Known owner:
None.

To prove:
`R_N(z) Z_N(z)` converges locally uniformly on compact subsets of the Cayley chart to `xi (z / (1 + z))`, with the needed zero-equivalence between `xi` and the limiting function.

Downstream unlock:
`HurwitzZeroTransferWitness.xiZeros_map_to_unit_circle`,
`RH_of_Hurwitz_LeeYang_limit`,
`RH_from_Correct_Hurwitz_LeeYang`.

Risk:
RH-level open analytic problem.

## D18: MBK Relative Pfaffian / Trace Identity

Socket:
`InfoGeometry.Canonical.PrimeMBKSelfAdjointTrace.MBKRelativeTraceXiSocket`

Premises:
- Berry-Keating dilation operator.
- Finite Majorana Fock couplings.
- Infinite-volume self-adjoint or Krein-self-adjoint extension.
- Well-defined relative trace/scattering determinant.

Known owner:
None.

To prove:
Construct the operator and prove the relative Mellin heat trace or relative Pfaffian/determinant identity equals the logarithmic derivative or completed xi factor.

Downstream unlock:
Operator-theoretic Hilbert-Polya corridor.

Risk:
Open program.

## D20: Mertens/LDP Boundary

Socket:
`InfoGeometry.Canonical.PrimeMertensDefectBoundary.MertensLDPBoundary`

Premises:
- `D : MobiusMertensData`.
- Large-deviation speed and rate function.
- Defect observable.
- Entropy barrier dominates parity defect cost.

Known owner:
None for the LDP implication as a proved repository theorem.  Latorre-Sierra is background for the Mobius state/RH-scale boundary, not a closure proof.

To prove:
For every `epsilon > 0`, eventually `|M(N)| <= C_epsilon * N^(1/2 + epsilon)`.

Downstream unlock:
`MertensBoundaryPacket.ofLDP` gains a constructive analytic owner.

Risk:
RH-scale open boundary.

## D21: Clifford-Wavelet MRA Completion

Socket:
`InfoGeometry.Wavelet.PrimeWaveletMRA.WaveletMRACompletionWitness`

Premises:
- Nested prime resolution bands.
- Nonvanishing scaling filter.
- Wavelet-completed limit.
- Zero-equivalence with completed xi.

Known owner:
Hitzer-style Clifford/geometric algebra wavelet transform is a candidate literature route for the transform/reconstruction substrate.  It does not prove the arithmetic xi convergence socket by itself.

To prove:
Turn Clifford MRA reconstruction into the locally uniform convergence and zero-equivalence required by D17.

Downstream unlock:
`toPrimeLeeYangConvergenceSocket`,
`RH_from_Wavelet_MRA`.

Risk:
Formalization route, not proof.

