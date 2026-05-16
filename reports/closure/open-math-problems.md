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

## D21: Clifford Wavelet Analytic Bridge

Socket:
`InfoGeometry.Canonical.PrimeCliffordWaveletXiLimit.locallyUniformRenormalizedLimit`

Current scaffold:
`InfoGeometry.Wavelet.PrimeWaveletMRA.WaveletMRACompletionWitness`

Premises:
- A real Clifford algebra `Cl(V,Q)` with a blade `B` satisfying `B^2 = -1`.
- A Clifford wavelet `psi` satisfying Hitzer admissibility.
- A Clifford wavelet transform `W_psi` and reconstruction operator `R_psi`.
- `SIM(n)`-based dilation/translation/rotation covariance.
- A reproducing kernel for the coefficient space.

Known owner:
Eckhard Hitzer, *Clifford (Geometric) Algebra Wavelet Transform*, arXiv:1306.1620.

To prove:
Own the Clifford-wavelet admissibility, reconstruction/inversion, covariance, and reproducing-kernel machinery. Do not claim the prime-gas identification, locally uniform convergence to `xi ∘ CayleyInv`, or RH.

Downstream unlock:
`PrimeHurwitzCliffordCascadeLimit.PrimeHurwitzCliffordCascadeRealization`,
`PrimeLeeYangToHurwitzWitness.toCorrectHurwitzZeroTransferWitness`,
`PrimeHurwitzLimit.RH_from_Correct_Hurwitz_LeeYang`.

Risk:
Formalization route, not proof.

Not owned:
- Identification of the prime Lee-Yang approximants with wavelet partial sums.
- Local uniform convergence to `xi ∘ CayleyInv`.
- RH.

## D24: Prime Hurwitz-Clifford Cascade Limit

Socket:
`InfoGeometry.Canonical.PrimeHurwitzCliffordCascadeLimit.PrimeHurwitzCliffordCascadeRealization.locallyUniformRenormalizedLimit`

Premises:
- Finite prime Lee-Yang approximants `Z_N`.
- Nonvanishing renormalization `R_N`.
- Discrete Hurwitz-Clifford paraunitary filter bank.
- Cascade partial sums `W_N`.
- Equality `W_N = R_N Z_N`.
- Compact-uniform tail estimate.
- Reconstruction equals `xi ∘ CayleyInv`.

Known owner:
None. This is the prime-specific discrete cascade convergence socket.

To prove:
`R_N(z) Z_N` converges locally uniformly on compact subsets to
`xi(z / (1 + z))` after realization as a discrete Hurwitz-Clifford cascade.
Do not claim this is already proved by the discrete wavelet literature.

Downstream unlock:
`PrimeLeeYangToHurwitzWitness.toCorrectHurwitzZeroTransferWitness`,
`PrimeHurwitzLimit.RH_from_Correct_Hurwitz_LeeYang`.

Risk:
RH-level open analytic problem.

Not owned:
- Lee-Yang stability of prime partition polynomials.
- Hurwitz zero transfer.
- RH.

## D27: Heisenberg-to-Mertens Gate Scaffold

Socket:
`InfoGeometry.Canonical.PrimeCliffordHeisenbergGate.HeisenbergMertensGate.vacuousTarget`

Premises:
- Clifford/Majorana vacuum readout with a Heisenberg lower bound.
- Explicit dispersion-to-Mertens bridge field.
- Heisenberg saturation witness.
- The gate theorem is intentionally vacuous and proves only `True`.

Known owner:
None. This is a witness scaffold, not a proof-bearing theorem.

To prove:
`CliffordLDPBridge.dispersion_scaling` as an actual analytic statement.
Do not claim Heisenberg saturation alone proves a Mertens bound.

Risk:
Witness scaffold, not proof.

Not owned:
- Mertens `O(x^(1/2+ε))`
- Heisenberg saturation implies RH
- Any stronger claim than the vacuous gate theorem

## D26: Prime Cl(1,1) CPT Wavelet Packet

Socket:
`InfoGeometry.Canonical.PrimeCl11ModularAtom.LaplaceMellinWaveletTransform.cpt_preservation`

Premises:
- A local `Cl(1,1)` atom with `c^2 = 1`, `d^2 = -1`, and anticommutation.
- Finite Lee-Yang approximants.
- The reciprocal inversion map `z ↦ z⁻¹`.
- Paraunitary boundedness witness.

Known owner:
None. This is the prime-local CPT-preserving Laplace--Mellin wavelet packet.

To prove:
CPT preservation of the finite prime wavelet packet at the level of Lee--Yang
zero sets. Do not claim prime-to-`xi` convergence, Hurwitz zero transfer, or RH.

Downstream unlock:
`PrimeLaplaceMellinHurwitzWaveletLimit.PrimeHurwitzWaveletXiRealization`,
`PrimeHurwitzCliffordCascadeLimit.PrimeHurwitzCliffordCascadeRealization`.

Risk:
Formalization route, not proof.

Not owned:
- prime-to-`xi` convergence
- Hurwitz zero transfer
- RH

## D25: Prime Laplace-Mellin Hurwitz-Wavelet Limit

Socket:
`InfoGeometry.Canonical.PrimeLaplaceMellinHurwitzWaveletLimit.PrimeHurwitzWaveletXiRealization.locallyUniformRenormalizedLimit`

Premises:
- Finite prime Lee-Yang approximants `Z_N`.
- Nonvanishing renormalization `R_N`.
- Discrete Hurwitz-Clifford cascade.
- Laplace-Mellin scale-shape packet.
- Finite wavelet partial reconstructions `W_N`.
- Equality `W_N = R_N Z_N`.
- Compact-uniform tail estimate.
- Reconstruction equals `xi ∘ CayleyInv`.

Known owner:
None. This is the prime-specific Laplace--Mellin / Hurwitz--Clifford
wavelet realization socket.

To prove:
`R_N(z) Z_N` converges locally uniformly on compact subsets to
`xi(z / (1 + z))` after being realized as a Laplace--Mellin /
Hurwitz--Clifford wavelet cascade. This is the exact analytic socket, not a
proof of RH.

Downstream unlock:
`PrimeLeeYangToHurwitzWitness.toCorrectHurwitzZeroTransferWitness`,
`PrimeHurwitzLimit.RH_from_Correct_Hurwitz_LeeYang`.

Risk:
RH-level open analytic problem.

Not owned:
- Lee-Yang stability of prime partition polynomials.
- Hurwitz zero transfer.
- RH.
