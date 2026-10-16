# Ground-Truth Contract: Jordan--Wigner / Markov Metriplectic Bridge

## Mathematical claim after rhetoric removal

For each positive Clifford tower stage `k + 1`, the real Jordan--Wigner
operators `U := jw_u_new k` and `V := jw_v_new k` satisfy the existing CAR.
Consequently `M := U - V` is a nonzero transpose-skew matrix with `M * M = -1`.
For a symmetric finite score kernel on the same finite index carrier, the
existing softmax stationary weight `π` is positive and detailed-balanced. The
existing weighted skew construction transforms `M` to the coefficient matrix
`Mᵢⱼ / πᵢ`; its left action on the full matrix algebra is skew for the
stationary-weighted Frobenius pairing. The existing finite Markov group inverse
then recovers the projected dissipative force, and the instantaneous pairing
with the constant energy force vanishes.

## Carrier and conventions

- Clifford representation: `MatStage (k + 1) = Matrix (Idx (k + 1)) (Idx (k + 1)) ℝ`.
- Markov rows/columns use that same `Idx (k + 1)` carrier. This is a finite
  kernel over representation indices; no identification with token positions
  is asserted.
- Reversible seed: `M = jw_u_new k - jw_v_new k`, an odd-generator difference
  / Majorana-type matrix. It is not called a bivector.
- The weighted reversible action is the established row-scaled transform
  `weightedSkewActionMatrix π M`; the raw `M` is not claimed skew for arbitrary
  nonuniform `π`.
- The dissipative operator remains left multiplication by `1 - P` and the
  group inverse is only the group inverse of `1 - P`.

## Existing owner results used

- `InfoGeometry.Clifford.JordanWignerCAR.jw_u_new_sq`
- `InfoGeometry.Clifford.JordanWignerCAR.jw_v_new_sq`
- `InfoGeometry.Clifford.JordanWignerCAR.jw_uv_anticomm_new`
- `InfoGeometry.QuantumContext.MarkovDrazin.ReversibleRotation.weightedSkewActionMatrix_weighted_skew`
- `InfoGeometry.QuantumContext.MarkovDrazin.ReversibleRotation.symmetricSoftmax_weightedSkewAction_energy_balance`
- `InfoGeometry.QuantumContext.MarkovDrazin.ReversibleRotation.exists_symmetricSoftmax_groupInverse_projection_and_weightedSkewAction_balance`
- `InfoGeometry.QuantumContext.markovRangeIdempotent`

The first three give the CAR input; the following results provide the
weighted finite Markov and group-inverse outputs. The new module proves the
missing exact transpose transport for these `jw_u_new`/`jw_v_new` operators.

## Consumer-minimal missing delta

1. Prove transpose swaps the actual Jordan--Wigner creation/annihilation
   matrices at the appended site.
2. Derive skewness, square `-1`, and nonzero-ness of their difference.
3. Instantiate the existing weighted symmetric-softmax group-inverse and
   energy-balance results with that Clifford seed, on the full matrix carrier.

## Claims not established by this contract

- The raw Majorana matrix is not proved skew for a nonuniform stationary
  weight; the action uses the repository's explicit weighted rescaling.
- No unitary flow, trajectory conservation, semigroup convergence, or
  oversmoothing theorem is asserted.
- No theorem identifies tower basis indices with Transformer token positions.
- This does not claim that a group inverse is itself a reversible generator.
- It does not add a projective-module `K₀` theorem; the existing Markov
  Grothendieck bridge is an additive ring-element class statement.
