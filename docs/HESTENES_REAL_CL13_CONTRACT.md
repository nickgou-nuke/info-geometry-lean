# Real spacetime spinors: theorem contract

Intake: `docs/sources/hestenes-real-cl13-intake-2026-11-17.txt`, 15,623 bytes,
SHA-256 `9cbd400b506852819ac6889d1c4c63a83e88e4eda41de091fce25864230ce039`.
Base: `08c34e03f610b452e03422037949196dc7d92d6d`.

## Carrier and conventions

Reuse `HestenesCl14.Q14`, `Cl14`, `ClPlus14`, and `gamma` from
`InfoGeometry.Canonical.HestenesClPlus14`: native Mathlib `CliffordAlgebra`
over real `Fin 4` coordinates with signature (+---). Reuse native reversion
and `HestenesHermitianAdjoint.hestenesAdjoint`. Noncommutative products remain
Clifford or quaternion matrix products until a specified real-linear readout.

## Intended missing implications

1. Construct an actual real algebra equivalence from Cl(1,3) to 2 by 2
   matrices over Mathlib's real quaternions, including generator readbacks.
2. Construct coordinates for the complete native even algebra, and prove
   normalized real-trace scalar readout, reversion, and observer-conjugation
   compatibility. Derive the (4,4) reversion form and positive observer form
   for all spinors, with a closed counterexample to indefinite Cauchy--Schwarz.
3. Prove the real right-bivector square, orthogonality, and two-plane Bessel
   bound. Keep the underlying noncommutative action explicit.
4. Prove right-mass coefficient square signs and the conditional squaring of
   a real linear field operator that respects multiplication by a constant
   right coefficient. Compare the naive pseudoscalar substitution with the
   correctly transformed equation.
5. Correct the negative-blade enumeration: three spatial vectors, three
   spatial bivectors, three time-plus-two-space trivectors, and the
   spacetime pseudoscalar square to minus one.
6. For the particular native time projector, establish nonzero idempotence,
   primitivity, and an eight-dimensional native principal left ideal through
   its first quaternion-matrix column. Prove minimality under the full
   Clifford left action; do not replace it with minimality of a real subspace.

## Existing owners and consumers

`HestenesEvenPauliEquiv` already proves full dimension 16 and even dimension
8 using a real exterior basis and the even/odd equivalence. Move these
unchanged declarations into a narrow owner while retaining their names.
`HestenesKreinMatrixBridge.reverseEven` and its linear/product laws move
unchanged to a native reversion owner; its matrix consumers retain imports.
`HestenesHermitianAdjoint` already owns the observer adjoint and its laws.
These source moves must preserve dependent Pauli and adjoint consumers.

## Scope boundaries

No physical rotational anisotropy/restoration, causal propagation, solution
existence, electromagnetic coupling, Fourier inversion, real Clifford
periodicity classification, or charged-Majorana doubling uniqueness is
inferred from finite algebra. A differential squaring theorem states its
operator hypotheses and is not an unconditional PDE construction. A change
from the bivector to the pseudoscalar changes the mass factor in the
correct equivalent equation. Only complete proofs enter source owners.

## Acceptance

Fresh pinned Lean 4.34.1 compilation, complete owned-declaration axiom audit,
strict placeholder and semantic review, independent mathematical audit and
independent acceptance. Allowed foundational axioms: propext,
Classical.choice, Quot.sound. Targeted verification is distinct from root
package integration, whose actual result will be recorded.
