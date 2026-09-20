# Krein Green-projector decomposition

This layer extends the [Krein Dirac adjunction](KREIN_HODGE_DIRAC.md) without
replacing its indefinite pairing by a positive inner product. The underlying
algebraic constructor does not require a metric at all; signed energy identities
use an explicitly supplied native real bilinear form.

## Proof dependency order

1. The existing `HodgeHelmholtzKreinDecomposition.HodgePacket` supplies
   `d² = δ² = 0` and `Δ = dδ + δd`.
2. `DrazinCommutant.inverse_commutes_of_commutes` proves that a Drazin inverse
   commutes with every operator commuting with the original operator.
3. `FiniteGeneralizedHodgeDecomposition.exists_commuting_green` combines this
   with the existing finite-dimensional Drazin existence theorem to obtain a
   Green operator `G` commuting with both `d` and `δ`. Neither `G` nor its
   commutation laws are assumptions of this existence theorem.
4. `HodgeGreenProjectorConstruction.decompositionFromGreen` constructs
   `Pex = dδG`, `Pcoex = δdG`, and `Pharm = 1 - Pex - Pcoex`. It proves all
   idempotence, mutual-annihilation, and partition laws required by the existing
   `HodgePacket.DecompositionPacket`, rather than assuming those laws.
5. `exists_generalized_hodge_decomposition` proves finite-dimensional existence
   of this packet, with `range Pex ⊆ range d`, `range Pcoex ⊆ range δ`, and
   `range Pharm = ker (Δ^index)`.
6. `DrazinPairingAdjunction.inverse_adjoint` proves that a Drazin inverse of a
   pairing-self-adjoint operator is pairing-self-adjoint. It works over a
   commutative ring with a supplied bilinear form; no positivity,
   nondegeneracy, finite-dimensionality, or ambient star operation is needed.
   The proof uses the existing Drazin power reduction and generalized-zero
   projector identities. Unlike the existing star-ring Drazin theorem, it
   applies directly to a bilinear adjoint relation without installing a star
   structure on endomorphisms.
7. `KreinGreenEnergy.laplacian_adjoint` derives pairing-self-adjointness of `Δ`
   from symmetric `B` and adjunction of `d` and `δ`. The new inverse theorem
   then derives `green_adjoint`. Consequently
   `constructed_projectors_adjoint` and `constructed_signed_energy` no longer
   require a separate adjunction hypothesis for `G`. The latter proves

   ```text
   B(x,x) = B(Pex x,Pex x) + B(Pcoex x,Pcoex x) + B(Pharm x,Pharm x).
   ```

8. `KreinFiniteGreenDecomposition.exists_adjoint_generalized_decomposition`
   combines finite-dimensional existence with these adjunction theorems. Its
   only metric hypotheses are symmetry of `B` and adjunction of `d` and `δ`;
   it requires neither a supplied Green operator nor supplied self-adjoint
   projectors. Signed energy and pairwise orthogonality follow from the
   existing projector lemmas.

The energy equation is signed, not a sum of nonnegative squared norms. An
arbitrary algebraic Hodge packet has no metric; its pairing-orthogonal
realization additionally requires the stated metric compatibility, not
positive definiteness.

The [bounded boundary realization](KREIN_DRAZIN_BOUNDARY_REALIZATION.md) connects
these pairing results to the existing `KreinSpace.kreinAdjoint` and constructs
the repository's existing Drazin boundary-support and complement-compatibility
packets, with their projector adjunction laws derived rather than assumed.

## Generalized zero sector is not necessarily harmonic

The legacy packet field name `Pharm` is retained for reuse. At arbitrary Drazin
index its proved range is the **generalized zero sector** `ker (Δ^index)`, not
necessarily `ker Δ`. The separate group-inverse theorem
`harmonic_projector_range_eq_kernel` proves the latter equality at index one.
Neither statement implies closedness, coclosedness, or a nonzero homology class
without additional assumptions in the indefinite setting.

`KreinNilpotentGreenTests.lean` checks the distinction on real triples:

```text
B(x,y) = x₁y₃ + x₂y₂ + x₃y₁
J(x₁,x₂,x₃) = (x₃,x₂,x₁)
d(x₁,x₂,x₃) = (x₂,0,0)
δ(x₁,x₂,x₃) = (0,x₃,0)
Δ(x₁,x₂,x₃) = (x₃,0,0).
```

The tests prove symmetry and nondegeneracy of `B`, exhibit both signs, verify
the square-sum formula for `B(x,Jx)`, and prove the adjunction `d♯ = δ` as an
adjoint-pair relation. Here `Δ ≠ 0` but `Δ² = 0`; `G = 0` satisfies the Drazin
laws at index two. The constructed `Pharm` has full range, strictly different
from `ker Δ`. In particular `(0,0,1)` is in the former and not the latter.

The other tests cover three nonzero projector sectors with `Δ = diag(1,1,0)`
and pairing `diag(1,1,-1)`, and the existing nonzero square-zero doubled Krein
operator. They also instantiate the finite-dimensional existence theorem.

`DrazinPairingAdjunctionTests.lean` additionally tests a mixed regular/nilpotent
operator, not just an idempotent or a zero Green operator:

```text
B(x,y) = x₁y₁ + x₂y₃ + x₃y₂
A(x₁,x₂,x₃) = (2x₁,x₃,0)
G(x₁,x₂,x₃) = (x₁/2,0,0).
```

It proves adjunction of `A`, the Drazin equations at index two, and derives
adjunction of `G`. The finite Krein regression then instantiates the new
existence theorem both on the three-sector example and on the nilpotent
Laplacian example.

## Validation boundary

The six regression modules are:

- `Canonical/HodgeGreenProjectorConstructionTests.lean`
- `Canonical/FiniteGeneralizedHodgeDecompositionTests.lean`
- `HodgeCohomology/KreinGreenEnergyTests.lean`
- `HodgeCohomology/KreinNilpotentGreenTests.lean`
- `Canonical/DrazinPairingAdjunctionTests.lean`
- `HodgeCohomology/KreinFiniteGreenDecompositionTests.lean`

All six regression modules pass serial, locked isolated Lean **4.28.x** checks
without warnings. Their 36 axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` or added axioms. These
checks use cached Mathlib revision `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
This is not a full repository build or verification under the pinned Lean
**4.28.1** toolchain.
The 4.28.1 compiler rejects the cached Mathlib `.olean` headers. The cached
Mathlib source revision itself declares 4.28.x; some cached indirect package
revisions also differ from the repository manifest. Pins and dependency source
have not been changed. A compatible pinned dependency build remains open.
