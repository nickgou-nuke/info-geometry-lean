# Ground-truth theorem contract: finite Majorana dimerization switch

## Claim

For the repository's finite Majorana Clifford data, the existing inter-cell
pairing Hamiltonian commutes with the left boundary generator, while the
complementary intra-cell pairing has commutator
`[H_intra, γ₀] = -(γ₁ + γ₁)`.

This is a finite operator-algebra dimerization comparison. It is not a theorem
about a parameter cycle, spectral gap closure, critical field theory, or a
topological parity pump.

## Carrier and conventions

The carrier is `A` with `[Ring A]`, multiplication in its given order, and
Majorana generators indexed by `Fin (2 * N)` inside
`InfoGeometry.Quantum.KitaevChain.MajoranaOperators`. For the exact nonzero
commutator, use the stronger existing `MajoranaCliffordOperators` datum, whose
`h_sq` states `γ i * γ i = 1`; `h_ortho` states
`γ i * γ j + γ j * γ i = 0` for distinct indices. The new alternative pairing
on `N+1` sites is
`γ₀γ₁ + ∑ j : Fin N, γ_(2j+2) γ_(2j+3)`.

## Source-confirmed owners

- `lean/InfoGeometry/Quantum/KitaevChain.lean`,
  `commutator` (line 343): `a * b - b * a`.
- Same file, `MajoranaOperators` (line 346): finite generator family and
  pairwise anticommutation law.
- Same file, `gamma_comm_product_of_avoids` (line 357): a generator anticommutes
  past the two-factor product when distinct from both factors.
- Same file, `sweetSpotHamiltonian` (line 377): the inter-cell pairing
  `∑ j < N-1, t * γ_(2j+1)γ_(2j+2)`.
- Same file, `left_majorana_zero_mode` (line 395): under `[CommRing A]`, the
  left endpoint commutes with this existing pairing.
- Same file, `MajoranaCliffordOperators` (line 451): extends the same
  noncommutative carrier with `γᵢ² = 1`.
- `lean/InfoGeometry/Canonical/KitaevChainOwnerTransport.lean` proves the
  existing pairing equals the canonical finite bond sum and transports its
  conserved-span characterization. This is a separate consumer/bridge; the
  proposed theorem remains in the Quantum owner.
- `lean/InfoGeometry/Quantum/KitaevPauliBraiding.lean` constructs an inhabitant
  `pauliMajoranaOperators : MajoranaCliffordOperators 2 Pauli4`, an actual
  noncommutative matrix operator instance for the finite carrier.

## Smallest source-confirmed gap

The source has a theorem for the inter-cell pairing but no corresponding exact
commutator theorem for the complementary intra-cell pairing. Add that pairing
and prove its left-boundary commutator from `h_sq` and `h_ortho`, then package
the comparison with the existing zero-mode theorem as a finite dimerization
switch archetype.

## Causal order

`MajoranaCliffordOperators.h_sq` + `MajoranaOperators.h_ortho`
→ `gamma_comm_product_of_avoids` (tail terms commute with `γ₀`)
→ exact intra-cell boundary commutator
→ comparison with `left_majorana_zero_mode`.

## Adjacent claims not established

No parameter-space loop or operator-valued homotopy is present in this claim;
no spectral-gap or phase-transition theorem follows from the commutator
comparison. The transcript's specific benchmark Hamiltonian and perturbation
family have not been identified in the cited owners. The existing scalar
Pfaffian path argument is not used as a substitute for this operator theorem.
