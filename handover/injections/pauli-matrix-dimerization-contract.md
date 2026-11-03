# Ground-truth contract: noncommutative matrix dimerization switch

## Claim

In the repository's concrete `4 × 4` complex matrix representation of four
Majorana generators, compare the two finite bilinear pairings
`γ₁γ₂` and `γ₀γ₁ + γ₂γ₃`. The first commutes with `γ₀`; the second has exact
commutator `-(γ₁ + γ₁)` with `γ₀`, and this commutator is nonzero in the given
matrix representation. Package these conclusions as a proved archetype.

## Carrier and conventions

The carrier is `Pauli4 := Matrix (Fin 4) (Fin 4) ℂ` with ordinary matrix
multiplication in the displayed order. The operators `pauliMajorana i` and
`pauliMajoranaOperators` are the repository's explicit four-generator
Clifford representation. The endpoint is `pauliMajorana 0`. The commutator
convention is `[H, γ] = H * γ - γ * H`.

## Source-confirmed declarations

- `lean/InfoGeometry/Quantum/KitaevPauliBraiding.lean` defines the explicit
  `Pauli4` matrices, proves their squares and pairwise anticommutation, and
  assembles `pauliMajoranaOperators : MajoranaCliffordOperators 2 Pauli4`.
- `lean/InfoGeometry/Quantum/KitaevChain.lean` defines the inter-cell
  `sweetSpotHamiltonian`, the complementary `intraCellDimerHamiltonian`, and
  the generic exact boundary commutator theorem for the latter.
- `gamma_comm_product_of_avoids` proves that a Majorana generator commutes
  with a two-generator product when it anticommutes with each factor.

## Causal order

Concrete matrix Clifford relations
→ inter-cell boundary commutation and intra-cell exact commutator
→ a nonzero matrix-entry witness
→ the registered dimerization-switch archetype.

## Scope boundary

This proves a finite matrix endpoint comparison. It does not prove a closed
parameter loop, a bulk spectral-gap closure, robustness under a specified
perturbation family, or the benchmark's complete parity-pumping claim. The
existing Pfaffian path theorem is scalar-valued and is not used as a substitute.
