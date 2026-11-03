# Plabic vertex contraction: ground-truth contract

## Claim

For three pairwise orthogonal Peirce idempotents `E₁,E₂,E₃`, let
`x = E₁ A E₂`, `y = E₂ C₁ E₁`, `u = E₂ C₂ E₃`, and `v = E₃ D E₂`.
The unipotent contraction of `E₂ + x + y + u + v` by
`(1-x-v)` on the left and `(1-y-u)` on the right is
`E₂ - xy - vu - xu - vy`. The signed contraction of
`E₂ + x-y+u-v` by `(1-x+v)` and `(1+y-u)` is
`E₂ + xy + vu - xu - vy`.

## Grounded owners and dependencies

- `InfoGeometry.OperatorAlgebra.PeirceSpine.IdempotentZornChainArchetypes`
  defines `shell1/2/3`, the nested-shell partition theorem
  `three_shell_partition`, the four directed root maps, and
  `corner_arrows_mul_zero`.
- The same owner defines the path bridge
  `edgeMajoranaPhi13 = edgeRoot13 + edgeRoot31` and the two link metrics.
- Its `zorn_plabic_twisted_chain_brackets` gives the corrected twisted
  commutator decomposition, retaining the edge bridge term.
- `zorn_plabic_parity_link_and_edge_action` and
  `zorn_plabic_parity_j_link_action` cover the Kasteleyn grading and its
  orientation-dependent action on the two links.
- `zorn_plabic_twisted_phi_chain_brackets` gives the `Φ₁₂-Φ₂₃` bracket,
  and `zorn_link_spin_action_on_boundary_paths` gives the sum/difference
  spin actions on the two directed boundary paths.
- `zorn_link_spin_derivation_curvature` proves the exact curvature
  correction. The two inner derivations do not commute unconditionally.

## Correction to the proposed identity

With `edgeMajoranaJ13 = xu - vy`, the signed contraction is **not**
`E₂ + xy + vu - edgeMajoranaJ13`: direct ordered multiplication gives
`E₂ + xy + vu - xu - vy`. The bridge contribution is therefore
`-edgeMajoranaPhi13`, not `-edgeMajoranaJ13`. The new theorem records the
ordered product and this corrected result over arbitrary `[Ring B]`.

The proposed `A₁₁₄` cross-bracket also has a sign/coordinate mismatch:
`zorn_plabic_twisted_phi_chain_brackets` proves that the commutator of
`Φ₁₂-Φ₂₃` with `Φ₁₂+Φ₂₃` is `2 * edgeMajoranaJ13`, while its
anticommutator is twice the link-metric difference. The source theorem is
the authority for these bracket coordinates.

## Scope limit

These are finite Peirce-ring product identities. They do not establish a
Postnikov square move, cluster mutation, Grassmannian boundary measurement,
Schur complement, or a physical integration-out theorem.
