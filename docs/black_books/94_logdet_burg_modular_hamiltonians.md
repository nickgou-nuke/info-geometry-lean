# Log-Det Potentials, Burg Divergence, and Modular Hamiltonians

This chapter records the finite SPD owner lane now attached to the canonical
surface, together with the operator/modular lift map.

## I. SPD Burg/Stein Owner Lane

New owner anchors:

- `REPO_THEOREM`
  [BurgStein.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Jordan/BurgStein.lean)
  - `burgKernel`
  - `burgKernel_nonneg`
  - `steinLoss`
  - `steinLoss_self`
  - `steinLoss_eq_trace_add_barrier_diff_sub_dim`

Definition now present on `SPD`:
`steinLoss(X,Y) = tr(Y⁻¹X) - log det(Y⁻¹X) - n`.

The scalar convex atom is also explicit:
`burgKernel(λ) = λ - log λ - 1`, with nonnegativity on `λ > 0`.

## II. Canonical Facade Integration

- `REPO_THEOREM`
  [Canonical/LogDet.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/LogDet.lean)
  now exports the new Burg/Stein owners alongside existing log-det owners.

This keeps the SPD log-det lane and the existing determinant/log-volume lane on
the same canonical import surface.

## III. Modular Lift Anchors

The noncommutative lift remains on these owner surfaces:

- `REPO_THEOREM`
  [RelativeModularOperator.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean)
- `REPO_THEOREM`
  [RelativeModularHamiltonian.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonian.lean)
- `REPO_THEOREM`
  [RNDeterminantConnesChainBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean)
- `INTERFACE_READY`
  [PedersenTakesakiRNInterface.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/PedersenTakesakiRNInterface.lean)

## IV. Δ-First Rule

Interpretation is strict and ordered:

1. multiplicative owner (`Δ`/cocycles),
2. additive readout (`-log Δ` lane),
3. scalar shadows (trace/log-det/Burg/entropy readouts).

Canonical guardrail:

- In Type III, `Δ` and `log Δ` are canonical.
- Determinant/trace scalarizations are representation-dependent shadows.
- Log-det geometry is the abelian shadow of modular theory, not the owner in
  the Type III lane.

## V. Corrected Lift Dictionary

- density ratio -> relative modular operator `Δ_{φ|ψ}`,
- surprisal -> modular Hamiltonian `K = -log Δ`,
- expectation -> state/weight pairing (GNS; natural-cone language only after
  choosing standard form),
- chain rule -> Connes cocycle (multiplicative), with additive generator only
  where logarithmic generator calculus is defined.

This preserves the cocycle/generator distinction and avoids collapsing finite
trace/determinant formulas into Type III ontology.

## VI. Boundary (Not Yet Owner-Complete)

- spectral-eigenvalue normal form theorem
  `steinLoss = Σ_i (λ_i - log λ_i - 1)` as an owner theorem surface;
- explicit Gaussian KL covariance decomposition theorem on the SPD owner lane;
- full affiliated-operator Pedersen-Takesaki/Vaes existence/uniqueness owner
  stack in Type III generality.

So the finite SPD Burg/Stein lane is now owner-compiled, while the full
infinite-dimensional spectral/operator endpoints remain on the active frontier.
