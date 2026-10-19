# QMS theorem contract: Section 146 finite Fisher–Drazin energy naturality

## Claim

For a nonempty finite score carrier `Fin m`, every coordinate permutation
`σ`, score vector `s`, and input `v`, the quadratic readout

`Q_s(v) = ∑ i, G_s(v)i * H_s(G_s(v))i`

is invariant under simultaneous relabeling:

`Q_(s ∘ σ)(v ∘ σ) = Q_s(v)`.

## Carrier and conventions

- `H_s` is `fisherHessianEnd s`, the linear endomorphism induced by the finite
  Fisher–Souriau Hessian `diag(p) - p pᵀ`.
- `G_s` is the explicit centered reciprocal-weight group-inverse candidate
  `fisherHessianGroupInverseCandidate s`.
- The coordinate action is precomposition `(scorePermutation σ) x = x ∘ σ`.
- The scalar quadratic readout is the existing group-inverse energy, not a
  claim of self-concordant barrier or Dikin containment.

## Existing owner evidence

- `FisherSouriauGroupInverse.lean` proves the group-inverse energy equals
  `∑ i, (centerScores v i)^2 / p_i(s)`.
- `FisherSouriauGroupInversePermutation.lean` proves centering, reciprocal
  weights, the Hessian endomorphism, and the group-inverse candidate are
  permutation natural.
- `Cl55FiveGradedDrazinDikinUnification.lean` proves the finite Gibbs
  permutation law used for the probability weights.

## Minimal delta

Compose the existing explicit energy formula with finite reindexing of the
sum to prove invariance of this scalar readout.

## Scope exclusions

This theorem does not construct a self-concordant barrier, identify the
Fisher potential with a Dikin barrier, prove filtered-colimit compatibility,
or connect the score carrier to a `Cl(5,5)` representation, modular flow, or
holographic boundary map.
