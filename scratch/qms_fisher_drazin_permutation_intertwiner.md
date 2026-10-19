# QMS theorem contract: Fisher--Souriau Drazin permutation intertwiner

## Claim

For a nonempty finite score carrier `Fin m`, a permutation `σ`, and the
coordinate relabeling `Pσ x = x ∘ σ`, the finite Fisher--Souriau Hessian and
its canonical index-one Drazin inverse are intertwined under the corresponding
relabeling of score parameters:

```lean
Pσ.comp (drazinInverse (fisherHessianEnd s)) =
  (drazinInverse (fisherHessianEnd (s ∘ σ))).comp Pσ
```

The operation `LinearMap.comp` acts right-to-left. This is a parameter-changing
intertwining statement; it asserts fixed-score commutation only when
`s ∘ σ = s`.

## Grounded carriers and prerequisites

- `fisherHessianEnd` is `Matrix.toLin'` of the exact finite Hessian
  `diag(p) - p pᵀ` in `FisherSouriauGroupInverse.lean`.
- `fisherHessianGroupInverseCandidate` is the centered reciprocal-weight
  operator on `Fin m → ℝ`.
- `fisherHessianGroupInverseCandidate_perm_equivariant` already proves its
  pointwise relabeling law in `FisherSouriauGroupInversePermutation.lean`.
- `fisherSouriauHessian_candidate_eq_drazinInverse` identifies that candidate
  with the repository's canonical Drazin inverse under
  `[Nonempty (Fin m)]`.
- `fisherSouriauLaplacian_perm_equivariant` and
  `gibbsProb_perm_equivariant` use the same convention
  `H(s ∘ σ)ᵢⱼ = H(s)_{σ i, σ j}`.

## Exact implementation delta

Define the linear endomorphism `scorePermutation σ` by `x ↦ x ∘ σ`. Prove the
composition identity for the explicit group-inverse candidate using its
existing pointwise theorem and `LinearMap.ext`, then rewrite both candidates
to the canonical Drazin inverse under the nonempty hypothesis. Add both new
declarations to the companion axiom audit.

## Scope limits

This contract is finite-dimensional and permutation-equivariant. It does not
assert Dikin containment, self-concordance, filtered-colimit transport,
five-grade preservation, or a continuous/infinite-dimensional Drazin theorem.
It does not claim an invariant potential under arbitrary linear maps.

## Acceptance evidence

Require independent A-A review of the precise orientation and theorem scope,
strict OpenGauss screening, locked serial builds of the owner, audit and
`InfoGeometry.Synthesis.All`, audited axiom output, Gate 4, and a distinct QA-A
rerun of the decisive checks. Record each observed result before acceptance.
