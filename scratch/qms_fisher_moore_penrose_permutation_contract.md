# Ground-Truth Contract: Euclidean Fisher–Moore–Penrose permutation naturality

## Claim

For a nonempty finite index type `Fin m`, let `Score := EuclideanSpace ℝ (Fin m)` and transport the coordinate relabeling `x ↦ x ∘ σ` to a continuous linear map `Pσ` using the existing `scoreEquiv` and `transportCLM`. Simultaneously relabeling the potential parameter `s` to `s ∘ σ` makes both the Fisher Hessian and its canonical Moore–Penrose inverse intertwine with `Pσ`.

## Carrier and convention

`Pσ x` corresponds under `scoreEquiv` to the function `x ∘ σ`. Linear-map composition is read right to left. The parameter is relabeled by the same `σ`.

## Existing proved inputs

- `FisherSouriauGroupInversePermutation.fisherHessianEnd_linear_intertwines_perm` proves the function-space Hessian intertwining.
- `FisherSouriauGroupInversePermutation.fisherHessianGroupInverseCandidate_linear_intertwines_perm` proves the function-space group-inverse candidate intertwining.
- `FisherSouriauMoorePenrose.fisherSouriauHessian_groupInverseCandidate_eq_moorePenroseInverse` identifies that candidate, after transport to `Score`, with the canonical closed-range Moore–Penrose inverse.

## Minimal delta

Transport the two function-space intertwining equalities to `Score`, then rewrite the transported candidate using its existing Moore–Penrose identification. Do not assume an isometry as a premise; no such premise is required for these equations.

## Exclusions

This does not prove self-concordance, Dikin-ball containment, compatibility with the five-graded colimit, a Cl(5,5)-to-score map, modular-flow equivariance, or holographic duality. It is a finite-dimensional permutation naturality theorem only.
