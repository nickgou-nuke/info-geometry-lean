# Finite Attention Identities and Their Scope

The prior draft claimed that skew-adjointness alone proves transformer
attention is a quantum fluid, and that finite softmax normalization verifies a
KMS state. Those conclusions do not follow from the stated calculations. This
note records the genuine finite statements retained from that draft.

## Verified finite chain

For a finite score family, the log-partition function has gradient equal to
the Gibbs/softmax mean and Hessian equal to the covariance matrix. Its
quadratic form is a variance, so it is nonnegative and vanishes exactly in
constant-logit directions. Finite softmax weights are finite Gibbs weights
after specifying energy as the negative score. A unique finite score maximum
gives a point-mass limit as inverse temperature tends to infinity; tied maxima
give the uniform law on the maximizing set.

Lean owners:

- `InfoGeometry.Analytic.LogSumExp`
- `InfoGeometry.Canonical.AttentionInformationGeometry`
- `InfoGeometry.Routing.FiniteSoftmax`
- `InfoGeometry.Canonical.DeterministicArgmaxAttention`
- `InfoGeometry.Canonical.AttentionGlauberCopulaBridge`

## Separate linear-algebra fact

For the explicitly chosen linear vector field `u(x)=A x`, divergence equals
`trace(A)`. A skew-symmetric real matrix has trace zero. This fact can be
formalized independently; no map in the finite attention theorem identifies
the attention probabilities with such a vector field.

Likewise, a finite Gibbs probability vector is not a KMS state by itself. A
KMS theorem needs a state on an observable algebra and a specified time
evolution satisfying the KMS boundary condition. Symbolic or numerical
checks of finite identities are examples, not proofs of these missing
identifications.
