# Dense twisted cyclicity

Uncompiled scratch candidate; intended native owner:
`InfoGeometry/OperatorAlgebra/DenseTwistedCyclicity.lean`.
No existing files edited and no builds/tests run. Independent AA/QA pending.

The sole theorem is
`InfoGeometry.OperatorAlgebra.DenseTwistedCyclicity.twisted_cyclicity_of_denseRange`.
Inputs: Ring A, NormedRing B, actual ring hom f : A ->+* B with DenseRange,
continuous psi : B -> complex, unit delta : Aˣ, and the twisted product identity
on f's algebraic image. Output: the same identity on all X,Y : B, twisting by
f(delta) on the left and f(delta inverse) on the right in that exact order.

Mathlib reuse: `DenseRange.induction_on` in Topology/DenseEmbedding.lean,
`isClosed_eq`, continuity of multiplication and composition. First fix Y and
extend in X; for each image point f(x), extend in Y; `map_mul` reduces the final
image-image obligation to the supplied algebraic identity. No new extension
construction or topology on A is needed; f need not be injective or continuous.

For James: use an actual continuous linear functional as the function argument
and its `.continuous` proof. The target need not have a complex-algebra instance
for this lemma. The unit is native and the image factors are literal ring-hom
images; no inverse or automorphism witness is assumed separately.

This transports an already proved algebraic boundary identity. It does not
assert existence of a state, positivity, a real-time star-automorphism flow,
analytic strip continuation, or unbounded modular dynamics. No theorem packets,
proxy fields, new carriers, or forwarding-only CLM wrapper are introduced.
