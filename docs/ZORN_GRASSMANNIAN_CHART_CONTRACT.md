# Zorn Grassmannian chart contract

Continue the corrected color operator development on the existing
`ZornVectorMatrix R`. Construct the linear splitting `(a,u,v,b) ↦ ((a,u),(v,b))`,
identify the existing left E11 projector with the standard first-summand
projector, and construct actual `Module.Grassmannian R (ZornVectorMatrix R) 4`
points from graph kernels. Mathlib's rank is QUOTIENT rank, not subspace rank.
Use the existing graph-chart/projector owners and actual quotient equivalences;
prove finite projective quotient and stalk rank rather than assume them.

Separately distinguish idempotent first-order directions from fixed-complement
graph directions, using the two off-diagonal blocks. The graph parameter space
has dimension 16 over a field; changing image and complement independently has
dimension 32. These are finite algebraic chart statements, not claims of an
analytic derivative, global supermanifold, sheaf gluing, or representability.
No colimit/continuum claim is involved. Preserve concurrent staged owners and
verify under the shared build lock with strict selected-owner axiom replay.
