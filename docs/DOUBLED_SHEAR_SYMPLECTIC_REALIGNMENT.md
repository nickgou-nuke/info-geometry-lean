# The doubled shear preserves the alternating form

`Krein.DoubleRealKreinShearDefect` proves that a nonzero upper shear fails to
preserve the canonical diagonal Krein pairing on a nonzero doubled space.
That statement remains valid. The constructive replacement keeps its action
and carrier while identifying the distinct form actually preserved.

`Krein.DoubledMatrixSymplectic` uses `DoubledSpace E`, `ρclock`, and the
existing `ChiralBoundarySymplectic.ChiralDoubled.symplecticForm`. The latter
is read on the native `WithLp.ofLp` coordinates; no new carrier or form is
introduced. For a real 2-by-2 matrix A and arbitrary doubled vectors X,Y:

    omega(rho(A)X,rho(A)Y) = det(A) * omega(X,Y).

Consequently determinant-one actions preserve omega, including every
`componentNReal t`. When E is nontrivial, preservation for all X,Y is
equivalent to determinant one: a nonzero vector placed on opposite sheets
detects the determinant through its positive self-inner-product.

The hypotheses are `NormedAddCommGroup E` and `InnerProductSpace ℝ E`;
completeness and finite dimensionality are not required. This does not make
the shear a Krein isometry, transport a metric without a map, or assert
continuum behavior. The existing form's actual definition is used; its
unrelated Boolean synthesis record supplies no proof evidence.

Grounding included the original defect and matrix-action owners, the chiral
form owner, maintained references, and all-maintained-Lean searches for
matrix-action/determinant/symplectic identities. The scalar-plane determinant
theorem in `Prequantum.LiouvilleCapacity` has a different carrier. No matching
general doubled-space covariance theorem was found in that bounded search.

## Verification

Parent audit session 87574 completed with exit 0 (3241 jobs). All five axiom
reports (four new theorems and the original obstruction) use exactly
`propext`, `Classical.choice`, `Quot.sound`; no new-source warnings occurred.
Log: `/tmp/doubled-symplectic-audit.log`. Independent semantic review and QA
accepted this scope. Combined QA session 69457 completed with terminal exit 0
(8980 jobs); `/tmp/shear-euler-krein-final-qa.log` records five shear reports,
all standard-axiom-only, and no scoped-source warnings. Scoped diffs and hole
checks passed. The shear source and audit passed strict screening cleanly.
