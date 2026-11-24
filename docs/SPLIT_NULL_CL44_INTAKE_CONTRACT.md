# Canonical split-octonion null incidence and real Clifford operators

## Intake and authority

The user supplied `Pasted text(20261124-132902).txt`, an audit of two earlier
drafts followed by `SplitOctonionCl44Complete`. The complete, unmodified text
is preserved in `docs/intake/split-null-cl44-20261124/proposal.txt`.
Its SHA-256 is
`e9015139d818aa18e98c5b37aed417ca17632b24af056746ccce071fd4147ee8`.
Its claims of successful compilation and instantaneous execution are intake
claims, not build receipts.

This task uses the canonical real Zorn algebra and the existing native
Clifford algebra owners. Source review, exact finite arithmetic, Lean
compilation, native axiom inspection, and geometric interpretation are
separate evidence levels. Native acceptance of the new owners is pending.

## Countermodels in the supplied multiplication table

Write `e_i` for the coordinate unit vectors of the submitted `octMul`.
Its literal table gives

\[
e_4 e_4=e_0,\qquad e_4 e_1=e_5,\qquad e_4 e_5=-e_1.
\]

Consequently `e₄ * (e₄ * e₁) = -e₁`, whereas
`(e₄ * e₄) * e₁ = e₁`. The submitted algebra is not alternative. In particular,
the claimed conjugate contraction is already false on this basis vector.

Two null elements make the composition failure equally explicit:
`x = e₀ + e₄` and `y = e₁ + e₅` have submitted norm zero, but their submitted
product is `2e₅`, with norm `-4`.

Exact integer arithmetic on the literal table also yields:

- `L₄² = diag(1,-1,-1,-1,1,-1,-1,-1)`;
- `trace(L₄ L_conj(4)) = 4`, where the draft asserts `-8`;
- `rank(L_(e₀+e₄)) = 7` and kernel dimension one, where the draft asserts four;
- `L₁ L₂ L₃ L₄ L₅ L₆ L₇ = diag(1,1,-1,-1,1,-1,-1,1)`, so the submitted
  `by decide` target asserting identity is false.

These computations refute the literal draft. They are not proofs about the
repository's canonical Zorn multiplication, which has a different, already
owned definition. The bad table is retained only as intake evidence.

The factor-of-four normalization correction is algebraically sound when its
Clifford hypotheses actually hold: if `P²=1`, `N²=-1`, and `PN=-NP`, then
`a=(P+N)/2` and `a†=(P-N)/2` satisfy `a a† + a† a = 1`.
The existing `Cl44Witt` owner already uses this normalization.

## Pinned API audit

Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` remain unchanged.
At that exact Mathlib source revision, `Fin.sum_univ_eight`,
`Matrix.mulVecLin_mul`, `Matrix.smul_mul`, and `Matrix.sub_mul` exist. The
attachment's blanket claim that these APIs are unavailable is inaccurate.

The native theorem `LinearMap.IsProj.trace` supplies the projection trace
formula. `IsIdempotentElem.isProj_range` and `Matrix.trace_toLin'_eq` already
give the general matrix idempotent rank/trace result. This task reuses native
projection trace directly in its actual kernel consumer; it does not add a
second custom decomposition theorem.

## Existing owners and boundaries

The bounded source search covered canonical and algebraic Zorn multiplication,
regular operators, norm contraction, coordinate bases, annihilator dimension,
Clifford representations, Witt generators, volume elements, and their imports
and consumers.

| Owner | Reused content and scope |
|---|---|
| `Lie.CanonicalZornRegularOperators` | Actual real `CanonicalZorn` carrier, `leftRegularRepresentation`, and injectivity of the linear lift |
| `Canonical.ZornCliffordRepresentation` | Canonical conjugation, norm quadratic form, conjugate contractions, real two-copy Dirac carrier, and native Clifford lift |
| `Lie.CanonicalZornRegularNorm` | Left/conjugate-left operator products, opposite-order contraction, and norm/unit criterion |
| `Lie.CanonicalZornRegularExactDet` | Actual regular matrix in the existing Cartesian basis and determinant equal to the fourth power of the reduced norm |
| `Lie.SplitOctonionWittPairingTransportBridge` | Existing `canonicalToCoord` linear equivalence and its genuine eight-element basis |
| `Lie.SplitOctonionImaginaryAction` | Nondegeneracy of the canonical polar form and dimension eight of the full real carrier |
| `Lie.SplitOctonionAnnihilatorDimension` | Prior range/kernel and dimension results for imaginary right multipliers; these do not already state the full arbitrary-null left result |
| `Clifford.Cl44Witt` | Native half-normalized Witt generators and CAR |
| `Clifford.Cl44VolumeElement` | Native volume-square and generator anticommutation identities |

The generic real `DiracSpinor16` carrier is `ZornMatrix ℝ × ZornMatrix ℝ`.
It must not be confused with a complex Dirac carrier restricted to real
scalars, which has real dimension 32. A quadratic isometry used to transport
the Clifford action is not an octonion multiplication isomorphism.

## Exact theorem contract: null incidence

Carrier: the existing `CanonicalZorn`, definitionally `ZornMatrix ℝ`.
Operator: the existing `leftRegularRepresentation X : Module.End ℝ CanonicalZorn`.
Norm: the existing `zornNormFun`; conjugation: the existing `zornConj`.
Hypotheses: `X ≠ 0` and `zornNormFun X = 0`. No imaginary or trace-zero
hypothesis is introduced.

Target conclusions:

\[
\operatorname{range}L_{\bar X}=\ker L_X,
\qquad \dim_{\mathbb R}\ker L_X=4,
\qquad \operatorname{rank}L_X=4.
\]

Native `QuadraticMap.polar` is the unhalved polarization. The intermediate
trace law is therefore `trace(L_X L_conj(Y)) = 4 * polar(norm) X Y`, equivalent
to eight times the corresponding halved bilinear pairing.

Dependency order:

1. Polarize the existing two conjugate contraction identities.
2. Evaluate operator trace using the already established Cartesian matrix.
3. Use polar nondegeneracy to select a partner `Y` with unhalved polar value one.
4. Construct `LinearMap.IsProj (ker L_X) (L_conj(X) * L_Y)` from the two
   contraction identities. The same operator supplies explicit preimages for
   the image/kernel equality.
5. Apply native projection trace, then rank-nullity for the original operator.

This is a theorem about actual four-dimensional linear subspaces. It does
not by itself construct a projective quadric, Grassmannian, twistor variety,
or incidence classification.

## Exact theorem contract: real sixteen-dimensional representation

Use the existing norm quadratic form and real two-copy Zorn carrier. Construct
an explicit quadratic isometry from the existing `splitQ44` coordinate owner,
then compose the induced native Clifford map with the existing Zorn Clifford
representation. Transport normalized Witt CAR and volume identities through
that algebra homomorphism. The negative four-generator product supplies the
Born involution and exchange of the two Witt families.

Any explicit volume/grading identity must use the actual coordinate order
and orientation of this isometry. A generator representation or verified CAR
does not establish an algebra isomorphism `Cl(4,4) ≃ₐ[ℝ] M₁₆(ℝ)` without
separate injectivity and surjectivity proofs. That stronger classification
claim is outside the current representation contract.

## Publication and validation

The new work is based on the repaired Zorn/Souriau branch, preserving its
literature-map addition. The separately published triality/cotangent branch
receives its own observed compiler-error repairs. Neither draft is marked
ready from source checks alone.

New owner candidates require independent semantic/API review, scoped source
gates, exact-pin compilation with fresh warnings-as-errors elaboration, and
native module-owned/transitive axiom inspection. The maintained shared build
lock is respected. Local lock contention is recorded as blocked execution,
never as a compiler pass. Hosted CI provides the alternate exact-head route.

The ordinary root workspace remains a distinct integration surface. Focused
verification does not certify all repository owners, external path packages,
physics interpretations, or an analytic completion.
