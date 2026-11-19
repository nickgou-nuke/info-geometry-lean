# Unified operator bridges: formal intent

Date: 2026-11-19. Base: `fea96b564201654cd4693008585039a56f66adf3`.

The original attachment is preserved byte for byte in
[`intake/2026-11-19-unified-architecture-original.txt`](intake/2026-11-19-unified-architecture-original.txt),
with length and SHA-256 in its companion manifest. It is a source of claims to
audit, not a record of completed research or a theorem certificate. The
accompanying chat narrative supplies the same proposed literature connections;
its first-person descriptions of verification are not adopted as evidence.

## Target A: cyclotomic powers of the actual twisted adjoint

Reuse `OperatorAlgebra/IntrinsicGradedAdjoint.lean`:

$$
\delta_{\theta,Q}(X)=QX-\theta(X)Q,
\qquad
\delta(XY)=\delta(X)Y+\theta(X)\delta(Y).
$$

1. On an associative algebra `A` over a field `k`, let `theta` be a native
   algebra automorphism, `N > 1`, `q : k` a primitive `N`th root, and
   `theta Q = q • Q`. Use the existing native `q_comm_power` theorem to derive
   the actual endomorphism identity
   $$
   \delta^N(X)=Q^N X-\theta^N(X)Q^N.
   $$
2. Under the additional hypothesis `theta^N = id`, derive
   `delta^N = ad(Q^N)` and `delta^N = 0` if and only if `Q^N` commutes with every
   element of `A`. Neither nilpotency nor centrality is stored as the conclusion
   in a custom structure.
3. Separately, over an arbitrary associative ring, allow an **internal**
   `q : A`, assume `q^2 + q + 1 = 0`, `theta q = q`, `Commute q Q`, and
   `theta Q = q * Q`. Prove the corresponding cubic identity without assuming
   `Commute q X` for arbitrary `X`. This is a full-ring statement; the
   field-scalar theorem alone does not establish it.
4. Construct a finite real operator instance using a real 2-by-2 order-three
   phase and a 3-by-3 clock/shift over that coefficient ring. Check that the
   internal phase is noncentral, the adjoint cube vanishes, and its square does
   not. Existing clock, shift, cyclotomic, and inner-conjugation definitions
   remain owners.

No external `Complex.I`, commutative replacement of `A`, assumed nilpotency,
or unproved identification with arbitrary `N`-complexes is permitted.

## Target B: mixed pairings and the boundary of divergence geometry

For real modules `E`, `F` and a native bilinear pairing
`B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`, construct the linear map

$$
\Phi_B:E\times F\longrightarrow E\times E^*,\qquad
(u,v)\longmapsto (u,B(-,v)).
$$

Pull back the existing `Clifford.NeutralPhaseSpaceCore.canonicalNeutralBilin`
along `Phi_B` in both slots. Its evaluation must be

$$
g_B((u,v),(u',v'))=B(u,v')+B(u',v).
$$

Prove that this native bilinear form is nondegenerate exactly when both
radicals of `B` vanish. For a square finite real matrix `C`, use the native
matrix-to-bilinear-form API to obtain nondegeneracy if and only if
`C.det ≠ 0`. This is an algebraic result about actual carriers and maps;
it does not assert global manifold, connection, integrability, or curvature
theorems.

Then verify actual derivatives of the smooth contrast

$$
D(x,y)=(x-y)^6-3(x-y)^4+3(x-y)^2.
$$

Prove positivity off the diagonal, vanishing on the diagonal, and

$$
-D_{xy}=6\bigl(5(x-y)^4-6(x-y)^2+1\bigr).
$$

The diagonal coefficient is `6`, but the coefficient at `(1,0)` is zero.
Exhibit degeneracy of the corresponding pulled-back form there. The
one-dimensional example refutes the unrestricted claim that every contrast
defines a nondegenerate neutral metric on the entire product. It is not a
replacement for the generic bilinear theorem.

## Existing results to reuse

- `Algebra/Quantum/QBinomial.lean`: quantum binomial expansion and primitive-root
  cancellation on a noncommutative algebra.
- `OperatorAlgebra/IntrinsicGradedAdjoint.lean`: actual adjoint, twisted Leibniz
  rule, involutive square identity, transport by algebra equivalences.
- `Clifford/NeutralPhaseSpaceCore.lean`: canonical evaluation pairing,
  para-involution, skew form, and nondegeneracy.
- `Geometry/ParaHessianMixedPotential.lean`: actual mixed derivatives and
  neutral geometry for a constant nondegenerate mixed potential.
- `Algebra/BlockSchurFactorization.lean`: ordered noncommutative Schur
  factorization and a counterexample to unrestricted multiplicativity of an
  ordinary determinant ratio.
- `Canonical/OperatorBerezinianDifferential.lean`: exact ordered
  multiplicativity defect and right logarithmic derivative of a unit ratio.

Owner searches cover declaration bodies, imports, native structures, and
selected consumers. They are bounded searches, not a claim that every
repository declaration or literature source has been exhausted. Existing
graph/index material is navigation evidence only; no refreshed global graph
certificate is claimed.

## Review and acceptance

Candidate authors work in isolated proposal directories. A separate reviewer
checks the exact integrated statements and assumptions. The runtime agent alone
runs native builds through the shared build lock, using the pinned Lean and
Mathlib revisions, without editing gates or dependency pins. Acceptance requires
the relevant source gates, native import-closure compilation, and a fresh axiom
audit of every declaration owned by the selected modules. Only the standard
Lean foundations `propext`, `Classical.choice`, and `Quot.sound` are allowed.

The final literature ledger must distinguish verified source content,
conditional connections, existing source proofs, new checked theorems, and
remaining work. No single-textbook, arbitrary-superdimension, Jones-tower,
or universal cyclotomic/nilpotent equivalence is asserted by this contract.
