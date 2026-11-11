# Ordered homotopes and independent twistor invariants

## Intake and scope

Source: the user attachment `Pasted text(20261111-123554).txt`, preserved byte
for byte in `docs/intake/TWISTOR_HOMOTOPE_STREAM_2026_11_11.txt`.
SHA256: `e129d3b8f4db815e72294c3cd41f1d689e29e56a2a657b881aa5aefa97e7bd2c`.
The attachment has 34,018 UTF-8 bytes. Its prose and proposed proofs are intake,
not an acceptance certificate.

Implementation base: `c143c264bc18bbf41d692be4e270b5b7f7405702`.
Branch: `formalize/twistor-homotope-invariants`. This is a separate change from
the Dahm exterior-square action in PR #310. Root configuration, pins, existing
owners, and hooks remain unchanged. Lean is `v4.34.1`; Mathlib is
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

The user has requested canonical Mathlib Lean proofs with the actual ordered
operator products retained, and upstream preservation rather than relying on
the temporary checkout. Publish a clearly labeled draft checkpoint if checks
are pending, then update that same branch with repairs and verification.
Publishing a draft does not establish acceptance. No merge is authorized.

## Existing owners and conventions

- `PenroseIncidence`: `Spinor2`, `Twistor4 = Spinor2 × Spinor2`.
- `PerjesConventions`: the left-conjugate-linear `wittPair`, `paperHelicity`,
  `paperScale`, and `paperScale_sq`.
- `InfinityTwistor`: the existing lower-spinor alternating form and its
  Plücker `p23` readout. It is a map into the dual, not an idempotent.
- `TwistorConstituentKinematics`: `Packet`, `pairMassSq`,
  `pairMomentum_determinant`, and `paper_pair_mass`. Native `pairMassSq` is
  one determinant; the paper-normalized mass square is twice this invariant.
- `TwistorInternalSymmetry`: `mix`, ordered `mix_mul`, and actual inverses.
- `ConstituentColumnEquivalence`: `columnEquiv`, `column_mix`, and
  `infinityRaisingMatrix`. The column action `Z ↦ Z U` is `mix Uᵀ Z`.
- `ConstituentMomentumTransport`: whole-matrix momentum preservation and
  the corresponding determinant preservation.
- `PerjesMomentOperator`: actual matrix operators, their square law, and
  noncommuting null-operator witnesses.

The general fixed-kernel product is not the existing Peirce-corner
`upperHomotopeBracket`. Reuse existing corner APIs where applicable; do not
redeclare them. The recurrence below is separate from the existing
Clifford-colimit nested-commutator recurrence.

## Claim ledger and corrected propositions

| ID | Exact finite claim | Scope and correction |
| --- | --- | --- |
| H1 | `product T X Y = X * T * Y` is associative in `X,Y`. | Arbitrary associative ring; no commutativity assumption. |
| H2 | Half-sum `jordan` and half-difference `bracket` reconstruct the ordered product. | A rational algebra supplies a central invertible scalar two. Nonzero bracket requires unequal ordered products. |
| H3 | `J(J(X,Y),Z)-J(X,J(Y,Z)) = K(Y,K(X,Z))`; `K(X,K(Y,Z))+K(Y,K(Z,X))+K(Z,K(X,Y))=0`, with the same fixed kernel throughout. | Explicit product order; not a postulated Lie structure or an assumed identity. |
| H4 | There exist actual moment matrices `T,X` with `T²=X²=0` and `K_T(X,1) ≠ 0`. | Choose `T=R_W`, `X=R_Z` from the existing noncommuting null pair. This is a nonzero square-zero kernel on the native matrix carrier. |
| G1 | `gram Z i j = wittPair (Z i) (Z j)` is Hermitian and transforms as `conjugateEntries U * gram Z * Uᵀ` under native `mix U`. | Full finite packet; right column mixing uses `Uᵀ`. |
| G2 | For a pair, `det gram = 4*s₁*s₂ - normSq τ`, with `sᵢ = paperHelicity (Z i)` and `τ = wittPair (Z 0) (Z 1)`. | This conformal Gram determinant is separate from `pairMassSq`. No universal inequality between them. |
| G3 | `Z₁=(0,e₁)`, `Z₂=(z e₁,t e₂)` realize infinity pairing `t`, Witt pairing `z`, and two zero self-pairings, for arbitrary complex `t,z`. | Constructive joint surjectivity of the two complex readouts. No nonzero-frame hypothesis is silently added. |
| G4 | `AlgebraicIndependent ℝ` for the two functions on `Packet (Fin 2)` given by `pairMassSq (Z 0) (Z 1)` and `normSq (wittPair (Z 0) (Z 1))`. | Use G3 and Mathlib polynomial extensionality on an infinite nonnegative real box if promoted. Two isolated examples alone are insufficient. |
| G5 | For the 2×2 pair Gram matrix, with `H₀=H-(trace H/2)I`, `H₀²=((s₁-s₂)²+normSq τ)I` and `trace(H₀²)/2=(s₁-s₂)²+normSq τ`. | Positive Hermitian quadratic invariant. The intake's negative half-trace and its quarter-sized norm use incompatible conventions. |
| C1 | Right unitary mixing preserves actual momentum and conjugates the Gram matrix. | Prove the required inverse/order laws; invariance of a readout is not the matrix commutator equation `[U,P]=0`. |
| C2 | `C=paperScale * [[1,1],[-1,1]]` is unitary with determinant one. Its action sends `diag(2s,-2s)` to `[[0,2s],[2s,0]]`. | Use `mix Cᵀ` for the displayed sign. It preserves the traceless quadratic invariant and momentum. |
| T1 | From `(M₀,S₀)=(1,0)` and `(Mₙ₊₁,Sₙ₊₁)=(3Mₙ+Sₙ,Mₙ+3Sₙ)`, derive `Mₙ+Sₙ=4ⁿ`, `Mₙ-Sₙ=2ⁿ`, and bounds. The transition fails to commute with the first-mode projection. | Explicit integer recurrence and its actual two-dimensional transition matrix. Identification with Clifford-space dimensions is not supplied by the recurrence. |

## Further corrections retained as boundaries

With `Ω=[[0,1],[-1,0]]`, the momentum projector is `E=diag(0,I)`;
the degenerate alternating matrix is `J=diag(0,Ω)`, with `J²=-E`.
The actual square-zero operator is `ΣJ=[[0,Ω],[0,0]]`, already represented by
`infinityRaisingMatrix`. Do not name `J` a nilpotent projector.

For the repository's standard Pauli convention, the half-trace readout of
`H₀` has coordinates `(Re τ,-Im τ,s₁-s₂)`. A quarter-trace convention gives
half these coordinates and one quarter of their squared norm. This change
formalizes the matrix invariant and states its factor explicitly; it does not
identify that invariant with a Wigner spin representation.

For null columns the defect `2*pairMassSq-det gram` is nonnegative and is
strictly positive only when at least one relevant pairing is nonzero.
Bounded spin with mass tending to zero does not force a divergent ratio:
both zero spin and proportional decay are counterexamples. Cayley mixing
rotates the associated vector; only its norm is invariant.

The Poincaré stabilizer classification, Pauli–Lubanski construction,
Weinberg–Witten attribution, representation limits, quantum spin spectrum,
colour emergence, cohomological identification, and unlimited `Gr(k,4)`
tower are open interpretation or construction debt, not theorem conclusions.

## Proof dependency order

Ring multiplication and the central half supply the decomposition, associator,
and Jacobi branches. The nonzero-bracket criterion and the existing null
moment-operator witnesses supply H4; H4 does not require the Jacobi proof.

The native forms supply joint realization G3 directly. G3, norm-square
realization, and polynomial extensionality supply G4. Gram entry identities
supply the determinant and half-trace formulas. Unitary mixing and Gram
covariance supply their invariance and the Cayley conversion. Joint
realization does not depend on the Gram determinant theorem.

The recurrence branch depends on its own initial values and transition law.
It has no proved dependency on the conformal defect or the Cayley twistor
interpretation. A graph's increasing labels establish acyclicity only; they
do not prove the claims assigned to its nodes. No bundled tautological
"master theorem" will substitute for these dependency-bearing lemmas.

## Verification and acceptance

Use a focused project with unchanged pins, the shared build lock on each
execution host, and a declaration-owner audit. The audit must enumerate all
new owner declarations, including generated ones, reject new axioms and
unsafe/partial code, and allow only `propext`, `Classical.choice`, and
`Quot.sound`. Keep source review, kernel compilation, static source gates,
and independent acceptance distinct.

Record exact source fingerprints, Git tree, run/attempt and artifact identities,
command outcomes, declaration/theorem counts, and remaining debt. The focused
workflow must run a build, a fresh audit, strict screen/refute, static Gate 4,
vacuity heuristics, and source/whitespace checks. Static gates are not kernel
checks. A separate non-authoring reviewer must rerun decisive hosted checks on
the frozen source and inspect the actual outputs before acceptance is claimed.
Whole-repository/root integration is a separate scope and is not certified by
this focused workflow.
