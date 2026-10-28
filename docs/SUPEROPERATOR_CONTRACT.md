# Matrix superoperators and graded Peirce geometry

## Intake and source boundary

This extension continues draft PR #251 from the independently accepted commit
`11c9b712ee0d52cfc21e84d4740dd04934377dd2`. Its fresh verification run
[40685683734](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40685683734)
compiled 39 source modules and audited 343 declarations. It is the accepted
baseline; the new extension has separate source-bound verification below.

The four original uploads are preserved unchanged. Their mathematical formulas
are candidate statements, not evidence that their advertised proofs compile.

| Uploaded source | Bytes | Lines | SHA256 |
| --- | ---: | ---: | --- |
| `Pasted text(20261028-121008).txt` | 13039 | 212 | `70a02c2bfae6f92aa8a21c60738777361541a52ec546ad8770474ffda75323af` |
| `Pasted text (2)(20261028-121122).txt` | 11978 | 188 | `da48160c8e6e84b3ba8696a97520282e8b4fd8e604346d215f8ea03d37602180` |
| `Pasted text (3)(10).txt` | 10871 | 191 | `9accca3218bb34d7bbc033e6c0c6ed17ad9718b526cd2e2d835c139d9974c308` |
| `Pasted text (4)(4).txt` | 12297 | 202 | `c9ea1b3660df958f1492aa1bb7aa48a1a59abb84439546bd958ba1180cfe8c85` |

## Carrier, conventions, and existing owners

All new mathematics acts on the full algebra `Matrix n n ℂ`, for an arbitrary
finite index type, with its ordered multiplication and native associative Lie
bracket. Endomorphisms use `Module.End ℂ (Matrix n n ℂ)` and native
`LieAlgebra.ad`. The already-owned
`Core.JordanMultiplicationClosure.jordanLeft` is the **unnormalized** action
`X ↦ U * X + X * U`; the differently normalized Jordan operator in
`Core.JordanPeirceDecomposition` is not substituted for it.

The following existing owners supply the mathematical primitives:

- `MatrixOperatorIdentities`: associative Leibniz, Jacobi, nested commutator
  expansion, and the native adjoint action.
- `Core.JordanMultiplicationClosure`: Jordan multiplication as a native linear
  endomorphism, its commutator identity, and its Leibniz law.
- `Core.PeirceDecomposition` and `Core.IdempotentCartan`: directed corners,
  complementary idempotents, square-zero corner products, even/odd projections,
  the reflection, and its actual involutive ring automorphism.
- `PeirceChiralGeometry`, `PeircePairGeometry`, and `PeircePairPositivity`:
  corner weights, square identities, reflection parity, ordered Lie–Jordan
  conversion, and adjoint-conditioned Gram positivity.
- `PeirceKrausGeometry`, `Quantum.ChoiCompletePositivity`, and
  `Quantum.KrausAmplificationCP`: the existing Kraus map and all finite matrix
  amplifications. No replacement channel carrier is introduced.

The existing `Core.DiracSuperalgebra` and `Core.DiracPeirceSuperalgebra` concern
a square-zero Moore–Penrose inverse pair. They do not permit identifying an
arbitrary reverse corner with that inverse. The generic Boolean formulas in
`Canonical.ChiralSuperderivationColimit` require separate homogeneous
membership; the new reflection formulas supply actual parity on the full
matrix algebra. `NCG.BlockSupermatrixGradedTrace` owns a tagged superbracket
derivation, with a distinct block carrier. No categorical or colimit carrier
is replaced by these finite matrix results.

## Exact mathematical contract

The notation below abbreviates expressions for this contract; it does not
authorize duplicate Lean definitions. Write

`D_U(X) = ⁅U, X⁆`, `J_U(X) = U*X + X*U`,
`Q = U*V + V*U`, `L = ⁅U,V⁆`,
`Φ(X) = U*X*V + V*X*U`, and `Ψ(X) = U*X*V - V*X*U`.

### Universal composition identities

For arbitrary full matrices, without nilpotence or commutation hypotheses:

- `J_U(D_V X) + J_V(D_U X) = D_Q X` and its Lie–Jordan ordering dual.
- `D_U(J_V X) - J_V(D_U X) = J_L X`.
- The raw mixed difference is corrected to
  `D_U(J_V X) - D_V(J_U X) = J_L X + 2 • Ψ(X)`.
- The symmetric Jordan and Lie compositions equal respectively
  `J_Q X + 2 • Φ(X)` and `J_Q X - 2 • Φ(X)`.
- Their sum and difference recover `2 • J_Q X` and `4 • Φ(X)`.
- `trace (Φ(X)) = trace (Q*X)` has no parity restriction on `X`.

If `U*U=0`, the alternating compositions `D_U ∘ J_U` and `J_U ∘ D_U`
vanish. The ordinary squares are instead `D_U²(X) = -2 • (U*X*U)` and
`J_U²(X) = 2 • (U*X*U)`.

### Genuine graded differential

For `p*p=p`, use the existing involution `σ = reflectionConj p hp`.
The expression `d_U(X) = U*X - σ(X)*U` satisfies twisted Leibniz.
If `σ(U)=-U`, its parity changes sign and `d_U²(X)=⁅U*U,X⁆`.
Thus the forward and reverse square-zero Peirce corners give actual
square-zero differentials on every matrix. For two odd matrices,
`d_U d_V + d_V d_U = D_Q`.

This last inner derivation is not asserted to be positive. In an adjoint
statement the projection must be self-adjoint, the reverse matrix must be
`star U`, and the adjoint candidate has the **plus** sign
`δ(X)=star U*X + σ(X)*star U`. Any claimed adjoint relation must be proved
with the native trace pairing, and its symmetric composition is the Jordan
action `J_(U*star U+star U*U)`, not the commutator action.

### Square-zero pair relations and inner action

For arbitrary `U*U=0` and `V*V=0`, put `E=U+V` and `J=U-V`.
The precise relations are

`E²=Q`, `J²=-Q`, `J*E=L`, `E*J=-L`, `L²=Q²`,

with exported commutation statements for `Q` and `E,J,L`. The inner actions are

`⁅L,E⁆ = 2 • (Q*J)`, `⁅L,J⁆ = 2 • (Q*E)`,

`⁅L,⁅L,E⁆⁆ = 4 • (Q*Q*E)`,
`⁅L,⁅L,J⁆⁆ = 4 • (Q*Q*J)`.

The two square equalities occur as checked local facts in the weighted-product
proofs; the extension does not add duplicate public square APIs.

For the two corners of the same input matrix, native `ad_p` reconstructs
them and satisfies `ad_p³=ad_p`. Reciprocal action hypotheses give the exact
Leibniz equivalences for vanishing of the quadratic products. No periodic
evolution is inferred from those algebraic equalities.

### Noncommuting witnesses and rejected strengthening

Use the already-checked nondiagonal projections `OperatorExtensionExamples.P`
and `.Q`, with `U=component10 P Q` and `V=component01 P Q=star U`.
The existing proof establishes `¬ Commute U V`. The new examples refute
the missing-defect identity at the nondiagonal input `P`, and ordinary
square-zero action at the noncommuting input `V`, within the full matrix
algebra. Coordinate evaluations witness nonzero matrices; they do not replace
the operator carrier by scalars.

The following narrative claims are excluded from the theorem contract:

- A scalar Clifford algebra or a real metric signature from operator-valued
  opposite squares; `Q` need not be scalar or invertible.
- Ambient centrality of `Q`; commuting with the generated pair is weaker.
- A positive Hodge Laplacian or a bicomplex from the commutator `D_Q`.
- Complete positivity of independent-input transport. The Kraus interpretation
  requires adjoint pairing; unitality or trace preservation additionally
  requires the appropriate completeness equation.
- Dynamics, frequencies, spectral gaps, physical fields, or cohomology without
  the structures and hypotheses those claims require.

## Proof order and acceptance

The six modules contain 80 named theorems and no new
mathematical definitions:

| Module | Named theorems | Mathematical endpoint |
| --- | ---: | --- |
| `MatrixLieJordanOperators` | 21 | Native endomorphism identities, exact defect, trace transport, finite amplification positivity |
| `MatrixSquareZeroPairs` | 14 | Ordered products and matrix-weighted iterated inner actions |
| `PeirceGradedDifferential` | 15 | Actual reflection parity, twisted Leibniz, square curvature, corner differentials |
| `PeirceGradedTraceGeometry` | 8 | Trace adjoint, positive quadratic form, exact joint kernel |
| `PeirceInnerAction` | 11 | Corner reconstruction, native cubic adjoint action, quadratic vanishing equivalences |
| `OperatorSuperoperatorExamples` | 11 | Full nondiagonal counterexamples to the three false strengthenings |

The adjoint and positivity endpoint has only a star projection and actual
oddness as premises; it does not require square-zero. Specifically, with
`V=star U` and the plus-sign companion `δ`, the checked statements are

`trace (star X * (Q*X + X*Q)) = trace (star (d X) * d X) + trace (star (δ X) * δ X)`,

`0 ≤ trace (star X * (Q*X + X*Q))`, and

`Q*X + X*Q = 0 ↔ d X = 0 ∧ δ X = 0`.

The concrete proofs use the same accepted noncommuting corners: the missing
defect entry is `-12800/59049`, the repeated ordinary Lie and Jordan entries
are respectively `-174080/4782969` and `174080/4782969`, and the commutator
quadratic trace at the dense nondiagonal input is `-18496/729`.

Universal identities precede square-zero consequences. Existing Peirce owners
supply the nilpotence and reflection hypotheses. The pair relations precede
their iterated inner actions. Exact examples consume these general results.
The published poset is generated from constants in checked declaration
types and proof values, with dependency-to-dependent orientation and a Hasse
reduction. Reciprocal algebraic identities are not dependency cycles.

The T16 static screener receives a bounded compatibility repair for the actual
imported fixture: a closed native `¬ Commute P Q` statement and nullary matrix
constants typed through simple local notation. Carrier dimensions and
coefficients must still match. Regression cases reject comment/string spoofing,
assumed or axiom-backed witnesses, ambiguous notation, and supported forms of
name shadowing.
The native predicate and all mathematical owners are unchanged. Focused
regressions accompany the repair, and the scoped CI workflow runs them before
the Lean check. This is a bounded source recognizer, not a Lean elaborator;
the checked declarations and kernel audit remain authoritative.

**Local kernel acceptance: PASS.** The exact selected closure contains 46
repository source modules. Incremental source compilation and a newly executed
complete declaration audit cover 453 declarations across 20 owners: 424
theorem-kind records and 29 existing definition-kind records. The six new
modules contribute 80 named theorems and 30 generated proof lemmas, with no
definition-kind records and no compiler warnings. The only transitive axioms
are `propext`, `Classical.choice`, and `Quot.sound`.

The exact checked dependency poset is committed in
`docs/SUPEROPERATOR_DEPENDENCIES.json`: 453 nodes, 792 direct edges, 467 Hasse
edges, and seven layers with sizes `182, 71, 91, 50, 31, 23, 5`. Its relation
is reflexive transitive proof dependency among the audited owners. It does
not claim unique mathematical necessity or a physical causality structure.

`docs/SUPEROPERATOR_VERIFICATION.json` binds the local source snapshot, audit,
graph, static receipts, and independent reviews. The local run reused validated
unchanged compiled artifacts; it is explicitly not a fresh published-commit CI
attestation. Fresh nonincremental acceptance of the published source tree is
reported separately in the PR body, after source, tool, dependency-pin, and
tested-merge-tree bindings have been verified. This scope is the complete
selected closure, not a whole-repository build. All 39 previously accepted
source files, the existing newly imported Jordan owner, and dependency pins
remain unchanged.
