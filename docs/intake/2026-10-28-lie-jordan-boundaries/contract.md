# Native boundary operators: ground-truth contract

## Frozen source and carrier

Four verbatim user streams are preserved in input order beside this contract,
with byte counts and SHA-256 hashes in provenance.json. Embedded declarations
of successful verification are untrusted intake. This extension starts from
PR #253 source `935473bc3015919107e0fc18f71f9aea20ea1f20`; dependency pins remain
Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.

Use associative unital rings and native `Module.End R A`, `LieAlgebra.ad`,
`LinearMap.mulLeftRight`, `LinearMap.range`, `LinearMap.ker`,
`ModuleCat`, `CochainComplex`, and full `Matrix n n ℂ`.
Use the existing `jordanLeft`, Peirce corners, parity projections, reflection,
and dense matrices P,S,U. Do not introduce replacement commutators, scalar
carriers, commuting restrictions, or structures that assume the target theorem.

Write D_a=ad_a, J_a=jordanLeft a, and S_ab(X)=a*X*b only in this document.
For opposite supported corners u,v write E=u+v, J=u-v, K=uv+vu,
C=[u,v], and γ=2p-1 as mathematical abbreviations.

## Source corrections

1. If u²=0, the mixed compositions D_u J_u and J_u D_u vanish.
   The ordinary squares are D_u²(X)=-2uXu and J_u²(X)=2uXu, and need not vanish.
   A genuine parity-sensitive differential must change the sign with parity.
2. The source's generator-swapped mixed difference is missing a defect:
   D_u J_v - D_v J_u = J_[u,v] + 2(S_uv-S_vu).
   The operator commutator D_u J_v - J_v D_u = J_[u,v] is a different,
   already owned statement.
3. The symmetric sandwich map Φ(X)=uXv+vXu obeys Tr Φ(X)=Tr(KX)
   without an evenness assumption. This is not trace preservation unless the
   corresponding normalization is imposed. Adjoint pairing supplies positivity;
   independent opposite inputs alone do not suffice.
4. A reciprocal commutator cycle and an operator-valued multiplier do not
   establish periodic time evolution or a scalar frequency.
5. Quadratic commutation with generated E,J,C is not centrality in the entire
   ambient matrix algebra. Opposite-square identities do not imply E³=E,
   self-Drazin inversion, or Moore–Penrose reflexivity.

## Existing owners and reuse

- Core.JordanMultiplicationClosure owns native `jordanLeft`.
- Core.LieJordanComposition owns native operator commutators, both ordered
  plus/minus products, and cyclic trace adjunction. In particular its
  `ad_jordan_bracket` is not the false generator-swapped source equation.
- Core.PeirceGrading owns native integer-linear even/odd projections,
  `odd_reconstruction`, `commutator_odd`, parity multiplication, reflection,
  and its conjugation endomorphism.
- Core.PeirceStarCharges owns commutator reconstruction, opposite squares,
  anticommutation, and star/Hermitian conditions.
- Core.PeirceCoupledCorners owns independent-corner extraction and support,
  coupled square, compressions, reflection duality, and exact zero conditions.
- Canonical.PeirceCouplingGeometry and PeirceCouplingPositivity own trace and
  kernel identities, Gram positivity, and its exact positive-definite criterion.
- Canonical.ChiralSuperderivationColimit owns Boolean-tagged, pointwise
  parity-alternating composition identities. Those tags alone do not prove
  membership in homogeneous subspaces. The new consumer must use the actual
  Peirce grading and native linear maps.
- Canonical.GrassmannianBundleCyclotomicOrientability already has a pointwise
  idempotent-adjoint cubic law. The new focused interface is the native
  endomorphism polynomial, its identification with the existing odd projection,
  and its range/kernel geometry; no novelty claim is made for the polynomial.
- Superalgebra.KahlerDiracWeitzenbockSynthesis owns square-zero endomorphism
  Laplacian centralizers. Singular.MoorePenrose / Core.DiracSuperalgebra own the
  normalized inverse-pair conclusions under explicit inverse hypotheses.
- Existing triangular boundary cochain modules are finite incidence complexes,
  not the full matrix-algebra differential requested here.
- Native Mathlib Derivation assumes a commutative algebra; it is not an
  appropriate replacement for the noncommutative inner action.

## Planned theorem interfaces

### Core.LieJordanBoundaryOperators

Native endomorphism equalities for arbitrary associative algebras:
D_a J_a=J_a D_a=D_(a²); both mixed sums equal D_(ab+ba);
the corrected mixed difference including its sandwich defect;
the pure Jordan and pure Lie symmetric compositions equal J_(ab+ba)
plus/minus twice the symmetric sandwich map; their sum/difference recover
twice J_(ab+ba) / four times the sandwich map.
Under a²=0 prove the two zero mixed composites, their native range/kernel
inclusions, and the exact nonzero-square obstruction formulas.
Use native Lie representation laws and existing commutator owners where applicable.

### Core.PeirceAdjointCycle

Identify ad_p² with the existing odd projection, prove ad_p³=ad_p and the
native range/kernel identifications. Extract the two corners directly from
p*[p,x] and -[p,x]*p. Prove the opposite-corner ±1 actions and the reciprocal
ad_p cycle using existing support laws; retain characteristic-two validity.

### Core.PeirceQuadraticFrame

For arbitrary independent opposite corners prove the weighted noncommutative
multiplication laws for E,J,K,C. Reuse the existing coupled-square and
commutator-square owners. Prove C=JE=-EJ, C²=K², commutation of K with the
generated E,J,C, [C,E]=2KJ, [C,J]=2KE, and both iterated-bracket identities.
Prove the precise Leibniz identities/equivalences for an arbitrary reciprocal
inner-derivation cycle. No normalization K=1 or E³=E is assumed or concluded.

### Canonical.PeirceBoundaryComplex

Construct an actual R-linear map on the full algebra,
d_u(X)=uX-γXγu, from native multiplication maps. For an idempotent p and
an odd u, prove its parity-dependent Lie/Jordan readouts, parity switching,
twisted Leibniz rule, and d_u²=ad_(u²). For opposite odd u,v prove
d_u d_v+d_v d_u=ad_(uv+vu). A supported corner is square-zero, so d_u²=0;
use this proved law to construct a native constant-module cochain complex.
No adjoint-codifferential or positive Hodge-Laplacian claim is inferred.

### Canonical.LieJordanSandwichGeometry

Prove the native matrix sandwich trace identity for arbitrary inputs, its
identity readout, the correctly normalized trace-preservation statement,
and positive-semidefinite preservation with adjoint pairing.
For supported opposite corners prove that the map takes values in the even
Peirce sector and annihilates odd inputs. Use existing native trace and
positive-matrix APIs.

### Canonical.LieJordanBoundaryExamples

Reuse dense P,S,U and Uᴴ to refute the source's ordinary square-zero action,
missing mixed-difference defect, ambient centrality, and unnormalized
tripotency assertions. Verify nontriviality of the actual graded differential.
All examples are in the full noncommutative Mat3 carrier; numerical probes
certify operator inequalities, not substitute scalar models for the theory.

## Proof-prerequisite partial order

Associativity/native Lie–Jordan actions -> exact ordered compositions and defects.
Idempotent support -> existing Peirce grading -> adjoint cycle / native parity.
Support + previous coupled square -> weighted quadratic frame.
Actual parity + odd multiplication -> graded differential identities ->
square-zero corner specialization -> native cochain complex.
Cyclic trace / native Gram positivity -> conditional sandwich geometry.
These branches meet in the dense full-matrix boundary witnesses.
Edges are proof prerequisites, not physical causation.

## Acceptance and scope

All new theorem bodies must be complete and kernel-checked. Acceptance requires
source-hash reconciliation, strict target warnings, constructivity/proof-proxy
scan, native ownership and axiom audit, isolated Lake build, independent semantic
review, and independent acceptance. Only propext, Classical.choice and Quot.sound
are permitted foundational axioms. Physics, differential geometry, topology,
spectral gaps, complete positivity, and normalized inverse interpretations are
not inferred beyond the exact native structures and theorems actually proved.
