# Ordered homotopes, two-twistor frames, and the real infinity pencil

## Intent and provenance

This change extracts finite algebraic claims from the supplied
`Pasted text(20261111-123420).txt`. The input SHA-256 is
`cd986f421c5a87d38161fcf0f3087468f2f8a2558ee6cc3ad8c8a521f01b5949`.
The implementation starts from upstream revision
`c143c264bc18bbf41d692be4e270b5b7f7405702` and retains its Lean and Mathlib pins.
The [formal intent envelope](twistor_homotope_infinity_contract.md) records
the allowed imports, hypotheses, and acceptance declarations for each branch.

The intended result is a set of native, reusable statements with explicit
carriers and maps. The input's philosophical node labels do not supply proof
dependencies. In particular, the nonzero polynomial `T*T-T` measures failure
of idempotence; it is not a logical contradiction or a proof of recursive
physical or cognitive evolution.

## Existing owners and missing implications

| Surface | Reused owner | Addition |
| --- | --- | --- |
| Ordered associative corner products | `OperatorAlgebra/FaithfulOperatorZornEnvelope` | Faithful upper embedding, ordered sandwich, symmetric and skew triple channels, doubled reconstruction |
| Actual two-twistor constituent mixing | `Twistor/TwistorInternalSymmetry`, `TwistorConstituentKinematics`, `ConstituentMomentumTransport` | Alternating-pairing determinant covariance and exact raw/normalized Hadamard readouts |
| Hermitian overlap convention | `Twistor/PerjesConventions` | Actual constituent Gram matrix, unitary invariants, and a determinant-one counterexample |
| Real chiral block square | `OperatorAlgebra/ChiralCouplingOperators` | The complementary infinity-form pencil, its square, inverse, and idempotency defect |
| Real split pairing and alternating spinor seed | `Quantum/NeutralKreinMajoranaFrame`, `Clifford/Cl11Matrix`, `Clifford/SignedPermutation` | Reuse of their actual matrices and relations |
| Genuine real dual-valued infinity form | `Twistor/RealInfinityTwistor` | Explicit matrix pairing identities in both argument conventions |
| Finite tensor stages | `Clifford/TowerMatrix` | Transpose-parity census of indexed real Pauli tensor words |

The bounded source search also inspected `PeirceSpine/KantorCornerAnomaly`
and `PeirceSpine/Bergman`, which already own homotope skew/Jacobi and Jordan
triple surfaces. No replacement tuple-matrix algebra is introduced. The
existing complex `TwistorKinematicTensor.infinityConjugate` is an antilinear
operation; it is distinct from the real linear matrix pencil here.

Related draft [PR #313](https://github.com/nickgou-nuke/info-geometry-lean/pull/313)
adds a complex infinity-raising algebra and a Hadamard operation on operators.
This branch remains based on upstream main and does not import that draft.
The present Hadamard action mixes the two constituent labels, while the real
pencil is connected explicitly to the already-owned real dual-valued form.

Related open drafts [#314](https://github.com/nickgou-nuke/info-geometry-lean/pull/314)
and [#315](https://github.com/nickgou-nuke/info-geometry-lean/pull/315) already
develop actual-packet Witt Gram covariance, unitary/Cayley invariance, ordered
homotopes, and recurrence orbits. In particular, #315's `ConstituentWittGram`
generalizes the Gram covariance here to every finite packet.
[#317](https://github.com/nickgou-nuke/info-geometry-lean/pull/317) separates
Witt and mass readouts and transports the existing operator Hadamard
construction to native matrices. This change shares those foundations.
Its additional focus is exact raw-versus-normalized constituent Hadamard
scaling and the determinant-one counterexample, the parameterized real
infinity pencil with explicit dual-form and raising-sign bridges, and the
transpose census derived from actual indexed Kronecker-word cardinalities.
The changed paths are disjoint at reviewed heads `b452340b`, `77b573e3`,
`7021de11`, and `812a2102`; this is not a combined-import or merge test.
Shared Gram and unitary interfaces should be consolidated when these drafts
are integrated.

## Ordered homotope reconstruction

For an arbitrary associative ring `A`, the existing carrier is
`Matrix (Fin 2) (Fin 2) A`. Its upper and lower corner embeddings satisfy

\[
u(x)\ell(z)u(y)=u(xzy),
\]
\[
[[u(x),\ell(z)],u(y)]=u(xzy+yzx),
\qquad
[u(x)\ell(z)+\ell(z)u(x),u(y)]=u(xzy-yzx).
\]

Adding the last two identities gives `2 • u (x*z*y)` without commuting any
coefficient factors. The upper embedding is injective. Cancellation or
division by two requires an additional hypothesis: in characteristic two,
the symmetric and skew channels can both vanish for a nonzero ordered
product. Consequently the unrestricted ring theorem asserts doubled
reconstruction, not recovery of an undoubled product in every ring.

## Actual two-twistor frame covariance

The existing packet action is `mix U Z i = ∑ j, U i j • Z j`.
The Witt pairing conjugates its first argument. Thus the actual overlap
matrix satisfies

\[
G(UZ)=\overline U\,G(Z)\,U^T,
\qquad
\mu(UZ)=\det(U)\,\mu(Z).
\]

The native `pairMassSq` is `Complex.normSq μ`. The paper's separate factor
two remains in its existing convention adapter. For

\[
H=\begin{pmatrix}1&1\\1&-1\end{pmatrix},\qquad Q=H/\sqrt2,
\]

the exact multipliers are:

| Readout | Raw `H` | Normalized `Q` |
| --- | --- | --- |
| Matrix square | `2 • 1` | `1` |
| Matrix determinant | `-2` | `-1` |
| Infinity pairing | `-2 μ` | `-μ` |
| Total momentum | `2 • P` | `P` |
| Pair mass squared | `4 m²` | `m²` |
| Gram determinant | `4 det G` | `det G` |
| Trace-free Gram determinant | `4 det G₀` | `det G₀` |

The normalized gate is unitary and involutive. Its determinant is negative
one, so it is not asserted to be an `SU(2)` matrix. For actual packets with
`G = diag(2s,-2s)`, raw mixing gives off-diagonal entries `4s`; normalized
mixing gives `2s`.

Unitary mixing preserves Gram trace, determinant, and trace-free determinant.
Determinant one alone is insufficient: an actual packet with `G = 1`, mixed
by `diag(2,1/2)`, has new Gram `diag(4,1/4)`. Its trace-free determinant changes
from zero to `-225/64`. The algebraic ratio theorem states its nonzero mass
denominator explicitly; it does not define a physical screw-pitch observable.

## Real infinity pencil and variance

The actual carrier is `DoubledMat4R`, indexed by `Fin 2 ⊕ Fin 2`, over `ℝ`.
With the existing alternating seed `Ω = Eminus` and split metric `Σ`, define

\[
I_- = \begin{pmatrix}0&0\\0&\Omega\end{pmatrix},\quad
I_+ = \begin{pmatrix}\Omega&0\\0&0\end{pmatrix},\quad
I_\lambda=I_-+\lambda I_+,\quad O_\lambda=\Sigma I_\lambda.
\]

The two projected forms `I₋` and `I₊` are skew, mutually annihilating, and
extracted by complementary Peirce projections. The operator satisfies

\[
O_\lambda^2=-\lambda I,\qquad
O_\lambda^2=0\iff\lambda=0,\qquad
O_\lambda\ne0.
\]

For nonzero real `λ`, the displayed inverse is `-λ⁻¹ • Oλ`. Its idempotency
defect is `(-λ) • 1 - Oλ`; the defect's fixed upper-right entry is `-1`, so
the defect is nonzero for every parameter.

The bridge proves actual evaluation identities with the existing real form:

\[
g(z,O_\lambda w)=I_\lambda(z,w),\qquad
g(w,-O_\lambda z)=I_\lambda(z,w).
\]

The second sign is necessary because `RealInfinityTwistor.infinityTwistor`
curries the first argument. The bilinear form, its curried dual map, and the
endomorphism remain distinct typed objects. No complex antilinear raising,
spacetime curvature, cosmological constant, or `SU(2,2)` representation is
inferred from this finite real square law.

## Transpose census contract

The census concerns indexed words in the four real seeds
`[1, Eplus, J1, Eminus]`, evaluated by native Kronecker products in
`TowerMatrix.Mat n`. Three seeds are symmetric and one is skew. Tensor
transpose multiplies their signs, so an odd number of `Eminus` letters
reverses the sign. Word orthogonality excludes a zero evaluation.

The intended exact counts are finite word counts, with recurrences

\[
M_0=1,\quad S_0=0,\quad
M_{n+1}=3M_n+S_n,\quad S_{n+1}=M_n+3S_n,
\]
\[
M_n+S_n=4^n,\qquad M_n=S_n+2^n.
\]

At level two these give ten symmetric and six skew indexed words. This
does not classify all metrics or symplectic forms, count arbitrary matrices,
or prove that word evaluation is an injective basis map. Such conclusions
require their own independence, spanning, and nondegeneracy arguments.

## Actual dependency order and remaining scope

The source declarations establish the following dependencies:

1. Native corner embeddings → ordered/symmetric/skew triple identities →
   doubled ordered reconstruction.
2. Actual constituent action and bilinear/Witt forms → determinant and Gram
   covariance → raw scaling and unitary invariance → normalized Hadamard
   preservation. The determinant-one counterexample is a separate direct
   evaluation from the packet and Gram definitions.
3. Native split metric, spinor square, and ordered chiral square → real pencil
   square → nilpotency criterion, inverse, and defect. Explicit pairing
   equalities connect this matrix branch to the genuine real dual-valued form.
4. Finite words, Boolean parity, and the head/tail equivalence → subtype
   cardinality recurrences → level-two counts. Separately, native seed
   transpose laws and Kronecker evaluation establish the matrix meaning of
   that parity; orthogonality excludes zero evaluations.

These branches share named owners where the source supplies them. A conjunction
of their conclusions would not establish new causal arrows between them.
There is no proved implication from a Gram overlap to spatial ray skewness,
from a trace-free determinant to a Pauli–Lubanski invariant, from the real
pencil parameter to de Sitter/anti-de Sitter curvature, or from increasing
packet size to a color representation. The change also supplies no infinite
analytic limit, Majorana protection theorem, Berry connection, modular
Radon–Nikodym theorem, or photon-as-Goldstone result.

## Earlier questions about the existing codebase

The following is a bounded source review of existing owners, not an absence
claim about the whole repository or a fresh kernel audit of these modules.

| Topic | Existing declaration or carrier | Exact scope seen in the source |
| --- | --- | --- |
| Hodge theory | `HodgeCohomology/FiniteHarmonicRepresentative.existsUnique_closed_coclosed_representative` | A square-zero differential on a finite-dimensional real inner-product space has a unique closed/coclosed representative of a closed state modulo its range. |
| Dirac/Hodge bridge | `OperatorAlgebra/FiniteTwoTermDiracHodgeZorn.diracHodge_sq_eq_hodgeLaplacian` | Actual two-term real matrix operators satisfy the Dirac square law; the owner also proves adjunction and two-sheet intertwining. |
| Berry transport | `Canonical/BerryConnection.deriv_berryOfOperator_expTransport_at_zero` | A derivative of the operator readout under exponential conjugation is the corresponding commutator readout. |
| Projector curvature | `Clifford/ChiralProjectorBerryCurvature.projectorCurvature` | The algebraic expression `P * [dPi,dPj] * P` accepts its three arguments as ring elements; the definition does not construct a differentiable projector family or require idempotency. |
| Finite relative modular action | `Physics/FiniteRelativeModularOperator.relativeModularOperator` | The actual linear map `X ↦ rho * X * sigmaInv` has ordered composition laws; inverse statements require explicit inverse equations. |
| Majorana-labelled protection | `Holography/MajoranaPlabicZeroModes.majorana_zero_mode_topological_protection` | The theorem type states `openHamiltonian w * danglingEdge = 0` on its four-component carrier. It supplies no perturbation family, locality hypothesis, or spectral-gap stability estimate. |
| Photon/Goldstone proposal | `Canonical/PhotonicParabolicTransfer` and `Canonical/PionChiralGoldstoneNative` | The inspected results prove shear composition and finite symmetric-pair/CAR identities respectively. Neither inspected owner identifies photons with Goldstone modes. |

There is also a specific interface issue in
`Canonical/ConnesTomitaModularAutomorphismBridge.RadonNikodymCocycle`, consumed
by `OperatorAlgebra/RadonNikodymCocycleKMSBridge`: its definition quantifies
the cocycle law over **every** unit-valued function `u`, rather than storing
one such function with its law. At times zero, a constant function with value
`v : Mˣ` gives `v = v * v`, because the flow at zero is the identity. Group
cancellation then gives `v = 1`. Thus this premise forces the unit group to
be trivial; it cannot serve as a constructed Connes cocycle for an operator
algebra with nontrivial units. This is a source-level algebraic implication,
not an additional Lean theorem or interface repair in this PR. The new
finite algebraic owners do not depend on that premise.

## Validation

Source candidates received independent semantic review before integration.
Kernel validation and declaration-level axiom audit are pending at this
checkpoint. No candidate or text scan is represented as a successful build.

The initial maintained root command
`python3 tools/infra/run_locked_lake_build.py InfoGeometry.Algebra.FiniteSpinAlgebra`
acquired the shared lock and exited with code 1 during package resolution:
the configured `external_refs/homotopy-hypothesis-lean4` directory is absent.
No toolchain, dependency pin, root package requirement, or existing cache was
changed to remove that failure. Focused exact-source validation uses the same
pins and must be reported separately from root integration.

The selected-source entry point delegates to the existing shared-lock,
exact-source checker and its native owning-module axiom audit:

```bash
python3 tools/quality/check_twistor_homotope_geometry.py \
  --mathlib-root .lake/packages/mathlib \
  --output tmp/twistor-homotope-check
```

The output directory must be fresh. The checker records the precise import
closure, source hashes, compiler version, aggregate declaration count, and axiom
footprint. It rejects a dependency-pin mismatch and does not reuse project
oleans. Its successful result would cover the selected exact source closure,
not the root Lake package.

The same five owners are added to the existing Perjes/Klein CI target list;
its workflow also checks its preexisting targets. The new local entry point
selects only this change's five owners and their exact import closure. The
shared checker accepts an explicit target list while preserving its default
CI selection and shared-lock behavior. It records independent compilation
failures, skips dependents of a failed import, and runs its native declaration
audit only after the entire selected closure succeeds.
