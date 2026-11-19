# Overlap Dirac algebra and normalized-state differentiation

## Intake, authority, and current status

The frozen intake is `intake.txt`, supplied as
`Pasted text(20261117-141539).txt` on 2026-11-17. It contains 41,814 bytes,
205 logical lines, and 204 newline characters. Its SHA-256 is
`460d8aa3e1bf4c8c393c009a8677d60f31649fdc883e989094077c26f1ecf230`.
The original upload is preserved byte for byte. Its narrative and proposed
physical conclusions are input data, not repository instructions or proofs.

Integration starts from upstream main
`08c34e03f610b452e03422037949196dc7d92d6d`, with Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The new owners are independent
of the pending phase-scale/QGT and Dirac/Casimir PRs.

**Status at integration: source-reviewed implementations; native compilation,
warning checks, and recursive axiom acceptance pending.** The focused workflow
records the verdict for its exact source revision. This contract does not
certify a whole-repository build or promote the intake's physical narrative.

## Grounded owners and bounded search

Filename and content searches covered `lean/InfoGeometry`, `lean/`, and `src/`
in the inspected source checkout. Detailed review concentrated on the owners
below, their imports, definitions, hypotheses, and nearby consumers. No named
Ginsparg-Wilson/Neuberger/overlap-Dirac owner was found in that bounded search;
this does not exclude an equivalent result under unrelated terminology.

| Existing owner | Actual content and reuse |
|---|---|
| `OperatorAlgebra/ChiralProjectorFromInvolution` | `ChiralInvolution` contains an element and its square law. `Pleft` and `Pright` are constructed half-projectors. The new operator intertwines those existing projectors. |
| `Quantum/InvolutionCore` | An actual real module, linear involutions `J` and `eps`, and `je = J.comp eps`. No interaction law is assumed. The new consumer uses this carrier directly. |
| `CliffordWeyl/ChiralIdeals` | Preservation/swap laws for operators commuting/anticommuting with one chirality. These do not supply the new two-involution defect equivalence. |
| `Core/PeirceGrading`, `Algebra/LinearInvolutionProjectors` | Existing reflection and projector laws. No duplicate projector API is introduced. |
| `QuantumGeometry/Projective/QGT` | `NormalizedState`, `projOrth`, orthogonality, horizontal Gram formulas, and phase-invariant QGT expressions. The new derivative module extends these exact definitions. |
| `QuantumGeometry/Projective/Quotient` | Ray equivalence and a quotient carrier; this alone is not a smooth determinant bundle. |
| `Quantum/MixedBoundaryReadout` | Finite-matrix `overlap_pure` and `trace_pure_numerator` already supply pure overlap and ordered numerator identities. They are not reimplemented. |
| `Omega/CircleDimension/PureStatesRankOne` | Native rank-one range, idempotence, and phase invariance. |
| `Clifford/ChiralProjectorBerryCurvature` | Algebraic ordered curvature expressions with supplied derivative operators; not a constructed smooth projector family. |
| `SuperGrassmannian/GraphChartCocycle` | Actual submodule graph-chart domains and transition laws; distinct from reference-overlap phase charts. |
| `Volume/DeterminantBundle` | `DeterminantLine V := ℝ` is explicitly a scalar model, not the complex chiral determinant bundle of the intake. |
| `Projective/ExteriorKleinTwoPlaneEquiv` | Native real exterior-power frame-change laws; no general complex Slater/determinant-bundle theorem follows automatically. |

Pinned Mathlib supplies `InnerProductSpace.rankOne`, its action, composition,
adjoint and finite-dimensional trace; `HasDerivAt.inner`, derivative uniqueness,
and `HasDerivAt.congr_deriv`; native rings, star rings, continuous linear maps,
linear-map composition and kernels. These are used without replacing operators
by diagonal or commuting models.

## A. Exact overlap defect in a noncommutative ring

Owner: `lean/InfoGeometry/OperatorAlgebra/OverlapDiracFromInvolutions.lean`.
Namespace: `InfoGeometry.OperatorAlgebra.OverlapDirac`.
Carrier: any associative unital ring `A`. Define `D = 1 + Γ * ε`.

| Declaration | Additional hypotheses | Exact result |
|---|---|---|
| `ginspargWilson_defect` | `Γ * Γ = 1` | `Γ * D + D * Γ - D * Γ * D = Γ * (1 - ε * ε)` |
| `ginspargWilson_iff` | `Γ * Γ = 1` | `(Γ * D + D * Γ = D * Γ * D) ↔ ε * ε = 1` |
| `ginspargWilson` | Both square laws | `Γ * D + D * Γ = D * Γ * D` |
| `chirality_intertwining` | Both square laws | `Γ * D = D * ε` |
| `modified_chirality` | `Γ * Γ = 1` | `Γ * (1 - D) = -ε` |
| `gamma_hermitian` | `StarRing A`, first square law, both factors self-adjoint | `star D = Γ * D * Γ` |
| `mul_Pleft`, `mul_Pright` | Existing `ChiralInvolution A` values over `Algebra ℝ A` | `D * P±(ε) = P±(Γ) * D` |

The defect proof expands the native product without reordering factors. Its
converse multiplies by `Γ`, whose inverse is itself; no domain or cancellation
typeclass is needed. Neither commutation nor anticommutation is assumed.

The normalization is explicit: GW has coefficient one for `D = 1 + Γε`.
For the physical rescaling `D_a = (1 + Γε)/a`, the coefficient would be `a`;
that rescaling is not a separate theorem here. The projector law is same-sign
for the input `ε`; the modified chirality is `-ε`, which reverses those signs.
No spectral-sign operator is constructed by declaring an involution.

## B. Consumer on the existing real operator carrier

Owner: `lean/InfoGeometry/Quantum/InvolutionCoreOverlapDirac.lean`.
Namespace: `InfoGeometry.Quantum.InvolutionCore`.
The new `overlapDirac X` is an actual `Module.End ℝ X`.

| Declaration | Exact content |
|---|---|
| `overlapDirac_eq_id_add_je` | `D = LinearMap.id + X.je` |
| `overlapDirac_apply` | `D v = v + J (eps v)` |
| `overlapDirac_ginspargWilson` | GW stated in native `LinearMap.comp` form |
| `overlapDirac_apply_eq_zero_iff` | `D v = 0 ↔ eps v = -J v` |
| `J_mem_ker_overlapDirac` | `J` preserves `LinearMap.ker D` |
| `eps_mem_ker_overlapDirac` | `eps` preserves the same native kernel |

The kernel statements evaluate GW and the intertwining identity on actual
vectors. The zero-mode equivalence includes the zero vector and asserts no
existence of a nonzero mode. There is no finite-dimensionality, Hilbert
completion, positivity, spectral gap, index, or primitive complex scalar
assumption in this real consumer.

## C. Actual derivatives of normalized overlaps

Owner:
`lean/InfoGeometry/QuantumGeometry/Projective/NormalizedOverlapDifferential.lean`.
Namespace: the existing `InfoGeometry.QuantumGeometry.Projective`.

Let `H` be a complex inner product space with its normed additive group.
Real-parameter calculus uses `NormedSpace ℝ H`. Completeness and finite
dimension are unnecessary. The existing `NormalizedState H` stores `u : H`
and `⟪u,u⟫_ℂ = 1`; the inner product is conjugate-linear in its first slot.
Use the native continuous linear maps

\[
P_u=\operatorname{rankOne}_{\mathbb C}(u,u),\qquad Q_u=1-P_u.
\]

For normalized curves with vector derivatives `u'`, `v'` at `t`, let
`z(t) = ⟪u(t),v(t)⟫_ℂ`. The main theorem is a genuine `HasDerivAt` statement:

\[
z'=(\langle v,v'\rangle-\langle u,u'\rangle)z
  +\langle Q_u u',v\rangle+\langle u,Q_v v'\rangle.
\]

Normalization is differentiated to derive
`⟪u',u⟫ = -⟪u,u'⟫`; it is not a hidden tangent assumption in the main result.

| Declaration | Exact content |
|---|---|
| `projOrth_eq_complement_rankOne_apply` | The owned horizontal vector equals the native complementary operator applied to its velocity. |
| `overlap_tangent_split` | Algebraic split with the left tangent condition explicit. |
| `normalizedState_derivative_inner_eq_neg` | Derives the tangent condition from normalization and derivative uniqueness. |
| `hasDerivAt_overlap_horizontal_split` | The displayed actual curve derivative. |
| `logarithmic_overlap_derivative_split` | The quotient formula `z'/z`, assuming `z ≠ 0`. |
| `hasDerivAt_overlap_projOrth_split` | Operator-generated velocities use the existing `projOrth` directly. |

Only complex scalar coefficients are normalized commutatively. The ray
operators retain their specified arguments. The undivided derivative is valid
at zero overlap; only the quotient excludes it. There is no claim about a
global branch of `Complex.log`, a field-theoretic current, or an anomaly.

## Dependency order and interpretation boundary

The formal dependency chains are:

1. First involution → exact defect → GW equivalence → two-involution GW.
2. Two involutions → intertwining → existing projector intertwiners.
3. The real core square laws → actual endomorphism GW and intertwining →
   kernel invariance.
4. Differentiable normalization → tangent identity; native rank-one action
   plus that identity → overlap split; native inner-product differentiation
   → `HasDerivAt`; nonzero overlap → quotient identity.

The ring and Hilbert-space lanes have different carriers. This PR does not
identify them as one physical system. The source audit records why the intake's
current labels, curvature criterion, determinant ranks, locality assertion,
insertion sign, and large-mass conclusion require correction.

Remaining work is explicit: construct spectral signs on the specified gap
domain; prove locality with quantitative hypotheses; build equal-rank Slater
overlaps and genuine determinant lines; establish phase/gauge transformation
laws and measure integrability; prove any index, anomaly coefficient, or
continuum-limit statement on the relevant owners. A conceptual causal poset
does not supply these missing implications.

## Validation contract

The patch adds 20 theorem declarations and two definitions in three focused
owners. Independent source review checked the signs, multiplication order,
kernel arguments, differentiation rules, conjugation, and pinned Mathlib APIs.
This is distinct from native acceptance.

The focused workflow uses the unchanged maintained
`tools/quality/check_clifford_dirac.py` with all three owners as explicit
`--target` arguments, exact pinned Mathlib, and the shared build lock. It checks
the repository import closure, compiles fresh selected sources, and recursively
audits every owned declaration, permitting only `propext`, `Classical.choice`,
and `Quot.sound`. An additional gate requires zero warnings in the selected
owners. The selected semantic audit must have complete requested file coverage.
Evidence includes the source revision, source hashes, per-module logs, audit
source and result, report, and evidence hashes.

Tracked pre-commit and pre-push gates have distinct scopes. Their presence is
not a passed check. A queued job or a shared-lock wait is not kernel evidence.
Any unavailable root Lake dependency is reported separately; the focused
closure is not represented as a successful root build. No proof holes,
custom axioms, unsafe/native proof bypasses, pin changes, or checker relaxations
are introduced.

### Observed source checks on 17 November 2026

- The installed staged proof gate passed on the complete patch.
- The strict three-owner scan found no proof holes, custom axioms, unsafe or
  native proof bypasses, or literal `True` proof wrappers.
- The selected semantic gate passed with complete 3/3 selected/read coverage
  and zero blocking or review findings.
- YAML, all workflow shell blocks, and all four embedded Python blocks parsed
  successfully. Independent review matched the actual checker report schemas.
- The recomputed closure contains 13 repository modules and 10 native import
  roots. All ten inherited owner files match the upstream base byte for byte.
  Trigger paths cover that closure, all three changed aggregators, pins, and
  the lock/audit helpers. The aggregators are not extra compilation targets.
- Native compilation and the recursive axiom report remain pending. The
  shared lock was observed held by an existing check. No lock or cache was
  removed and no checker, pin, or gate was relaxed.

Completed source-gate commands:

```bash
python3 tools/quality/proof_proxy_staged_gate.py
python3 tools/quality/semantic_content_audit.py \
  --module-prefix InfoGeometry.OperatorAlgebra.OverlapDiracFromInvolutions \
  --module-prefix InfoGeometry.Quantum.InvolutionCoreOverlapDirac \
  --module-prefix InfoGeometry.QuantumGeometry.Projective.NormalizedOverlapDifferential \
  --include-review --gate
```
