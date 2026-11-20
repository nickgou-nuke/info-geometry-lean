# Contact grading, curvature detection, and the supplied dependency graph

## Intake and provenance

Source: user-supplied SOLVE/COAGULA text, 2026-11-16, beginning “PHASE 0 —
SOLVE: ELENCTIC DISSOLUTION INTO IRREDUCIBLE PRIMITIVES” and ending with a
claimed unique “5-Graded Cartan Epistemic Gauge Synthesis”. The text mixes
explicit matrix formulas, differential geometry, a fifteen-node directed
graph, and psychological/philosophical interpretation. The latter is
interpretation, not a mathematical premise or a diagnosis.

The exact mathematical intake retained here is:

- H = diag(1,0,0,-1); U1 = E12+E34; U2 = E13-E24; V1,V2 are their transposes.
- A symplectic Lie algebra on a real 1+2+1 dimensional decomposition, with
  claimed homogeneous dimensions 1,2,4,2,1.
- [U1,U2] = -2 E14, [V1,V2] = 2 E41, same-sign degree-three truncation,
  and opposite-grade bracket back into degree zero.
- Curvature F = dA + (1/2)[A,A], covariant square ad(F), Maurer–Cartan
  flatness, and Bianchi identity.
- The supplied fifteen nodes and exactly their listed predecessor edges,
  the asserted rank values 0 through 6, terminal join, and claimed uniqueness.
- The source further claims that nonzero curvature forces a nonzero adjoint
  square, flatness destroys information, mixed brackets force harmonic
  curvature, a nonzero obstruction colimit follows, and five-grade closure
  uniquely requires this sp(4) model. These are not silently adopted.

Matrix indices in Lean start at zero. E14 in the intake is `Matrix.single 0 3 1`.

Base revision: `08c34e03f610b452e03422037949196dc7d92d6d` of
`nickgou-nuke/info-geometry-lean`, independently confirmed against GitHub main.
Pins: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
No dependency changes are part of this work.

## Source-grounded owner search

Search covered canonical `lean/InfoGeometry` filenames, declarations and
consumers for sp4, symplectic, contact/five grading, Peirce, covariant curvature,
Maurer–Cartan, Bianchi, and causal-poset variants. Relevant owners read:

| Owner | Actual available content and reuse decision |
| --- | --- |
| `Parafermion/TetractysSp4PositiveGrassmannianPoset` | Integer sample symplectic matrices and arithmetic counts. Its own contract explicitly excludes a ten-element basis and dimension theorem. Different symplectic basis. |
| `Canonical/Sp4ParaHyperkahlerPresymplecticBridge` | Specific real matrix membership with another symplectic form; does not supply this contact grading. |
| `Algebra/FiveGradedLieClosure` | Conditional closure interface; closure is a supplied structure field. Do not use it to assume the target. |
| `Algebra/NonAssocDerivation` | Native Lie subalgebra of Leibniz endomorphisms, with proved commutator closure. |
| `Algebra/DerivationLieLane` and `DerivationLieLaneRepresentation` | Faithful derivation action and proved representation/Leibniz laws. |
| `OperatorAlgebra/DerivationDifferentialForms` | Native low-degree CE cochains, constructed differential, square-zero identities, curvature, `covariantDerivative_commutator`, and `connectionCurvature_bianchi`. Reuse rather than duplicate. |
| `OperatorAlgebra/DerivationMatrixGeometry` | Full matrix derivation lane and `matrixInnerLieHom`; use to construct the actual sp4 action. |
| `NCG/CausalPoset` | Zorn-sector identities and a prose dependency order; a different carrier from this finite graph. |
| Mathlib `Algebra/Lie/SkewAdjoint` | Native `skewAdjointMatricesLieSubalgebra`; use for the actual carrier. |
| Mathlib `Data/Matrix/Basis` | Scalar-center characterization; use to prove faithfulness of the concrete inner action. |

This is a bounded source search, not a claim about every historical/archive
file. The categorical infrastructure map was consulted. No categorical
colimit or analytic completion is claimed. No graph-service freshness is
asserted; the dependency evidence is the inspected imports and declarations.

## Exact contracts and dependency order

1. **Concrete symplectic algebra.** In `Matrix (Fin 4) (Fin 4) ℝ`, use
   Ω = [[0,0,0,1],[0,0,-1,0],[0,1,0,0],[-1,0,0,0]]. Construct the native
   skew-adjoint Lie subalgebra, explicit ten-coordinate linear equivalence,
   actual finrank, basis elements and nonzero commutators.
2. **Contact grading.** Construct homogeneous submodules for ad(H), prove
   additive bracket degree, five-component decomposition and dimensions,
   vanishing outside degrees -2 through 2, and same-sign two-step nilpotency.
   Construct the native `GradedLieAlgebra` instance and prove zero radical of
   both degree-one bracket pairings, supplying the contact nondegeneracy.
3. **Curvature action.** Reuse the existing CE owners. Prove the exact
   centrality criterion for vanishing adjoint curvature. Construct the
   faithful sp4 action on the full matrix algebra and its scaled-inclusion
   connection; compute its curvature, flat/nonflat parameters, and Bianchi.
   Also construct a central-valued full-matrix connection with nonzero
   curvature and identically zero adjoint curvature action.
4. **Supplied finite graph.** Construct a native partial order from exactly
   the supplied edges. Prove reachability/cover correspondence, strict-height
   acyclicity, bottom/top and the specified terminal join. Prove that it has
   no cover rank and that the thesis/shadow pair has no least upper bound.
   These graph facts do not make its labels into implication theorems.

Items 1 → 2 and 1 + existing matrix derivations + CE calculus → 3 are actual
mathematical dependencies. Item 4 is an independent audit of the supplied
diagram. It is not used as evidence for 1–3.

## Corrections and excluded inferences

| Intake assertion | Corrected scope |
| --- | --- |
| [Z,W] = H for Z=-2E14,W=2E41 | [Z,W]=-4H. The unscaled E14,E41 bracket is H. |
| Five-grade closure iff two-step nilpotency and Jacobi, uniquely sp4 | The explicit sp4 realization is sufficient. Nilpotency/Jacobi alone neither classify the full algebra nor force this dimension. |
| F≠0 implies ad(F)≠0 | Vanishing adjoint action means central curvature. For the constructed sp4 matrix coefficients, centrality forces zero; this needs proof. |
| Covariant nilpotency equivalent to projector idempotence | Distinct typed equations. No map relating them is supplied. |
| Mixed bracket automatically gives harmonic curvature | A bracket is a curvature contribution; differential terms can cancel it. Harmonic curvature requires a defined cohomological projection and hypotheses. |
| Flatness annihilates transport/information | Local pure gauge does not imply trivial global holonomy on a nonsimply connected base, nor a general claim about information. |
| Nonzero F forces nonidentity holonomy for the chosen loop | Loop and surface hypotheses, integration and ordering are missing; no such theorem is asserted. |
| Nonzero finite obstruction implies nonzero L-infinity colimit | No directed system, maps, higher brackets or universal property are supplied. |
| Supplied graph is graded and provides unique synthesis | Its height strictly increases, but covers admit unequal-length paths. A selected terminal join is a property of the defined graph. |

The algebraic connection here is a derivation-based CE connection. It does not
construct a principal bundle, manifold Cartan connection, analytic holonomy,
Tanaka prolongation classification, Kostant harmonic projection or L-infinity
colimit. Those require separate theorem contracts.

## Constructed connection examples and conventions

The direction algebra is the actual `Sp` carrier, acting on the full matrix
coefficient algebra by `X(a) = Xa-aX`. The generic CE connection owner uses
`F(X,Y) = X(Γ(Y))-Y(Γ(X))-Γ([X,Y])+[Γ(X),Γ(Y)]`.
For `Γ_c(X)=cX`, the constructed proofs give

```text
∇^(c)_X(a) = (c+1)[X,a]
F_c(X,Y) = c(c+1)[X,Y]
F_c = 0 ↔ c=0 or c=-1.
```

In particular, the negative inclusion has noncommuting connection values but
cancels the background action: its total covariant derivative is zero. This
example makes no claim of nontrivial transport. The positive inclusion has
nonzero curvature. Both satisfy the existing proved Bianchi identity.

A second connection is `Γ(X)=λ(X)I`, with `λ(X)=X₀₀`. Its curvature is
`F(X,Y)=-λ([X,Y])I`, so `F(zPlus,zMinus)=-I` although its adjoint action
vanishes on every matrix coefficient. This connection is deliberately valued
in the full matrix algebra; it is not sp4-valued. For curvature in the sp4
subalgebra, the proved scalar-center calculation gives the stronger exact
detection criterion on all full-matrix observables.

Machine-readable source bindings and the navigation-only discovery receipt
are in `docs/contracts/sp4-contact-curvature.json` and
`docs/contracts/sp4-contact-curvature-discovery.json`. Their validator checks
source hashes and declaration headers, not the truth of the interpretation.

## Verification and review plan

Use the unchanged `tools/quality/check_clifford_dirac.py` with explicit targets,
the pinned runtime, fresh task-specific outputs and the shared build lock.
It compiles the exact repository import closure and audits declarations with
the unchanged native audit generator. Run staged proof-integrity, whitespace,
placeholder, static refutation and semantic-vacuity checks. Independent
mathematical/source audit and separate execution QA will inspect the final
source. Record exact commands, outcomes, source hashes and remaining limits
below after execution; pending checks are not evidence of success.

## Recorded acceptance evidence

Parent native verification passed on the five new owner modules and their
eleven-module repository import closure with Lean 4.34.1 and the unchanged
Mathlib revision above. The five new owners have zero compiler warnings.
The native all-declaration audit includes private/generated declarations:

| New owner | Audited declarations |
| --- | ---: |
| `Algebra.Sp4Contact` | 70 |
| `Algebra.Sp4ContactGrading` | 55 |
| `OperatorAlgebra.DerivationCurvatureDetection` | 3 |
| `OperatorAlgebra.Sp4ContactConnection` | 35 |
| `Order.ContactDependencyPoset` | 95 |
| Total | 258 |

Only `propext`, `Classical.choice`, and `Quot.sound` occur in those declaration
dependencies. No source or dependency pin was changed to achieve compilation.

Independent A-A source review passed on the frozen source hashes below. The
reviewer authored no proof source and ran no Lean compilation. The reviewer
checked the concrete carrier, noncommutativity witnesses, coordinate and
grading proofs, curvature convention, graph reachability, source/index
identity, and source-bound contract metadata.

| File | SHA-256 |
| --- | --- |
| `Sp4Contact.lean` | `b6bdfdfbc2d604334df15290dd3b371a89c0e4900764eac7800aed09994ca470` |
| `Sp4ContactGrading.lean` | `c311407b17ba334ff6533e81571d0f87026ef408cdaeaecc11a099dfe3b8005b` |
| `DerivationCurvatureDetection.lean` | `ae373233de57fc1359c78fb5c52b628c1110ec14db254ca873053f23e2863105` |
| `Sp4ContactConnection.lean` | `bd6e7bc8e795fec24f0a56fbd180535c24eca92dff10dd8ce5342ab72c51b75e` |
| `ContactDependencyPoset.lean` | `0dbc1be4ad2cbdd1292698ee37734c8a87ad35d5bdfa6d1fb8e0d8013f38c396` |

Staged proof-integrity, whitespace, strict OpenGauss refutation, semantic
vacuity with `--fail-on error`, and strict placeholder checks passed. The
refutation report has zero traps. The semantic-vacuity checker reports eight
nonblocking API-unfolding/corollary warnings; the placeholder checker reports
five soft findings concerning legitimate generic section hypotheses, a direct
corollary and finite `decide` proofs. The independent source reviewer inspected
all these findings and found no vacuous headline theorem, concealed target
assumption, or proof hole. These heuristic checks are not kernel evidence.

Independent QA-A then rebuilt the eleven-module source closure in a fresh
output directory without incremental reuse and repeated the all-declaration
audit: PASS, all 258 declarations covered, the same three standard axioms,
and zero warnings in every new owner. The unchanged imported owners emit
thirteen pre-existing linter warnings (one in `DerivationLieLane`, three in
`DerivationLieLaneRepresentation`, nine in `DerivationDifferentialForms`).
The independent verifier checked the five source hashes against this record
and the parent's report. The QA agent authored no proof source and modified
no gates, dependency pins or toolchain.

The native check is reproducible with the unchanged repository runner:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /path/to/pinned/mathlib-4.34.1 \
  --lean /path/to/lean-4.34.1/bin/lean \
  --output /path/to/fresh/check-output \
  --target InfoGeometry.Algebra.Sp4Contact \
  --target InfoGeometry.Algebra.Sp4ContactGrading \
  --target InfoGeometry.OperatorAlgebra.DerivationCurvatureDetection \
  --target InfoGeometry.OperatorAlgebra.Sp4ContactConnection \
  --target InfoGeometry.Order.ContactDependencyPoset
```

This is scoped native acceptance. It does not assert that the root Lake or
repository publication gate passed.
