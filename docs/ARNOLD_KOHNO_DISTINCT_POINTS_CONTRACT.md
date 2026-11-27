# Distinct-point Arnold coefficients and native KZ triangle cancellation

## Provenance and scope

The user supplied Arnold's logarithmic forms and the KZ curvature argument,
requested native Mathlib Lean 4 implementation, and explicitly requested
upstream publication on 2026-11-27. This patch starts from upstream main
`fe24e350b08fdea04f74c0748ef9fd9417c47529` and repairs the existing canonical
owners. It does not depend on the separate, unmerged [four-point draft
PR470](https://github.com/nickgou-nuke/info-geometry-lean/pull/470).

The implemented claim is a scalar coefficient repair followed by a native
exterior-algebra construction and noncommutative, tensor-valued triangle
cancellation. The implementation is algebraic over a field and specializes
to the rationals, reals, and complexes without introducing an imaginary unit.
Its generators are elements of an explicit module; no configuration manifold
or exterior differential is supplied by this construction.

## Why the old coefficient contract excluded the intended examples

The former `LogarithmicOneFormData.partial_fraction` applied to all triples,
including `(i,j,i)`. With skew symmetry and commutative multiplication it gives

\[
0=c_{ij}c_{ji}+c_{ji}c_{ii}+c_{ii}c_{ij}=-c_{ij}^{2}.
\]

Every coefficient is therefore square-zero. If the coefficient ring has no
zero divisors, every coefficient is zero. The audit records both implications
as Lean theorems; no characteristic-zero assumption is needed.

The repaired scalar hypothesis is

\[
c_{ij}c_{jk}+c_{jk}c_{ki}+c_{ki}c_{ij}=0
\quad\text{for pairwise distinct }i,j,k.
\]

The existing all-index form theorem retains its statement. Repeated-index
cases are proved separately by vanishing of the common alternating expression.
Consumers therefore do not acquire new distinctness arguments.

## Mathematical dependency order and actual carriers

All owner paths below are relative to `lean/InfoGeometry/`.

| Stage | Owner and construction | Hypotheses and conclusion |
| --- | --- | --- |
| Reciprocal scalar identity | `Projective/AmplituhedronBostConnesSynthesis.arnold_rational_field_syzygy` | Existing theorem over a field for three unequal coordinate values. Reused directly. |
| Corrected coefficient data | `Canonical/ArnoldCohenBCFWBridge.LogarithmicOneFormData` | Skew coefficients and the partial-fraction identity only at pairwise distinct indices. The original `ℕ` index API remains. |
| Actual reciprocal constructor | `LogarithmicOneFormData.reciprocalDifference` | Takes `dz : ℕ → M`, `z : ℕ → K`, and `Function.Injective z`; constructs `c i j = 1 / (z i - z j)`. |
| Native degree-one forms | `LogarithmicOneFormData.exteriorForm` | Uses `ExteriorAlgebra.ι R (c i j • (dz i - dz j))` in the native `ExteriorAlgebra R M`. |
| Native Arnold identity | `native_arnold_three_term_relation` and `reciprocalDifference_exterior_arnold` | Genuine exterior products of the constructed degree-one forms satisfy the cyclic identity, including separately proved repeated-index cases. |
| Noncommutative triangle | `Canonical/ArnoldKohnoParaKahlerConnection.reciprocalDifference_kohno_triangle_flat` | Reuses `arnold_kohno_triangle_flat` for residues in a native Lie algebra and supplies the constructed Arnold identity. |

Injectivity of `z : ℕ → K` is an explicit assumption. The patch does not assert
that every field admits an injective countably infinite configuration. The
rational witness supplies one. Lean's total inverse defines diagonal scalar
values, but distinctness is required for a nonzero geometric denominator.

The native exterior algebra is not made an instance of the older
`ExteriorFormAlgebra`: multiplication on the entire exterior algebra is not
alternating. Only its degree-one image is used in the native proof.

For cyclic residues `x,y,t`, the two Kohno assumptions are

\[
[x,t+y]=0,\qquad [y,x+t]=0.
\]

They imply equality of the three cyclic brackets. The existing owner factors

\[
[x,y]\otimes(ab)+[y,t]\otimes(bc)+[t,x]\otimes(ca)
=[x,y]\otimes(ab+bc+ca),
\]

which vanishes by the newly constructed native Arnold identity. Pairwise
commutativity of the residues is not assumed.

## Concrete regression and nonvacuity checks

`Canonical/ArnoldKohnoDistinctPointsAudit.lean` records the former-contract
obstruction and exercises the new definitions with `z n = n` over `ℚ`.
The coefficients at `(0,1,2)` are `(-1,-1,1/2)`, and the first is nonzero.

Let `e0,e1` be the native coordinate basis of `Fin 2 → ℚ`, and set
`dz 0 = e0`, `dz 1 = 0`, `dz 2 = -e1`, with all other values zero. The native
forms are `a = -ι(e0)`, `b = -ι(e1)`, and
`c = -(1/2) • (ι(e0) + ι(e1))`. The first product `a*b` is the nonzero blade
`ι(e0)*ι(e1)`. Its nonvanishing reuses the existing
`Canonical.DecomposableBivector` owner and the linear independence of
`Pi.basisFun`, rather than assuming a nonzero exterior carrier.

The residue witness uses actual rational matrices

\[
x=\begin{pmatrix}0&1\\0&0\end{pmatrix},\qquad
y=\begin{pmatrix}0&0\\1&0\end{pmatrix},\qquad t=-x-y.
\]

Their commutator is `diag(1,-1)`, which is nonzero; the audit also proves
`x * y ≠ y * x` explicitly. Both Kohno assumptions hold. The resulting
tensor-valued triangle is zero by application of the
constructed-coordinate theorem. A repeated-index native example also checks
the branch that must not use the distinct-index scalar identity.

The audit checks declarations by actual imported module ownership, including
private and generated declarations, in the two changed owners and the two
directly reused mathematical owners. It additionally checks the named witness
declarations. It rejects introduced axioms, unsafe or partial definitions,
empty owner selections, and transitive axioms other than `propext`,
`Classical.choice`, and `Quot.sound`.

## Compatibility and bounded source review

The active direct consumers of the coefficient-data API found in the reviewed
canonical sources are `ParaKahlerMaurerCartanQGT` and `ArnoldParaKahlerBCFW`.
They use the unchanged form theorem rather than the coefficient field directly.
No additional coefficient constructor or direct `partial_fraction` elimination
was found in the bounded repository Lean-source search. The corresponding
`src/` lane is separate and is not modified or certified by this canonical patch.

The changed owners drop unrelated imports and import the mathematical
dependencies they use. Direct consumers were inspected for dependence on the
removed transitive imports. This source review is distinct from compiling
those consumers or certifying a complete root build.

## Validation and publication record

Validation was performed on 2026-11-27 with the repository's Lean `v4.34.1`
(compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`) and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The Mathlib checkout and all eight
of its dependency revisions matched the root manifest and had no tracked
source modifications. No dependency pin, toolchain, quality gate, or root Lake
configuration is changed.

The exact repository sources were elaborated in dependency order using the
maintained exclusive `/tmp/info-geometry-build.lock`, the pinned compiler,
the existing pinned Mathlib artifacts, and a separate task-owned output
directory. No existing cache was deleted, replaced, or symlinked. Each command
had the form `lean -j1 -R <checkout>/lean <source> -o <task-output>`.

| Check | Observed result |
| --- | --- |
| `AmplituhedronBostConnesSynthesis` | Exact source compiled, exit 0. |
| `ArnoldCohenBCFWBridge` | Exact changed source compiled, exit 0. |
| `ArnoldKohnoParaKahlerConnection` | Exact changed source compiled, exit 0. |
| `DecomposableBivector` | Exact reused source compiled, exit 0. |
| `ArnoldKohnoDistinctPointsAudit` | Entire audit compiled, exit 0; all rational, exterior, repeated-index, and noncommuting-matrix witnesses passed. |
| Transitive kernel axiom audit | Passed for 234 declarations: 65 coefficient-owner declarations, 27 KZ-owner declarations, 2 decomposable-bivector declarations, 87 rational-owner declarations, and 53 witness declarations. Only `propext`, `Classical.choice`, and `Quot.sound` were reported. |
| Final compiler diagnostics | No warnings or errors in the five selected module checks. |
| Actual `.githooks/pre-commit` | Passed after adding the explicit multiplication noncommutativity witness. The earlier screening rejection was resolved in the mathematical source; no gate was changed or disabled. |
| `tools/infra/axiom_audit.py --fail-on-gaps` | Scoped lexical scan passed; no explicit proof holes or custom axioms. |
| `tools/quality/semantic_content_audit.py --gate` | Scoped scan passed with zero findings. |
| `tools/quality/repo_lean_scope_audit.py --fail-on authoritative` | Scoped scan passed with zero debt findings. |
| `tools/quality/semantic_vacuity_gate.py --fail-on error` | Passed at the error threshold. Six warning-level findings were reviewed: the four explicit algebraic structure assumptions, the native form evaluation equation, and the pre-existing conditional commuting-curvature lemma. The reciprocal and noncommuting witnesses establish the intended nontrivial instances. |
| Independent mathematical review | Passed for the corrected index assumptions, repeated-index cases, native carrier, noncommutative instantiation, consumer signatures, and claim boundary. |
| Root dependency preflight / publication gate | Preflight failed: HomotopyHypothesis and Atlas are missing untracked path dependencies; the pinned GIFT gitlink is uninitialized. The tracked InfoGeometryCore dependency passed preflight. A root build and the full publication gate are not certified. |

This is a draft publication under the user's explicit upstream-publication
instruction. Focused kernel success does not turn the failed root dependency
preflight into a passing full gate or establish merge readiness. The `src/`
lane and downstream consumers were not compiled as part of this patch.

Final checked source hashes:

| Changed Lean source | SHA-256 |
| --- | --- |
| `ArnoldCohenBCFWBridge.lean` | `bbbf040d7d9f8ad58591be8ff38fa06e0b3d0bf8980bf6920fc0b210d5be73a7` |
| `ArnoldKohnoParaKahlerConnection.lean` | `60c8b84c44e606c6e9ce1800bad2c3ca1c557f0cd449574291a13d4095cba9af` |
| `ArnoldKohnoDistinctPointsAudit.lean` | `628e07aecb9d3514d3d6345939ae8430415797eb8aae2b45dbc4e9db0a10612e` |

The maintained focused reproduction route is:

```bash
python3 verification/clifford-peirce-walsh/check.py build InfoGeometry.Canonical.ArnoldKohnoDistinctPointsAudit
python3 verification/clifford-peirce-walsh/check.py env lean "$PWD/lean/InfoGeometry/Canonical/ArnoldKohnoDistinctPointsAudit.lean"
```

Focused validation covers the selected source/import closure and the entire
audit file. It does not certify unrelated root dependencies or default targets.

## Literature and remaining implications

This is a standard mathematical construction. Kohno's [local-systems and KZ
paper](https://www.ms.u-tokyo.ac.jp/~kohno/papers/kohno_config.pdf), section 5,
equations (5.2)–(5.4), states the distinct-index infinitesimal braid relations
and logarithmic KZ connection. Bar-Natan and Stoimenow's [*The Fundamental
Theorem of Vassiliev Invariants*](https://arxiv.org/pdf/q-alg/9702009),
proposition 2.5 and equations (2.3)–(2.4), separates differential closedness
from the Arnold/STU three-channel cancellation. Its sections 2.5.2–2.5.4
separately address critical points and knot normalization.

Analytic closedness of the variable forms, a global connection and its exterior
derivative, the complete disjoint/triple curvature decomposition, parallel
transport, and monodromy are not established by this patch. Neither are a
configuration-space de Rham comparison, normalized Kontsevich invariance,
CHY representation, or Feynman-integral evaluation. These require additional
constructions and proofs beyond the finite algebraic triangle.
