# Query attention, neutral evaluation, and a prescribed spiral

## Verification status — 2026-11-25

The four mathematical owners contain **53 compiled public theorems**. Their
actual **19-module repository import closure** was compiled from the exact
sources under the unchanged Lean 4.34.1 / Mathlib pins below. All four owners
compiled with warnings treated as errors and produced no diagnostics.

A fresh native declaration audit passed for **93 owned declarations**:
23 query-geometry, 13 Gibbs-duality, 38 query/key, and 19 rotary-flow declarations.
This covers definitions and private/generated declarations as well as the
named public theorems. Transitive axiom dependencies are restricted to
`propext`, `Classical.choice`, and `Quot.sound`. The independent reconciler
checked complete owner coverage, declaration counts, and the exact axiom union.

Current local evidence:

- [Exact-source local validation and provenance](evidence/extension-local-validation.json).
- [Complete 93-declaration native audit](evidence/extension-declaration-audit.jsonl).
- [Independent semantic review of the final source hashes](evidence/extension-semantic-review.md).

The local compilation occurred across preserved development runs. Eleven
unchanged dependency receipts are explicitly labeled post-run snapshots of
successful commands; four other dependencies have recorded before/after
compilation receipts. The current audit checked the complete final artifact
chain before and after execution. No failed run is relabeled as a complete
successful run. Three unchanged dependencies emit existing deprecation or
unused-section-variable warnings; the four audited owners emit none.

The scoped workflow `.github/workflows/attention-query-geometry.yml` provides
the fresh full-closure reproduction: independent checkouts, all 19 source
compilations, strict four-owner checks, and the complete native audit. It
uploads its source copies, compiler logs, and exact receipts for independent
QA against the published PR source. Read its result for the current PR commit;
the local readiness result does not substitute for that fresh CI acceptance.

The original three-owner evidence in `evidence/local-validation.json` and
`evidence/local-declaration-audit.jsonl` is preserved as historical evidence for
snapshot `a03c5bf1653d10ef87c102aa11013f87d16e46b3` (41 public theorems and 76
owned declarations). It does not certify the Gibbs/RoPE extension.

These are scoped source/kernel checks, separate from root Lake workspace and
publication routing checks. No whole-repository build certificate is claimed.
Dependency pins, unchanged repository owners, and shared-lock/cache rules are
preserved.

The maintained locked root build was also attempted for the four explicit
owners. Lake exited with code 1 while loading the existing `HomotopyHypothesis`
path package, whose directory `external_refs/homotopy-hypothesis-lean4` is
absent in this checkout. It did not reach those target compilations. The
separate exact-pin source-closure result above remains the relevant local
kernel check.

## Source owners

| Module | Content |
|---|---|
| `InfoGeometry.Canonical.AttentionQueryGeometry` | Real continuous-dual query model, actual Fréchet first derivative, actual log-probability derivative, second line derivative, Fisher covariance, and exact null-direction criterion. |
| `InfoGeometry.Canonical.AttentionQueryGibbsDuality` | Existing finite Gibbs model specialized to query logits; exact relative-entropy gap, variational upper bound, unique positive-simplex maximizer, and attained Massieu–entropy identity. |
| `InfoGeometry.Canonical.AttentionQueryKeyReversal` | Existing neutral summand inclusions connected to rectangular matrix logits; transpose and rank bound; row/column normalization; a symmetric rank-at-most-one score matrix whose softmax has rank two. |
| `InfoGeometry.Rotary.RotaryAttentionFlow` | Real-position rotor transpose, relative rotated scores and common-shift invariance; actual differential equation, composition and inverse of the existing prescribed spiral; normalization by a boosted null coordinate; an anisotropic counterexample. |

The 53 named public theorems comprise 11 query-geometry, 8 Gibbs-duality,
21 query/key, and 13 rotary-flow results. The native audit includes these
within the 93 total owned declarations.

## Mathematical scope

For a real normed space `E`, nonempty finite keys `K_j : E →L[ℝ] ℝ`, and
inverse temperature `β`, put

\[
s_j(q)=\beta K_j(q),\qquad
\Phi_\beta(q)=\log\sum_j e^{s_j(q)},\qquad
p_j(q)=\frac{e^{s_j(q)}}{\sum_l e^{s_l(q)}}.
\]

The Fréchet derivative and line curvature are

\[
D\Phi_\beta(q)=\beta\sum_j p_j(q)K_j,
\]

\[
\left.\frac{d^2}{dt^2}\Phi_\beta(q+tu)\right|_{t=0}
=\beta^2\sum_jp_j(q)\left(K_j(u)-\sum_l p_l(q)K_l(u)\right)^2.
\]

Fisher information is defined using the actual derivative of `log p_j(q+tu)`,
then connected to this curvature. For `β ≠ 0`, its null directions are precisely
the directions on which all keys agree. Positive definiteness needs a
separation condition on key differences.

The derivative is a continuous covector on the query space. A vector gradient
requires an inner-product identification, and an attention output using
arbitrary value vectors is a separate construction.

For strictly positive normalized comparison weights μ, specializing the
existing finite Gibbs model to energy `-β K_j(q)` gives the exact entropy gap

\[
\Phi_\beta(q)-\left(\beta\sum_j\mu_jK_j(q)
  -\sum_j\mu_j\log\mu_j\right)
=D_{\mathrm{KL}}(\mu\Vert p(q)).
\]

Consequently the entropy-regularized expected score is at most the query
potential, with equality precisely at μ = p(q). The maximizer is admissible
because the actual softmax weights are positive and sum to one. This proves
finite entropy variational duality on the positive simplex; it does not assert
the complete extended-real Fenchel conjugate on the closed simplex.

The neutral evaluation bridge uses the existing inclusions into `E ⊕ E*`:

\[
B((q,0),(0,k))=k(q).
\]

For coordinate arrays this gives `L=Q Kᵀ`, with `rank L ≤ d`. Swapping the
families transposes `L`. The sign mirror `(-x,ξ)` is a different operation.
The elementary normalization counterexample is

\[
S=\begin{pmatrix}0&0\\0&1\end{pmatrix},\qquad
\operatorname{rowSoftmax}(S)=
\begin{pmatrix}\frac12&\frac12\\
\frac1{1+e}&\frac e{1+e}\end{pmatrix}.
\]

Its determinant `(e−1)/(2(1+e))` is positive: row softmax neither preserves
the latent rank bound nor generally commutes with transpose.

The flow module uses the existing real matrix
`F(t)=exp(κt) R(ωt)`, and proves

\[
\frac{d}{dt}F(t)x_0=(\kappa I+\omega J)F(t)x_0,
\qquad J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},
\qquad F(-t)F(t)=I.
\]

Its unscaled rotor also obeys, for arbitrary real positions m and n,

\[
R_\omega(m)^\mathsf{T}R_\omega(n)=R_\omega(n-m),\qquad
\langle R_\omega(m)q,R_\omega(n)k\rangle
=\langle q,R_\omega(n-m)k\rangle.
\]

A common position shift preserves this unscaled dot-product score. The
exponential scale in F is not included in that invariance statement.

The direct link from null scaling plus transverse rotation to a planar spiral
is the chart identity, for `u ≠ 0`:

\[
\frac{R(\omega t)z}{e^{\kappa t}u}
=e^{-\kappa t}R(\omega t)\frac zu.
\]

This is an explicit map between the displayed coordinates. A full Lorentz
group action, a Transformer layer recurrence, physical CPT, a plabic planar
embedding, and empirical LLM dialogue dynamics are not constructed here. The
full intake classification is in `THEOREM_CONTRACT.md`.

## Verification commands

The repository pins are unchanged: Lean `v4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

Use the maintained locked root build when the complete root workspace is
available:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.AttentionQueryGeometry \
  InfoGeometry.Canonical.AttentionQueryGibbsDuality \
  InfoGeometry.Canonical.AttentionQueryKeyReversal \
  InfoGeometry.Rotary.RotaryAttentionFlow
```

For a source-closure check using an already provisioned clean checkout of the
same pinned Mathlib, use the included checker. It shares the same build lock,
compiles unchanged repository dependencies in full, applies warnings-as-errors
to the new owners, and runs the native declaration audit. No dependency pins,
imports, or lock rules are replaced by this checker. Each run requires a new,
empty output directory, preventing stale artifacts from shadowing imports.

```bash
python3 verification/attention-query/verify.py \
  --mathlib /absolute/path/to/pinned/mathlib \
  --work /absolute/path/to/separate/verification-output \
  --lake /absolute/path/to/lean-4.34.1/bin/lake \
  --wait
```

This produces `validation.json`, exact source/artifact hashes, compiler logs,
and a declaration audit. `AttentionDeclarationAudit.lean` enumerates all
declarations owned by the four mathematical modules and checks transitive axiom
dependencies. The only permitted foundational axioms are `propext`,
`Classical.choice`, and `Quot.sound`. `review_audit.py` independently reconciles
the resulting JSON log for completeness and consistency.

The isolated source-closure pass is reported separately from a root Lake
build. No whole-repository build claim is intended.
