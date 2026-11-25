# Query attention, neutral evaluation, and a prescribed spiral

## Verification status — 2026-11-25

All three new owners and their actual 12-module repository import closure
**compile successfully** with the unchanged Lean 4.34.1 / Mathlib pins below.
The three new owners were compiled with warnings treated as errors and
produced no diagnostics.

The native declaration audit passed for **76 owned declarations**, including
the 41 public theorems, definitions, and generated declarations. Their
transitive axiom dependencies are restricted to `propext`, `Classical.choice`,
and `Quot.sound`. The independent log reconciler verified complete owner
coverage and consistent declaration counts. The exact source/artifact hashes,
commands, and native results are in [the local receipt](evidence/local-validation.json)
and [the complete declaration audit](evidence/local-declaration-audit.jsonl).

Independent semantic review passed. The focused GitHub workflow
`.github/workflows/attention-query-geometry.yml` repeats the exact-pin
source-closure check and uploads its own receipts, source copies, and logs.
It is separate from the root Lake package: the root/package publication gates
have not passed, and this result is not a whole-repository build certificate.

Earlier attempts were blocked by the shared build lock or incomplete Mathlib
artifacts. A fresh independent checkout of the same pinned Mathlib and
targeted cache retrieval resolved that environment limitation. Actual compiler
diagnostics then guided syntax, API, and linter repairs. No dependency pin,
imported repository owner, lock rule, or theorem conclusion was weakened.

## Source owners

| Module | Content |
|---|---|
| `InfoGeometry.Canonical.AttentionQueryGeometry` | Real continuous-dual query model, actual Fréchet first derivative, actual log-probability derivative, second line derivative, Fisher covariance, and exact null-direction criterion. |
| `InfoGeometry.Canonical.AttentionQueryKeyReversal` | Existing neutral summand inclusions connected to rectangular matrix logits; transpose and rank bound; row/column normalization; a symmetric rank-at-most-one score matrix whose softmax has rank two. |
| `InfoGeometry.Rotary.RotaryAttentionFlow` | Actual differential equation, composition and inverse of the existing prescribed spiral; normalization by a boosted null coordinate; an anisotropic counterexample. |

There are 41 compiled public theorem declarations across these owners:
11 query-geometry, 21 query/key, and 9 flow results. The native audit covers
23, 38, and 15 total declarations respectively, including generated helpers.

## Verified mathematics

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
declarations owned by the three new modules and checks transitive axiom
dependencies. The only permitted foundational axioms are `propext`,
`Classical.choice`, and `Quot.sound`. `review_audit.py` independently reconciles
the resulting JSON log for completeness and consistency.

The isolated source-closure pass is reported separately from a root Lake
build. No whole-repository build claim is intended.
