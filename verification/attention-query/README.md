# Query attention, neutral evaluation, and a prescribed spiral

## Status

This is a source-reviewed implementation draft. The new Lean files have **not
yet been compiled** and no declaration-axiom result has been obtained. Static
source checks are not a kernel certificate.

The requested locked owner build was queued behind other verification work
holding `/tmp/info-geometry-build.lock`. Our waiting command was interrupted
with exit 130 before it acquired the lock or started Lake. A subsequent
nonblocking source-closure verification attempt on 2026-11-25 exited with
`BuildLockBusyError` while `dirac-plabic-coarse:2` held the lock. No compiler or
native declaration audit ran in either attempt.

Independent semantic review and a separate source-level verification review
completed. Strict source refutation, the static GATE_4 review, the staged proof
gate, and whitespace checks passed. GATE_4 explicitly returned
`STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED`. The root Lake build and publication
build gate have not passed. These results support publication as a reviewable
draft, not acceptance as verified mathematics. Existing verification processes,
lock rules, dependency pins, and caches were preserved.

## Source owners

| Module | Content |
|---|---|
| `InfoGeometry.Canonical.AttentionQueryGeometry` | Real continuous-dual query model, actual Fréchet first derivative, actual log-probability derivative, second line derivative, Fisher covariance, and exact null-direction criterion. |
| `InfoGeometry.Canonical.AttentionQueryKeyReversal` | Existing neutral summand inclusions connected to rectangular matrix logits; transpose and rank bound; row/column normalization; a symmetric rank-at-most-one score matrix whose softmax has rank two. |
| `InfoGeometry.Rotary.RotaryAttentionFlow` | Actual differential equation, composition and inverse of the existing prescribed spiral; normalization by a boosted null coordinate; an anisotropic counterexample. |

There are 41 proposed public theorem declarations across these owners. That
count is a source inventory, not a count of kernel-verified theorems.

## Exact mathematics represented by the draft

For a real normed space `E`, nonempty finite keys `K_j : E →L[ℝ] ℝ`, and
inverse temperature `β`, put

\[
s_j(q)=\beta K_j(q),\qquad
\Phi_\beta(q)=\log\sum_j e^{s_j(q)},\qquad
p_j(q)=\frac{e^{s_j(q)}}{\sum_l e^{s_l(q)}}.
\]

The target Fréchet derivative and line curvature are

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
`F(t)=exp(κt) R(ωt)`, and targets

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
imports, or lock rules are replaced by this checker.

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

An isolated source-closure pass, once actually obtained, must be reported
separately from a root Lake build. No whole-repository build claim is intended.
