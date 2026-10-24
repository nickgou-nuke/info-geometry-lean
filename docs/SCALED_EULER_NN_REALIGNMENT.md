# Scaled Euler-mode NN criterion

The existing `Arithmetic.SelfConcordantZetaBarrierProofs` proves failure of
the constant-two NN bound for the unscaled convex Euler-mode slots. Its
negative-Massieu-sign obstruction is separate and remains valid.

The proposed replacement in `Arithmetic.ScaledEulerNN` reuses `NNBoundSq`.
For E>0, 0<q<1, c>0, it asserts that scaling both derivative slots by c
satisfies NN exactly when `(1+q)^2 ≤ 4*c*q`. On a nonempty cutoff interval
`0<q₀≤q<1`, the exact uniform scale condition is
`(1+q₀)^2/(4*q₀) ≤ c`. Necessity follows at the left endpoint, with explicit
`q₀<1` excluding an empty interval. No full-function derivative theorem,
infinite Euler-product assertion, or zeta barrier certificate follows.

Source grounding: the maintained Lean search for `NNBoundSq` and scaled Euler
criteria led to the existing arithmetic owner; its references include
`AllExhaustive`. Related canonical barrier owners explicitly use formal
derivative slots. This is a bounded source search, not an absence certificate
for every archive or external reference in the all-folder inventory.

Independent mathematical contract and source reviews passed. Initial locked
build 48877 returned one rational-normalization proof error; clearing the
nonzero denominator repaired it. The audit build then passed (session 95640,
terminal exit 0, 3095 jobs). All six axiom reports use exactly `propext`,
`Classical.choice`, `Quot.sound`.

`ScaledEulerNNAudit` covers four new and two existing theorem heads, plus an
exact `q=1/2, c=9/8` equality example and the unscaled failure at `q=1/2`.
An unreachable trailing tactic was removed after that build. The cleaned
source passed parent replay in session 1283 (terminal exit 0, 8979 combined
jobs), log `/tmp/shear-euler-krein-build.log`. Independent QA accepted the
scope in session 69457 (terminal exit 0, 8980 combined jobs), with six
standard-axiom-only Euler reports, both examples compiled, and no scoped
warnings. Log: `/tmp/shear-euler-krein-final-qa.log`. Strict screening emitted
three unused-hypothesis flags for hE, hq, hc; independent source review checked
that `positivity` uses those hypotheses implicitly and classified them as false
positives. Scoped diffs and hole checks passed.
Initial evidence log: `/tmp/scaled-euler-nn-audit.log`.
This is a scoped algebraic result, not an
exhaustive repository certificate.
