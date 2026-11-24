# NullIncidence native-diagnostic repair

## Provenance and scope

The original is the exact `Algebra/ZornNullIncidence.lean` owner at commit
`c97caca572514f128e846212ca30f050414dabac`, fetched read-only from GitHub after
the previous `/tmp` checkout became unavailable. Its Git blob is
`dc7660eac51f97149b99c9f1f55975aed5e7fd1e`; its SHA-256 is the diagnostic
receipt's expected
`b6818a42c5c3f6057878438891042eb36fd479d69d3eb3ec433f7eb97e9b24a2`.

The diagnostics are from GitHub Actions run
[45416776463](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45416776463),
job `138525022894`, isolated diagnostic execution
`c73ae23678dd44f398d46c2a8ef7184f`. This diagnostic continuation was
nonaccepting; the full strict suite remained failed.

Candidate SHA-256:
`6696706bfb2db944fd8f8899fc729c17bd417f983b99d6bb7e0884018bf26a37`.

## Every diagnostic in this owner's log

| Original location | Observed diagnostic | Candidate repair |
| --- | --- | --- |
| 95 | `zero_mul` does not match native `mul 0 (conj y)` | Change kernel membership to the explicit `ZornVectorMatrix.zero` before rewriting with the explicit multiplication lemma. |
| 138 | `omega` treats two printed-identical kernel finranks as separate atoms | Name the kernel and range dimensions once, change the goal to that shared kernel dimension, and give all three arithmetic facts explicit types using those same names. |
| 172 | Conjugating the zero equality leaves `x = conj 0` | Change both the hypothesis and resulting target to the explicit Zorn zero before applying `conj_conj` and `conj_zero`. |
| 130, 144, 167, 185 | Proposition proofs should use `let`, not `letI` | Replace each reported `letI` with `let`, retaining the identical finite-dimensional instance proof. |

The rank-nullity equality is now produced by
`(LinearMap.finrank_range_add_finrank_ker ...).trans zorn_finrank` at the
explicit expected type `rangeDim + kernelDim = 8`. Thus `omega` receives
exactly the two shared natural-number dimensions in the goal and hypotheses.
The proof still uses both null-subspace dimension bounds and the genuine
eight-dimensional carrier theorem.

## Native source evidence

The exact repository carrier source assigns `zero := zero` in its
`AddCommGroup (ZornVectorMatrix R)` instance at lines 488–500. Consequently
the `change` steps normalize definitionally equal presentations of zero;
they introduce no new assumption or equality axiom. The explicit
`ZornVectorMatrix.conj_zero` and `zero_mul` theorems retain their existing
statements and are reused directly.

Pinned Mathlib at `d13f23b723b8a846827a245b89c10fc7d3f11612` provides:

- `FiniteDimensional.of_finrank_eq_succ`, in
  `Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`, line 143.
- `LinearMap.finrank_range_add_finrank_ker`, in
  `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`, line 173; its order is
  range dimension plus kernel dimension equals source dimension.
- `Submodule.eq_of_le_of_finrank_eq`, in
  `Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`, line 258; the existing
  exactness proof uses its inclusion and equal-dimension hypotheses unchanged.

## Validation boundary

All theorem statements, nonzero hypotheses, null hypotheses, and the two
conjugate-range exactness lemmas' mathematical contracts are preserved.
There are no import, pin, gate, audit, or linter-option changes.

This is a source-reviewed candidate only. The worker ran no Lean compiler,
build, cache download, or test, and made no tracked repository or GitHub
mutation. Native verification and root integration remain pending.
