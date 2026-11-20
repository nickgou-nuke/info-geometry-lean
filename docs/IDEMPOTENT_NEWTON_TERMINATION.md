# Finite Newton correction of a noncommutative idempotency defect

## Intake and theorem contract

Source: user attachment `Pasted text(20261116-140901).txt`, received 2026-11-16.
SHA-256: `4ff46518b5d98b9308522f99b9f4c805cdd8bf6cef944b0f4c81f860a081e82c`.
The original attachment is retained with the task intake. This document records
its mathematical content and corrections; the psychological interpretation is
not a theorem hypothesis or conclusion.

Base revision: `08c34e03f610b452e03422037949196dc7d92d6d`.
Canonical owner: `lean/InfoGeometry/Core/IdempotentDefectIteration.lean`.
Namespace: `InfoGeometry.Core.IdempotentGraphGrassmannian`.

The carrier is an arbitrary unital associative ring `B`. Its multiplication
need not commute, its characteristic is unrestricted, and there is no finite
dimension, topology, norm, adjoint, or scalar diagonalization assumption.
The existing definitions are

\[
\delta(x)=x^2-x,\qquad N(x)=3x^2-2x^3.
\]

The task extends the already proved one-step factorization

\[
\delta(N(x))=\delta(x)^2(4\delta(x)-3)
\]

to finite termination:

\[
\delta(x)^m=0,\quad m\le 2^n
\quad\Longrightarrow\quad
N^{[n]}(x)^2=N^{[n]}(x).
\]

All later iterates equal this idempotent. Ring homomorphisms and ordered
intertwining relations transport the actual iteration, so this construction
also gives an explicit lift of an idempotent image when the initial defect
satisfies the stated nilpotence bound.

The notes do not specify a correction recurrence. The recurrence here is the
repository's existing Newton polynomial; it is not identified with the raw
defect orbit `idempotencyDefect^[n] x`.

## Source-grounded extraction

| Informal motif | Exact object | Existing owner or new result |
|---|---|---|
| Binary cut | `p * p = p`, complement `1 - p` | `Core/PeirceDecomposition.lean` |
| Four relational components | `pxp`, `px(1-p)`, `(1-p)xp`, `(1-p)x(1-p)` | `peirce_decomposition`, `idempotencyDefect_peirce_components` |
| Ordered round trips | `bc` and `cb` on different corners | `OperatorAlgebra/PeirceCoupling/Algebra.lean` |
| Symmetric and directed coupling | `bc + cb` and `bc - cb` | `reflection_mul_jordan`, `jordan_eq_zero_iff_products_eq_zero` |
| Spectral correspondence | Explicit equivalence of partner eigenspaces for nonzero eigenvalues | `PartnerEigenspaces.nonzeroEigenspaceEquiv`; generalized version in `PartnerGeneralizedEigenspaces.lean` |
| Failure of idempotency | `delta(x) = x*x - x` | `Core/IdempotentGraphGrassmannian.lean` |
| Repeated defect extraction | Finite iterates of `delta` | Existing `Core/IdempotentDefectIteration.lean` |
| Corrective recursion | Iterates of the existing `newtonPeirceStep` | New finite termination, stationarity, and transport theorems |

The source search covered canonical `lean/`, the separate `src/` lane, direct
consumers, and the pinned Mathlib idempotent/nilpotent interfaces. Searches for
Newton/Peirce, nilpotent correction, and dyadic defect powers found the existing
one-step identity but no all-depth termination theorem for this iteration.
This is a bounded source search, not a claim of mathematical novelty.

Mathlib's `Mathlib/RingTheory/Idempotents.lean` already proves idempotent lifting
along nil ideals, including `isIdempotentElem_one_sub_one_sub_pow_pow` and
`exists_isIdempotentElem_eq_of_ker_isNilpotent`. The new result supplies an exact
iteration bound and transport laws for this repository's chosen cubic
correction. It does not claim to introduce idempotent lifting itself.

## Proved dependency order

1. The existing polynomial defect and Newton step.
2. The existing one-step factorization.
3. Local commutation of the two polynomials in the same defect, allowing native
   `Commute.mul_pow`; this does not assume that `B` is commutative.
4. Exact factorization of every natural power of the corrected defect.
5. Induction on the number of corrections, using the exponent `2^n`.
6. Idempotency and stabilization under the nilpotence bound.
7. Ring-homomorphism naturality and ordered intertwining, followed by the
   explicit lifting theorem.

This is the proof dependency order. It does not assert a physical causal
relation between the interpretive labels in the notes.

## Necessary corrections to the source

An idempotent cut has zero defect by definition. A nonzero defect belongs to a
different, arbitrary operator being decomposed. For its blocks `a,b,c,d`, full
idempotency is equivalent to the four ordered equations

\[
a^2+bc=a,\quad ab+bd=b,\quad ca+dc=c,\quad cb+d^2=d.
\]

Nonzero round trips do not prevent full idempotency: the existing
`PeirceDefectMatrixWitness.state_idempotent` and `boundary_metric_value` prove
the rational rank-one matrix example with nonzero coupling. Conversely, zero
quadratic coupling does not force a zero off-diagonal current, as the same
owner's one-sided example proves.

Raw defect iteration is not a correction algorithm. The existing
`PeirceDefectNoncollapse.algebraic_metric_without_eventual_vanishing` supplies
noncommuting corner seeds whose metric is `2 I`, a nonzero fixed point of the
defect map. Nilpotence in the new theorem is an explicit sufficient hypothesis;
algebraicity alone cannot replace it.

Skew-adjointness alone does not imply a half-turn identity for an exponential.
The algebraic normalization `omega^3 = -omega` would imply that `-omega^2` is an
idempotent supported on the active part, but identifying a polynomial half turn
with an analytic exponential requires a separate analytic proof. A Spin
representation and covering map are further data. None is supplied by the new
Newton theorems.

A Drazin decomposition permits a nonzero nilpotent remainder. Therefore
`omega * Pcore = omega` is not a consequence of a general Drazin decomposition;
the existing `QuantumContext/DrazinSpectralKernel.lean` distinguishes general
index from the index-one reconstruction law.

Lean's logic can formalize noncommutative rings directly. The defect polynomial
does not quantify semantic truth, psychological states, or statistical
overfitting. The new results concern the stated ring elements and maps.

## Validation and scope

Acceptance requires compilation with the repository's pinned Lean and Mathlib,
axiom inspection, placeholder and semantic checks, an independent semantic
review, and an independent rerun of decisive checks. The audit companion is
`Core/IdempotentDefectIterationAudit.lean`. The new matrix example uses the full
ring `Matrix (Fin 3) (Fin 3) ℤ`, with a nilpotent defect of index three; its first
correction is not idempotent and its second correction is the identity.

No changes are made to dependency pins or the separate `src/` source lane.
Compilation of the selected owners and their import closure does not certify a
whole-repository build. Publication gates and source-closure verification are
reported separately in the task's validation record.


### Observed validation on 2026-11-16

The parent and an independent verifier compiled the selected source closure
with Lean `4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The independent run used fresh
output files and the unchanged repository checker:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/64554963d837/mathlib-4.34.1 \
  --lean /workspace/scratch/64554963d837/lean-runtime/bin/lean \
  --output /workspace/scratch/0b027a897d29/verification-qa \
  --target InfoGeometry.Core.IdempotentDefectIteration \
  --target InfoGeometry.Core.IdempotentNewtonIterationExamples \
  --target InfoGeometry.OperatorAlgebra.PeirceSpine.DefectNoncollapseMatrix
```

This passed for all eleven repository modules in that import closure. Native
axiom inspection covered 66 declarations in the three selected owners,
including 34 in the iteration owner, 16 in the new example, and 16 in the
existing noncollapse regression owner. Only `propext`, `Classical.choice`, and
`Quot.sound` occurred. The command-only audit companion was also compiled
separately under the shared build lock against the same checked dependencies.

The modified iteration owner, new example, and audit companion produced zero
compiler warnings. Two inherited warnings remain in the selected import
closure: an unnecessary sequencing tactic in `PeirceDecomposition` and the
deprecated `Mathlib.Data.Real.Basic` import in `DefectNoncollapseMatrix`.

The staged proof gate, strict source screener, strict refutation checks, and
diff checks passed. Static `GATE_4` returned
`STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED`; the actual kernel checks are the
separate compilations and native axiom audits above.

Two source heuristics were reviewed independently and retained as false
positives: `trivial_surface` on the useful polynomial naturality lemma
`map_newtonPeirceStep`, and `no_hyp_use` on the parameter `k` in
`chain_later_corrections`, where rewrite matching instantiates the generic
stability theorem at that parameter. The semantic gate run with
`--fail-on warning` therefore returned 1; it is not reported as an automated
warning-free pass. Independent semantic review accepted the four-file change.

The canonical locked-file wrapper was also attempted with the pinned Lake
executable. It failed during root-package dependency resolution because
`external_refs/homotopy-hypothesis-lean4` is absent. This is an observed
root-package blocker, not a Lean proof failure in the checked source closure.
No dependency pins, gate scripts, or theorem hypotheses were changed to avoid
that blocker. Publication still requires the repository's pre-push gate.
