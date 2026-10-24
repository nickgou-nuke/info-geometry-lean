# Complex-time closed-strip bound v2: native-import adaptation

Source-only, uncompiled. No live edits or builds. Independent Popper AA and
serialized QA remain separate from this import-delta review.

## Frozen inputs and exact change

Original Kepler source: `scratch/ComplexTimeStripBound20261024.lean`, SHA256
`a08cf10bd172bf7b8193359452c07c8e3fe818e4cba320a42c50bf3ac4cbee79`.
Original contract: `scratch/ComplexTimeStripBound20261024.md`, SHA256
`613bab90002573f99171427ba88d5e1324cebe319191492444738b051a5c0602`.
Parent reports Popper semantic AA of that candidate.

The ONLY source change in v2 is replacing
`import scratch.ComplexTimeConjugation20261024` with
`import InfoGeometry.OperatorAlgebra.ComplexTimeConjugation`.
Other imports, comments, five theorem statements, hypotheses and proof bodies
are byte-for-byte preserved. The uncompiled/pending-QA comment is retained;
parent reports native dependency QA running, not an acceptance receipt here.

Native dependency read SHA256:
`5ac781530aed13fdd016a60550f87740838adb7552888ac907cf9b806f8140b9`.
Its promotion from reviewed ComplexTime v2 changed comments only. The consumed
alpha definition and alpha_analyticAt, alpha_ofReal_eq_unitary and alpha_add
have the same namespace and mathematical contracts expected by this consumer.

## Unchanged mathematical contract

For an existing CStarAlgebra A, self-adjoint G, arbitrary continuous complex
linear functional φ, X,Y:A, and real β with 0≤β, derive

    ∃ M:ℝ, 0≤M ∧ ∀ z:ℂ, 0≤z.im → z.im≤β →
      ‖φ (Y * alpha (G:A) z X)‖ ≤ M.

The five existing lemmas establish imaginary-axis continuity, real-time norm
preservation, equality of orbit norm with its imaginary-axis value, compact
interval norm boundedness, and the scalar bound. The constant is
‖φ‖*(‖Y‖*C), with nonnegativity derived. β=0 is included. No positivity,
normalization, faithfulness or traciality of φ is assumed. No new carrier,
state, orbit, package, budget or transparency setting is introduced.

## Delta review and scope

Source comparison confirms only the dependency import changes. The proof chain
still uses entire-orbit continuity, native unitary conjugation isometry,
compactness of [0,β], then operator norm and submultiplicativity. No real-time
bound is assumed, and no complex-time star-automorphism claim is needed.

This is a source delta review by the adaptation author, not a replacement for
independent Popper AA or a kernel receipt. The original contract's concrete
consumer limitations remain: no represented finite-seed specialization, scalar
KMS boundary, positivity theorem, unbounded generator or growing family is
established by this file. Both original files remain unchanged.
