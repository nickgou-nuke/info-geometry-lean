# Candidate source-semantic review 08: entry normalization

Reviewer: /root/graded_unroll_intake.

Scope: independent read-only review of the last projector proof-script diff.
No mathematical source edits, Lean/Lake execution, tests, or GitHub operations
were performed by this reviewer.

## Exact snapshots

Integrated owner:
/workspace/scratch/9009f3c86480/graded-unroll-extension/lean/InfoGeometry/Clifford/Cl11GradedProjectorDefects.lean

- Current SHA-256:
  **78e26a1729dc7cd2147a3419e0ef9611869a6cf7c421d9505ac493be9203033b**
- Current length: 315 lines.
- Previous reviewed SHA-256:
  cf582a853fc7c4e2f64627d36aa1a951d0c77fae590f2d4b88f180e9b245943e.
- Immutable local comparison revision:
  d1cfb307343b4238e3114c43f920c9a5cde927f0.

The complete byte diff against that exact previous snapshot was inspected.

## Verdict

**No source-semantic blocker found.**

The only changes append a second normalization step to each of the three
finite matrix readouts. It unfolds Matrix.add_apply, Pi.add_apply,
Matrix.kroneckerMap, Matrix.of_apply, and Matrix.one_apply.

These are the same native matrix/function entry operations already present
in the goals. Their expansion does not alter the Clifford carrier, its
Jordan–Wigner representation, the eight-coordinate index, the vacuum
coordinate, or the order of the pair/triple/middle-word products.

No theorem statement, mathematical definition, hypothesis, or defect value
changes. The normalization does not assume multiplicativity of entry
evaluation, injectivity of the representation, or any desired numerical
readout. Those readouts still require the finite native matrix calculation
to close under Lean.

The previously reviewed normalized scaling defect remains −1/32, and the
ordinary idempotence defects remain −1/8.

## Execution boundary

The parent reports that the preceding b910-series CI run compiled 43 of 44
closure modules and did not reach the axiom audit because projector leaf
normalization remained incomplete. This reviewer did not reauthenticate that
remote execution during this narrow source review.

The present record neither promotes the partial run to acceptance nor
certifies that the appended normalization succeeds. Exact-source compilation
of the updated snapshot and the subsequent owned-declaration axiom audit
remain separate requirements.
