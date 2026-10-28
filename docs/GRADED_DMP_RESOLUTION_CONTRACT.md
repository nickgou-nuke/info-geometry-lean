# Graded DMP/MPD resolution: source contract

## Intake and provenance

Continuation of PR #233 at `eff3c64b95a2cb9e1cd79015cd3fdd9b12f2916f`.
The earlier rectangular retract work is retained unchanged and is included in
the new scoped compilation and all-declaration audit. PR #227 is a separate
already-published twistor/glide development; this change does not rewrite it.

Sources:
- `Pasted text(20261027-140948).txt`, SHA-256
  `11183ae1f29cd7b1b3b3f4c439e274e7a6a4501fa08d43c71061f5ae529487a4`.
- `Pasted text(20261027-141750).txt`, SHA-256
  `27e46c54d049917d76bd322efcd5456c7d4af529d7e0c4fe762454e323825969`.

The first source supplies retract/Peirce/core-inverse identities. The second
supplies division-free parity and ordered DMP/MPD identities. Their literal
standalone Lean blocks are not claimed to compile unchanged.

## Existing owners, not replacement predicates

- `Core.PeirceDecomposition`: actual four ordered corners.
- `Core.IdempotentCartan`: complementary additive projections, native reflection
  ring equivalence, parity products, characteristic-qualified eigenspaces.
- `Canonical.Drazin.IsDrazinInverse`: the three indexed Drazin equations and
  actual Fitting summands.
- `Singular.MoorePenrose.IsMoorePenroseInverse`: all four Penrose equations.
- `Canonical.DrazinMoorePenrosePartition`: existing ordered `dmpInverse` and
  `dualDmpInverse`, and their outer-inverse equations.
- #233 `Algebra.RectangularRetract` and `QuantumContext.RectangularDrazinLift`:
  the nonunital corner homomorphism and constructed indexed ambient inverse.

No generalized-inverse predicate is introduced. A direct theorem translates
between the two existing indexed Drazin APIs. All proofs concern arbitrary
associative rings/star rings or full real matrix algebras; the operator algebra
is never replaced by scalar readouts. No complexification is introduced.

## Required reconciliation of the source

1. Neither uploaded `CoreNilpotentSplit` nor `DrazinResolution` contains an
   actual nilpotence hypothesis. Corner annihilation is not nilpotence. The
   new joint theory uses the native indexed Drazin predicate. The rectangular
   constructor keeps the explicit `N^r=0` assumption.
2. Peirce decomposition is characteristic-free. Recovering its two parts as
   distinct reflection sign eigenspaces needs injective doubling, as already
   stated by `Core.IdempotentCartan.sign_eigenspaces`. In characteristic two
   the reflection alone loses the grading.
3. The two corners are not automatically two-sided ideals in the entire
   algebra. They are corners and are ideals within the corresponding even
   subalgebra. No centrality of the support is assumed.
4. For A:domain -> codomain, A*M is the target/range support and M*A is the
   source/co-range support. The source note's labels are not used interchangeably.
5. `U*A*U=U` is an outer-inverse law. It does not imply `A*U*A=A`.
   This continuation proves the exact latter defect equals the Fitting
   complementary summand.
6. A finite square real retract cannot have a nontrivial complementary
   support. The rectangular carrier of #233 is retained.

## New theorem contract

Write P=A*D, U=D*A*M, V=M*A*D. D is an indexed native Drazin witness,
and M is a supplied native Moore-Penrose witness whenever the Penrose equations
are used. Then:

- U*A=P=A*V; A*U=P*(A*M), V*A=(M*A)*P.
- U*A*V=P*M*P, and adding the complementary corner recovers evenPart P M.
- U-V=P*M-M*P; its odd projection is itself and it anticommutes with 2P-1.
- oddPart P M=(2P-1)*(U-V), so U=V iff oddPart P M=0.
- The square of the difference is even, not necessarily zero.
- A-A*U*A=A-A*V*A=A*(1-P). Thus U is also an inner inverse exactly
  when the Fitting complementary summand vanishes.
- The two hybrid supports are idempotent, not asserted self-adjoint.
- Adjoint covariance exchanges the ordered inverse products. Adjoint
  compatibility of Peirce parity explicitly requires a self-adjoint support.
- MP source and target reflections are unitary separately; the arrow A
  intertwines their action.

The rectangular bridge applies these theorems to the constructed Drazin inverse
of K*A*Q+N. Its ambient MP witness is separate. A second theorem constructs MP
transport for the genuinely isometric case K^*K=1. It does not grant MP
covariance under arbitrary oblique similarities.

## Noncommuting witness

A full real 4-by-4 example has a nonscalar regular corner, nonzero square-zero
Fitting part, oblique spectral support, A*M != M*A, U != V, and (U-V)^2 != 0.
Both inverse witnesses are explicit rational-entry real matrices, with all
three Drazin equations and all four Penrose equations checked in Lean.
No diagonalization is used in those proofs.

## Dependency partial order

The mathematical compilation order is:

rectangular retract -> Peirce support -> indexed Drazin transport
                                                   \
                                                    -> ordered hybrid recovery
four Penrose equations -> metric supports ----------/

Peirce reflection + ordered products -> exact odd difference and even feedback.
Isometric corner + Penrose equations -> metric-compatible rectangular transport.
The real matrix instance exercises the resulting distinctions.

`GradedDMPDependencyOrder` constructs a native finite `PartialOrder` with the
algebraic and metric inverse branches incomparable. This is an explicit
stage specification, not an extracted complete Lean declaration graph and
not a claim about physical causality.

## Verification: completed 2026-10-28

The initial candidate status is superseded by the successful scoped run:

- Workflow: [Graded DMP resolution, run 40666574338](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40666574338).
- Kernel job: `122742472342`, conclusion `success`.
- Source head: `785ca77ee9b68f32e5f1cdf073997c966c405212`.
- Checked PR merge: `d9dc532bec0e37a9a473ce6cbd478db13febf6b5`.
  GitHub compare reports no changed files between this merge and the source head.
- Official Lean `4.34.1`, executable commit
  `5045d0056413266e57c625dcd7c365b10e377c52`.
- Unchanged Mathlib pin `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The workflow compiled all **20 repository modules** in the complete selected
import closure from their actual source files, sequentially under the shared
build lock. All returned exit code zero. The four new modules contain **42
named theorems** (24 resolution, 3 transport, 10 matrix-witness, 5 dependency-order
results). The three retained rectangular modules contribute **28 named theorems**,
so this run rechecks 70 named theorems across the seven target owners.

The public `Lean.collectAxioms` audit enumerated **147 declarations** owned by
those seven target modules, including definitions and generated declarations.
It rejected unsafe/partial declarations and every axiom outside `propext`,
`Classical.choice`, and `Quot.sound`. The audit passed, with no `sorryAx` or
custom axioms. The audit count is not a theorem count and does not claim that
every declaration in all 20 dependencies was separately enumerated.

There were no Lean warnings in the four new module logs. Existing deprecation
and style warnings in the unchanged `Singular.MoorePenrose` dependency remain.
The semantic-vacuity check found **zero errors and two warnings**:

- `dualDmp_eq_mul_projection`: a short reassociation of the existing ordered
  product and spectral-support definitions, used by the recovery theorems.
- `star_dmpInverse`: a short application of anti-multiplicativity of `star`,
  recording the exact reversal of the existing ordered products.

Both warnings were reviewed against their full statements and proofs. They
are explicit algebraic interface lemmas, not supplied theorem conclusions,
zero operators, or unsupported physical interpretations. No linter suppression
or axiom exemption was added.

### Artifact and source integrity

Artifact `graded-dmp-verification`, ID `12806503174`, contains the exact checked
sources, 20 per-module logs, the generated declaration-audit driver and log,
Lean version, source-hash manifest and semantic-vacuity report.

The downloaded ZIP SHA-256 was checked against the upload log:

`2d3466f78d180ec9b68145b78bf8f43216f8d19716700a4bb0f04e8884833182`.

All 20 extracted source hashes match `status.json`. The four new source hashes are:

| Module | SHA-256 |
| --- | --- |
| `Canonical.GradedDMPResolution` | `a27e17e21d4d0824c0dd4c6a31c988a7aaa7eb2c7dec2a8b63c29ef4238c204c` |
| `QuantumContext.GradedDMPTransport` | `36fb2fc2558f3458b68785476032592e11053608a015d7b403ab2d3f77a6d356` |
| `Canonical.GradedDMPMatrixWitness` | `4f3d48655caac5354ab26ee78493e0d4c81423a14bdd2c54412a46fc0f11239a` |
| `Canonical.GradedDMPDependencyOrder` | `d72c75d1fb02f90869dc3da6db5f61d2d8071120b62eda1c0f6e584ae16f4a43` |

A supplemental exact-rational matrix calculation independently reproduced the
three Drazin and four Penrose equations, oblique support, nonzero nilpotent
part, noncommuting MP pair and unequal ordered inverses. This is a semantic
cross-check, not a replacement for the successful Lean proof run. A lexical
scan of the seven target sources found no explicit proof holes, custom axioms,
unsafe/partial declarations or `native_decide` uses.

This finalization changes only this verification document. The compiled Lean
sources, workflow, checker, dependency metadata and pins are unchanged.

## Publication and remaining scope

PR #248 is the continuation, stacked on the ready-for-review PR #233; PR #227
is the separate twistor/glide development. No merge into the parent or main
is performed. There is no local Lean executable in this authoring environment;
the compilation evidence above is the completed GitHub Actions run and its
retrieved artifact, not a claimed local build.

The focused check is not a full root Lake build or an all-green-CI claim.
For the checked source head, the unrelated Sorry Gate and thesis/blueprint/docs
workflows report failure. Their failures are not relabeled as passes. The
present result establishes the stated algebraic theorem package and its
complete selected import closure, not an analytic completion, physical
causality, automatic inverse existence, or minimal Drazin index.
