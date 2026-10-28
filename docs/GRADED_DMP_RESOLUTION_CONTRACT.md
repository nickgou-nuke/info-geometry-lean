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

## Verification boundary

At initial publication this continuation is a proof candidate pending the
new exact-pin scoped GitHub workflow. No local Lean executable is available
in the authoring environment. The workflow reuses the repository's existing
source-closure compiler and public `Lean.collectAxioms` audit, including
all declarations owned by the earlier three rectangular modules and the four
new modules. It rejects unsafe/partial declarations and non-foundational
axioms, including `sorryAx`.

No root toolchain, Lake manifest, dependency source, or existing Lean owner is
modified. The focused check is not a full root Lake build. The final successful
or failed run will be recorded with its actual commit and observed result.
