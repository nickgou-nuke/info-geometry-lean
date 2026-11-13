# Matrix amplification and its faithful algebraic colimit

## Intake and intended result

The source is the user attachment `Pasted text(20261112-084417).txt`, SHA-256
`bf7dcff9c5bfd48699edb83ce2ead3c983cf2a9dd8b17a5f6dc3d41c97a6177f`.
Implementation starts from upstream `a392af178af1fe2bcba2ba39eb405700c6ee103c`.
The attachment is retained as intake, not evidence of compiler validation.

The mathematical target is the unital ring tower
`A₀ = A`, `Aₖ₊₁ = Matrix n n Aₖ`, with successor homomorphism
`Matrix.scalar n`. Its entries are arbitrary elements of the previous full
matrix ring. Multiplication is never assumed commutative in this tower.

The dependency order is:

1. Native ring homomorphisms and matrix units.
2. Matrix endofunctor and its scalar-amplification natural transformation.
3. The existing iterated bonding maps and native `DirectLimit` carrier.
4. An actual `RingCat` diagram, cocone and `IsColimit` witness for that carrier.
5. Injective transition maps and injective canonical stage maps.
6. Reflection of commutation, nonzero commutators and strict stage growth.
7. Infinitude of the limit carrier from the strictly increasing subring chain.

This order refers to maps and theorem dependencies, not a physical causal order.

## Owner search and reuse

`InfoGeometry.Algebra.DirectLimitSuperClosureLemmas` already supplies
`bondMap`, `bondMap_apply_trans`, `bondDirectedSystem`,
`DirectLimitSuperClosure`, `directLimitOf`, `directLimitOf_bondMap`,
`directLimitOf_bond`, `directLimitOf_injective`, `directLimitLift`,
`directLimitLift_of`, and `directLimitLift_unique`. Reuse this construction;
do not construct a second quotient or recursive interval-composition API.

`Categorical/FilteredDirectLimitOwner` packages arbitrary categorical
colimits; it does not identify the concrete one-step ring direct limit as a
native colimit. `Canonical/SplitCliffordDirectLimit` and
`Clifford/Cl11TensorTowerLimit` provide specialized faithful-tower precedents.
`Canonical/MatrixStageInductiveLimit` constructs a specialized complex
star-algebra tower with normalized trace. The present target permits arbitrary
noncommutative coefficient rings and arbitrary finite index types.

The older `Canonical/UHFDirectLimitCARAlgebra` has finite CAR data and an
identity map on a fixed matrix carrier. `UHFInductiveColimitBoundary` concerns
diagonal functions. Neither is a replacement for the target full matrix tower.
Existing finite trace-obstruction owners include
`Canonical/FiniteDimensionalCCRNoGo` and the real finite-matrix sandbox owner.
The new finite trace statement records the exact cardinality-cast hypothesis.

## Hypotheses and scope

| Claim | Required hypotheses |
|---|---|
| Matrix functor, natural amplification and categorical colimit | Finite decidable index; arbitrary unital ring |
| Faithful amplification and stage inclusions | Additionally nonempty index |
| Nonzero opposite-unit commutator and strict stage growth | Additionally two distinct indices and nontrivial seed |
| Ordinary matrix trace annihilates a commutator | Commutative coefficient ring; matrices remain arbitrary |
| A matrix commutator differs from the identity | Its dimension cast is nonzero; characteristic zero plus nonempty index suffices |

The nonempty and two-distinct-index assumptions are substantive. The empty
index produces a zero matrix ring; the singleton index gives no strict growth.
No assumption that an operator-valued scalar matrix is central is made.

## Corrections to the intake's analytic interpretation

This change concerns an algebraic and categorical colimit. UHF/CAR
C*-algebra identification requires compatible star and norm structures and an
actual completion. The normalized-trace L² completion is a Hilbert space;
constructing a hyperfinite II₁ factor additionally requires the GNS operator
representation and its weak or strong closure. A poset diagram alone does not
supply Haag–Kastler locality. These are separate targets, not consequences of
the ring-colimit universal property.

Nor does norm completion remove the bounded-operator obstruction to an exact
identity commutator. Unbounded CCR require domain control; Weyl relations are
a different formulation. The matrix units in this change are not advertised
as Weyl operators.

## Acceptance record

Source generation, independent semantic review and independent QA use separate
agent roles. Compiler checks use the unchanged Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` pins. A focused build does not
establish a whole-repository build or discharge analytic targets.

Preparation on 12 November 2026:

- Independent semantic review: PASS for the exact mathematical statements,
  categorical orientation, faithful stage maps, strict growth and carrier
  infinitude. This is source review, not kernel validation.
- Independent package/API review: pins, native dependency revisions, source
  ownership and exhaustive audit coverage agree. The focused manifest's
  `inputRev` was aligned with its literal commit pin.
- `opengauss_screener.py --strict --json`: exit 0, no violations.
- `opengauss_cli.py refute --strict --json`: PASS for all three owners,
  zero traps.
- `opengauss_cli.py review --gate GATE_4 --json`: all four new Lean files
  returned `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED`.
- The vacuity linter emitted a parameter-use heuristic for the matrix owner
  and empty-body/parameter-use heuristics for the tower. Source inspection
  shows actual proof terms and parameter-dependent propositions: the empty-body
  warning is on a multiline application of `directLimitOf_injective`; the
  scalar proofs use their parameters through the elaborated native theorem
  application. No theorem or hypothesis was changed to silence these heuristics.
- Installed staged and pre-commit proof gates: `proof_proxy_staged_gate: ok`.
- `git diff --check`: passed.

Kernel status is **PASS for the three mathematical owners**. Focused CI run
[`43197957178`](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43197957178)
completed successfully on commit
`802fb260ae0052a31d89302179d48243f64072a7`, tree
`d5575ea242af8f18c3bdc52b8a63c9a9becd6340`. The independently checked local
source tree was identical. The run executed both commands:

```bash
python3 verification/matrix-amplification/check.py build
python3 verification/matrix-amplification/check.py env lean lean/InfoGeometry/Categorical/MatrixAmplificationAudit.lean
```

The focused build reported success (3102 Lake jobs). Its declaration audit
and the separate fresh audit both passed. The workflow's audit parser checked
completion and owner coverage. Fresh Lean output gives:

| Mathematical owner | Audited declarations |
|---|---:|
| `InfoGeometry.Algebra.MatrixAmplification` | 13 |
| `InfoGeometry.Categorical.SequentialRingColimit` | 15 |
| `InfoGeometry.Categorical.MatrixAmplificationTower` | 30 |
| **Total** | **58** |

The axiom union is exactly `[propext, Classical.choice, Quot.sound]`.
Independent QA reconciled 58 distinct declaration names and the per-owner
counts, and verified that the CI merge checkout and reviewed head have the
same tree.
The audit includes generated and private declarations, rejects unsafe and
partial declarations, and rejects every axiom outside that allowed set. Its
source is unchanged from the initial draft publication. The three owners
contain 43 explicit mathematical declarations, including 27 theorems; the
larger audit count includes generated declarations.

CI-guided repairs made coefficient and cocone codomain types explicit, exposed
the matrix naturality equation before entrywise extensionality, and corrected
two existential binders. The recursive stage definition now uses native
`Nat.rec`, preserving its defining equations while avoiding an owned
`stage._unsafe_rec` helper. An explicit stage coefficient type supplies the
existing nontriviality instance in the commutator theorem. No hypothesis was
strengthened, and the audit and configured quality gates were not weakened.
Lean reported non-failing simplification and local-instance style suggestions;
no linter was disabled.

Local kernel execution did not start because another task held the shared
build lock. After CI supplied the successful build and fresh audit, the still
queued local wrapper was interrupted before it launched Lake. No other build
process or shared lock was changed. Draft publication was explicitly
authorized with the initially pending kernel checks and the separate root
gate disclosed. Kernel acceptance is now established by the linked CI run;
whole-repository acceptance remains separate. The `Categorical.All` integration
is present but is not built by this focused target.

Separately, `python3 tools/infra/ci_bootstrap.py paths` reports missing,
untracked `HomotopyHypothesis` and `Atlas` path dependencies, and the
uninitialized GIFT gitlink. These are root-package reproducibility failures,
not errors established in the new mathematical source. Root dependency pins,
shared lock, installed hooks and quality gates are unchanged.
