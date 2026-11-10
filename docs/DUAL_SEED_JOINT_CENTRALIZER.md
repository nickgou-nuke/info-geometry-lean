# Dual seeds, joint centralizers, and trace orthogonality

## Intake and theorem contract

Source: the user's Bulgarian mathematical intake of 2026-11-10, applied to
`nickgou-nuke/info-geometry-lean` at base revision
`732d97c30f292d61ea332ca9da4d1e1d8f69bd00`.

The intake identifies `P₀ = C(P₁) ∩ C(P₂)` for isotropic source and sink
subalgebras, then associates it with the center of their joint algebra, a
common orthogonal complement, and an Apollonian radical axis. These are
different claims. The table preserves their scope rather than silently
promoting the geometric interpretation to an algebraic theorem.

| Intake claim | Exact mathematical boundary |
| --- | --- |
| Common commutant | `C_A(P₁) ∩ C_A(P₂) = C_A(P₁ ⊔ P₂)`, already native Mathlib. No isotropy is required. |
| Center of the joint algebra | For `B = P₁ ⊔ P₂`, the embedded center is `B ⊓ C_A(B)`. Equality with the whole relative commutant needs `C_A(B) ≤ B`. |
| Common orthogonal complement | A bilinear form must be specified. For the nondegenerate bilinear matrix trace form, `C_A(S) = [S,A]ᗮ`, where `[S,A]` means the span of all commutator images. It is not generally `Sᗮ`. |
| Stable kernel | A centralizer is the common kernel of inner commutators. The new construction gives an explicit linear retraction onto it for the existing reflexive square-zero seed pairs. |
| Hyperbolic axis | Existing Cartan relations give `[H,d]=2d` and `[H,b]=-2b`. Such an `H` generally normalizes the root lines and does not centralize the seeds. |
| Harmonic support | Existing `zeroModeSupport d b` is the element `1-db-bd`, not the entire joint-centralizer subalgebra. Its corner is one contribution to that subalgebra. |
| Apollonian/radical axis | Existing Apollonius owners concern specified cross-ratio/level-set geometries. No general realization map identifying the relative commutant with such an axis is supplied by this intake. This identification remains open. |

The square-zero seed lines used here are Lie subalgebras or nonunital associative
subalgebras; they should not be silently typed as unital `Subalgebra`s.
Dual numbers (`ε²=0`) and split-complex numbers (`j²=1`) are also distinct.

## Owner search and reuse

The current-source search covered filenames, exact declaration bodies,
imports, all `IsDualSeedPair` consumers, and alternate formulations involving
centralizers, commutants, corners, projections, Reynolds maps, and fixed
points. It did not locate the retraction below. This is a bounded source
search, not a claim of mathematical novelty or a fresh declaration-graph audit.

| Owner | Reuse or inspected precedent |
| --- | --- |
| `Core/DualSeedPeirce.lean` | `IsDualSeedPair`; the existing pole/support aliases; `pp`, `qq`, `pq`, `qp`, and the eight seed/support multiplication laws. |
| `Core/DualSeedCartan.lean` | Native `IsSl2Triple`, Cartan weights, and nonzero active support. |
| `Core/PeirceRotor.lean` | `harmonic_idempotent`, `harmonic_block`. |
| `Core/PeirceBilateralAction.lean` | The existing `bilateral` linear maps `a ↦ u*a*v`. |
| `Core/JordanMultiplicationClosure.lean` | Reused `trace_adjoint_identity`, the cyclic-trace commutator identity. |
| `Canonical/LieJordanMatrixGeometry.lean` | Reused `traceBilinear`, `traceBilinear_apply`, and `traceBilinear_nondegenerate`. |
| `OperatorAlgebra/LieJordanTraceDuality.lean` | Inspected cyclic trace identities; no duplicate trace pairing was introduced. |
| `Canonical/FiniteMatrixGibbsCentralizer.lean` | Inspected complex weighted-trace centralizer converse. The new ordinary-trace statement works over arbitrary commutative rings and arbitrary sets of generators; it does not reprove a weighted-trace result. |
| `OperatorAlgebra/PeirceCoupling/RealCartanWitnesses.lean` | Existing dense, noncommuting real `3 × 3` reflexive square-zero pair. |
| `OperatorAlgebra/CliffordDirac/Spectators.lean` | Inspected existing noncommuting Hermitian members of a full `8 × 8` matrix centralizer; outside the compiled import closure of this change. |
| Mathlib `Subalgebra.Centralizer` | `centralizer_coe_sup`, the native generated-algebra/common-centralizer identity. |
| Mathlib matrix trace and bilinear-form APIs | Trace separation and the actual orthogonal-complement construction. |

The categorical infrastructure map was checked. The present contract is
algebraic, with no colimit, completion, or new categorical carrier.

## Constructive retraction

Let `A` be an arbitrary associative unital ring and let the existing
`IsDualSeedPair d b` provide exactly

```text
d*d = 0,  b*b = 0,  d*b*d = d,  b*d*b = b.
```

Write `p = db`, `q = bd`, and `r = 1-p-q`, using the existing aliases.
For a commutative base ring `R` with `Algebra R A`, define the native linear
endomorphism

```text
Φ(a) = p*a*p + b*a*d + r*a*r.
```

The new proof obligations are:

1. Every `Φ(a)` commutes with both seeds.
2. `Φ(a)=a` exactly when `a` belongs to their native joint centralizer.
3. `Φ ∘ Φ = Φ`, `Φ(1)=1`, and its native linear range is that centralizer's
   underlying submodule.
4. For centralizing `c,e`, `Φ(c*a*e)=c*Φ(a)*e`. This bimodule identity needs
   no seed equations; the coefficients are polynomials in the two seeds.
5. `Φ(d)=Φ(b)=0` but `Φ(db)=p+q`. Thus for a nonzero seed the projection is
   not multiplicative. It must not be packaged as an algebra homomorphism.

This construction retains an arbitrary noncommutative active corner and an
independent residual corner. It makes no star, positivity, dimension,
division-by-two, or full-support assumption. Choosing the positive corner
makes the retraction directional; swapping the seeds can change the map.

## Dependency order

The actual proof order is: seed multiplication laws and harmonic annihilation
→ image in the joint centralizer → identity on centralizing elements →
fixed-point/range/idempotence results. The bimodule law uses only polynomial
commutation. Nonmultiplicativity uses the seed images and nonzero active
support. The center restriction and trace orthogonality results use separate
native subalgebra and trace-separation arguments.

No dependency arrow is asserted from these algebraic results to a geometric
radical axis or a physical flow.

## Validation record

Validation date: 2026-11-10. The author (G-A), independent mathematical
reviewer (A-A), and independent execution reviewer (QA-A) were distinct agents.
The Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` pins are unchanged.

### Kernel and semantic scope

The independent nonincremental source-closure run used:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root .lake/packages/mathlib \
  --output scratch/dual-seed-qa \
  --target InfoGeometry.Core.DualSeedCentralizer \
  --target InfoGeometry.Canonical.JointCentralizerGeometry \
  --target InfoGeometry.Canonical.JointCentralizerGeometryAudit
```

The existing verifier accepts explicit generic targets; its historical
filename does not enlarge this run's scope. All 36 repository modules in
these targets' import closure were rebuilt from their exact sources. No
previous repository module artifacts were reused. The selected targets
compiled with zero warnings; 24 warnings remain in unchanged imported
owners (`MoorePenrose`: 14; `PeirceDecomposition`: 1;
`JordanPeirceDecomposition`: 2; `JordanAssociator`: 7).

The native audit enumerated all 36 new declarations, including private and
generated helpers: 22 in the core owner, 12 in the geometry owner, and 2 named
audit consumers. Their combined axiom set is exactly
`[propext, Classical.choice, Quot.sound]`. The exact-source report, module
logs, generated audit and hash manifest are in `scratch/dual-seed-qa/`.
There are no added proof holes, custom axioms, or unsafe proof bypasses.

QA-A also recompiled each of the three exact copied target sources with
`lean -DwarningAsError=true`, sequentially under the shared build lock and
the recorded `LEAN_PATH`. All three commands exited 0. Their command/result
record is `scratch/dual-seed-qa/wfail-results.json`.

The independent A-A source review passed the three mathematical files and
the scoped workflow. It checked the noncommutative carrier, nonvacuous dense
real witness, direction/sign of the trace identity, characteristic/torsion
boundary, and separation of algebraic results from geometric interpretation.

### Static checks

Each of the following commands was run on all three changed Lean files:

```text
python3 tools/infra/opengauss_screener.py --strict <three paths>
python3 tools/infra/opengauss_cli.py refute <three paths> --strict
python3 tools/infra/opengauss_cli.py review <three paths> --gate GATE_4
```

The strict screener and refuter reported zero traps. The review command
reported `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED`; its static result is not
being substituted for the separate successful kernel and native axiom checks.

The additional `tools/scripts/vacuity-linter.py` heuristic completed with
exit code 0 on each file. It reported one `no_hyp_use` signal, score 0.35, on
`dualSeed_trace_zero`. Both independent reviewers classified it as a false
positive: the proof uses `h.pd.symm` and `h.dp`, while this regex inspects only
the initial `calc` line and retains trailing whitespace in its `"h "`
parameter capture. The signal is retained and classified, not suppressed.
The core and dense audit files had no findings from this heuristic.

### Root package and publication boundary

The actual root-package command was also attempted:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Core.DualSeedCentralizer \
  InfoGeometry.Canonical.JointCentralizerGeometry \
  InfoGeometry.Canonical.JointCentralizerGeometryAudit
```

It exited with code 1 before elaboration because the declared path dependency
`external_refs/homotopy-hypothesis-lean4` is absent. This is a root-package
configuration blocker. The selected import-closure result does not certify
the root Lake package or a whole-repository build.

The added workflow reproduces the selected source-closure and native audit,
requires zero warnings for the three new targets, runs the strict screener,
and retains reports/logs/copied sources as CI artifacts. Its path filter
covers the three new files, this document and the workflow; it does not
monitor every future dependency-only change. No hosted execution is claimed.
Existing repository gates and dependency pins are unchanged.
QA-A parsed the workflow YAML, checked all five shell steps with `bash -n`,
and parsed its three embedded Python blocks with `ast.parse`; all passed.

### Reviewed mathematical source hashes

| File | SHA256 |
| --- | --- |
| `Core/DualSeedCentralizer.lean` | `b98a6b6342c0bbc153db96281a12ebec3af10b2b3e186b4c9d3af0830da7585b` |
| `Canonical/JointCentralizerGeometry.lean` | `0985f86a97b410dd91619a66992398253a1714b7bce2f2bf58b9d0f72774d3cb` |
| `Canonical/JointCentralizerGeometryAudit.lean` | `3801d51cd2eda25489cd940c23c9b3c135b50e56f0826b7620a9026faf003406` |
