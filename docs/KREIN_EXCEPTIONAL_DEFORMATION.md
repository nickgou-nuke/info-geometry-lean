# Krein exceptional deformation: theorem contract and claim boundary

## Intake and provenance

This task comes from the 2026-11-04 user request to extract an ordered,
noncommutative theorem chain from a narrative about an indefinite metric,
exceptional points, a nilpotent-to-idempotent transition, four Peirce corners,
and repeated idempotency defects. The source example was
`M(epsilon) = [[0, 1], [epsilon^2, 0]]`; the source printed the same matrix for
both spectral projectors and attributed phase-transition and stability claims
to their singular normalization.

The inspected base revision is
`3d7eb6d9b0af5636ab12b3d0b91b82740507e49e`. The task preserves the pinned Lean
`v4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Exact contract

The algebraic carrier is an arbitrary associative unital real algebra `A`,
including noncommutative matrix algebras and bounded endomorphism algebras.
Two independently supplied elements satisfy

```text
u * u = 0,  v * v = 0,  u * v + v * u = 1.
```

The last equation is an explicit normalization hypothesis. It is not derived
from the first two equations. The intended construction is

```text
D(delta) = u + delta • v
K(t) = t⁻¹ • u + t • v                 (t ≠ 0)
P±(t) = (1 ± K(t))/2.
```

The targets are the exact quadratic, projector, spectral, and residue
identities. The topological extension uses a Hausdorff topological real algebra and an actual
`Filter.Tendsto` statement: the residues `t • P±(t)` tend to `±u/2` along
nonzero parameters tending to zero. A nonzero residue excludes any finite
limit of the corresponding projector. A separate closed-locus theorem
excludes a nonzero nilpotent limit of idempotents.

The bilinear adapter uses the native noncommutative algebra `Module.End ℝ E`
with a real bilinear form `B`. The additional hypotheses are that `u` and `v`
are self-adjoint relative to `B`, expressed by `LinearMap.IsAdjointPair`.
This applies to the bilinear form underlying a real Krein space; the proofs
do not need completeness, positivity, symmetry or nondegeneracy of the form.
The targets are total isotropy of the
square-zero image, nullness of an eigenvector in a real Jordan chain, adjoint
exchange of the ordered round trips, and Krein orthogonality of the spectral
sectors. The signed quadratic equation also excludes real eigenvectors for a
negative deformation parameter. Definiteness of either spectral sector is
not an input or a target. The module does not introduce a new Krein-space class.

## Existing owners and reuse

| Layer | Existing source and relevant declarations |
|---|---|
| Binary cut and four corners | `Core/PeirceDecomposition.lean` and `Core/PeirceGrading.lean` |
| Ordered round trips | `Core/PeirceCoupledCorners.lean`: `coupled_square`, `component11_jordan`, `component00_jordan`, `reflection_mul_jordan` |
| Quadratic frame | `Core/PeirceQuadraticFrame.lean` |
| Idempotents from a normalized pair | `Algebra/IsotropicCyclotomicGenesis.lean`: `normalized_square_zero_pair_generates_orthogonal_idempotents` |
| Involution projectors | `GrandUnification/ArchetypeDictionary.lean`: `peircePlus`, `peirceMinus` and their square, product, sum and difference laws |
| Defect recursion | `Core/IdempotencyDefect.lean`, `Core/DefectIteration.lean` |
| Real Krein conventions, inspected as context | `Krein/KreinSpace.lean`: `kreinAdjoint`, `kreinInner_kreinAdjoint`, `kreinBilin`; not imported by the new modules |
| Local null-image theorem | `HodgeCohomology/KreinHodgeDirac.lean`: `square_zero_implies_isotropic_image` |

Search included tracked source filenames, related symbols, imports, bounded
Mathlib searches, the categorical infrastructure map and the local preflight.
No fresh declaration-DAG artifact was available; no graph freshness or global
absence claim is made. The new work is the parameterized deformation and its
topological and Krein adapters, rather than another implementation of the
existing four-corner algebra.

## Claims excluded by the contract

An indefinite metric alone does not imply an integrable pseudo-Kähler or
para-Kähler manifold. A phase-space metric does not force an indefinite
quantum-state inner product. A nonzero nilpotent is not a positive density
operator. A singular spectral projector is not by itself a thermodynamic
phase transition. An opposite-signature collision permits instability but
does not force it for every perturbation. Defect iteration has no general
convergence theorem: nonzero square-zero inputs over ℝ already give a two-cycle.

The parameterization `delta = t^2` only describes the nonnegative side of
the discriminant. Claims about complex eigenvalues, dynamical stability,
quantization, Kähler integrability and thermodynamic limits require additional
operators, structures and proofs. They are not consequences claimed for these
modules.

## Verification record

### New theorem surface

| Module | Public theorems | Result |
|---|---:|---|
| [`SquareZeroPairDeformation`](../lean/InfoGeometry/Algebra/SquareZeroPairDeformation.lean) | 26 | Ordered square formula, necessary noncommutativity, normalized involution, both projector branches, left/right spectral identities and exact residues |
| [`SquareZeroPairDeformationLimits`](../lean/InfoGeometry/Algebra/SquareZeroPairDeformationLimits.lean) | 7 | Closed idempotent locus, nilpotent-limit obstruction, deformation/residue limits and absence of finite projector limits |
| [`ExceptionalPointBilinear`](../lean/InfoGeometry/Krein/ExceptionalPointBilinear.lean) | 11 | Totally isotropic image, local Jordan-chain nullness, adjoint exchange, self-adjoint spectral splitting, orthogonality and signed real-eigenvalue obstruction |

The [audit companion](../lean/InfoGeometry/Krein/ExceptionalPointDeformationAudit.lean)
prints axiom dependencies for all 44 new public theorems and seven reused
Peirce/defect declarations. The private scalar square-zero helper is included
transitively in those dependency checks.

### Dependency order and its scope

The dependency order is supplied by the actual theorem uses and imports:

1. A chosen idempotent supplies the four Peirce corners; the directed corners
   are square-zero and have the two ordered round trips `u*v` and `v*u`.
2. A square-zero pair gives `D(delta)^2 = delta • (u*v + v*u)`.
3. The separate normalization `u*v + v*u = 1` gives `K(t)^2 = 1` for `t ≠ 0`.
4. The established Peirce-projector owner gives the complementary idempotents;
   the new module derives the left and right spectral equations.
5. Bilinear adjunction gives isotropy, adjoint exchange and spectral-sector
   orthogonality. Continuity and a Hausdorff limit give the residue obstruction.
6. Separately, the existing defect iteration preserves centralizers and gives
   an antitone chain of generated native subalgebras. Neither strict decrease
   nor convergence follows from that order statement.

No arbitrary finite enumeration is presented as a proof of physical causality.
The normalization and adjunction hypotheses are additional inputs to this
dependency graph, not consequences of the first Peirce cut.

### Exact interpretation of the limit

For a nonzero first generator, the verified relation is

```text
D(t²) = t • (P+(t) - P-(t)) → u,
t • P+(t) → u/2,
t • P-(t) → -u/2.
```

The two projectors have no finite limit along a nonbottom filter of eventually
nonzero parameters tending to zero. The code does not state a norm-to-infinity
theorem. A norm estimate can be derived in a normed specialization, but is not
part of this theorem surface.

For the bilinear model, the ordered products `u*v` and `v*u` are adjoint to
one another, and their ranges are isotropic. The spectral projectors are
individually self-adjoint and have orthogonal ranges. These are different
decompositions, and neither spectral range is asserted to be definite.

### Build and review evidence

The three new theorem modules and their complete local `InfoGeometry` import
closure, ending in the audit companion, were compiled with the repository's
shared-lock file-check wrapper. The local closure contains 16 modules.
Compilation uses the unchanged pinned Mathlib checkout and Lean executable;
the isolated Lake adapter selects that dependency environment and the new
checkout's compiled imports. Its runtime compatibility shim only maps the
process executable lookup to `/proc/self/exe`; it does not change Lean's
kernel or elaborator.

The reproducible file-level command shape is:

```bash
python3 tools/infra/run_locked_lean.py --lake <pinned-Mathlib-adapter> \
  lean/InfoGeometry/Algebra/SquareZeroPairDeformation.lean
python3 tools/infra/run_locked_lean.py --lake <pinned-Mathlib-adapter> \
  lean/InfoGeometry/Algebra/SquareZeroPairDeformationLimits.lean
python3 tools/infra/run_locked_lean.py --lake <pinned-Mathlib-adapter> \
  lean/InfoGeometry/Krein/ExceptionalPointBilinear.lean
python3 tools/infra/run_locked_lean.py --lake <pinned-Mathlib-adapter> \
  lean/InfoGeometry/Krein/ExceptionalPointDeformationAudit.lean
```

This is an isolated source-closure check, not a successful root-package Lake
build. The genuine root-package command was also attempted:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Algebra.SquareZeroPairDeformationLimits \
  InfoGeometry.Krein.ExceptionalPointBilinear
```

It stopped during dependency resolution because
`external_refs/homotopy-hypothesis-lean4` is absent. The missing path dependency
was not fabricated, and no manifest, toolchain or quality gate was changed.

Independent semantic review returned `PASS`. The strict OpenGauss refuter and
staged proof gate pass. The automated GATE_4 source preflight reports
`STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED`: that particular invocation does not
run its package-level kernel route. Kernel evidence instead comes from the
explicit locked source checks and the separate independent QA rerun.

Independent QA returned `ACCEPTED_WITH_LIMITED_SCOPE`: all 16 local source
modules compiled successfully, and the corrected bilinear owner and audit
companion were rerun. All 51 axiom reports were inspected; their union is
exactly `propext`, `Classical.choice` and `Quot.sound`. There are no custom
axioms or proof holes. The strict refuter and staged proof gate also passed
when independently rerun.

The four new Lean files have no compiler warnings. One inherited dependency
warning remains in `KreinHodgeDirac.lean` for its deprecated
`Mathlib.Data.Real.Basic` import. Static heuristics retain two nonblocking
findings on `deformation_zero`: the legacy regex treats the grouped binder
`u v` as one unused name, and the semantic scanner labels the intended
simplification lemma a `trivial_surface`. Its actual statement is precisely
`u + 0 • v = u`; it supplies an ordinary `[simp]` normalization rule rather
than a substantive spectral claim. The findings are recorded without changing
the scanners.

### Accepted theorem-source fingerprints

| File | SHA-256 |
|---|---|
| `SquareZeroPairDeformation.lean` | `fb24d7c986f79fb3ba39c1e49888a1a989ca9c7d7f4126b5677139dfc4777703` |
| `SquareZeroPairDeformationLimits.lean` | `4282828b40e240261bb9ef2e1b79d2edb8c8e88cd364e32c3b20cf2126aa8ae0` |
| `ExceptionalPointBilinear.lean` | `3563bab9e9a3ebaafff32036ff9b96b9a38f4bd7588c8c0f2fe0d6dc75a55186` |
| `ExceptionalPointDeformationAudit.lean` | `18a089ca5370572220007ba64039521899db021ebde96c8aabd62df597096235` |
