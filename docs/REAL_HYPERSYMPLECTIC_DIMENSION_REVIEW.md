# Real hypersymplectic dimension: review and validation scope

## Mathematical review

Independent G-A supplied the new owner. Independent A-A checked its actual
source, Mathlib interfaces, signs, hypotheses, determinant argument, zero-space
case, and the existing real four-dimensional reference model. The parent
integrated the candidate and added the three metric-compatibility boundary
lemmas. A-A reviewed those and the source-local PR386 repairs independently.
When PR386 advanced, its exact upstream repairs replaced the competing local
proof-body repairs before publication.

Final new-owner source SHA256:
`2845a0b689f2ca0919300ab5af2cd73fcf443558f9ffa01f8c569a1f2d6d73e2`.

The theorem constructs an actual cross-leaf linear equivalence and native
alternating nondegenerate leaf form. Neither cross nondegeneracy nor parity
is stored as an assumption. Both skew laws are explicit hypotheses on the
same symmetric nondegenerate form. The zero-dimensional case is included.

The common-omega boundary proves elliptic self-adjointness and anti-isometry
for the para-contracted form, and excludes simultaneous skew-adjointness on
a nonzero nondegenerate carrier. It does not prohibit other choices of metric
or operator pair on that carrier.

## Corrections prompted by actual checks

The inherited scoped CI run for PR386 was
[44065838743](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44065838743),
job 133979170834, artifact 14324016427. All 17 inherited dependencies
compiled. The generic compatibility owner compiled with one deprecated-import
warning; the oblique owner had a matrix-to-endomorphism conversion error and
three warnings; the phase-space owner had six algebraic proof errors.

The upstream continuation `1838b7dfc27cac18937136f6e4c168a8dc314e29` repairs
those exact proof bodies, and this PR consumes it. The ordered products,
matrices, forms, theorem statements, and dependency pins are preserved.
The intended root ring rewrites are qualified to avoid specialized imported
names; the transported matrix anticommutator exposes the native composition
and identity. The two overlapping merge conflicts were resolved by retaining
these exact upstream owner files. The three new boundary lemmas merged into
the generic owner without conflicting with its import repair.

The first source-only strict screener reported T16 on two arithmetic steps
inside the dimension owner. Independent review identified real-number and
natural-number goals rather than operator rewrites. The author replaced them
with explicit multiplication cancellation and natural-number distributivity.
The unchanged screener is retained; no exception or weakening was introduced.

An initial sparse checkout could read all four selected owners but not the
global importer/manifest sources required by the semantic-content gate. Its
exit-2 coverage failure was retained. The exact task files were transferred
to the existing complete independent checkout before rerunning that gate.

## Native verification route

The focused workflow is
`.github/workflows/real-hypersymplectic-dimension.yml`. It selects exactly:

- `InfoGeometry.Geometry.SymplecticMetricCompatibility`
- `InfoGeometry.Geometry.ObliqueSymplecticInvolution`
- `InfoGeometry.Clifford.PhaseSpaceSymplecticMetricCompatibility`
- `InfoGeometry.Geometry.HypersymplecticDimension`

The actual import traversal contains 24 repository source modules and 39
Mathlib import roots. It imports the established Hestenes/Krein split datum,
Peirce eigenspaces and neutral-form API. The new owner uses no complex scalar
or complex vector-space instance.

The maintained `check_clifford_dirac.py` is unchanged. This workflow requires
its complete owned-declaration audit and then separately rejects any warning
or error in the four selected owners. Permitted foundational axioms remain
`propext`, `Classical.choice`, and `Quot.sound`. It restores only pinned Lean
and Mathlib dependencies, rebuilds repository sources from the exact PR head,
and uploads logs, source hashes, dependency fingerprints and audit output.
No `--skip-audit` or repository artifact cache is used.

Reproduce against the unchanged dependency pins:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root ../mathlib \
  --lean lean \
  --output ../hypersymplectic-report \
  --target InfoGeometry.Geometry.SymplecticMetricCompatibility \
  --target InfoGeometry.Geometry.ObliqueSymplecticInvolution \
  --target InfoGeometry.Clifford.PhaseSpaceSymplecticMetricCompatibility \
  --target InfoGeometry.Geometry.HypersymplecticDimension
```

Acceptance additionally requires `warnings == 0` on every selected owner;
the generic helper's default namespace warning check alone is insufficient.
The workflow performs that report check explicitly.

## Publication boundary

At initial source preparation, the local native run was waiting for the
maintained shared build lock. An earlier unstarted wait was stopped before
integrating the strict-screen proof repair; no running external Lean/Lake
process was stopped. Source review and source scanners are not kernel proof
certificates. The PR's exact-head workflow result supplies the current native
status; this document does not predeclare its success.

The selected-owner route does not certify a root Lake build or the exhaustive
`InfoGeometry.All` aggregator. The latter receives an import for discoverability
only. Root package acceptance remains separately subject to the maintained
pre-push gate and the repository's path-dependency initialization.

This PR is stacked on PR386 to reuse its genuine metric-compatibility owner.
The separate uncertainty PR379 retains its own real positive-Hilbert theorem
and native right-phase construction. Its inherited LeanArchitect compatibility
failure is not imported into this 24-module closure and is not repaired by a
claim about this extension's validation.

No signature classification, manifold integrability, curved connection,
Fisher/BKM identification, full metriplectic dynamics, or philosophical
uniqueness theorem is asserted here. The contract preserves the raw intake
and classifies those stronger statements explicitly.
