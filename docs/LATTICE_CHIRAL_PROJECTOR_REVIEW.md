# Lattice chiral projector integration: review and verification

## Scope

This change adds three focused owners over the existing native Mathlib and
repository carriers. The [source contract](LATTICE_CHIRAL_PROJECTOR_CONTRACT.md)
records provenance, the external formalization, exact hypotheses, search
coverage and mathematical boundaries.

| Owner | New declarations | Main result |
| --- | --- | --- |
| `OperatorAlgebra/GinspargWilson.lean` | Four definitions and twenty theorems | Two involutions construct a GW solution and intertwine two distinct pairs of existing chiral projectors |
| `OperatorAlgebra/PeirceTangentTrace.lean` | Four theorems | A cyclic additive functional annihilates an ordered product of three idempotent tangents |
| `OperatorAlgebra/RectangularProjectorStabilization.lean` | Two definitions and fifteen theorems | A rectangular split embedding and disjoint fixed sector preserve projectors, tangents and ordered curvature traces |

No dependency pin, existing owner, proof checker, gate, or root Lake
configuration is changed. The new workflow uses the maintained checker and
requires the selected owners to compile without warnings and pass the native
axiom audit. It records the actual source head and hashes in its artifacts.

## Independent source review

Separate reviews checked the candidate generation against actual existing
owners and pinned Mathlib declarations. The parent inspected and integrated
the candidates.

- GW signs agree with the paper after identifying the normalized operator
  with `a * D_phys` and the second involution with `-sign(H_W)`.
- The half-projectors are the existing `ChiralInvolution` constructions.
  The range witnesses use actual `Module.End` composition and native
  `LinearMap.range`; they prove inclusion, not surjectivity.
- The star section has explicit self-adjointness premises. It asserts no
  positive inner product, ghost elimination or spectral-sign construction.
- The triple-tangent proof uses ordered products, the exact tangent-defect
  expansion and the existing cyclic corner theorem. It needs no division
  by two and is valid in positive characteristic as well.
- The rectangular proof contracts `V * U`, never assumes `U * V = 1`, and
  uses the native rectangular trace cycle with its actual index types.
  The one-sided trace and compressed curvature trace are separate statements.
- Review split the positive-projector simplification into two explicit
  steps and clarified that the rectangular lift *need not* preserve the
  ambient unit. Neither correction changes a theorem statement.

## Source gates

Commands were run against all three selected owner files:

```bash
python3 tools/quality/placeholder_audit.py --strict --root <owner> --json-out <report>
python3 tools/quality/semantic_vacuity_gate.py <three owners> --fail-on warning --json-out <report>
```

The strict placeholder scans passed with zero hard findings. Four soft
findings in the rectangular owner identify three short structural proofs
and the section variables `U` and `V`. Those variables are native matrix
arguments, not proof fields supplying the conclusions. The semantic heuristic reported three
`warning/trivial_surface` findings, on `liftMatrix_add`, `liftMatrix_sub`, and
`liftMatrix_one`, so its deliberately warning-strict invocation returned 1.
These are reviewed distributivity/unit identities for the explicitly defined
rectangular lift, not hypotheses restated as conclusions or physical claims.
The first two are used by the tangent and commutator proofs; the third exposes
the precise unit image `U * V`. The findings remain visible. The scanner and
proof formatting have not been changed to suppress them.

The workflow YAML and its three embedded Python programs were parsed, and its
target list was compared with the source-closure inventory. This is a syntax
and configuration check, not an execution of GitHub Actions.

## Kernel and push-gate status at draft preparation

The complete selected source closure has **17 repository modules** and ten
direct Mathlib import roots. The reproducible command is:

```bash
python3 -u tools/quality/check_clifford_dirac.py \
  --mathlib-root <pinned-mathlib> \
  --lean <lean-4.34.1>/bin/lean \
  --output <fresh-output> \
  --target InfoGeometry.OperatorAlgebra.GinspargWilson \
  --target InfoGeometry.OperatorAlgebra.PeirceTangentTrace \
  --target InfoGeometry.OperatorAlgebra.RectangularProjectorStabilization
```

Local native checking is pending the shared build lock. An initial two-owner
snapshot predates the reviewed projector-proof adjustment and is not an
acceptance receipt for the final sources. The new focused CI workflow checks
the exact published head with fresh repository artifacts, the unchanged
Mathlib pin, and the native declaration/axiom audit enabled. Its result must
be read before describing these owners as kernel verified.

The tracked pre-commit hook ran and reported `proof_proxy_staged_gate: ok`.
Tracked commit and push hooks are used separately. A pending or blocked root
gate does not become a pass because a focused source check succeeds. Current
PR status should distinguish source review, source heuristics, selected
kernel validation, and whole-package validation.

## Interpretation boundary

This is reusable finite operator algebra for the chiral-projector comparison
mechanism. It does not add a Wilson lattice kernel, functional-calculus sign,
admissibility theorem, refinement map, differential projector family, Kato
ODE, determinant-line section, convergent measure current, reflection
positivity, interacting continuum theory, or an octonion-to-lattice bridge.
The external formalization contains much more of the source construction;
its recorded verification is separate from validation of this repository.
