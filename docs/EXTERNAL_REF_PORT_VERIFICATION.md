# External-reference production ports: verified

## Scope and result

Lean **v4.34.1**, using the superproject's pinned Mathlib checkout
`d13f23b723b8a846827a245b89c10fc7d3f11612` and shared package cache.

| Package | Selected Lean files, including root | Audited declarations | Build / source scan / axiom audit |
| --- | ---: | ---: | --- |
| `external_refs/ExteriorPowers` | 30 | 950 | PASS |
| `external_refs/ProjectiveSpace_lean4` | 12 | 386 | PASS |
| `external_refs/AbstractSimplicialComplex` | 11 | 778 | PASS |
| **Total** | **53** | **2,114** | **PASS** |

This closes the **production-library ports**, not every historical experiment.
The exact source inventory and SHA-256 hashes are recorded in
[`EXTERNAL_REF_PORT_VERIFICATION.json`](EXTERNAL_REF_PORT_VERIFICATION.json).
Each package's build and axiom-audit exit codes are zero, and its sources were
unchanged during verification.

The root modules now import all production modules. For simplicial complexes,
`FacePoset` and `OrderOnFacets` import the core owner directly to avoid an
umbrella-import cycle. All modules were also requested explicitly, including
`ExteriorPowers.PortAuditCharts`. Thus neither a minimal default target nor a
small sample of named theorems is being substituted for source coverage.

## Checks

- Locked Lake builds, serialized with other compiler tasks; no task terminated.
- Source-aware scan using the repository's nested-comment/string lexer: no active
  `sorry`, `admit`, `sorryAx`, custom axioms, `unsafe`, `partial`, or `#exit` in the
  selected sources.
- Existing `tools/infra/axiom_check.lean` run on **every selected module's olean**:
  all declarations pass its partial/unsafe checks and transitive axiom audit.
  Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
- Package-local staged whitespace checks pass.

No dependency update, cache cleanup, or new dependency revision was needed in
this closure pass. Changes are staged; this pass created no commit.

## Native Mathlib ownership

- Grassmannian charts, transition smoothness, finite-codimension complements,
  frame quotient/descent, GL action, and algebraic/smooth Plücker maps compile.
  The normed subspace carrier and arbitrary ambient spaces are retained; the
  ring-theoretic Mathlib Grassmannian is not substituted for a different carrier.
- Exterior powers, basis coordinates, multilinear calculus, continuous-linear
  retractions, open embeddings, and manifold infrastructure use native APIs.
- Aggregate imports exposed conflicting tensor declarations that isolated builds
  did not detect. The port now imports Mathlib's tensor seminorms, universal
  lifts, and evaluation maps instead of installing duplicate instances.
  `PiTensorProduct.injectiveSeminorm_eq_projectiveSeminorm` proves that the old
  supremum over **all** multilinear tests is the projective seminorm. It is not
  advertised as the mathematical injective tensor seminorm.
- Two copied Lean 3 Mathlib drop-ins in ProjectiveSpace now import their native
  owners without redeclaring normed-field classes or balanced hull/core theory.
- `ProjectiveSpace/Charts.lean` now proves both formerly unfinished openness
  results using native openness of linear independence and continuous preimages.
- The simplicial categorical layer uses `TypeCat`, `InducedCategory`, native
  `PartOrd`, current adjunction/reflective APIs, and `uliftYoneda.leftKanExtension`.

## Explicit historical exclusions

These are preserved, not counted as successful builds or audited source:

- ExteriorPowers: root `Multilinear.lean`, `ExteriorPowers/playground.lean`,
  `ExteriorPowers/playground2.lean`.
- ProjectiveSpace: `ProjectiveSpace/playground.lean` and the five files under
  `ProjectiveSpace/old/` (`ClosedHyperplanes`, `MapFromSphere`,
  `ProjectiveSpaceGeneral`, `ProjectiveSpaceManifold`, `SmoothMaps`).
- AbstractSimplicialComplex: `AbstractSimplicialComplex/playground.lean`,
  `playground1.lean`, and `playground2.lean`.

Lake configuration files and vendored dependency trees are not library sources.
This report does not certify all of `external_refs`, the entire superproject,
or import compatibility between these independently built upstream packages.

## Reproduction

From `/home/goutev/repos/info-geometry-lean`:

```sh
# Read-only inventory/source scan:
python3 tools/infra/verify_external_ref_ports.py --inventory-only

# Serialized explicit builds and full declaration audits:
python3 tools/infra/verify_external_ref_ports.py
```

The verifier discovers Git-selected sources, rejects unclassified root sources,
reports historical exclusions, waits for compiler tasks, uses the shared lock,
and writes build logs, axiom logs, source hashes, and exit codes. Use
`--output-dir PATH` to select a receipt directory.

Final session logs: `/tmp/external-ref-ports-final-formatted/`.
The JSON receipt is preserved alongside this document because `/tmp` is ephemeral.
