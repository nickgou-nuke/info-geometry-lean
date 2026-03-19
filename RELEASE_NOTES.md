# Alpha Release Notes (Draft)

This file captures the release strategy for the first public alpha of the repository.

## Release Goal

The alpha release should present the repository as:
- a formal Lean 4 theory library;
- a semantic DAG extraction and analysis engine;
- a reproducible research artifact with preserved Git history.

## Exit Criteria

Before tagging alpha:

1. The canonical umbrella and core tooling build cleanly.
2. Trusted semantic export succeeds on heavy capstones.
3. The master skeleton/frontier picture is stable enough to explain publicly.
4. Bridge gaps are named and localized, even if not all are closed.
5. Root documentation is strong enough for first-time researchers and coding agents.

## Release Artifacts

Planned release set:
- source tree with full `.git` history
- signed source archive
- `SHA256SUMS`
- root `README.md`
- `lean/DAG/README.md`
- this release note

Generated DAG artifacts are useful operationally, but should not be the primary tracked release payload.

## Archive Strategy

Recommended procedure:

1. manually remove large build/output artifacts
2. keep `.git`
3. produce a signed source archive
4. publish checksum alongside the archive

Representative command pattern:

```bash
tar -czvf InfoGeometry-Alpha-FullHistory-v1.0.tar.gz .
sha256sum InfoGeometry-Alpha-FullHistory-v1.0.tar.gz
```

## Public Story

The alpha should present two verified claims:

1. the repository contains a large Lean 4 formal theory of information geometry and adjacent operator/topological structures;
2. the repository includes a working semantic graph engine that can extract purified theory topology from heavy Lean modules.

Avoid overstating “complete unification”. The stronger and safer phrasing is:

- the architecture is real,
- the capstone bridge frontiers are visible,
- and the missing closures are now localized enough to attack systematically.

## Next Frontier

The leading bridge frontier is:

`InfoGeometry.KK.KasparovCycle.analyticalIndex`
→
`InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex`

This is the most natural place to continue closing the KK-to-geometry web after the alpha-release surface is in place.
