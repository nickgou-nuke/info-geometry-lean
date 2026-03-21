# Alpha Release Notes (Draft)

This file captures the release strategy for the first public alpha of the repository.

## Release Goal

The alpha release should present the repository as:
- a formal Lean 4 theory library;
- a semantic DAG extraction and analysis engine;
- a reproducible research artifact with preserved Git history.

## Exit Criteria

Before tagging alpha:

1. `InfoGeometry.All` and the canonical umbrella build cleanly.
2. Trusted semantic export succeeds on heavy capstones.
3. The master skeleton/frontier picture is stable enough to explain publicly.
4. Bridge gaps are named and localized, even if not all are closed.
5. Root documentation is synchronized with the live theorem surface and repository scale.

## Release Artifacts

Planned release set:
- source tree with full `.git` history
- signed source archive
- `SHA256SUMS`
- root `README.md`
- `THEORY_CANOPY.md`
- `UNIFICATION_INDEX.md`
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

The alpha should present three verified claims:

1. the repository contains a large Lean 4 formal theory of information geometry, gauge transport, KK/index structure, modular/CPT shadows, and finite topological phase scaffolds;
2. the repository includes a working semantic graph engine that can extract purified theory topology from heavy Lean modules;
3. the repository now exposes more than one visible unification corridor:
   - KK / analytical index / synthesis,
   - source-tension / Rosetta / modular anomaly,
   - discrete Hurwitz shell / RG stationarity,
   - finite Pfaffian-sign critical crossing.

Avoid overstating “complete unification”. The stronger and safer phrasing is:

- the architecture is real,
- the major bridge families are visible,
- and the remaining closures are localized enough to attack systematically.

## Next Frontier

The older KK / analytical-index bridge remains central, but it is no longer the only frontier.

The next alpha-facing closure pressure is:

1. richer concrete realizations of the Weyl-scale to KK / Jordan-KKT transport interfaces;
2. stronger dynamic continuity layers for the finite Kitaev / Pfaffian phase scaffolds;
3. less assumption-driven double-copy transport, so the current checked implication surface becomes a deeper derivation.
