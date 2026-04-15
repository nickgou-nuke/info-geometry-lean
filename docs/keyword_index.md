# Keyword Index

This index now has two explicit layers:

1. machine index over **all tracked Lean files** (sorted lexical frequency),
2. deep declaration search (`theorem`/`lemma`/`axiom`) over selected
   characteristic terms, then story synthesis.

## Full Lean Corpus Index (Machine)

Command:

```bash
python3 tools/infra/generate_keyword_research_report.py
```

Outputs:

- [docs/auto/lean_keyword_research_report.md](auto/lean_keyword_research_report.md)
- `reports/keywords/lean_keyword_research_report.json`

Properties:

- corpus is all tracked `*.lean` files in repo,
- terms are sorted by frequency (with lexical cleanup),
- each term includes hotspot files.

## Characteristic-Term Deep Search and Story

Command:

```bash
python3 tools/infra/generate_repo_story_from_keyword_index.py
```

Outputs:

- [docs/auto/repo_story_from_keyword_index.md](auto/repo_story_from_keyword_index.md)
- `reports/keywords/characteristic_term_deep_search.json`

Properties:

- characteristic terms are selected from the sorted full index,
- deep search scans declaration blocks for `theorem`, `lemma`, `axiom`,
- story is refactored from declaration-grounded evidence, not prose-first tags.

## Black Books Corpus (Parallel Lane)

Machine index on black books only:

```bash
python3 tools/infra/generate_black_books_keyword_report.py
```

Story synthesis (profile-aware):

```bash
python3 tools/infra/generate_black_books_story_from_keyword_index.py --profile balanced
python3 tools/infra/generate_black_books_story_from_keyword_index.py --profile physics \
  --story-out docs/auto/black_books_story_from_keyword_index.physics.md \
  --json-out reports/keywords/black_books_characteristic_term_deep_search.physics.json
python3 tools/infra/generate_black_books_story_from_keyword_index.py --profile methodology \
  --story-out docs/auto/black_books_story_from_keyword_index.methodology.md \
  --json-out reports/keywords/black_books_characteristic_term_deep_search.methodology.json
```

Outputs:

- [docs/auto/black_books_keyword_research_report.md](auto/black_books_keyword_research_report.md)
- [docs/auto/black_books_story_from_keyword_index.md](auto/black_books_story_from_keyword_index.md)
- `reports/keywords/black_books_keyword_research_report.json`
- `reports/keywords/black_books_characteristic_term_deep_search*.json`

## Curated Anchor Map (Human)

This table remains a conservative human navigation layer over the stable owner
lanes.

| Topic | Current high-confidence files |
| --- | --- |
| Modular / relative / operator lanes | `lean/InfoGeometry/Canonical/RelativeModularOperator.lean`, `lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean`, `lean/InfoGeometry/Canonical/ConnesArakiTomita.lean`, `lean/InfoGeometry/Canonical/TomitaTakesaki.lean` |
| Krein / Clifford / doubled geometry | `lean/InfoGeometry/Krein/KreinSpace.lean`, `lean/InfoGeometry/Krein/DoubledSpace.lean`, `lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean`, `lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean` |
| Transport / thermo / KMS | `lean/InfoGeometry/Canonical/BogoliubovTransport.lean`, `lean/InfoGeometry/Canonical/TransportLieDerivative.lean`, `lean/InfoGeometry/Canonical/SinkhornFoundation.lean`, `lean/InfoGeometry/Canonical/SinkhornKMSCore.lean` |
| Anomaly / Drazin / inverse-kernel | `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean`, `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`, `lean/InfoGeometry/Canonical/DrazinSupercharge.lean`, `lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean` |
| Projective / potential / measure roots | `lean/InfoGeometry/PositiveMeasure.lean`, `lean/InfoGeometry/Projective/Normalize.lean`, `lean/InfoGeometry/Canonical/PositiveRayCore.lean`, `lean/InfoGeometry/Canonical/RelativePotentialCore.lean`, `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean` |
| Quantum geometric tensor / Weyl / gauge | `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean`, `lean/InfoGeometry/Canonical/WeylGaugeField.lean`, `lean/InfoGeometry/Canonical/WeylTransport.lean`, `lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean` |

## Use Rule

Treat this file as an entrypoint only.

1. Start from the generated machine reports above.
2. Confirm with source in the cited Lean files.
3. Keep curated table changes synchronized with regenerated reports.
