# Name Equivalence Registry

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This registry is the curated companion to the auto-generated equivalence
dictionary (`reports/dag/equivalence-dictionary.{json,md}`).

Purpose:
- encode stable aliases and naming unifications that are semantically intended
  but may not be discoverable from lexical theorem/def surfaces alone
- keep those curated links version-controlled and reviewable

Source file:
- `docs/NameEquivalenceRegistry.json`

The generator merges this curated file when running:

```bash
python3 tools/infra/generate_equivalence_dictionary.py \
  --curated-json docs/NameEquivalenceRegistry.json \
  --json-out reports/dag/equivalence-dictionary.json \
  --md-out reports/dag/equivalence-dictionary.md
```

## JSON Schema (v1)

`docs/NameEquivalenceRegistry.json` must be either:
- an object with key `pairs: [...]`, or
- a top-level list of pairs.

Each pair can be:
- object form:
  - `lhs` (required)
  - `rhs` (required)
  - `relationKind` (optional, default `curated_alias`)
  - `note` (optional)
  - `source` (optional, default `curated`)
- tuple form: `["lhs", "rhs"]`

Example:

```json
{
  "schemaVersion": 1,
  "pairs": [
    {
      "lhs": "InfoGeometry.Canonical.TomitaTakesaki.modularComplexI",
      "rhs": "InfoGeometry.Krein.clockAxis",
      "relationKind": "curated_alias",
      "note": "Canonical axis naming merge across legacy surfaces."
    }
  ]
}
```

## Curation Rule

Add only theorem-backed or architecture-owned equivalences. Do not add speculative
pairs that are not yet justified on the Lean surface.
