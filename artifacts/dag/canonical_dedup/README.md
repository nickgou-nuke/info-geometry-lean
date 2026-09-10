# Canonical deduplication candidates

`candidate_groups.jsonl` is a non-destructive inventory generated from the
`infogeometry_codebase_canonical_v2_20260910` Arango database.  Each row groups
declarations that share the same kind, canonical type digest, and canonical
value digest.

These are candidates only.  A digest is a finite index, so it is not a proof of
definitional equality.  No declaration, edge, export, or source file may be
removed from such a group until the Lean kernel establishes the required
`isDefEq` relation and all public names have forwarding compatibility checked.
The `dagShapeHash` is included for navigation only and is never used as an
identity key.
