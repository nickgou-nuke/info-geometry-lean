# Methodology: Ensuring Lean Declarations are Indexed as Graph Anchors

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

To guarantee that theorems, definitions, and lemmas from Lean files are recognized as graph anchors in the Info-Geometry Spire's DAG index (and thus available for audit, debt reporting, and closure enforcement), follow this protocol:

## 1. Namespace Discipline
- **Define all important declarations at the top-level of their namespace.**
  - Avoid placing key theorems/defs/lemmas inside local `section ... end` blocks unless necessary.
  - If using sections, ensure the declarations are not shadowed or made private.

## 2. Export Attributes
- **Explicitly export all critical declarations using the `@[export ...]` attribute.**
  - The export name must match the fully qualified Lean name, e.g.:
    ```lean
    namespace InfoGeometry.Canonical.BekensteinBound
    @[export InfoGeometry.Canonical.BekensteinBound.topologicalBekensteinBound_of_connesCocycle]
    theorem topologicalBekensteinBound_of_connesCocycle ...
    ```
  - This ensures the declaration is visible to the DAG indexer and appears as a graph anchor.

## 3. Naming Consistency
- **Check that declaration names in Lean files match the names in the DAG index.**
  - Use the full namespace path for all exported items.
  - Avoid duplicate or ambiguous names.

## 4. Verification
- **After building and ingesting the DAG, verify anchor presence:**
  - Search `artifacts/dag/index/decls.jsonl` for your declaration's fully qualified name.
  - If missing, check for missing `@[export ...]` or namespace issues.

## 5. Example Workflow
1. Add `@[export ...]` to all public theorems/defs/lemmas you want indexed.
2. Rebuild the Lean project and refresh the DAG index.
3. Re-ingest the DAG into ArangoDB if needed.
4. Confirm presence in `decls.jsonl` and successful debt/audit reporting.

---

**Summary:**
- Only top-level, exported, and properly named declarations are indexed as graph anchors.
- Use `@[export ...]` and namespace discipline to guarantee inclusion.
- Always verify in the DAG index after changes.
