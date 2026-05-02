# Closure Debt Auditor Tool: Identifying Unanchored Declarations and Theory Islands

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Not part of the maintained authority surface unless explicitly promoted.
> See: [README.md](../../README.md), [docs/README.md](../../docs/README.md), [docs/CODEBASE_STATUS.md](../../docs/CODEBASE_STATUS.md)

## Purpose
This tool scans Lean source files and the DAG index to:
- Identify all public theorems/defs/lemmas that are **not present as graph anchors** ("closure debts").
- Detect **theory islands**: clusters of declarations that are disconnected from the main dependency graph (i.e., not rooted in foundational seeds).
- Highlight **holes**: declarations that are not reachable from or do not reach any foundational axiom, definition, or trusted theorem.

## Methodology
1. **Parse Lean Source**: Collect all public theorems/defs/lemmas in target files.
2. **Parse DAG Index**: Load all graph-anchored declarations from `artifacts/dag/index/decls.jsonl`.
3. **Compare**: List all public declarations missing from the DAG index as closure debts.
4. **Graph Analysis**:
    - Build the dependency graph from `edges.jsonl`.
    - Identify connected components (theory islands).
    - Mark components not connected to foundational seeds as isolated.
    - Mark declarations with no incoming/outgoing edges as holes.
5. **Report**: Output a Markdown/JSON report listing:
    - Closure debts (unanchored declarations)
    - Theory islands (disconnected clusters)
    - Holes (unreachable or rootless declarations)

## Usage
- Run: `python3 tools/quality/closure_debt_auditor.py --lean-root lean/ --dag-index artifacts/dag/index/decls.jsonl --dag-edges artifacts/dag/index/edges.jsonl --out reports/closure_debt_audit.md`
- The tool will output a detailed audit of closure debts and theory structure.

## Benefits
- Ensures all critical theorems/defs are graph-anchored and auditable.
- Detects fragmentation in the formal theory (islands, holes).
- Supports closure discipline and foundational integrity.

---

**Next Step:** Implement `tools/quality/closure_debt_auditor.py` following this protocol.
