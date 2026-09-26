## 2026-09-22T06:55:14Z
Task: Phase 0 Bottleneck Survey — Repository-wide `native_decide` Scan & Ranking:
1. Scan the entire `lean/` repository for all remaining occurrences of `native_decide`.
2. Group occurrences by file and module. Enumerate the exact theorem names and line numbers where `native_decide` is used.
3. Check which files are active/live modules vs test/dead code.
4. Assess and rank the files by compilation cost/impact and bottleneck severity.
5. Identify the top 1-3 worst `native_decide` compiler bottlenecks in the repository for surgical O(1) refactoring.
Constraints: BASH-ONLY MODE, continuous git add -A, read-only on Lean code.
