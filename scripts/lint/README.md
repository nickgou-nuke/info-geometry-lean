# Repository lint policy

`required/lint_all.sh` is the changed-source gate. Its eight Lean checks run in
this order: style, locked Lake build (unless `--skip-build`), direct import
completeness, duplicate TODO/FIXME comments, `@[pseudo]` attribution, module
documentation layout, theorem policy plus the project Lake lint driver, and
transitive Lean import closure. It then runs the ninth repo-shape check in
`required/repo_structure_lint.py`.

Pass explicit Lean paths to restrict linting to a change range. `--all` scans
the Lean tree. The `theorem_lint.py` allowlist in `exemptions/Theorems.txt`
preserves current theorem-keyword files; all theorem declarations still need
docstrings. New files should use `lemma` unless the allowlist is reviewed.

The optional spelling checker uses `exemptions/spellingWords.txt`. Structural
exceptions are exact paths in `exemptions/structural.txt`; the current floating
GitHub Action reference is visible debt, and new floating references fail.

`tools/quality/unified_gate.py` runs blocking placeholder, vacuity, and
mathfulness audits. The existing hollow-theorem detector remains advisory
because it is regex-based and its current entry point returns success even
when it prints findings. The PR summary and proof-golf helper report Git/header
evidence only; neither replaces Lean compilation or semantic review.

The repository currently has no repo-owned Physlib package/linter entry point.
The transitive import check therefore follows root-package modules and
available `.lake/packages` sources. It does not certify external Physlib CI.
