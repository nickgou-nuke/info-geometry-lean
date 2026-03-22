# Docs Tools

This directory contains the maintained documentation orchestrators.

Canonical entrypoints:
- [generate_auto_docs.py](/home/goutev/LEAN4/info-geometry-lean/tools/docs/generate_auto_docs.py)
- [update_repo_docs.py](/home/goutev/LEAN4/info-geometry-lean/tools/docs/update_repo_docs.py)

Use this layer for:
- regenerating `docs/auto/index.md`
- orchestrating semantic export refreshes
- refreshing current derived report surfaces from the trusted DAG and frontier inputs

Top-level `tools/generate_auto_docs.py` and `tools/update_repo_docs.py` remain
as compatibility wrappers, but this directory is the canonical maintained
surface.
