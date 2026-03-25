"""Top-level Python package for active InfoGeometry scripting helpers.

This package keeps the still-supported helpers that remain under `scripts/`
after archiving the old graph/bootstrap generators into `archive/legacy/`.
"""

from __future__ import annotations

from .analysis import (
    filter_project_decls,
    utils,
)

from .docs import (
    build_doc_map,
    emit_markdown_index,
    gen_content_auto_tex_from_header,
    proof_gap_report,
)

__all__ = [
    "filter_project_decls",
    "utils",
    "build_doc_map",
    "emit_markdown_index",
    "gen_content_auto_tex_from_header",
    "proof_gap_report",
]
