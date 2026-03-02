"""Top-level Python package for InfoGeometry scripting helpers.

This package consolidates the various utility scripts that formerly lived
as independent executables under ``scripts/``.
"""

from __future__ import annotations

from .analysis import (
    make_graph,
    filter_project_decls,
    cluster_theory,
    refactor_plan,
    utils,
)

from .docs import (
    build_doc_map,
    emit_markdown_index,
    auto_tag,
    generate_library_index,
    graph_to_blueprint,
    agent_doc_gen,
    build_theory_manifest,
    gen_content_auto_tex_from_header,
    proof_gap_report,
)

__all__ = [
    "make_graph",
    "filter_project_decls",
    "cluster_theory",
    "refactor_plan",
    "utils",
    "build_doc_map",
    "emit_markdown_index",
    "auto_tag",
    "generate_library_index",
    "graph_to_blueprint",
    "agent_doc_gen",
    "build_theory_manifest",
    "gen_content_auto_tex_from_header",
    "proof_gap_report",
]
