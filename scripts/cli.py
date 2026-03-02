#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
from typing import Callable

# import modules from package level
from . import (
    build_doc_map,
    emit_markdown_index,
    auto_tag,
    filter_project_decls,
    generate_library_index,
    make_graph,
    refactor_plan,
    graph_to_blueprint,
    cluster_theory,
    agent_doc_gen,
    proof_gap_report,
)

COMMAND_MODULES: dict[str, Callable[[], int]] = {
    "build-doc-map": build_doc_map.main,
    "emit-markdown-index": emit_markdown_index.main,
    "auto-tag": auto_tag.main,
    "filter-project-decls": filter_project_decls.main,
    "make-graph": make_graph.main,
    "generate-library-index": generate_library_index.main,
    "refactor-plan": refactor_plan.main,
    "graph-to-blueprint": graph_to_blueprint.main,
    "cluster-theory": cluster_theory.main,
    "agent-doc-gen": agent_doc_gen.main,
    "proof-gap-report": proof_gap_report.main,
}


def main() -> int:
    ap = argparse.ArgumentParser(prog="scripts")
    ap.add_argument("command", choices=COMMAND_MODULES.keys(),
                    help="subcommand to run")
    ap.add_argument("args", nargs=argparse.REMAINDER,
                    help="arguments passed through to the command")
    parsed = ap.parse_args()

    func = COMMAND_MODULES[parsed.command]
    # rewrite sys.argv for the underlying module so its own argparse works
    sys.argv = [parsed.command] + parsed.args
    try:
        return func()
    except SystemExit as e:
        # propagate exit code
        return getattr(e, "code", 1) or 0


if __name__ == "__main__":
    sys.exit(main())
