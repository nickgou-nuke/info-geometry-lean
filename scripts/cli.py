#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
from typing import Callable

# import modules so we can dispatch to their `main` functions
from . import (
    build_doc_map,
    emit_markdown_index,
    auto_tag,
    filter_project_decls,
    generate_library_index,
    make_graph,
    graph_to_blueprint,
    namespace_patch_plan,
    refactor_plan,
)

COMMAND_MODULES: dict[str, Callable[[list[str]], int]] = {
    "build-doc-map": build_doc_map.main,
    "emit-markdown-index": emit_markdown_index.main,
    "auto-tag": auto_tag.main,
    "filter-project-decls": filter_project_decls.main,
    "make-graph": make_graph.main,
    "graph-to-blueprint": graph_to_blueprint.main,
    "generate-library-index": generate_library_index.main,
    "namespace-plan": namespace_patch_plan.main,
    "refactor-plan": refactor_plan.main,
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
