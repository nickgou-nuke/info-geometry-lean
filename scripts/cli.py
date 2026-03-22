#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
from typing import Callable

# Active commands only. Legacy graph/bootstrap generators were moved to
# archive/legacy/scripts and are intentionally no longer exposed here.
from . import (
    build_doc_map,
    emit_markdown_index,
    filter_project_decls,
    make_graph,
    refactor_plan,
    proof_gap_report,
)

COMMAND_MODULES: dict[str, Callable[[], int]] = {
    "build-doc-map": build_doc_map.main,
    "emit-markdown-index": emit_markdown_index.main,
    "filter-project-decls": filter_project_decls.main,
    "make-graph": make_graph.main,
    "refactor-plan": refactor_plan.main,
    "proof-gap-report": proof_gap_report.main,
}


def main() -> int:
    ap = argparse.ArgumentParser(
        prog="scripts",
        description=(
            "Active compatibility CLI for the remaining scripts/ lane. "
            "Archived blueprint/bootstrap generators now live under archive/legacy/scripts/."
        ),
    )
    ap.add_argument("command", choices=COMMAND_MODULES.keys(),
                    help="subcommand to run")
    ap.add_argument("args", nargs=argparse.REMAINDER,
                    help="arguments passed through to the command")
    parsed = ap.parse_args()

    func = COMMAND_MODULES[parsed.command]
    sys.argv = [parsed.command] + parsed.args
    try:
        return func()
    except SystemExit as e:
        return getattr(e, "code", 1) or 0


if __name__ == "__main__":
    sys.exit(main())
