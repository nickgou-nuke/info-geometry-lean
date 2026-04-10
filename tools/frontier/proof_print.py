#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.frontier.compiler_bridge_client import call_bridge_method


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Print the cheapest useful proof-facing view for a Lean file. "
            "Defaults to the first goal target at a cursor."
        )
    )
    parser.add_argument("input", help="Path to the .lean source file")
    parser.add_argument(
        "--mode",
        choices=("goal-target", "proof-state", "decl-value"),
        default="goal-target",
        help=(
            "`goal-target` prints the first goal target (fastest), "
            "`proof-state` prints the first full goal pretty string, "
            "`decl-value` pretty-prints the declaration value/proof term."
        ),
    )
    parser.add_argument("--line", type=int, default=None, help="0-based line")
    parser.add_argument("--character", type=int, default=0, help="0-based character")
    parser.add_argument(
        "--decl-name",
        help="Required for --mode decl-value (for example, My.Namespace.theoremName)",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=120.0,
        help="Per-request timeout in seconds (default: 120)",
    )
    parser.add_argument(
        "--server-mode",
        choices=("custom", "stdlib"),
        default="custom",
        help="Bridge server mode (default: custom)",
    )
    parser.add_argument(
        "--skip-wait-for-diagnostics",
        action="store_true",
        help="Skip textDocument/waitForDiagnostics before the RPC call",
    )
    parser.add_argument(
        "--json-out",
        help="Optional path for the full raw JSON response",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    started = time.perf_counter()
    if args.mode == "decl-value":
        if not args.decl_name:
            raise SystemExit("--decl-name is required for --mode decl-value")
        method = "validateDecl"
        pretty_print_value = True
    elif args.mode == "proof-state":
        method = "getProofState"
        pretty_print_value = False
    else:
        method = "getGoalTargets"
        pretty_print_value = False

    result = call_bridge_method(
        input_path=Path(args.input),
        line=args.line,
        character=args.character,
        timeout_s=args.timeout,
        server_mode=args.server_mode,
        inject_rpc_import_flag=False,
        wait_for_diagnostics=not args.skip_wait_for_diagnostics,
        rpc_method=method,
        decl_name=args.decl_name,
        pretty_print_type=False,
        pretty_print_value=pretty_print_value,
    )
    elapsed_ms = round((time.perf_counter() - started) * 1000)

    if args.json_out:
        out_path = Path(args.json_out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    if args.mode == "decl-value":
        text = result.get("declarationValue", "")
    elif args.mode == "proof-state":
        goals = result.get("goals", [])
        text = goals[0]["pretty"] if goals else ""
    else:
        goals = result.get("goals", [])
        text = goals[0]["target"] if goals else ""

    if not isinstance(text, str):
        text = ""
    sys.stdout.write(text.rstrip() + "\n")
    print(f"[proof-print] method={method} elapsedMs={elapsed_ms}", file=sys.stderr, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
