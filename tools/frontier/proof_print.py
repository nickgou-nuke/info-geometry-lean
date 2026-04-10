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
from tools.frontier.proof_runtime import (
    PROOF_PRINT_MODE_CHOICES,
    call_spec_for_print_mode,
    extract_print_text,
)


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
        choices=PROOF_PRINT_MODE_CHOICES,
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
    try:
        call_spec = call_spec_for_print_mode(args.mode, args.decl_name)
    except ValueError as exc:
        raise SystemExit(str(exc)) from exc

    result = call_bridge_method(
        input_path=Path(args.input),
        line=args.line,
        character=args.character,
        timeout_s=args.timeout,
        server_mode=args.server_mode,
        inject_rpc_import_flag=False,
        wait_for_diagnostics=not args.skip_wait_for_diagnostics,
        rpc_method=call_spec.method,
        decl_name=call_spec.decl_name,
        pretty_print_type=call_spec.pretty_print_type,
        pretty_print_value=call_spec.pretty_print_value,
    )
    elapsed_ms = round((time.perf_counter() - started) * 1000)

    if args.json_out:
        out_path = Path(args.json_out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    text = extract_print_text(result, args.mode)
    sys.stdout.write(text.rstrip() + "\n")
    print(
        f"[proof-print] method={call_spec.method} elapsedMs={elapsed_ms}",
        file=sys.stderr,
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
