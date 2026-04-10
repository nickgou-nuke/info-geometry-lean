#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.frontier.compiler_bridge_client import CompilerBridgeSession


ALLOWED_METHODS = {
    "getGoalTargets",
    "getProofState",
    "checkSnippet",
    "validateDecl",
    "getEnvFingerprint",
    "didChange",
    "reloadFromDisk",
}


def emit(payload: dict[str, Any]) -> None:
    sys.stdout.write(json.dumps(payload, ensure_ascii=False) + "\n")
    sys.stdout.flush()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Keep one compiler-bridge session open for a file and answer bridge "
            "queries from JSON lines on stdin."
        )
    )
    parser.add_argument("input", help="Path to the .lean source file")
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
        "--inject-rpc-import",
        action="store_true",
        help="Inject `import Agent.ProofServerRpc` into virtual didOpen text",
    )
    parser.add_argument(
        "--skip-wait-for-diagnostics",
        action="store_true",
        help="Skip `textDocument/waitForDiagnostics` during session setup",
    )
    parser.add_argument(
        "--transcript",
        help="Optional path for JSONL LSP transcript output",
    )
    parser.add_argument(
        "--stderr-log",
        help="Optional path for server stderr output",
    )
    return parser.parse_args()


def request_error(req_id: Any, message: str) -> dict[str, Any]:
    return {
        "id": req_id,
        "ok": False,
        "error": {
            "type": "RequestError",
            "message": message,
        },
    }


def main() -> int:
    args = parse_args()
    session = CompilerBridgeSession(
        input_path=Path(args.input),
        timeout_s=args.timeout,
        server_mode=args.server_mode,
        inject_rpc_import_flag=args.inject_rpc_import,
        wait_for_diagnostics=not args.skip_wait_for_diagnostics,
        transcript_path=Path(args.transcript) if args.transcript else None,
        stderr_path=Path(args.stderr_log) if args.stderr_log else None,
    )
    try:
        session.open()
        emit(
            {
                "event": "ready",
                "input": str(Path(args.input).resolve()),
                "serverMode": args.server_mode,
            }
        )
        for raw in sys.stdin:
            line = raw.strip()
            if not line:
                continue
            try:
                req = json.loads(line)
            except json.JSONDecodeError as exc:
                emit(request_error(None, f"invalid JSON: {exc}"))
                continue
            req_id = req.get("id")
            method = req.get("method")
            if method in ("close", "exit"):
                emit({"id": req_id, "ok": True, "event": "closing"})
                break
            if method not in ALLOWED_METHODS:
                emit(request_error(req_id, f"unsupported method: {method}"))
                continue
            started = time.perf_counter()
            if method == "didChange":
                text = req.get("text")
                if not isinstance(text, str):
                    emit(request_error(req_id, "didChange requires string field `text`"))
                    continue
                try:
                    session.did_change(
                        text,
                        wait_for_diagnostics=req.get("waitForDiagnostics"),
                    )
                except Exception as exc:
                    emit(
                        {
                            "id": req_id,
                            "ok": False,
                            "method": method,
                            "error": {
                                "type": type(exc).__name__,
                                "message": str(exc),
                            },
                        }
                    )
                    continue
                emit(
                    {
                        "id": req_id,
                        "ok": True,
                        "method": method,
                        "version": session.version,
                        "timingsMs": {
                            "bridge": round((time.perf_counter() - started) * 1000),
                        },
                    }
                )
                continue
            if method == "reloadFromDisk":
                try:
                    session.reload_from_disk(
                        wait_for_diagnostics=req.get("waitForDiagnostics"),
                    )
                except Exception as exc:
                    emit(
                        {
                            "id": req_id,
                            "ok": False,
                            "method": method,
                            "error": {
                                "type": type(exc).__name__,
                                "message": str(exc),
                            },
                        }
                    )
                    continue
                emit(
                    {
                        "id": req_id,
                        "ok": True,
                        "method": method,
                        "version": session.version,
                        "timingsMs": {
                            "bridge": round((time.perf_counter() - started) * 1000),
                        },
                    }
                )
                continue
            try:
                result, resolved_line, resolved_character = session.call(
                    rpc_method=method,
                    line=req.get("line"),
                    character=int(req.get("character", 0)),
                    decl_name=req.get("declName"),
                    pretty_print_type=bool(req.get("prettyPrintType", False)),
                    pretty_print_value=bool(req.get("prettyPrintValue", False)),
                )
            except Exception as exc:
                emit(
                    {
                        "id": req_id,
                        "ok": False,
                        "method": method,
                        "error": {
                            "type": type(exc).__name__,
                            "message": str(exc),
                        },
                    }
                )
                continue
            emit(
                {
                    "id": req_id,
                    "ok": True,
                    "method": method,
                    "line": resolved_line,
                    "character": resolved_character,
                    "timingsMs": {
                        "bridge": round((time.perf_counter() - started) * 1000),
                    },
                    "result": result,
                }
            )
    finally:
        session.close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
