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
from tools.frontier.proof_runtime import (
    BRIDGE_METHOD_CHOICES,
    SESSION_METHOD_CHOICES,
    build_prewarm_request,
    summarize_bridge_response,
)


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
    parser.add_argument(
        "--prewarm-method",
        choices=BRIDGE_METHOD_CHOICES,
        default=None,
        help="Optional bridge method to run before emitting the ready event.",
    )
    parser.add_argument(
        "--prewarm-decl-name",
        help="Declaration name for prewarm validateDecl.",
    )
    parser.add_argument(
        "--prewarm-line",
        type=int,
        default=None,
        help="0-based line for prewarm goal/proof-state/snippet methods.",
    )
    parser.add_argument(
        "--prewarm-character",
        type=int,
        default=0,
        help="0-based character for the prewarm request (default: 0).",
    )
    parser.add_argument(
        "--prewarm-pretty-print-type",
        action="store_true",
        help="Pretty-print the type during prewarm validateDecl.",
    )
    parser.add_argument(
        "--prewarm-pretty-print-value",
        action="store_true",
        help="Pretty-print the value/proof term during prewarm validateDecl.",
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


def handle_request(
    session: CompilerBridgeSession,
    req: dict[str, Any],
    *,
    req_id: Any,
) -> dict[str, Any]:
    method = req.get("method")
    started = time.perf_counter()
    if method == "didChange":
        text = req.get("text")
        if not isinstance(text, str):
            return request_error(req_id, "didChange requires string field `text`")
        session.did_change(
            text,
            wait_for_diagnostics=req.get("waitForDiagnostics"),
        )
        return {
            "id": req_id,
            "ok": True,
            "method": method,
            "version": session.version,
            "timingsMs": {
                "bridge": round((time.perf_counter() - started) * 1000),
            },
        }
    if method == "reloadFromDisk":
        session.reload_from_disk(
            wait_for_diagnostics=req.get("waitForDiagnostics"),
        )
        return {
            "id": req_id,
            "ok": True,
            "method": method,
            "version": session.version,
            "timingsMs": {
                "bridge": round((time.perf_counter() - started) * 1000),
            },
        }
    result, resolved_line, resolved_character = session.call(
        rpc_method=method,
        line=req.get("line"),
        character=int(req.get("character", 0)),
        decl_name=req.get("declName"),
        pretty_print_type=bool(req.get("prettyPrintType", False)),
        pretty_print_value=bool(req.get("prettyPrintValue", False)),
    )
    return {
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
        ready_payload: dict[str, Any] = {
            "event": "ready",
            "input": str(Path(args.input).resolve()),
            "serverMode": args.server_mode,
        }
        prewarm_req = build_prewarm_request(
            method=args.prewarm_method,
            decl_name=args.prewarm_decl_name,
            line=args.prewarm_line,
            character=args.prewarm_character,
            pretty_print_type=args.prewarm_pretty_print_type,
            pretty_print_value=args.prewarm_pretty_print_value,
        )
        if prewarm_req is not None:
            try:
                prewarm_result = handle_request(session, prewarm_req, req_id="prewarm")
            except Exception as exc:
                ready_payload["prewarm"] = {
                    "ok": False,
                    "error": {
                        "type": type(exc).__name__,
                        "message": str(exc),
                    },
                }
            else:
                ready_payload["prewarm"] = summarize_bridge_response(prewarm_result)
        emit(
            ready_payload
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
            if method not in SESSION_METHOD_CHOICES:
                emit(request_error(req_id, f"unsupported method: {method}"))
                continue
            try:
                response = handle_request(session, req, req_id=req_id)
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
            emit(response)
    finally:
        session.close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
