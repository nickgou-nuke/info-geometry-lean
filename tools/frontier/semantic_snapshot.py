#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.build_lock import acquire_build_lock
from tools.infra.build import ensure_built_executable
from tools.pathing import lean_root, repo_root
from tools.frontier.semantic_block_export import (
    JsonRpcError,
    LspClient,
    adjust_pos,
    adjust_stable_id,
    fetch_semantic_blocks,
)
from tools.frontier.compiler_bridge_client import (
    CompilerBridgeSession,
    build_rpc_invocation,
    call_bridge_method,
    resolve_bridge_position,
)


SEMANTIC_RPC_IMPORT = "import DAG.SemanticServerRpc\n"
BRIDGE_RPC_IMPORT = "import Agent.ProofServerRpc\n"
SNAPSHOT_VERSION = {"schema": 1, "protocol": "ig.semantic-snapshot/v1"}


def log_stage(message: str) -> None:
    print(f"[semantic-snapshot] {message}", file=sys.stderr, flush=True)


def snapshot_server_command(
    repo: Path, mode: str
) -> tuple[list[str], dict[str, str] | None]:
    if mode == "stdlib":
        return ["lake", "env", "lean", "--server"], None
    built = ensure_built_executable(repo, "semanticSnapshotServer")
    return ["lake", "env", str(built)], None


def inject_snapshot_imports(text: str) -> tuple[str, int, int]:
    prefix = ""
    if not text.startswith(SEMANTIC_RPC_IMPORT):
        prefix += SEMANTIC_RPC_IMPORT
    if BRIDGE_RPC_IMPORT not in text[: len(prefix) + len(BRIDGE_RPC_IMPORT)]:
        prefix += BRIDGE_RPC_IMPORT
    if not prefix:
        return text, 0, 0
    return prefix + text, len(prefix.encode("utf-8")), prefix.count("\n")


def normalize_semantic_payload(payload: Any, byte_delta: int, line_delta: int) -> Any:
    if not isinstance(payload, dict):
        return payload
    out = dict(payload)
    if byte_delta != 0:
        if "rawBlocks" in out and isinstance(out["rawBlocks"], int):
            out["rawBlocks"] = max(0, int(out["rawBlocks"]) - 1)
        for key in ("blocks", "skeleton"):
            entries = out.get(key)
            if not isinstance(entries, list):
                continue
            normalized: list[Any] = []
            for entry in entries:
                if not isinstance(entry, dict):
                    normalized.append(entry)
                    continue
                norm_entry = dict(entry)
                if isinstance(norm_entry.get("stableId"), str):
                    norm_entry["stableId"] = adjust_stable_id(norm_entry["stableId"], byte_delta)
                if isinstance(norm_entry.get("startPos"), dict):
                    norm_entry["startPos"] = adjust_pos(norm_entry["startPos"], line_delta)
                if isinstance(norm_entry.get("stopPos"), dict):
                    norm_entry["stopPos"] = adjust_pos(norm_entry["stopPos"], line_delta)
                normalized.append(norm_entry)
            out[key] = normalized
    return out


def normalize_bridge_payload(payload: Any, line_delta: int) -> Any:
    if line_delta == 0 or not isinstance(payload, dict):
        return payload
    out = dict(payload)
    diagnostics = out.get("diagnostics")
    if isinstance(diagnostics, list):
        normalized: list[Any] = []
        for diag in diagnostics:
            if not isinstance(diag, dict):
                normalized.append(diag)
                continue
            norm_diag = dict(diag)
            if isinstance(norm_diag.get("line"), int):
                norm_diag["line"] = max(0, int(norm_diag["line"]) - line_delta)
            normalized.append(norm_diag)
        out["diagnostics"] = normalized
    return out


def module_name_guess(input_path: Path) -> str | None:
    root = lean_root().resolve()
    try:
        rel = input_path.resolve().relative_to(root)
    except ValueError:
        return None
    parts = list(rel.parts)
    if not parts or not parts[-1].endswith(".lean"):
        return None
    parts[-1] = parts[-1][:-5]
    return ".".join(part for part in parts if part)


def first_error(diagnostics: list[dict[str, Any]]) -> dict[str, Any] | None:
    for diag in diagnostics:
        if diag.get("severity") == "error":
            return diag
    return diagnostics[0] if diagnostics else None


def call_rpc(
    client: LspClient,
    *,
    uri: str,
    session_id: Any,
    method: str,
    params: dict[str, Any],
    line: int,
    character: int,
    timeout_s: float,
) -> Any:
    return client.request(
        "$/lean/rpc/call",
        {
            "textDocument": {"uri": uri},
            "position": {"line": line, "character": character},
            "sessionId": session_id,
            "method": method,
            "params": params,
        },
        timeout_s=timeout_s,
    )


def build_snapshot(
    *,
    input_path: Path,
    line: int | None,
    character: int,
    decl_name: str | None,
    timeout_s: float,
    server_mode: str,
    include_semantic_blocks: bool,
    include_env_fingerprint: bool,
    bridge_method: str,
    transcript_path: Path | None,
    stderr_path: Path | None,
    wait_for_diagnostics: bool,
    single_session: bool,
    pretty_print_type: bool,
    pretty_print_value: bool,
) -> dict[str, Any]:
    if not single_session:
        return build_snapshot_sequential(
            input_path=input_path,
            line=line,
            character=character,
            decl_name=decl_name,
            timeout_s=timeout_s,
            server_mode=server_mode,
            include_semantic_blocks=include_semantic_blocks,
            include_env_fingerprint=include_env_fingerprint,
            bridge_method=bridge_method,
            transcript_path=transcript_path,
            stderr_path=stderr_path,
            wait_for_diagnostics=wait_for_diagnostics,
            pretty_print_type=pretty_print_type,
            pretty_print_value=pretty_print_value,
        )
    return build_snapshot_single_session(
        input_path=input_path,
        line=line,
        character=character,
        decl_name=decl_name,
        timeout_s=timeout_s,
        server_mode=server_mode,
        include_semantic_blocks=include_semantic_blocks,
        include_env_fingerprint=include_env_fingerprint,
        bridge_method=bridge_method,
        transcript_path=transcript_path,
        stderr_path=stderr_path,
        wait_for_diagnostics=wait_for_diagnostics,
        pretty_print_type=pretty_print_type,
        pretty_print_value=pretty_print_value,
    )


def build_snapshot_sequential(
    *,
    input_path: Path,
    line: int | None,
    character: int,
    decl_name: str | None,
    timeout_s: float,
    server_mode: str,
    include_semantic_blocks: bool,
    include_env_fingerprint: bool,
    bridge_method: str,
    transcript_path: Path | None,
    stderr_path: Path | None,
    wait_for_diagnostics: bool,
    pretty_print_type: bool,
    pretty_print_value: bool,
) -> dict[str, Any]:
    abs_input = input_path.resolve()
    source_text = abs_input.read_text(encoding="utf-8")
    resolved_line, resolved_character = resolve_bridge_position(
        source_text=source_text,
        rpc_method=bridge_method,
        line=line,
        character=character,
        decl_name=decl_name,
    )
    timings_ms: dict[str, int] = {}
    started = time.perf_counter()
    semantic_blocks: Any = None
    env_fingerprint: Any = None
    bridge_payload: dict[str, Any] = {
        "method": bridge_method,
        "ok": bridge_method == "none",
        "result": None,
        "error": None,
    }
    bridge_session: CompilerBridgeSession | None = None

    if include_semantic_blocks:
        t0 = time.perf_counter()
        semantic_blocks = fetch_semantic_blocks(
            input_path=abs_input,
            timeout_s=timeout_s,
            transcript_path=transcript_path,
            stderr_path=stderr_path,
            server_mode=server_mode,
            inject_rpc_import_flag=False,
            wait_for_diagnostics=wait_for_diagnostics,
        )
        timings_ms["semanticBlocks"] = round((time.perf_counter() - t0) * 1000)

    if include_env_fingerprint or bridge_method != "none":
        bridge_session = CompilerBridgeSession(
            input_path=abs_input,
            timeout_s=timeout_s,
            server_mode=server_mode,
            inject_rpc_import_flag=False,
            wait_for_diagnostics=wait_for_diagnostics,
            transcript_path=transcript_path,
            stderr_path=stderr_path,
        )
        try:
            if include_env_fingerprint:
                t0 = time.perf_counter()
                env_fingerprint, _, _ = bridge_session.call(
                    rpc_method="getEnvFingerprint",
                    line=line,
                    character=character,
                    decl_name=None,
                    pretty_print_type=False,
                    pretty_print_value=False,
                )
                timings_ms["envFingerprint"] = round((time.perf_counter() - t0) * 1000)

            if bridge_method != "none":
                t0 = time.perf_counter()
                try:
                    bridge_payload["result"], _, _ = bridge_session.call(
                        rpc_method=bridge_method,
                        line=line,
                        character=character,
                        decl_name=decl_name,
                        pretty_print_type=pretty_print_type,
                        pretty_print_value=pretty_print_value,
                    )
                except Exception as exc:
                    bridge_payload["ok"] = False
                    bridge_payload["error"] = {"type": type(exc).__name__, "message": str(exc)}
                else:
                    bridge_payload["ok"] = True
                timings_ms["bridge"] = round((time.perf_counter() - t0) * 1000)
        finally:
            bridge_session.close()

    return finalize_snapshot_payload(
        input_path=abs_input,
        line=resolved_line,
        character=resolved_character,
        decl_name=decl_name,
        server_label=("sequential-stdlib" if server_mode == "stdlib" else "sequential-custom"),
        semantic_blocks=semantic_blocks,
        env_fingerprint=env_fingerprint,
        bridge_payload=bridge_payload,
        timings_ms=timings_ms,
        started=started,
    )


def build_snapshot_single_session(
    *,
    input_path: Path,
    line: int | None,
    character: int,
    decl_name: str | None,
    timeout_s: float,
    server_mode: str,
    include_semantic_blocks: bool,
    include_env_fingerprint: bool,
    bridge_method: str,
    transcript_path: Path | None,
    stderr_path: Path | None,
    wait_for_diagnostics: bool,
    pretty_print_type: bool,
    pretty_print_value: bool,
) -> dict[str, Any]:
    repo = repo_root()
    cmd, env = snapshot_server_command(repo, server_mode)
    abs_input = input_path.resolve()
    uri = abs_input.as_uri()
    original_text = abs_input.read_text(encoding="utf-8")
    if server_mode == "stdlib":
        text, byte_delta, line_delta = inject_snapshot_imports(original_text)
    else:
        text, byte_delta, line_delta = original_text, 0, 0
    workspace_uri = repo.resolve().as_uri()
    build_lock = acquire_build_lock(None, f"semantic-snapshot:{abs_input}")
    client = LspClient(cmd, repo, env, transcript_path, stderr_path)
    timings_ms: dict[str, int] = {}
    started = time.perf_counter()
    resolved_line, resolved_character = resolve_bridge_position(
        source_text=original_text,
        rpc_method=bridge_method,
        line=line,
        character=character,
        decl_name=decl_name,
    )
    call_line = max(0, ((resolved_line or 0) + line_delta))

    try:
        t0 = time.perf_counter()
        log_stage(f"server command: {' '.join(cmd)}")
        log_stage("initialize")
        client.request(
            "initialize",
            {
                "processId": None,
                "clientInfo": {"name": "semantic-snapshot", "version": "0.1"},
                "capabilities": {},
                "rootUri": workspace_uri,
                "workspaceFolders": [{"uri": workspace_uri, "name": repo.name}],
                "trace": "off",
            },
            timeout_s=timeout_s,
        )
        client.notify("initialized", {})
        client.drain(timeout_s=min(1.0, timeout_s))
        timings_ms["initialize"] = round((time.perf_counter() - t0) * 1000)

        t0 = time.perf_counter()
        log_stage(f"didOpen {abs_input}")
        client.notify(
            "textDocument/didOpen",
            {
                "textDocument": {
                    "uri": uri,
                    "languageId": "lean",
                    "version": 1,
                    "text": text,
                }
            },
        )
        if wait_for_diagnostics:
            log_stage("waitForDiagnostics")
            client.request(
                "textDocument/waitForDiagnostics",
                {"uri": uri, "version": 1},
                timeout_s=timeout_s,
            )
        else:
            log_stage("skip waitForDiagnostics")
            client.drain(timeout_s=min(1.0, timeout_s))
        timings_ms["didOpen"] = round((time.perf_counter() - t0) * 1000)

        t0 = time.perf_counter()
        log_stage("rpc/connect")
        rpc_connected = client.request(
            "$/lean/rpc/connect",
            {"uri": uri},
            timeout_s=timeout_s,
        )
        session_id = rpc_connected["sessionId"]
        timings_ms["rpcConnect"] = round((time.perf_counter() - t0) * 1000)

        semantic_blocks: Any = None
        env_fingerprint: Any = None
        bridge_payload: dict[str, Any] = {
            "method": bridge_method,
            "ok": bridge_method == "none",
            "result": None,
            "error": None,
        }

        if include_semantic_blocks:
            t0 = time.perf_counter()
            log_stage("rpc/call DAG.Server.semanticBlocks")
            raw = call_rpc(
                client,
                uri=uri,
                session_id=session_id,
                method="DAG.Server.semanticBlocks",
                params={"withText": False},
                line=0,
                character=0,
                timeout_s=timeout_s,
            )
            semantic_blocks = normalize_semantic_payload(raw, byte_delta, line_delta)
            timings_ms["semanticBlocks"] = round((time.perf_counter() - t0) * 1000)

        if include_env_fingerprint:
            t0 = time.perf_counter()
            log_stage("rpc/call IG.Compiler.getEnvFingerprint")
            raw = call_rpc(
                client,
                uri=uri,
                session_id=session_id,
                method="IG.Compiler.getEnvFingerprint",
                params={"version": {"schema": 1, "protocol": "ig.compiler/v1"}},
                line=call_line,
                character=resolved_character,
                timeout_s=timeout_s,
            )
            env_fingerprint = normalize_bridge_payload(raw, line_delta)
            timings_ms["envFingerprint"] = round((time.perf_counter() - t0) * 1000)

        if bridge_method != "none":
            t0 = time.perf_counter()
            rpc_name, rpc_params = build_rpc_invocation(
                rpc_method=bridge_method,
                line=resolved_line,
                character=resolved_character,
                line_delta=line_delta,
                decl_name=decl_name,
                pretty_print_type=pretty_print_type,
                pretty_print_value=pretty_print_value,
            )
            log_stage(f"rpc/call {rpc_name}")
            try:
                raw = call_rpc(
                    client,
                    uri=uri,
                    session_id=session_id,
                    method=rpc_name,
                    params=rpc_params,
                    line=call_line,
                    character=resolved_character,
                    timeout_s=timeout_s,
                )
                bridge_payload["result"] = normalize_bridge_payload(raw, line_delta)
            except Exception as exc:
                bridge_payload["ok"] = False
                bridge_payload["error"] = {"type": type(exc).__name__, "message": str(exc)}
            else:
                bridge_payload["ok"] = True
            timings_ms["bridge"] = round((time.perf_counter() - t0) * 1000)

        t0 = time.perf_counter()
        log_stage("shutdown")
        client.request("shutdown", {}, timeout_s=timeout_s)
        client.notify("exit", {})
        timings_ms["shutdown"] = round((time.perf_counter() - t0) * 1000)

        block_count = 0
        skeleton_count = 0
        raw_blocks = 0
        if isinstance(semantic_blocks, dict):
            blocks = semantic_blocks.get("blocks")
            skeleton = semantic_blocks.get("skeleton")
            if isinstance(blocks, list):
                block_count = len(blocks)
            if isinstance(skeleton, list):
                skeleton_count = len(skeleton)
            if isinstance(semantic_blocks.get("rawBlocks"), int):
                raw_blocks = int(semantic_blocks["rawBlocks"])

        return finalize_snapshot_payload(
            input_path=abs_input,
            line=resolved_line,
            character=resolved_character,
            decl_name=decl_name,
            server_label=("single-session-stdlib" if server_mode == "stdlib" else "single-session-custom"),
            semantic_blocks=semantic_blocks,
            env_fingerprint=env_fingerprint,
            bridge_payload=bridge_payload,
            timings_ms=timings_ms,
            started=started,
        )
    finally:
        client.close()
        build_lock.release()


def finalize_snapshot_payload(
    *,
    input_path: Path,
    line: int | None,
    character: int,
    decl_name: str | None,
    server_label: str,
    semantic_blocks: Any,
    env_fingerprint: Any,
    bridge_payload: dict[str, Any],
    timings_ms: dict[str, int],
    started: float,
) -> dict[str, Any]:
    block_count = 0
    skeleton_count = 0
    raw_blocks = 0
    if isinstance(semantic_blocks, dict):
        blocks = semantic_blocks.get("blocks")
        skeleton = semantic_blocks.get("skeleton")
        if isinstance(blocks, list):
            block_count = len(blocks)
        if isinstance(skeleton, list):
            skeleton_count = len(skeleton)
        if isinstance(semantic_blocks.get("rawBlocks"), int):
            raw_blocks = int(semantic_blocks["rawBlocks"])

    summary = {
        "module": module_name_guess(input_path),
        "blockCount": block_count,
        "skeletonCount": skeleton_count,
        "rawBlocks": raw_blocks,
        "bridgeMethod": bridge_payload["method"],
        "hasBridgeResult": bridge_payload["result"] is not None,
        "line": line,
        "character": character,
        "ok": True,
    }
    if isinstance(env_fingerprint, dict):
        diagnostics = env_fingerprint.get("diagnostics")
        if isinstance(diagnostics, list):
            summary["diagnosticCount"] = len(diagnostics)
            err = first_error([d for d in diagnostics if isinstance(d, dict)])
            if err is not None:
                summary["firstDiagnostic"] = {
                    "severity": err.get("severity"),
                    "line": err.get("line"),
                    "column": err.get("column"),
                    "message": err.get("message"),
                }
                if err.get("severity") == "error":
                    summary["ok"] = False
        ok = env_fingerprint.get("ok")
        if ok is False:
            summary["ok"] = False
    if bridge_payload.get("ok") is False:
        summary["ok"] = False
    bridge_result = bridge_payload.get("result")
    if isinstance(bridge_result, dict):
        goals = bridge_result.get("goals")
        if isinstance(goals, list):
            summary["goalCount"] = len(goals)
            if goals and isinstance(goals[0], dict) and isinstance(goals[0].get("target"), str):
                summary["firstGoalTarget"] = goals[0]["target"]
        decl_value = bridge_result.get("declarationValue")
        if isinstance(decl_value, str) and decl_value:
            summary["declarationValueLength"] = len(decl_value)
            summary["declarationValuePreview"] = decl_value[:240]

    return {
        "schemaVersion": SNAPSHOT_VERSION["schema"],
        "protocol": SNAPSHOT_VERSION["protocol"],
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "input": {
            "path": str(input_path),
            "line": line,
            "character": character,
            "declName": decl_name,
        },
        "servers": {
            "snapshot": server_label,
        },
        "timingsMs": {
            **timings_ms,
            "total": round((time.perf_counter() - started) * 1000),
        },
        "summary": summary,
        "envFingerprint": env_fingerprint,
        "semanticBlocks": semantic_blocks,
        "bridge": bridge_payload,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Write one server-backed snapshot packet combining semantic blocks, "
            "environment fingerprint, and an optional compiler-bridge query."
        )
    )
    parser.add_argument("input", help="Path to the .lean source file")
    parser.add_argument("output", help="Path to the output JSON snapshot")
    parser.add_argument("--line", type=int, default=None, help="0-based line for bridge query")
    parser.add_argument(
        "--character",
        type=int,
        default=0,
        help="0-based character for bridge query",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=300.0,
        help="Per-request timeout in seconds (default: 300)",
    )
    parser.add_argument(
        "--server-mode",
        choices=("custom", "stdlib"),
        default="custom",
        help="Use the combined custom snapshot server (default) or stdlib lean --server.",
    )
    parser.add_argument(
        "--bridge-method",
        choices=("none", "getGoalTargets", "getProofState", "checkSnippet", "validateDecl", "getEnvFingerprint"),
        default="none",
        help="Optional extra bridge method to include in the snapshot packet.",
    )
    parser.add_argument(
        "--decl-name",
        help="Declaration name for --bridge-method validateDecl",
    )
    parser.add_argument(
        "--pretty-print-type",
        action="store_true",
        help="Render declaration types via Lean's pretty printer for validateDecl (slower).",
    )
    parser.add_argument(
        "--pretty-print-value",
        action="store_true",
        help="Render declaration values/proof terms via Lean's pretty printer for validateDecl (slower).",
    )
    parser.add_argument(
        "--skip-semantic-blocks",
        action="store_true",
        help="Skip semantic-block extraction and keep only environment/proof-state data.",
    )
    parser.add_argument(
        "--skip-env-fingerprint",
        action="store_true",
        help="Skip the environment fingerprint query.",
    )
    parser.add_argument(
        "--skip-wait-for-diagnostics",
        action="store_true",
        help="Do not call textDocument/waitForDiagnostics before the RPC queries.",
    )
    parser.add_argument(
        "--proof-fast",
        action="store_true",
        help=(
            "Shortcut for low-latency proof-state snapshots: "
            "skip semantic blocks, skip env fingerprint, and skip waitForDiagnostics."
        ),
    )
    parser.add_argument(
        "--print-fast",
        action="store_true",
        help=(
            "Shortcut for the cheapest useful proof printout: "
            "use getGoalTargets and skip semantic blocks, env fingerprint, and diagnostics wait."
        ),
    )
    parser.add_argument(
        "--single-session",
        action="store_true",
        help="Use the experimental combined snapshot server instead of the stable sequential path.",
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


def main() -> int:
    args = parse_args()
    if args.proof_fast:
        args.skip_semantic_blocks = True
        args.skip_env_fingerprint = True
        args.skip_wait_for_diagnostics = True
        if args.bridge_method == "none":
            args.bridge_method = "getProofState"
    if args.print_fast:
        args.skip_semantic_blocks = True
        args.skip_env_fingerprint = True
        args.skip_wait_for_diagnostics = True
        if args.bridge_method == "none":
            args.bridge_method = "getGoalTargets"
    if args.bridge_method == "validateDecl" and args.pretty_print_value:
        args.skip_semantic_blocks = True
        args.skip_env_fingerprint = True
    snapshot = build_snapshot(
        input_path=Path(args.input),
        line=args.line,
        character=args.character,
        decl_name=args.decl_name,
        timeout_s=args.timeout,
        server_mode=args.server_mode,
        include_semantic_blocks=not args.skip_semantic_blocks,
        include_env_fingerprint=not args.skip_env_fingerprint,
        bridge_method=args.bridge_method,
        transcript_path=Path(args.transcript) if args.transcript else None,
        stderr_path=Path(args.stderr_log) if args.stderr_log else None,
        wait_for_diagnostics=not args.skip_wait_for_diagnostics,
        single_session=args.single_session,
        pretty_print_type=args.pretty_print_type,
        pretty_print_value=args.pretty_print_value,
    )
    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(
        json.dumps(snapshot, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    log_stage(f"wrote {output_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
