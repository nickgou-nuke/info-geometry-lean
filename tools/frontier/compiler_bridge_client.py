#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.build_lock import acquire_build_lock
    from tools.pathing import repo_root
    from tools.frontier.semantic_block_export import (
        JsonRpcError,
        LspClient,
        inject_rpc_import,
    )
else:
    from tools.build_lock import acquire_build_lock
    from tools.pathing import repo_root
    from tools.frontier.semantic_block_export import (
        JsonRpcError,
        LspClient,
        inject_rpc_import,
    )


RPC_IMPORT = "import Agent.ProofServerRpc\n"
BRIDGE_VERSION = {"schema": 1, "protocol": "ig.compiler/v1"}


def log_stage(message: str) -> None:
    print(f"[compiler-bridge] {message}", file=sys.stderr, flush=True)


def server_command(repo: Path, mode: str) -> tuple[list[str], dict[str, str] | None]:
    if mode == "stdlib":
        return ["lake", "env", "lean", "--server"], None
    built = repo / ".lake" / "build" / "bin" / "compilerBridgeServer"
    if built.exists():
        env = os.environ.copy()
        env["LEAN_WORKER_PATH"] = str(built)
        return ["lake", "env", str(built)], env
    return ["lake", "exe", "compilerBridgeServer"], None


def normalize_result(result: Any, line_delta: int) -> Any:
    if line_delta == 0 or not isinstance(result, dict):
        return result
    out = dict(result)
    diagnostics = out.get("diagnostics")
    if isinstance(diagnostics, list):
        norm_diags: list[Any] = []
        for diag in diagnostics:
            if not isinstance(diag, dict):
                norm_diags.append(diag)
                continue
            norm = dict(diag)
            if isinstance(norm.get("line"), int):
                norm["line"] = max(0, int(norm["line"]) - line_delta)
            norm_diags.append(norm)
        out["diagnostics"] = norm_diags
    return out


def build_rpc_invocation(
    rpc_method: str,
    line: int,
    character: int,
    line_delta: int,
    decl_name: str | None,
) -> tuple[str, dict[str, Any]]:
    pos_line = max(0, line + line_delta)
    if rpc_method == "getProofState":
        return (
            "IG.Compiler.getProofState",
            {
                "version": BRIDGE_VERSION,
                "posLine": pos_line,
                "posCharacter": character,
            },
        )
    if rpc_method == "checkSnippet":
        return (
            "IG.Compiler.checkSnippet",
            {
                "version": BRIDGE_VERSION,
                "posLine": pos_line,
                "posCharacter": character,
            },
        )
    if rpc_method == "getEnvFingerprint":
        return ("IG.Compiler.getEnvFingerprint", {"version": BRIDGE_VERSION})
    if rpc_method == "validateDecl":
        if not decl_name:
            raise ValueError("--decl-name is required for --rpc-method validateDecl")
        return (
            "IG.Compiler.validateDecl",
            {
                "version": BRIDGE_VERSION,
                "declName": decl_name,
            },
        )
    raise ValueError(f"Unsupported rpc method: {rpc_method}")


def call_bridge_method(
    input_path: Path,
    line: int,
    character: int,
    timeout_s: float,
    server_mode: str,
    inject_rpc_import_flag: bool,
    wait_for_diagnostics: bool,
    rpc_method: str,
    decl_name: str | None,
) -> dict[str, Any]:
    repo = repo_root()
    cmd, env = server_command(repo, server_mode)
    effective_inject_rpc_import = inject_rpc_import_flag or server_mode == "stdlib"
    if server_mode == "stdlib" and not inject_rpc_import_flag:
        log_stage("auto-enable RPC shim import for stdlib server mode")
    abs_input = input_path.resolve()
    uri = abs_input.as_uri()
    original_text = abs_input.read_text(encoding="utf-8")
    if effective_inject_rpc_import and not original_text.startswith(RPC_IMPORT):
        text, _, line_delta = inject_rpc_import(original_text)
    else:
        text, line_delta = original_text, 0
    workspace_uri = repo.resolve().as_uri()
    build_lock = acquire_build_lock(None, f"compiler-bridge:{abs_input}")
    client = LspClient(cmd, repo, env)

    try:
        log_stage(f"server command: {' '.join(cmd)}")
        client.request(
            "initialize",
            {
                "processId": None,
                "clientInfo": {"name": "compiler-bridge-client", "version": "0.1"},
                "capabilities": {},
                "rootUri": workspace_uri,
                "workspaceFolders": [{"uri": workspace_uri, "name": repo.name}],
                "trace": "off",
            },
            timeout_s=timeout_s,
        )
        client.notify("initialized", {})
        client.drain(timeout_s=min(1.0, timeout_s))
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
            client.request(
                "textDocument/waitForDiagnostics",
                {"uri": uri, "version": 1},
                timeout_s=timeout_s,
            )
        else:
            client.drain(timeout_s=min(1.0, timeout_s))
        rpc_connected = client.request(
            "$/lean/rpc/connect",
            {"uri": uri},
            timeout_s=timeout_s,
        )
        rpc_name, method_params = build_rpc_invocation(
            rpc_method=rpc_method,
            line=line,
            character=character,
            line_delta=line_delta,
            decl_name=decl_name,
        )
        rpc_params = {
            "textDocument": {"uri": uri},
            "position": {"line": max(0, line + line_delta), "character": character},
            "sessionId": rpc_connected["sessionId"],
            "method": rpc_name,
            "params": method_params,
        }
        try:
            result = client.request(
                "$/lean/rpc/call",
                rpc_params,
                timeout_s=timeout_s,
            )
        except JsonRpcError as exc:
            msg = str(exc)
            if (
                server_mode == "stdlib"
                and effective_inject_rpc_import
                and f"No RPC method '{rpc_name}' found" in msg
            ):
                client.request(
                    "textDocument/waitForDiagnostics",
                    {"uri": uri, "version": 1},
                    timeout_s=timeout_s,
                )
                client.drain(timeout_s=min(1.0, timeout_s))
                rpc_connected = client.request(
                    "$/lean/rpc/connect",
                    {"uri": uri},
                    timeout_s=timeout_s,
                )
                rpc_params["sessionId"] = rpc_connected["sessionId"]
                result = client.request(
                    "$/lean/rpc/call",
                    rpc_params,
                    timeout_s=timeout_s,
                )
            else:
                raise
        client.request("shutdown", {}, timeout_s=timeout_s)
        client.notify("exit", {})
        return normalize_result(result, line_delta)
    finally:
        client.close()
        build_lock.release()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Call IG.Compiler bridge RPC methods for a Lean source file."
    )
    parser.add_argument("input", help="Path to the .lean source file")
    parser.add_argument("--line", type=int, default=0, help="0-based line")
    parser.add_argument("--character", type=int, default=0, help="0-based character")
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
        help="Use the dedicated compiler bridge server or stdlib `lean --server`",
    )
    parser.add_argument(
        "--inject-rpc-import",
        action="store_true",
        help="Inject `import Agent.ProofServerRpc` into virtual didOpen text",
    )
    parser.add_argument(
        "--skip-wait-for-diagnostics",
        action="store_true",
        help="Skip `textDocument/waitForDiagnostics` before the RPC call",
    )
    parser.add_argument(
        "--output",
        help="Optional path for the JSON result; stdout is used when omitted",
    )
    parser.add_argument(
        "--rpc-method",
        choices=("getProofState", "checkSnippet", "validateDecl", "getEnvFingerprint"),
        default="getProofState",
        help="Bridge method to invoke (default: getProofState)",
    )
    parser.add_argument(
        "--decl-name",
        help="Declaration name for validateDecl (for example, `My.Namespace.thmName`)",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    result = call_bridge_method(
        input_path=Path(args.input),
        line=args.line,
        character=args.character,
        timeout_s=args.timeout,
        server_mode=args.server_mode,
        inject_rpc_import_flag=args.inject_rpc_import,
        wait_for_diagnostics=not args.skip_wait_for_diagnostics,
        rpc_method=args.rpc_method,
        decl_name=args.decl_name,
    )
    payload = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(payload, encoding="utf-8")
    else:
        sys.stdout.write(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
