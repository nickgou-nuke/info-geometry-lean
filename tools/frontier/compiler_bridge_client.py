#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.build_lock import acquire_build_lock
from tools.pathing import repo_root
from tools.infra.build import ensure_built_executable
from tools.frontier.semantic_block_export import (
    JsonRpcError,
    LspClient,
    inject_rpc_import,
)
from tools.frontier.proof_runtime import BRIDGE_METHOD_CHOICES


RPC_IMPORT = "import Agent.ProofServerRpc\n"
BRIDGE_VERSION = {"schema": 1, "protocol": "ig.compiler/v1"}
DECL_HEAD_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:private\s+|protected\s+)?"
    r"(?:theorem|lemma|def|abbrev|opaque|instance)\s+([^\s:(\[{]+)"
)


def log_stage(message: str) -> None:
    print(f"[compiler-bridge] {message}", file=sys.stderr, flush=True)


def server_command(repo: Path, mode: str) -> tuple[list[str], dict[str, str] | None]:
    built = ensure_built_executable(repo, "compilerBridgeServer")
    env = os.environ.copy()
    env["LEAN_WORKER_PATH"] = str(built)
    if mode == "stdlib":
        log_stage(
            "stdlib server mode does not expose IG.Compiler RPC methods; "
            "using compilerBridgeServer instead"
        )
    return ["lake", "env", str(built)], env


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


def infer_decl_position_in_text(text: str, decl_name: str) -> tuple[int, int] | None:
    short_name = decl_name.rsplit(".", 1)[-1]
    for idx, raw_line in enumerate(text.splitlines()):
        match = DECL_HEAD_RE.match(raw_line)
        if match is None or match.group(1) != short_name:
            continue
        column = raw_line.find(short_name)
        return idx, max(0, column)
    return None


def resolve_bridge_position(
    *,
    source_text: str,
    rpc_method: str,
    line: int | None,
    character: int,
    decl_name: str | None,
) -> tuple[int | None, int]:
    if line is not None or rpc_method not in ("validateDecl", "getDeclValue") or not decl_name:
        return line, character
    inferred = infer_decl_position_in_text(source_text, decl_name)
    if inferred is None:
        return None, character
    return inferred


def build_rpc_invocation(
    rpc_method: str,
    line: int | None,
    character: int,
    line_delta: int,
    decl_name: str | None,
    pretty_print_type: bool = False,
    pretty_print_value: bool = False,
) -> tuple[str, dict[str, Any]]:
    if rpc_method == "getGoalTargets":
        if line is None:
            raise ValueError("--line is required for --rpc-method getGoalTargets")
        pos_line = max(0, line + line_delta)
        return (
            "IG.Compiler.getGoalTargets",
            {
                "version": BRIDGE_VERSION,
                "posLine": pos_line,
                "posCharacter": character,
            },
        )
    if rpc_method == "getProofState":
        if line is None:
            raise ValueError("--line is required for --rpc-method getProofState")
        pos_line = max(0, line + line_delta)
        return (
            "IG.Compiler.getProofState",
            {
                "version": BRIDGE_VERSION,
                "posLine": pos_line,
                "posCharacter": character,
            },
        )
    if rpc_method == "checkSnippet":
        if line is None:
            raise ValueError("--line is required for --rpc-method checkSnippet")
        pos_line = max(0, line + line_delta)
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
        params: dict[str, Any] = {
            "version": BRIDGE_VERSION,
            "declName": decl_name,
            "prettyPrintType": pretty_print_type,
            "prettyPrintValue": pretty_print_value,
        }
        if line is not None:
            params["posLine"] = max(0, line + line_delta)
            params["posCharacter"] = character
        return (
            "IG.Compiler.validateDecl",
            params,
        )
    if rpc_method == "getDeclValue":
        if not decl_name:
            raise ValueError("--decl-name is required for --rpc-method getDeclValue")
        params: dict[str, Any] = {
            "version": BRIDGE_VERSION,
            "declName": decl_name,
        }
        if line is not None:
            params["posLine"] = max(0, line + line_delta)
            params["posCharacter"] = character
        return (
            "IG.Compiler.getDeclValue",
            params,
        )
    raise ValueError(f"Unsupported rpc method: {rpc_method}")


class CompilerBridgeSession:
    def __init__(
        self,
        *,
        input_path: Path,
        timeout_s: float,
        server_mode: str,
        inject_rpc_import_flag: bool,
        wait_for_diagnostics: bool,
        transcript_path: Path | None = None,
        stderr_path: Path | None = None,
    ) -> None:
        repo = repo_root()
        cmd, env = server_command(repo, server_mode)
        actual_stdlib_server = cmd[:3] == ["lake", "env", "lean"]
        effective_inject_rpc_import = inject_rpc_import_flag or actual_stdlib_server
        if actual_stdlib_server and not inject_rpc_import_flag:
            log_stage("auto-enable RPC shim import for stdlib server mode")
        abs_input = input_path.resolve()
        uri = abs_input.as_uri()
        original_text = abs_input.read_text(encoding="utf-8")
        if effective_inject_rpc_import and not original_text.startswith(RPC_IMPORT):
            text, _, line_delta = inject_rpc_import(original_text)
        else:
            text, line_delta = original_text, 0
        self.repo = repo
        self.cmd = cmd
        self.env = env
        self.server_mode = server_mode
        self.actual_stdlib_server = actual_stdlib_server
        self.effective_inject_rpc_import = effective_inject_rpc_import
        self.abs_input = abs_input
        self.uri = uri
        self.source_text = original_text
        self.text = text
        self.line_delta = line_delta
        self.version = 1
        self.timeout_s = timeout_s
        self.wait_for_diagnostics = wait_for_diagnostics
        self.workspace_uri = repo.resolve().as_uri()
        self.build_lock = acquire_build_lock(None, f"compiler-bridge:{abs_input}")
        self.client = LspClient(cmd, repo, env, transcript_path, stderr_path)
        self.session_id: Any | None = None
        self._opened = False
        self._closed = False

    def _set_source_text(self, source_text: str) -> None:
        if self.effective_inject_rpc_import and not source_text.startswith(RPC_IMPORT):
            text, _, line_delta = inject_rpc_import(source_text)
        else:
            text, line_delta = source_text, 0
        self.source_text = source_text
        self.text = text
        self.line_delta = line_delta

    def open(self) -> None:
        if self._opened:
            return
        log_stage(f"server command: {' '.join(self.cmd)}")
        log_stage("initialize")
        self.client.request(
            "initialize",
            {
                "processId": None,
                "clientInfo": {"name": "compiler-bridge-client", "version": "0.1"},
                "capabilities": {},
                "rootUri": self.workspace_uri,
                "workspaceFolders": [{"uri": self.workspace_uri, "name": self.repo.name}],
                "trace": "off",
            },
            timeout_s=self.timeout_s,
        )
        log_stage("initialized")
        self.client.notify("initialized", {})
        self.client.drain(timeout_s=min(1.0, self.timeout_s))
        log_stage(f"didOpen {self.abs_input}")
        self.client.notify(
            "textDocument/didOpen",
            {
                "textDocument": {
                    "uri": self.uri,
                    "languageId": "lean",
                    "version": self.version,
                    "text": self.text,
                }
            },
        )
        if self.wait_for_diagnostics:
            log_stage("waitForDiagnostics")
            self.client.request(
                "textDocument/waitForDiagnostics",
                {"uri": self.uri, "version": self.version},
                timeout_s=self.timeout_s,
            )
        else:
            log_stage("skip waitForDiagnostics")
            self.client.drain(timeout_s=min(1.0, self.timeout_s))
        self._connect_rpc()
        self._opened = True

    def _connect_rpc(self) -> None:
        log_stage("rpc/connect")
        rpc_connected = self.client.request(
            "$/lean/rpc/connect",
            {"uri": self.uri},
            timeout_s=self.timeout_s,
        )
        self.session_id = rpc_connected["sessionId"]

    def did_change(self, source_text: str, wait_for_diagnostics: bool | None = None) -> None:
        self.open()
        self.version += 1
        self._set_source_text(source_text)
        log_stage(f"didChange {self.abs_input} version={self.version}")
        self.client.notify(
            "textDocument/didChange",
            {
                "textDocument": {
                    "uri": self.uri,
                    "version": self.version,
                },
                "contentChanges": [{"text": self.text}],
            },
        )
        should_wait = self.wait_for_diagnostics if wait_for_diagnostics is None else wait_for_diagnostics
        if should_wait:
            log_stage("waitForDiagnostics")
            self.client.request(
                "textDocument/waitForDiagnostics",
                {"uri": self.uri, "version": self.version},
                timeout_s=self.timeout_s,
            )
        else:
            log_stage("skip waitForDiagnostics")
            self.client.drain(timeout_s=min(1.0, self.timeout_s))
        self.session_id = None

    def reload_from_disk(self, wait_for_diagnostics: bool | None = None) -> None:
        self.did_change(
            self.abs_input.read_text(encoding="utf-8"),
            wait_for_diagnostics=wait_for_diagnostics,
        )

    def call(
        self,
        *,
        rpc_method: str,
        line: int | None,
        character: int,
        decl_name: str | None,
        pretty_print_type: bool = False,
        pretty_print_value: bool = False,
    ) -> tuple[dict[str, Any], int | None, int]:
        self.open()
        resolved_line, resolved_character = resolve_bridge_position(
            source_text=self.source_text,
            rpc_method=rpc_method,
            line=line,
            character=character,
            decl_name=decl_name,
        )
        call_line = max(0, ((resolved_line or 0) + self.line_delta))
        rpc_name, method_params = build_rpc_invocation(
            rpc_method=rpc_method,
            line=resolved_line,
            character=resolved_character,
            line_delta=self.line_delta,
            decl_name=decl_name,
            pretty_print_type=pretty_print_type,
            pretty_print_value=pretty_print_value,
        )
        if self.session_id is None:
            log_stage("rpc/connect refresh")
            self._connect_rpc()
        rpc_params = {
            "textDocument": {"uri": self.uri},
            "position": {"line": call_line, "character": resolved_character},
            "sessionId": self.session_id,
            "method": rpc_name,
            "params": method_params,
        }
        log_stage(f"rpc/call {rpc_name} session={self.session_id}")
        try:
            result = self.client.request(
                "$/lean/rpc/call",
                rpc_params,
                timeout_s=self.timeout_s,
            )
        except JsonRpcError as exc:
            msg = str(exc)
            if "Outdated RPC session" in msg:
                log_stage("rpc/connect refresh")
                self._connect_rpc()
                rpc_params["sessionId"] = self.session_id
                log_stage(f"rpc/call retry {rpc_name} session={self.session_id}")
                result = self.client.request(
                    "$/lean/rpc/call",
                    rpc_params,
                    timeout_s=self.timeout_s,
                )
                return normalize_result(result, self.line_delta), resolved_line, resolved_character
            if (
                self.server_mode == "stdlib"
                and self.effective_inject_rpc_import
                and f"No RPC method '{rpc_name}' found" in msg
            ):
                self.client.request(
                    "textDocument/waitForDiagnostics",
                    {"uri": self.uri, "version": self.version},
                    timeout_s=self.timeout_s,
                )
                self.client.drain(timeout_s=min(1.0, self.timeout_s))
                log_stage("rpc/connect retry")
                self._connect_rpc()
                rpc_params["sessionId"] = self.session_id
                log_stage(f"rpc/call retry {rpc_name} session={self.session_id}")
                result = self.client.request(
                    "$/lean/rpc/call",
                    rpc_params,
                    timeout_s=self.timeout_s,
                )
            else:
                raise
        return normalize_result(result, self.line_delta), resolved_line, resolved_character

    def close(self) -> None:
        if self._closed:
            return
        try:
            if self._opened:
                log_stage("shutdown")
                try:
                    self.client.request("shutdown", {}, timeout_s=self.timeout_s)
                except Exception:
                    pass
                try:
                    self.client.notify("exit", {})
                except Exception:
                    pass
        finally:
            self.client.close()
            self.build_lock.release()
            self._closed = True


def call_bridge_method(
    input_path: Path,
    line: int | None,
    character: int,
    timeout_s: float,
    server_mode: str,
    inject_rpc_import_flag: bool,
    wait_for_diagnostics: bool,
    rpc_method: str,
    decl_name: str | None,
    pretty_print_type: bool = False,
    pretty_print_value: bool = False,
    transcript_path: Path | None = None,
    stderr_path: Path | None = None,
) -> dict[str, Any]:
    session = CompilerBridgeSession(
        input_path=input_path,
        timeout_s=timeout_s,
        server_mode=server_mode,
        inject_rpc_import_flag=inject_rpc_import_flag,
        wait_for_diagnostics=wait_for_diagnostics,
        transcript_path=transcript_path,
        stderr_path=stderr_path,
    )
    try:
        result, _, _ = session.call(
            rpc_method=rpc_method,
            line=line,
            character=character,
            decl_name=decl_name,
            pretty_print_type=pretty_print_type,
            pretty_print_value=pretty_print_value,
        )
        return result
    finally:
        session.close()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Call IG.Compiler bridge RPC methods for a Lean source file."
    )
    parser.add_argument("input", help="Path to the .lean source file")
    parser.add_argument(
        "--line",
        type=int,
        default=None,
        help=(
            "0-based line. Required for getProofState/checkSnippet; optional for "
            "validateDecl/getDeclValue, where it is auto-inferred when possible."
        ),
    )
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
        help=(
            "Use the dedicated compiler bridge server (default). "
            "`stdlib` is accepted for compatibility but is routed through "
            "the dedicated server because Lean stdlib server mode does not "
            "expose IG.Compiler RPC methods."
        ),
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
        choices=BRIDGE_METHOD_CHOICES,
        default="getProofState",
        help="Bridge method to invoke (default: getProofState)",
    )
    parser.add_argument(
        "--decl-name",
        help="Declaration name for validateDecl/getDeclValue (for example, `My.Namespace.thmName`)",
    )
    parser.add_argument(
        "--pretty-print-type",
        action="store_true",
        help="Render the declaration type via Lean's pretty printer (slower).",
    )
    parser.add_argument(
        "--pretty-print-value",
        action="store_true",
        help="Render the declaration value/proof term via Lean's pretty printer (slower).",
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
        pretty_print_type=args.pretty_print_type,
        pretty_print_value=args.pretty_print_value,
        transcript_path=Path(args.transcript) if args.transcript else None,
        stderr_path=Path(args.stderr_log) if args.stderr_log else None,
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
