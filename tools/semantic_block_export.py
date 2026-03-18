#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import queue
import subprocess
import sys
import threading
import time
import re
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from pathing import repo_root
else:
    from tools.pathing import repo_root


class JsonRpcError(RuntimeError):
    pass


RPC_IMPORT = "import DAG.ServerExport\n"


class LspClient:
    def __init__(
        self,
        cmd: list[str],
        cwd: Path,
        env: dict[str, str] | None = None,
        transcript_path: Path | None = None,
        stderr_path: Path | None = None,
    ) -> None:
        self.proc = subprocess.Popen(
            cmd,
            cwd=str(cwd),
            env=env,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            bufsize=0,
        )
        assert self.proc.stdin is not None
        assert self.proc.stdout is not None
        assert self.proc.stderr is not None
        self._stdin = self.proc.stdin
        self._stdout = self.proc.stdout
        self._stderr = self.proc.stderr
        self._queue: queue.Queue[dict[str, Any]] = queue.Queue()
        self._backlog: list[dict[str, Any]] = []
        self._next_id = 1
        self._transcript: list[dict[str, Any]] = []
        self._stderr_lines: list[str] = []
        self._transcript_path = transcript_path
        self._stderr_path = stderr_path

        self._stdout_thread = threading.Thread(target=self._stdout_reader, daemon=True)
        self._stderr_thread = threading.Thread(target=self._stderr_reader, daemon=True)
        self._stdout_thread.start()
        self._stderr_thread.start()

    def _log(self, direction: str, payload: Any) -> None:
        self._transcript.append(
            {"ts": time.time(), "direction": direction, "payload": payload}
        )

    def _read_exact(self, n: int) -> bytes:
        chunks: list[bytes] = []
        remaining = n
        while remaining > 0:
            chunk = self._stdout.read(remaining)
            if not chunk:
                raise EOFError("stdout closed while reading LSP message body")
            chunks.append(chunk)
            remaining -= len(chunk)
        return b"".join(chunks)

    def _read_message(self) -> dict[str, Any]:
        headers: dict[str, str] = {}
        while True:
            line = self._stdout.readline()
            if not line:
                raise EOFError("stdout closed while reading LSP headers")
            if line == b"\r\n":
                break
            key, _, value = line.decode("utf-8").partition(":")
            headers[key.strip().lower()] = value.strip()
        try:
            length = int(headers["content-length"])
        except Exception as exc:  # pragma: no cover
            raise JsonRpcError(f"missing/invalid Content-Length header: {headers}") from exc
        body = self._read_exact(length)
        return json.loads(body.decode("utf-8"))

    def _stdout_reader(self) -> None:
        try:
            while True:
                msg = self._read_message()
                self._queue.put(msg)
        except EOFError:
            self._queue.put({"__eof__": True})

    def _stderr_reader(self) -> None:
        while True:
            line = self._stderr.readline()
            if not line:
                return
            text = line.decode("utf-8", errors="replace")
            self._stderr_lines.append(text)
            self._log("stderr", text.rstrip("\n"))

    def _write_message(self, payload: dict[str, Any]) -> None:
        body = json.dumps(payload, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
        header = f"Content-Length: {len(body)}\r\n\r\n".encode("ascii")
        self._stdin.write(header)
        self._stdin.write(body)
        self._stdin.flush()

    def _respond_to_server_request(self, payload: dict[str, Any]) -> None:
        method = payload.get("method")
        params = payload.get("params", {})
        if method == "workspace/configuration":
            result: Any = [None for _ in params.get("items", [])]
        elif method == "workspace/workspaceFolders":
            result = []
        else:
            result = None
        response = {"jsonrpc": "2.0", "id": payload["id"], "result": result}
        self._log("out", response)
        self._write_message(response)

    def _handle_incoming_message(self, payload: dict[str, Any]) -> bool:
        if payload.get("__eof__"):
            raise JsonRpcError("LSP process exited unexpectedly")
        if "method" not in payload:
            return False
        if "id" in payload:
            self._respond_to_server_request(payload)
        return True

    def notify(self, method: str, params: dict[str, Any]) -> None:
        payload = {"jsonrpc": "2.0", "method": method, "params": params}
        self._log("out", payload)
        self._write_message(payload)

    def _take_message(self, timeout_s: float) -> dict[str, Any]:
        if self._backlog:
            return self._backlog.pop(0)
        try:
            return self._queue.get(timeout=timeout_s)
        except queue.Empty as exc:
            raise TimeoutError("timed out waiting for LSP response") from exc

    def request(self, method: str, params: dict[str, Any], timeout_s: float) -> Any:
        req_id = self._next_id
        self._next_id += 1
        payload = {"jsonrpc": "2.0", "id": req_id, "method": method, "params": params}
        self._log("out", payload)
        self._write_message(payload)
        deadline = time.monotonic() + timeout_s
        while True:
            if time.monotonic() >= deadline:
                raise TimeoutError(f"timed out waiting for LSP response to {method}")
            remaining = max(0.01, deadline - time.monotonic())
            msg = self._take_message(remaining)
            self._log("in", msg)
            if self._handle_incoming_message(msg):
                continue
            if msg.get("id") != req_id:
                self._backlog.append(msg)
                continue
            if "error" in msg:
                raise JsonRpcError(json.dumps(msg["error"], ensure_ascii=False))
            return msg.get("result")

    def drain(self, timeout_s: float) -> None:
        deadline = time.monotonic() + timeout_s
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                return
            try:
                msg = self._take_message(min(0.1, remaining))
            except TimeoutError:
                return
            self._log("in", msg)
            if self._handle_incoming_message(msg):
                continue
            self._backlog.append(msg)

    def close(self) -> None:
        try:
            self.proc.terminate()
        except ProcessLookupError:
            pass
        try:
            self.proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.wait(timeout=5)
        if self._transcript_path is not None:
            self._transcript_path.parent.mkdir(parents=True, exist_ok=True)
            with self._transcript_path.open("w", encoding="utf-8") as f:
                for event in self._transcript:
                    f.write(json.dumps(event, ensure_ascii=False) + "\n")
        if self._stderr_path is not None:
            self._stderr_path.parent.mkdir(parents=True, exist_ok=True)
            self._stderr_path.write_text("".join(self._stderr_lines), encoding="utf-8")


def server_command(
    repo: Path, mode: str
) -> tuple[list[str], dict[str, str] | None]:
    if mode == "stdlib":
        return ["lake", "env", "lean", "--server"], None
    built = repo / ".lake" / "build" / "bin" / "semanticBlockServer"
    if built.exists():
        env = os.environ.copy()
        env["LEAN_WORKER_PATH"] = str(built)
        return ["lake", "env", str(built)], env
    return ["lake", "exe", "semanticBlockServer"], None


def log_stage(message: str) -> None:
    print(f"[semantic-block-export] {message}", file=sys.stderr, flush=True)


def inject_rpc_import(text: str) -> tuple[str, int, int]:
    if text.startswith(RPC_IMPORT):
        return text, 0, 0
    return RPC_IMPORT + text, len(RPC_IMPORT.encode("utf-8")), RPC_IMPORT.count("\n")


def adjust_stable_id(stable_id: str, byte_delta: int) -> str:
    m = re.fullmatch(r"block:(\d+)-(\d+)", stable_id)
    if m is None or byte_delta == 0:
        return stable_id
    start = max(0, int(m.group(1)) - byte_delta)
    stop = max(0, int(m.group(2)) - byte_delta)
    return f"block:{start}-{stop}"


def adjust_pos(pos: dict[str, Any], line_delta: int) -> dict[str, Any]:
    if line_delta == 0:
        return pos
    return {
        **pos,
        "line": max(1, int(pos["line"]) - line_delta),
    }


def normalize_payload(payload: Any, byte_delta: int, line_delta: int) -> Any:
    if not isinstance(payload, dict):
        return payload
    out = dict(payload)
    if byte_delta != 0:
        if "rawBlocks" in out and isinstance(out["rawBlocks"], int):
            out["rawBlocks"] = max(0, out["rawBlocks"] - 1)
        for key in ("blocks", "skeleton"):
            entries = out.get(key)
            if not isinstance(entries, list):
                continue
            norm_entries: list[Any] = []
            for entry in entries:
                if not isinstance(entry, dict):
                    norm_entries.append(entry)
                    continue
                norm_entry = dict(entry)
                if "stableId" in norm_entry and isinstance(norm_entry["stableId"], str):
                    norm_entry["stableId"] = adjust_stable_id(norm_entry["stableId"], byte_delta)
                if "startPos" in norm_entry and isinstance(norm_entry["startPos"], dict):
                    norm_entry["startPos"] = adjust_pos(norm_entry["startPos"], line_delta)
                if "stopPos" in norm_entry and isinstance(norm_entry["stopPos"], dict):
                    norm_entry["stopPos"] = adjust_pos(norm_entry["stopPos"], line_delta)
                norm_entries.append(norm_entry)
            out[key] = norm_entries
    return out


def export_semantic_blocks(
    input_path: Path,
    output_path: Path,
    timeout_s: float,
    transcript_path: Path | None,
    stderr_path: Path | None,
    server_mode: str,
    inject_rpc_import_flag: bool,
    wait_for_diagnostics: bool,
) -> None:
    repo = repo_root()
    cmd, env = server_command(repo, server_mode)
    log_stage(f"server command: {' '.join(cmd)}")
    client = LspClient(cmd, repo, env, transcript_path, stderr_path)
    abs_input = input_path.resolve()
    uri = abs_input.as_uri()
    original_text = abs_input.read_text(encoding="utf-8")
    if inject_rpc_import_flag:
        text, byte_delta, line_delta = inject_rpc_import(original_text)
    else:
        text, byte_delta, line_delta = original_text, 0, 0
    workspace_uri = repo.resolve().as_uri()

    try:
        log_stage("initialize")
        client.request(
            "initialize",
            {
                "processId": None,
                "clientInfo": {"name": "semantic-block-export", "version": "0.1"},
                "capabilities": {},
                "rootUri": workspace_uri,
                "workspaceFolders": [{"uri": workspace_uri, "name": repo.name}],
                "trace": "off",
            },
            timeout_s=timeout_s,
        )
        log_stage("initialized")
        client.notify("initialized", {})
        client.drain(timeout_s=min(1.0, timeout_s))
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
        log_stage("rpc/connect")
        rpc_connected = client.request(
            "$/lean/rpc/connect",
            {"uri": uri},
            timeout_s=timeout_s,
        )
        session_id = rpc_connected["sessionId"]
        log_stage(f"rpc/call DAG.Server.semanticBlocks session={session_id}")
        result = client.request(
            "$/lean/rpc/call",
            {
                "textDocument": {"uri": uri},
                "position": {"line": 0, "character": 0},
                "sessionId": session_id,
                "method": "DAG.Server.semanticBlocks",
                "params": {"withText": False},
            },
            timeout_s=timeout_s,
        )
        result = normalize_payload(result, byte_delta, line_delta)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(
            json.dumps(result, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )
        log_stage(f"wrote {output_path}")
        log_stage("shutdown")
        client.request("shutdown", {}, timeout_s=timeout_s)
        client.notify("exit", {})
    finally:
        client.close()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Export semantic block JSON for a Lean source file through an external Lean server process."
    )
    parser.add_argument("input", help="Path to the .lean source file")
    parser.add_argument("output", help="Path to the output JSON file")
    parser.add_argument(
        "--timeout",
        type=float,
        default=300.0,
        help="Per-request timeout in seconds (default: 300)",
    )
    parser.add_argument(
        "--transcript",
        default=None,
        help="Optional path for JSONL LSP transcript output",
    )
    parser.add_argument(
        "--stderr-log",
        default=None,
        help="Optional path for server stderr output",
    )
    parser.add_argument(
        "--server-mode",
        choices=("custom", "stdlib"),
        default="custom",
        help="Server launch mode: custom semanticBlockServer (default) or stdlib lean --server",
    )
    parser.add_argument(
        "--inject-rpc-import",
        action="store_true",
        help="Inject `import DAG.ServerExport` into the virtual didOpen text (experimental; mainly for stdlib server experiments).",
    )
    parser.add_argument(
        "--skip-wait-for-diagnostics",
        action="store_true",
        help="Do not call `textDocument/waitForDiagnostics` before connecting RPC; useful when the RPC itself already waits on snapshots.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    input_path = Path(args.input)
    output_path = Path(args.output)
    transcript_path = Path(args.transcript) if args.transcript else None
    stderr_path = Path(args.stderr_log) if args.stderr_log else None
    export_semantic_blocks(
        input_path=input_path,
        output_path=output_path,
        timeout_s=args.timeout,
        transcript_path=transcript_path,
        stderr_path=stderr_path,
        server_mode=args.server_mode,
        inject_rpc_import_flag=args.inject_rpc_import,
        wait_for_diagnostics=not args.skip_wait_for_diagnostics,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
