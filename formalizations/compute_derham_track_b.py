#!/usr/bin/env python3
"""Track B helper for compute_derham.m2.

Commands:
  - launch a background Macaulay2 run and record its PID/log
  - monitor an existing or just-completed run
  - emit compact JSON status/reports for CI notes or evidence logs
"""

from __future__ import annotations

import argparse
import json
import os
import shlex
import signal
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Optional


def run_cmd(cmd: list[str], timeout: int | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=timeout, check=False)


def _find_m2_pid(script_path: str) -> Optional[int]:
    script_base = Path(script_path).name
    cp = run_cmd(["ps", "-eo", "pid=,cmd="])  # plain text dump
    if cp.returncode != 0:
        return None
    for line in cp.stdout.splitlines():
        if "M2" not in line or "--script" not in line:
            continue
        if script_base not in line and script_path not in line:
            continue
        if "compute_derham.m2" not in line:
            continue
        if "grep" in line:
            continue
        parts = line.strip().split(maxsplit=1)
        if not parts:
            continue
        try:
            return int(parts[0])
        except ValueError:
            continue
    return None


def _is_running(pid: int) -> bool:
    return os.path.exists(f"/proc/{pid}")


def _process_state(pid: int) -> str:
    cp = run_cmd(["ps", "-p", str(pid), "-o", "state=,etime=,pcpu=,pmem=,"])  # e.g. S+  00:00:03
    if cp.returncode != 0 or not cp.stdout.strip():
        return "absent"
    return cp.stdout.strip().replace("\n", " ")


def _tail_new_lines(path: Path, cursor: int) -> tuple[str, int]:
    if not path.exists():
        return "", cursor
    with path.open("r", encoding="utf-8", errors="ignore") as f:
        f.seek(0, os.SEEK_END)
        end = f.tell()
        if cursor > end:
            cursor = 0
        f.seek(cursor)
        text = f.read()
        cursor = f.tell()
    return text, cursor


def _parse_output(text: str) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "started": "DLOCALIZE_EXT:status=starting" in text,
        "warning": "DLOCALIZE_EXT:warning=heavy Oaku localization; run with an external timeout" in text,
        "localization_completed": "DLOCALIZE_EXT:localization=completed" in text,
        "ext_started": "DLOCALIZE_EXT:computing=rationalFunctionExt" in text,
        "result_marker": "DLOCALIZE_EXT:result=" in text,
    }

    result = None
    marker = "DLOCALIZE_EXT:result="
    if marker in text:
        tail = text.split(marker, 1)[1]
        lines = [ln.strip() for ln in tail.splitlines() if ln.strip()]
        if lines:
            result = lines[0]
            if len(lines) > 1:
                # keep a compact excerpt in case result spans multiple lines
                result = "\\n".join(lines[:4])
    payload["result_excerpt"] = result

    if payload["result_marker"] and "DLOCALIZE_EXT:status=starting" in text:
        status = "completed"
    elif "timeout" in text.lower() or "timed out" in text.lower():
        status = "timed_out"
    elif payload["started"]:
        status = "running"
    else:
        status = "idle"
    payload["status"] = status
    return payload


def launch(script: Path, log_path: Path) -> int:
    M2 = shutil_which("M2") or shutil_which("m2-stack")
    if M2 is None:
        raise RuntimeError("M2 executable not found")
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_f = log_path.open("w", encoding="utf-8")
    p = subprocess.Popen(
        [M2, "--script", str(script)],
        stdout=log_f,
        stderr=subprocess.STDOUT,
        preexec_fn=os.setsid,
    )
    print(f"LAUNCHED pid={p.pid}")
    return p.pid


def shutil_which(name: str) -> str | None:
    for d in os.get_exec_path():
        p = Path(d) / name
        if p.is_file() and os.access(p, os.X_OK):
            return str(p)
    return None


def watch(pid: int | None, log_path: Path, interval: float, timeout: float | None, watch_stdout: bool) -> dict[str, Any]:
    start = time.time()
    cursor = 0
    last_result: dict[str, Any] = {"status": "unknown"}

    while True:
        if watch_stdout:
            chunk, cursor = _tail_new_lines(log_path, cursor)
            if chunk:
                for ln in chunk.rstrip("\n").splitlines():
                    print(f"[{time.strftime('%H:%M:%S')}] {ln}")

        if pid is not None:
            running = _is_running(pid)
            state = _process_state(pid)
        else:
            running = False
            state = "unknown"

        text = log_path.read_text(encoding="utf-8", errors="ignore") if log_path.exists() else ""
        status = _parse_output(text)
        if running and status.get("status") == "idle":
            status["status"] = "running"
        status.update({"pid": pid, "log": str(log_path), "process_state": state})
        last_result = status

        if not running:
            break

        if timeout is not None and (time.time() - start) >= timeout:
            print(f"watch timeout reached after {timeout:.1f}s")
            break

        time.sleep(interval)

    return last_result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--script", default="compute_derham.m2", help="path to track-b Macaulay2 script")
    parser.add_argument("--log", default="/tmp/compute_derham.out", help="log file to capture/read")
    parser.add_argument("--pid", type=int, default=None, help="M2 pid to monitor")
    parser.add_argument("--launch", action="store_true", help="launch compute_derham.m2 in background")
    parser.add_argument("--watch", action="store_true", help="stream log while watching process")
    parser.add_argument("--interval", type=float, default=5.0, help="poll interval (seconds)")
    parser.add_argument("--timeout", type=float, default=None, help="watch timeout (seconds)")
    parser.add_argument("--json", action="store_true", help="emit compact JSON report")
    args = parser.parse_args()

    script = Path(args.script)
    if not script.exists():
        print(f"Script not found: {script}", file=sys.stderr)
        return 1

    log_path = Path(args.log)

    if args.launch:
        pid = launch(script, log_path)
        if not args.watch:
            print(f"Launched Track B computation in background. Tail with:")
            print(f"  python3 {Path(__file__).name} --pid {pid} --log {shlex.quote(str(log_path))} --watch")
            return 0
        args.pid = pid

    pid = args.pid
    if pid is None:
        found = _find_m2_pid(str(script))
        pid = found

    final = watch(pid, log_path, args.interval, args.timeout, args.watch)

    if final.get("status") == "completed":
        code = 0
    elif final.get("status") in {"running", "timed_out", "unknown"}:
        code = 0
    elif final.get("status") == "idle":
        code = 1
    else:
        code = 1

    if args.json:
        print(json.dumps(final, indent=2, sort_keys=True))
    else:
        # concise human status
        if pid is not None:
            print(f"PID={pid}")
        print(f"LOG={log_path}")
        print(f"STATUS={final.get('status')}")
        print(f"STARTED={final.get('started')} LOCALIZED={final.get('localization_completed')} EXT={final.get('ext_started')}")
        if final.get("result_excerpt"):
            print(f"RESULT_EXCERPT={final.get('result_excerpt')}")

    return code


if __name__ == "__main__":
    raise SystemExit(main())
