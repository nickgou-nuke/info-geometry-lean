#!/usr/bin/env python3
"""BuildBee worker for first-class Hive build.verify tasks.

This worker is intentionally narrow:
- claims only `task_kind = "build.verify"`;
- runs Lake only through `tools/infra/run_locked_lake_build.py`;
- emits `BuildPacket` rows for visible lock-wait/running/final state;
- leaves proof truth and promotion to Lean/audit gates.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.infra import hive_arango_queue as queue_tool

DEFAULT_HIVE_ENDPOINT = queue_tool.DEFAULT_ENDPOINT
DEFAULT_HIVE_DATABASE = queue_tool.DEFAULT_DATABASE
DEFAULT_HIVE_USERNAME = queue_tool.DEFAULT_USERNAME
DEFAULT_HIVE_PASSWORD = queue_tool.DEFAULT_PASSWORD
DEFAULT_QUEUE = "build-verify"
DEFAULT_WORKER_ID = "hive-buildbee-001"
DEFAULT_LEASE_SECONDS = 7200
BUILD_WRAPPER = ROOT / "tools" / "infra" / "run_locked_lake_build.py"


@dataclass(frozen=True)
class BuildBeeConfig:
    hive_endpoint: str
    hive_database: str
    hive_username: str
    hive_password: str
    queue_name: str
    worker_id: str
    lease_seconds: int
    timeout: int


def emit_build_packet(
    config: BuildBeeConfig,
    task: dict[str, Any],
    *,
    state: str,
    command: list[str],
    returncode: int | None = None,
    stdout: str = "",
    stderr: str = "",
    started_at: str | None = None,
    finished_at: str | None = None,
    elapsed_s: float | None = None,
) -> dict[str, Any]:
    verification_key = str(task.get("verification_key") or "")
    target = str(task.get("target") or "")
    packet = {
        "schema": "hive.packet.build.v1",
        "authority": "build_checked",
        "representation_class": "owner",
        "representation_depth": "operatorial",
        "source_regime": "theorem_lane",
        "build_origin": "locked_lake_build",
        "verification_key": verification_key,
        "target": target,
        "state": state,
        "command": command,
        "returncode": returncode,
        "stdout_tail": stdout[-8000:],
        "stderr_tail": stderr[-8000:],
        "worker_id": config.worker_id,
        "task_key": task.get("_key"),
        "started_at": started_at,
        "finished_at": finished_at,
        "elapsed_s": elapsed_s,
    }
    dependencies = []
    if verification_key:
        dependencies.append({"schema": "hive.packet.verification.v1", "packet_key": verification_key})
    return queue_tool.import_packet_with_lineage(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        packet=packet,
        task_key_value=str(task.get("_key") or ""),
        dependencies=dependencies,
    )["packet"]


def claim_build_task(config: BuildBeeConfig) -> dict[str, Any] | None:
    queue_tool.init_schema(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
    )
    queue_tool.heartbeat_worker(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        worker_id=config.worker_id,
        capabilities=["build-verify", "locked-lake-build"],
        queues=[config.queue_name],
    )
    return queue_tool.claim_next_task(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        worker_id=config.worker_id,
        queue_name=config.queue_name,
        lease_seconds=config.lease_seconds,
        task_kind="build.verify",
    )


def command_for_task(task: dict[str, Any]) -> list[str]:
    target = str(task.get("target") or "").strip()
    if not target:
        raise ValueError("build.verify task requires target")
    cmd = [sys.executable, str(BUILD_WRAPPER), "--wait-for-build-lock"]
    if task.get("wfail"):
        cmd.append("--wfail")
    cmd.append(target)
    return cmd


def run_one(config: BuildBeeConfig) -> dict[str, Any]:
    task = claim_build_task(config)
    if not task:
        return {"status": "idle", "worker_id": config.worker_id, "queue_name": config.queue_name}

    command = command_for_task(task)
    lock_wait_packet = emit_build_packet(config, task, state="lock_wait", command=command)
    queue_tool.update_task_status(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        task_key_value=str(task["_key"]),
        worker_id=config.worker_id,
        status="lock_wait",
        extra_fields={"last_build_packet_key": lock_wait_packet["packet_key"]},
    )

    started_at = queue_tool.iso_now()
    running_packet = emit_build_packet(config, task, state="running", command=command, started_at=started_at)
    queue_tool.update_task_status(
        config.hive_endpoint,
        config.hive_database,
        config.hive_username,
        config.hive_password,
        task_key_value=str(task["_key"]),
        worker_id=config.worker_id,
        status="running",
        extra_fields={"last_build_packet_key": running_packet["packet_key"], "build_started_at": started_at},
    )

    env = os.environ.copy()
    env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env.get('PATH', '')}"
    t0 = time.time()
    try:
        proc = subprocess.run(
            command,
            cwd=ROOT,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=config.timeout,
            check=False,
        )
        elapsed = time.time() - t0
        finished_at = queue_tool.iso_now()
        state = "passed" if proc.returncode == 0 else "failed"
        final_packet = emit_build_packet(
            config,
            task,
            state=state,
            command=command,
            returncode=proc.returncode,
            stdout=proc.stdout or "",
            stderr=proc.stderr or "",
            started_at=started_at,
            finished_at=finished_at,
            elapsed_s=round(elapsed, 6),
        )
    except subprocess.TimeoutExpired as exc:
        elapsed = time.time() - t0
        finished_at = queue_tool.iso_now()
        stdout = exc.stdout if isinstance(exc.stdout, str) else ""
        stderr = exc.stderr if isinstance(exc.stderr, str) else ""
        final_packet = emit_build_packet(
            config,
            task,
            state="environment_blocked",
            command=command,
            returncode=None,
            stdout=stdout,
            stderr=stderr or f"build timed out after {config.timeout}s",
            started_at=started_at,
            finished_at=finished_at,
            elapsed_s=round(elapsed, 6),
        )
        state = "environment_blocked"

    if state == "passed":
        updated_task = queue_tool.complete_task(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            task_key_value=str(task["_key"]),
            worker_id=config.worker_id,
        )
    else:
        updated_task = queue_tool.fail_task(
            config.hive_endpoint,
            config.hive_database,
            config.hive_username,
            config.hive_password,
            task_key_value=str(task["_key"]),
            worker_id=config.worker_id,
            error_message=f"locked lake build {state}",
        )
    return {"status": state, "task": updated_task or task, "build_packet": final_packet}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hive-endpoint", default=DEFAULT_HIVE_ENDPOINT)
    parser.add_argument("--hive-database", default=DEFAULT_HIVE_DATABASE)
    parser.add_argument("--hive-username", default=DEFAULT_HIVE_USERNAME)
    parser.add_argument("--hive-password", default=DEFAULT_HIVE_PASSWORD)
    parser.add_argument("--queue-name", default=DEFAULT_QUEUE)
    parser.add_argument("--worker-id", default=DEFAULT_WORKER_ID)
    parser.add_argument("--lease-seconds", type=int, default=DEFAULT_LEASE_SECONDS)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--once", action="store_true", help="run one build task and exit")
    parser.add_argument("--poll-interval", type=int, default=15)
    return parser.parse_args()


def config_from_args(args: argparse.Namespace) -> BuildBeeConfig:
    return BuildBeeConfig(
        hive_endpoint=str(args.hive_endpoint).rstrip("/"),
        hive_database=str(args.hive_database),
        hive_username=str(args.hive_username),
        hive_password=str(args.hive_password),
        queue_name=str(args.queue_name),
        worker_id=str(args.worker_id),
        lease_seconds=int(args.lease_seconds),
        timeout=int(args.timeout),
    )


def main() -> int:
    args = parse_args()
    config = config_from_args(args)
    while True:
        result = run_one(config)
        print(json.dumps(result, indent=2, ensure_ascii=False, sort_keys=True))
        if args.once:
            return 0
        time.sleep(max(1, int(args.poll_interval)))


if __name__ == "__main__":
    raise SystemExit(main())
