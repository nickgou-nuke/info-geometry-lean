#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Mapping

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.alexandria.schema import SCHEMA_VERSION, content_hash, stable_key
else:
    from tools.alexandria.schema import SCHEMA_VERSION, content_hash, stable_key


@dataclass
class GateResult:
    key: str
    attemptKey: str | None
    gate: str
    command: list[str]
    passed: bool
    returncode: int
    stdout: str
    stderr: str
    elapsedSeconds: float


@dataclass
class RepairAttempt:
    key: str
    brokenNodeKey: str
    purifiedNodeKey: str | None
    representation: str
    agent: str
    gate: str
    status: str
    candidateHash: str
    errorDigest: str
    startedAtUnix: float
    completedAtUnix: float
    schema: str = SCHEMA_VERSION


def node_collection(node: Mapping[str, Any]) -> str:
    collection = node.get("_collection")
    if isinstance(collection, str) and collection:
        return collection
    if "chunkKind" in node:
        return "alexandria_chunks"
    if "entityType" in node:
        return "alexandria_entities"
    if "sourceKind" in node:
        return "alexandria_documents"
    raise ValueError("node must include _collection or recognizable Alexandria fields")


def node_key(node: Mapping[str, Any]) -> str:
    key = node.get("_key") or node.get("key")
    if not isinstance(key, str) or not key:
        raise ValueError("node must include _key or key")
    return key


def arango_id(node: Mapping[str, Any]) -> str:
    return f"{node_collection(node)}/{node_key(node)}"


def run_gate(command: list[str], *, gate: str, cwd: Path | None = None, timeout: int = 300) -> GateResult:
    start = time.time()
    try:
        completed = subprocess.run(
            command,
            cwd=str(cwd) if cwd else None,
            check=False,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return GateResult(
            key="",
            attemptKey=None,
            gate=gate,
            command=command,
            passed=completed.returncode == 0,
            returncode=completed.returncode,
            stdout=completed.stdout,
            stderr=completed.stderr,
            elapsedSeconds=round(time.time() - start, 6),
        )
    except subprocess.TimeoutExpired as exc:
        return GateResult(
            key="",
            attemptKey=None,
            gate=gate,
            command=command,
            passed=False,
            returncode=124,
            stdout=exc.stdout or "",
            stderr=exc.stderr or f"timeout after {timeout}s",
            elapsedSeconds=round(time.time() - start, 6),
        )


def purified_chunk_from_broken(
    broken: Mapping[str, Any],
    purified_text: str,
    *,
    representation: str,
    agent: str,
    gate_result: GateResult,
) -> dict[str, Any]:
    broken_key = node_key(broken)
    now = time.time()
    purified_hash = content_hash(purified_text)
    provenance = dict(broken.get("provenance", {})) if isinstance(broken.get("provenance"), dict) else {}
    provenance.update(
        {
            "schema": SCHEMA_VERSION,
            "representation": representation,
            "role": "verified" if gate_result.passed else "repair",
            "status": "compiled" if gate_result.passed else "failed",
            "authority": "compiler" if gate_result.passed else "test",
            "provenance": "llm_repaired",
            "repairAgent": agent,
            "repairOf": broken_key,
            "repairGate": gate_result.gate,
            "repairGatePassed": gate_result.passed,
            "purifiedAtUnix": now,
        }
    )
    purified = dict(broken)
    purified.update(
        {
            "_key": stable_key("purified", broken_key, purified_hash, gate_result.gate),
            "text": purified_text,
            "contentHash": purified_hash,
            "active": bool(gate_result.passed),
            "replacesNodeKey": broken_key,
            "representation": representation,
            "role": "verified" if gate_result.passed else "repair",
            "status": "compiled" if gate_result.passed else "failed",
            "authority": "compiler" if gate_result.passed else "test",
            "provenance": provenance,
        }
    )
    return purified


def build_repair_attempt(
    broken: Mapping[str, Any],
    purified: Mapping[str, Any] | None,
    *,
    candidate_text: str,
    representation: str,
    agent: str,
    gate_result: GateResult,
    started_at: float | None = None,
) -> RepairAttempt:
    broken_key = node_key(broken)
    purified_key = node_key(purified) if purified is not None else None
    status = "verified" if gate_result.passed and purified_key else "failed"
    error_text = "\n".join(part for part in [gate_result.stderr, gate_result.stdout] if part).strip()
    attempt = RepairAttempt(
        key=stable_key("repair", broken_key, content_hash(candidate_text), gate_result.gate, status),
        brokenNodeKey=broken_key,
        purifiedNodeKey=purified_key,
        representation=representation,
        agent=agent,
        gate=gate_result.gate,
        status=status,
        candidateHash=content_hash(candidate_text),
        errorDigest=content_hash(error_text[:4000]) if error_text else "",
        startedAtUnix=started_at if started_at is not None else time.time() - gate_result.elapsedSeconds,
        completedAtUnix=time.time(),
    )
    gate_result.key = stable_key("repair_gate", attempt.key, gate_result.gate, gate_result.returncode)
    gate_result.attemptKey = attempt.key
    return attempt


def build_lineage_edges(
    broken: Mapping[str, Any],
    attempt: RepairAttempt,
    purified: Mapping[str, Any] | None,
    *,
    gate_result: GateResult,
) -> list[dict[str, Any]]:
    broken_id = arango_id(broken)
    attempt_id = f"alexandria_repair_attempts/{attempt.key}"
    edges = [
        {
            "_key": stable_key("repair_edge", attempt.key, "attempted_on", node_key(broken)),
            "_from": broken_id,
            "_to": attempt_id,
            "kind": "attempted_repair",
            "provenance": "deterministic",
            "deterministic": True,
            "status": attempt.status,
            "gate": gate_result.gate,
        }
    ]
    if purified is not None:
        purified_id = arango_id(purified)
        edges.extend(
            [
                {
                    "_key": stable_key("repair_edge", attempt.key, "produced", node_key(purified)),
                    "_from": attempt_id,
                    "_to": purified_id,
                    "kind": "produced_candidate",
                    "provenance": "deterministic",
                    "deterministic": True,
                    "status": attempt.status,
                    "gate": gate_result.gate,
                },
                {
                    "_key": stable_key("repair_edge", node_key(purified), "replaces", node_key(broken)),
                    "_from": purified_id,
                    "_to": broken_id,
                    "kind": "replaces",
                    "provenance": "compiler_verified" if gate_result.passed else "repair_failed",
                    "deterministic": True,
                    "activeReplacement": bool(gate_result.passed),
                    "gate": gate_result.gate,
                },
                {
                    "_key": stable_key("repair_edge", node_key(broken), "superseded_by", node_key(purified)),
                    "_from": broken_id,
                    "_to": purified_id,
                    "kind": "superseded_by",
                    "provenance": "compiler_verified" if gate_result.passed else "repair_failed",
                    "deterministic": True,
                    "activeReplacement": bool(gate_result.passed),
                    "gate": gate_result.gate,
                },
            ]
        )
    return edges


def append_jsonl(path: Path, rows: list[Mapping[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(dict(row), ensure_ascii=True) + "\n")


def main() -> int:
    ap = argparse.ArgumentParser(description="Record Alexandria repair lineage for a broken node and compiler-gated candidate")
    ap.add_argument("--broken-node-json", required=True, type=Path)
    ap.add_argument("--candidate", required=True, type=Path)
    ap.add_argument("--output-dir", required=True, type=Path)
    ap.add_argument("--representation", required=True, choices=["lean4", "latex", "python", "sympy", "markdown"])
    ap.add_argument("--agent", default="codex")
    ap.add_argument("--gate", required=True, help="gate label, e.g. lake, latex-parser, py_compile, pytest")
    ap.add_argument("--command", nargs=argparse.REMAINDER, help="optional command to run as the compiler/parser/test gate; keep this as the final option")
    ap.add_argument("--cwd", type=Path)
    ap.add_argument("--timeout", type=int, default=300)
    args = ap.parse_args()

    broken = json.loads(args.broken_node_json.read_text(encoding="utf-8"))
    candidate_text = args.candidate.read_text(encoding="utf-8")
    started_at = time.time()
    if args.command:
        gate_result = run_gate(args.command, gate=args.gate, cwd=args.cwd, timeout=args.timeout)
    else:
        gate_result = GateResult("", None, args.gate, [], True, 0, "", "", 0.0)

    purified = purified_chunk_from_broken(
        broken,
        candidate_text,
        representation=args.representation,
        agent=args.agent,
        gate_result=gate_result,
    )
    attempt = build_repair_attempt(
        broken,
        purified if gate_result.passed else None,
        candidate_text=candidate_text,
        representation=args.representation,
        agent=args.agent,
        gate_result=gate_result,
        started_at=started_at,
    )
    edges = build_lineage_edges(broken, attempt, purified if gate_result.passed else None, gate_result=gate_result)

    append_jsonl(args.output_dir / "alexandria_repair_attempts.jsonl", [asdict(attempt)])
    if gate_result.passed:
        append_jsonl(args.output_dir / f"{node_collection(purified)}.jsonl", [purified])
    append_jsonl(args.output_dir / "alexandria_repair_lineage_edges.jsonl", edges)
    append_jsonl(args.output_dir / "alexandria_repair_gate_results.jsonl", [asdict(gate_result)])
    return 0 if gate_result.passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
