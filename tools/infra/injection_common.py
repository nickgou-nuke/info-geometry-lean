#!/usr/bin/env python3
"""Shared helpers for knowledge-injection packet tooling."""

from __future__ import annotations

import fcntl
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    import jsonschema
except Exception as e:  # pragma: no cover - strict dependency gate
    raise SystemExit("Missing dependency: jsonschema==4.23.0") from e

from tools.infra.build import run_locked_lake_build

LANES = ("raw", "distilled", "translated", "gated", "accepted", "rejected", "archive")
STATUS_MAP = {"archive": "archived"}
SOURCE_TYPES = {"web", "chat", "manual", "llm", "paper", "other"}
STATUSES = {"raw", "distilled", "translated", "gated", "accepted", "rejected", "archived"}
WORKFLOW_MODES = {"standard", "gemini-hermes-codex"}
AUTHORITY_TIERS = {"repo_native", "external_analogy"}

DEFAULT_PACKET_LOCK_DIR = Path("/tmp/info-geometry-injection-packet-locks")
TRANSITION_GRAPH: dict[str, set[str]] = {
    "raw": {"distilled", "rejected", "archive"},
    "distilled": {"translated", "rejected", "archive"},
    "translated": {"gated", "rejected", "archive"},
    "gated": {"accepted", "rejected", "archive"},
    "accepted": {"archive"},
    "rejected": {"archive"},
    "archive": set(),
}


class PacketLockBusyError(RuntimeError):
    def __init__(self, lock_path: Path, metadata: dict[str, Any] | None = None) -> None:
        self.lock_path = lock_path
        self.metadata = metadata or {}
        owner = self.metadata.get("owner")
        pid = self.metadata.get("pid")
        details = []
        if owner:
            details.append(f"owner={owner}")
        if pid:
            details.append(f"pid={pid}")
        suffix = f" ({', '.join(details)})" if details else ""
        super().__init__(f"packet lock busy: {lock_path}{suffix}")


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def default_packet_id() -> str:
    return "EXT-" + datetime.now(timezone.utc).strftime("%Y%m%d-%H%M%S")


def status_for_lane(lane: str) -> str:
    return STATUS_MAP.get(lane, lane)


def repo_root() -> Path:
    return Path(__file__).resolve().parents[2]


def injections_root(root: Path | None = None) -> Path:
    return (root or repo_root()) / "handover" / "injections"


def schema_path(root: Path | None = None) -> Path:
    return injections_root(root) / "schema" / "claim_packet.schema.json"


def resolve_packet(injections: Path, ref: str) -> Path:
    p = Path(ref)
    if p.exists():
        return p
    for lane in LANES:
        cand = injections / lane / f"{ref}.json"
        if cand.exists():
            return cand
    raise FileNotFoundError(f"packet not found for ref={ref}")


def _parse_iso_datetime(value: str, field: str) -> None:
    try:
        # Accept explicit `Z` as UTC too.
        datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError as exc:
        raise ValueError(f"{field} must be ISO datetime: {value!r}") from exc


def _require_dict(v: Any, name: str) -> dict[str, Any]:
    if not isinstance(v, dict):
        raise ValueError(f"{name} must be an object")
    return v


def _require_str(v: Any, name: str, *, min_len: int = 0) -> str:
    if not isinstance(v, str):
        raise ValueError(f"{name} must be a string")
    if len(v) < min_len:
        raise ValueError(f"{name} must have length >= {min_len}")
    return v


def _require_str_list(v: Any, name: str) -> list[str]:
    if not isinstance(v, list):
        raise ValueError(f"{name} must be a list")
    out: list[str] = []
    for i, item in enumerate(v):
        if not isinstance(item, str):
            raise ValueError(f"{name}[{i}] must be a string")
        out.append(item)
    return out


def _assert_no_extra_keys(data: dict[str, Any], allowed: set[str], name: str) -> None:
    extra = set(data.keys()) - allowed
    if extra:
        raise ValueError(f"{name} has unsupported keys: {', '.join(sorted(extra))}")


def _non_empty_str(v: Any, name: str) -> str:
    s = _require_str(v, name)
    if not s.strip():
        raise ValueError(f"{name} must be non-empty")
    return s


def validate_packet_schema(packet: dict[str, Any], *, schema_file: Path | None = None) -> None:
    """
    Strictly validate packet contract (hard fail).
    JSON Schema is mandatory.
    """
    sf = schema_file or schema_path()
    if not sf.exists():
        raise ValueError(f"schema file missing: {sf}")
    schema = json.loads(sf.read_text(encoding="utf-8"))
    validator = jsonschema.Draft202012Validator(schema, format_checker=jsonschema.FormatChecker())
    errors = sorted(validator.iter_errors(packet), key=lambda e: list(e.path))
    if errors:
        top = errors[0]
        where = ".".join(str(x) for x in top.path) or "<root>"
        raise ValueError(f"schema validation failed at {where}: {top.message}")

    # Additional hard checks beyond schema.
    required_top = {
        "packet_id",
        "title",
        "source",
        "raw_text",
        "distilled_claim",
        "repo_mapping",
        "verification_plan",
        "status",
        "history",
    }
    missing = [k for k in required_top if k not in packet]
    if missing:
        raise ValueError(f"packet missing required fields: {', '.join(sorted(missing))}")

    _require_str(packet["packet_id"], "packet_id", min_len=3)
    _require_str(packet["title"], "title", min_len=3)
    _require_str(packet["raw_text"], "raw_text")
    _require_str(packet["distilled_claim"], "distilled_claim")
    tier = str(packet.get("authority_tier", "repo_native"))
    if tier not in AUTHORITY_TIERS:
        raise ValueError(f"authority_tier must be one of {sorted(AUTHORITY_TIERS)}")

    status = _require_str(packet["status"], "status")
    if status not in STATUSES:
        raise ValueError(f"status must be one of {sorted(STATUSES)}")

    source = _require_dict(packet["source"], "source")
    _assert_no_extra_keys(source, {"type", "ref", "date"}, "source")
    stype = _require_str(source.get("type"), "source.type")
    if stype not in SOURCE_TYPES:
        raise ValueError(f"source.type must be one of {sorted(SOURCE_TYPES)}")
    _require_str(source.get("ref"), "source.ref")
    sdate = _require_str(source.get("date"), "source.date")
    _parse_iso_datetime(sdate, "source.date")

    repo_mapping = _require_dict(packet["repo_mapping"], "repo_mapping")
    _assert_no_extra_keys(
        repo_mapping,
        {"owner_files", "symbols", "target_theorems"},
        "repo_mapping",
    )
    _require_str_list(repo_mapping.get("owner_files"), "repo_mapping.owner_files")
    _require_str_list(repo_mapping.get("symbols"), "repo_mapping.symbols")
    _require_str_list(repo_mapping.get("target_theorems"), "repo_mapping.target_theorems")

    verification = _require_dict(packet["verification_plan"], "verification_plan")
    _assert_no_extra_keys(
        verification,
        {"build_targets", "audit_targets"},
        "verification_plan",
    )
    _require_str_list(verification.get("build_targets"), "verification_plan.build_targets")
    if "audit_targets" in verification:
        _require_str_list(verification.get("audit_targets"), "verification_plan.audit_targets")

    history = packet["history"]
    if not isinstance(history, list):
        raise ValueError("history must be a list")
    for i, row in enumerate(history):
        if not isinstance(row, dict):
            raise ValueError(f"history[{i}] must be an object")
        _assert_no_extra_keys(row, {"at", "event", "note"}, f"history[{i}]")
        if "at" not in row or "event" not in row:
            raise ValueError(f"history[{i}] missing required fields: at,event")
        _parse_iso_datetime(_require_str(row["at"], f"history[{i}].at"), f"history[{i}].at")
        _require_str(row["event"], f"history[{i}].event")
        if "note" in row:
            _require_str(row["note"], f"history[{i}].note")

    research = packet.get("research")
    if research is not None:
        if not isinstance(research, dict):
            raise ValueError("research must be an object when present")
        _assert_no_extra_keys(
            research,
            {"topic", "questions", "sources", "coverage", "workflow", "segments"},
            "research",
        )
        if "topic" in research:
            _require_str(research.get("topic"), "research.topic")
        if "questions" in research:
            _require_str_list(research.get("questions"), "research.questions")
        if "coverage" in research:
            _require_str(research.get("coverage"), "research.coverage")
        if "sources" in research:
            sources = research["sources"]
            if not isinstance(sources, list):
                raise ValueError("research.sources must be a list")
            for i, src in enumerate(sources):
                if isinstance(src, dict):
                    if "kind" in src:
                        _require_str(src["kind"], f"research.sources[{i}].kind")
                    if "ref" in src:
                        _require_str(src["ref"], f"research.sources[{i}].ref")
                    if "title" in src:
                        _require_str(src["title"], f"research.sources[{i}].title")
                    if "date" in src:
                        _require_str(src["date"], f"research.sources[{i}].date")
                elif not isinstance(src, str):
                    raise ValueError(f"research.sources[{i}] must be object or string")
        if "workflow" in research:
            workflow = research["workflow"]
            if not isinstance(workflow, dict):
                raise ValueError("research.workflow must be an object")
            _assert_no_extra_keys(
                workflow,
                {
                    "mode",
                    "creative_provider",
                    "verification_provider",
                    "coding_provider",
                    "creative_complete",
                    "verification_complete",
                },
                "research.workflow",
            )
            mode = _require_str(workflow.get("mode"), "research.workflow.mode")
            if mode not in WORKFLOW_MODES:
                raise ValueError(
                    f"research.workflow.mode must be one of {sorted(WORKFLOW_MODES)}"
                )
            _non_empty_str(workflow.get("creative_provider"), "research.workflow.creative_provider")
            _non_empty_str(
                workflow.get("verification_provider"), "research.workflow.verification_provider"
            )
            _non_empty_str(workflow.get("coding_provider"), "research.workflow.coding_provider")
            if not isinstance(workflow.get("creative_complete"), bool):
                raise ValueError("research.workflow.creative_complete must be boolean")
            if not isinstance(workflow.get("verification_complete"), bool):
                raise ValueError("research.workflow.verification_complete must be boolean")
        if "segments" in research:
            segments = research["segments"]
            if not isinstance(segments, list):
                raise ValueError("research.segments must be a list")
            seen_ids: set[str] = set()
            for i, seg in enumerate(segments):
                if not isinstance(seg, dict):
                    raise ValueError(f"research.segments[{i}] must be an object")
                _assert_no_extra_keys(
                    seg,
                    {
                        "segment_id",
                        "title",
                        "source_span",
                        "seed_text",
                        "creative_notes",
                        "enriched_context",
                        "claims",
                        "inference_flags",
                        "confidence",
                        "literature_evidence",
                    },
                    f"research.segments[{i}]",
                )
                seg_id = _non_empty_str(seg.get("segment_id"), f"research.segments[{i}].segment_id")
                if seg_id in seen_ids:
                    raise ValueError(f"duplicate research segment_id: {seg_id}")
                seen_ids.add(seg_id)
                _require_str(seg.get("seed_text"), f"research.segments[{i}].seed_text")
                if "title" in seg:
                    _require_str(seg["title"], f"research.segments[{i}].title")
                if "source_span" in seg:
                    _require_str(seg["source_span"], f"research.segments[{i}].source_span")
                if "creative_notes" in seg:
                    _require_str(seg["creative_notes"], f"research.segments[{i}].creative_notes")
                if "enriched_context" in seg:
                    _require_str(seg["enriched_context"], f"research.segments[{i}].enriched_context")
                if "claims" in seg:
                    _require_str_list(seg["claims"], f"research.segments[{i}].claims")
                if "inference_flags" in seg:
                    _require_str_list(
                        seg["inference_flags"], f"research.segments[{i}].inference_flags"
                    )
                if "confidence" in seg and not isinstance(seg["confidence"], (int, float)):
                    raise ValueError(f"research.segments[{i}].confidence must be numeric")
                if "literature_evidence" in seg:
                    evs = seg["literature_evidence"]
                    if not isinstance(evs, list):
                        raise ValueError(
                            f"research.segments[{i}].literature_evidence must be a list"
                        )
                    for j, ev in enumerate(evs):
                        if not isinstance(ev, dict):
                            raise ValueError(
                                f"research.segments[{i}].literature_evidence[{j}] must be an object"
                            )
                        _assert_no_extra_keys(
                            ev,
                            {"url", "title", "date", "summary", "relevance"},
                            f"research.segments[{i}].literature_evidence[{j}]",
                        )
                        _non_empty_str(
                            ev.get("url"),
                            f"research.segments[{i}].literature_evidence[{j}].url",
                        )
                        _non_empty_str(
                            ev.get("summary"),
                            f"research.segments[{i}].literature_evidence[{j}].summary",
                        )
                        if "title" in ev:
                            _require_str(
                                ev["title"],
                                f"research.segments[{i}].literature_evidence[{j}].title",
                            )
                        if "date" in ev:
                            _require_str(
                                ev["date"],
                                f"research.segments[{i}].literature_evidence[{j}].date",
                            )
                        if "relevance" in ev:
                            _require_str(
                                ev["relevance"],
                                f"research.segments[{i}].literature_evidence[{j}].relevance",
                            )


def append_history_event(
    packet: dict[str, Any],
    *,
    event: str,
    note: str = "",
    at: str | None = None,
    idempotent: bool = True,
) -> bool:
    hist = packet.setdefault("history", [])
    if not isinstance(hist, list):
        raise ValueError("history must be a list")
    note_hash = hashlib.sha256(note.encode("utf-8")).hexdigest()
    if idempotent:
        for row in hist:
            if not isinstance(row, dict):
                continue
            row_note = str(row.get("note", ""))
            row_note_hash = hashlib.sha256(row_note.encode("utf-8")).hexdigest()
            if str(row.get("event", "")) == event and row_note_hash == note_hash:
                return False
    hist.append({"at": at or utc_now(), "event": event, "note": note})
    return True


def write_json_atomic(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + f".tmp.{os.getpid()}")
    data = json.dumps(payload, ensure_ascii=True, indent=2) + "\n"
    with tmp.open("w", encoding="utf-8") as f:
        f.write(data)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)
    # fsync parent dir for rename durability.
    dir_fd = os.open(str(path.parent), os.O_RDONLY)
    try:
        os.fsync(dir_fd)
    finally:
        os.close(dir_fd)


def read_lock_metadata(lock_path: Path) -> dict[str, Any] | None:
    try:
        raw = lock_path.read_text(encoding="utf-8").strip()
    except FileNotFoundError:
        return None
    except OSError:
        return None
    if not raw:
        return None
    try:
        data = json.loads(raw)
    except json.JSONDecodeError:
        return {"raw": raw}
    return data if isinstance(data, dict) else {"raw": data}


def packet_lock_path(packet_id: str, *, lock_dir: Path = DEFAULT_PACKET_LOCK_DIR) -> Path:
    safe_id = re.sub(r"[^A-Za-z0-9_.-]+", "_", packet_id)
    return lock_dir / f"{safe_id}.lock"


class PacketLock:
    def __init__(self, packet_id: str, owner: str, *, block: bool = True) -> None:
        self.packet_id = packet_id
        self.owner = owner
        self.block = block
        self.lock_path = packet_lock_path(packet_id)
        self._handle: Any | None = None
        self.wait_seconds: float = 0.0

    def acquire(self) -> "PacketLock":
        self.lock_path.parent.mkdir(parents=True, exist_ok=True)
        handle = self.lock_path.open("a+", encoding="utf-8")
        flags = fcntl.LOCK_EX
        if not self.block:
            flags |= fcntl.LOCK_NB
        started = time.monotonic()
        try:
            fcntl.flock(handle.fileno(), flags)
        except BlockingIOError as exc:
            handle.close()
            raise PacketLockBusyError(self.lock_path, read_lock_metadata(self.lock_path)) from exc
        self.wait_seconds = max(0.0, time.monotonic() - started)
        handle.seek(0)
        handle.truncate(0)
        handle.write(
            json.dumps(
                {
                    "owner": self.owner,
                    "pid": os.getpid(),
                    "packet_id": self.packet_id,
                    "acquiredAt": time.time(),
                    "waitSeconds": self.wait_seconds,
                },
                ensure_ascii=False,
            )
            + "\n"
        )
        handle.flush()
        self._handle = handle
        return self

    def release(self) -> None:
        if self._handle is None:
            return
        handle = self._handle
        self._handle = None
        try:
            handle.seek(0)
            handle.truncate(0)
            handle.flush()
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
        finally:
            handle.close()

    def __enter__(self) -> "PacketLock":
        return self.acquire()

    def __exit__(self, exc_type, exc, tb) -> None:
        self.release()


def acquire_packet_lock(packet_id: str, owner: str, *, block: bool = True) -> PacketLock:
    # Return an unacquired context-managed lock; callers should use:
    #   with acquire_packet_lock(...) as lock:
    return PacketLock(packet_id, owner, block=block)


def packet_prompt_hash(packet: dict[str, Any]) -> str:
    """Deterministic hash for packet semantic input surface."""
    research = packet.get("research", {}) if isinstance(packet.get("research"), dict) else {}
    payload = {
        "packet_id": packet.get("packet_id", ""),
        "title": packet.get("title", ""),
        "raw_text": packet.get("raw_text", ""),
        "distilled_claim": packet.get("distilled_claim", ""),
        "topic": research.get("topic", ""),
        "questions": research.get("questions", []),
        "sources": research.get("sources", []),
        "workflow": research.get("workflow", {}),
        "segments": research.get("segments", []),
    }
    serialized = json.dumps(payload, sort_keys=True, ensure_ascii=True, separators=(",", ":"))
    return hashlib.sha256(serialized.encode("utf-8")).hexdigest()


def _run_version_cmd(cmd: list[str], cwd: Path) -> dict[str, Any]:
    exe = cmd[0] if cmd else ""
    if not exe:
        return {"cmd": cmd, "error": "empty command"}
    if shutil.which(exe) is None:
        return {"cmd": cmd, "missing": True}
    try:
        proc = subprocess.run(
            cmd,
            cwd=cwd,
            check=False,
            capture_output=True,
            text=True,
            timeout=2,
        )
        return {
            "cmd": cmd,
            "exit": proc.returncode,
            "stdout": proc.stdout.strip(),
            "stderr": proc.stderr.strip(),
        }
    except subprocess.TimeoutExpired:
        return {"cmd": cmd, "timeout_sec": 2}
    except Exception as exc:  # pragma: no cover - defensive
        return {"cmd": cmd, "error": str(exc)}


def collect_runtime_fingerprint(root: Path) -> dict[str, Any]:
    env_models = {
        "HERMES_MODEL": os.environ.get("HERMES_MODEL", ""),
        "OPENAI_MODEL": os.environ.get("OPENAI_MODEL", ""),
        "GEMINI_MODEL": os.environ.get("GEMINI_MODEL", ""),
        "LLM_MODEL": os.environ.get("LLM_MODEL", ""),
    }
    return {
        "python": sys.version,
        "platform": platform.platform(),
        "env_models": env_models,
        "versions": {
            "git_rev_parse": _run_version_cmd(["git", "rev-parse", "HEAD"], root),
            "git_describe": _run_version_cmd(["git", "describe", "--always", "--dirty"], root),
            "lake_version": _run_version_cmd(["lake", "--version"], root),
            "lean_version": _run_version_cmd(["lean", "--version"], root),
        },
    }


def current_gpu_memory_snapshot() -> dict[str, Any]:
    """
    Return per-GPU memory snapshot when nvidia-smi exists.
    """
    def parse_gpu_int(value: str) -> int | None:
        value = value.strip()
        if value in {"", "N/A", "[N/A]"}:
            return None
        return int(value)

    probe = _run_version_cmd(
        ["nvidia-smi", "--query-gpu=index,memory.total,memory.used,memory.free", "--format=csv,noheader,nounits"],
        repo_root(),
    )
    if probe.get("exit", 1) != 0:
        return {"available": False, "raw": probe}
    rows = []
    for line in probe.get("stdout", "").splitlines():
        parts = [p.strip() for p in line.split(",")]
        if len(parts) != 4:
            continue
        rows.append(
            {
                "index": int(parts[0]),
                "memory_total_mb": parse_gpu_int(parts[1]),
                "memory_used_mb": parse_gpu_int(parts[2]),
                "memory_free_mb": parse_gpu_int(parts[3]),
            }
        )
    return {"available": True, "gpus": rows}


def record_manifest_event(root: Path, row: dict[str, Any]) -> Path:
    events = injections_root(root) / "manifests" / "events.jsonl"
    events.parent.mkdir(parents=True, exist_ok=True)
    payload = dict(row)
    payload.setdefault("at", utc_now())
    payload.setdefault("gpu", current_gpu_memory_snapshot())
    line = json.dumps(payload, ensure_ascii=True, separators=(",", ":")) + "\n"
    with events.open("a", encoding="utf-8") as f:
        f.write(line)
        f.flush()
        os.fsync(f.fileno())
    return events


def write_run_manifest(
    root: Path,
    *,
    packet: dict[str, Any],
    stage: str,
    command_argv: list[str],
    result: dict[str, Any] | None = None,
    extra: dict[str, Any] | None = None,
) -> Path:
    packet_id = str(packet.get("packet_id", "unknown"))
    ts = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H%M%S.%fZ")
    out_dir = injections_root(root) / "manifests" / packet_id
    out_dir.mkdir(parents=True, exist_ok=True)
    stage_slug = stage.replace(":", "_")
    out = out_dir / f"{ts}-{stage_slug}.json"
    if out.exists():
        # Collision-safe fallback for concurrent or rapid same-loop writes.
        suffix = 1
        while True:
            candidate = out_dir / f"{ts}-{stage_slug}-{suffix}.json"
            if not candidate.exists():
                out = candidate
                break
            suffix += 1

    manifest = {
        "packet_id": packet_id,
        "stage": stage,
        "timestamp": utc_now(),
        "prompt_hash": packet_prompt_hash(packet),
        "command": command_argv,
        "runtime": collect_runtime_fingerprint(root),
        "result": result or {},
        "extra": extra or {},
    }
    write_json_atomic(out, manifest)
    record_manifest_event(
        root,
        {
            "packet_id": packet_id,
            "stage": stage,
            "command": command_argv,
            "result": result or {},
            "extra": extra or {},
        },
    )
    return out


def _non_empty_str_list(v: Any) -> list[str]:
    if not isinstance(v, list):
        return []
    return [str(x).strip() for x in v if str(x).strip()]


def packet_authority_tier(packet: dict[str, Any]) -> str:
    tier = str(packet.get("authority_tier", "repo_native")).strip()
    return tier if tier else "repo_native"


def check_transition_allowed(src_lane: str, dst_lane: str) -> None:
    if src_lane == dst_lane:
        return
    allowed = TRANSITION_GRAPH.get(src_lane, set())
    if dst_lane not in allowed:
        raise ValueError(f"invalid transition: {src_lane} -> {dst_lane}")


def enforce_translation_gate(packet: dict[str, Any]) -> None:
    mapping = packet.get("repo_mapping", {}) if isinstance(packet.get("repo_mapping"), dict) else {}
    owner_files = _non_empty_str_list(mapping.get("owner_files"))
    symbols = _non_empty_str_list(mapping.get("symbols"))
    target_theorems = _non_empty_str_list(mapping.get("target_theorems"))
    if not owner_files:
        raise ValueError("translated gate failed: repo_mapping.owner_files is empty")
    if not symbols:
        raise ValueError("translated gate failed: repo_mapping.symbols is empty")
    if not target_theorems:
        raise ValueError("translated gate failed: repo_mapping.target_theorems is empty")
    enforce_dual_stage_research_gate(packet)


def enforce_external_analogy_translation_gate(packet: dict[str, Any]) -> None:
    """
    External-analogy packets may be mapped to owner files/symbols but may not
    claim canonical theorem targets.
    """
    mapping = packet.get("repo_mapping", {}) if isinstance(packet.get("repo_mapping"), dict) else {}
    owner_files = _non_empty_str_list(mapping.get("owner_files"))
    symbols = _non_empty_str_list(mapping.get("symbols"))
    target_theorems = _non_empty_str_list(mapping.get("target_theorems"))
    if not owner_files:
        raise ValueError(
            "translated gate failed: external_analogy packet requires repo_mapping.owner_files"
        )
    if not symbols:
        raise ValueError(
            "translated gate failed: external_analogy packet requires repo_mapping.symbols"
        )
    if target_theorems:
        raise ValueError(
            "translated gate failed: external_analogy packet must not set repo_mapping.target_theorems"
        )
    enforce_dual_stage_research_gate(packet)


def enforce_gated_gate(packet: dict[str, Any]) -> None:
    enforce_translation_gate(packet)
    verification = (
        packet.get("verification_plan", {})
        if isinstance(packet.get("verification_plan"), dict)
        else {}
    )
    builds = _non_empty_str_list(verification.get("build_targets"))
    if not builds:
        raise ValueError("gated gate failed: verification_plan.build_targets is empty")


def enforce_authority_tier_transition_gate(packet: dict[str, Any], dst_lane: str) -> None:
    tier = packet_authority_tier(packet)
    if tier != "external_analogy":
        return
    if dst_lane in {"gated", "accepted"}:
        raise ValueError(
            "authority gate failed: external_analogy packets cannot be promoted to gated/accepted"
        )


def enforce_dual_stage_research_gate(packet: dict[str, Any]) -> None:
    """
    If packet declares gemini-hermes-codex workflow, enforce both stages are complete
    and segment cards are evidence-enriched.
    """
    research = packet.get("research")
    if not isinstance(research, dict):
        return
    workflow = research.get("workflow")
    if not isinstance(workflow, dict):
        return
    mode = str(workflow.get("mode", "")).strip()
    if mode != "gemini-hermes-codex":
        return

    if workflow.get("creative_complete") is not True:
        raise ValueError(
            "translated gate failed: research.workflow.creative_complete must be true for gemini-hermes-codex mode"
        )
    if workflow.get("verification_complete") is not True:
        raise ValueError(
            "translated gate failed: research.workflow.verification_complete must be true for gemini-hermes-codex mode"
        )

    segments = research.get("segments")
    if not isinstance(segments, list) or not segments:
        raise ValueError(
            "translated gate failed: research.segments must be non-empty for gemini-hermes-codex mode"
        )

    for i, seg in enumerate(segments):
        if not isinstance(seg, dict):
            raise ValueError(f"translated gate failed: research.segments[{i}] must be object")
        creative_notes = str(seg.get("creative_notes", "")).strip()
        if not creative_notes:
            raise ValueError(
                f"translated gate failed: research.segments[{i}].creative_notes is empty"
            )
        evs = seg.get("literature_evidence", [])
        if not isinstance(evs, list) or not evs:
            raise ValueError(
                f"translated gate failed: research.segments[{i}].literature_evidence is empty"
            )


def run_and_record_build_targets(root: Path, packet: dict[str, Any]) -> dict[str, Any]:
    verification = (
        packet.get("verification_plan", {})
        if isinstance(packet.get("verification_plan"), dict)
        else {}
    )
    targets = _non_empty_str_list(verification.get("build_targets"))
    if not targets:
        raise ValueError("accepted gate failed: verification_plan.build_targets is empty")

    started = time.monotonic()
    results: list[dict[str, Any]] = []
    overall_ok = True
    for target in targets:
        rc = run_locked_lake_build([target], wait_for_lock=True)
        ok = rc == 0
        overall_ok = overall_ok and ok
        results.append({"target": target, "exit": rc, "ok": ok})
        if not ok:
            break
    elapsed = max(0.0, time.monotonic() - started)

    if not isinstance(packet.get("verification_results"), dict):
        packet["verification_results"] = {}
    verification_results = packet["verification_results"]
    verification_results["last_build_targets"] = targets
    verification_results["last_build_results"] = results
    verification_results["last_build_ok"] = overall_ok
    verification_results["last_build_at"] = utc_now()
    verification_results["last_build_elapsed_sec"] = elapsed
    if not overall_ok:
        failed = [r["target"] for r in results if not r["ok"]]
        raise ValueError(f"accepted gate failed: build targets failed: {failed}")
    return verification_results
