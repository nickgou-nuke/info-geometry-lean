#!/usr/bin/env python3
"""Build canonical tactic SFT/DPO/failure datasets from local telemetry.

This script is intentionally conservative:

* SFT rows require a verified/successful transition with goal_before and tactic.
* DPO rows are created only from same theorem + same normalized goal hash.
* Failure-only rows remain separate unless paired with a real success.
* LeanTrail dependency failures are preserved as failure telemetry, not tactic SFT.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.infra.aesop_tactic_prior import classify_tactic


SCHEMA_SFT = "info_geometry.tactic_sft.v1"
SCHEMA_DPO = "info_geometry.tactic_dpo.v1"
SCHEMA_FAILURE = "info_geometry.tactic_failure.v1"
SCHEMA_STATS = "info_geometry.tactic_training_dataset.stats.v1"


def iter_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    if not path.exists():
        return
    with path.open("r", encoding="utf-8") as handle:
        for raw in handle:
            line = raw.strip()
            if not line:
                continue
            try:
                row = json.loads(line)
            except Exception:
                continue
            if isinstance(row, dict):
                yield row


def iter_json_docs(path: Path) -> Iterable[dict[str, Any]]:
    if path.is_file() and path.suffix == ".jsonl":
        yield from iter_jsonl(path)
        return
    if path.is_file() and path.suffix == ".json":
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            return
        if isinstance(payload, dict):
            yield payload
        elif isinstance(payload, list):
            for row in payload:
                if isinstance(row, dict):
                    yield row
        return
    if path.is_dir():
        for child in sorted(path.rglob("*.json")):
            yield from iter_json_docs(child)
        for child in sorted(path.rglob("*.jsonl")):
            yield from iter_json_docs(child)


def stable_hash(*parts: Any) -> str:
    text = json.dumps(parts, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return hashlib.sha1(text.encode("utf-8")).hexdigest()


def normalize_goal(text: Any) -> str:
    if text is None:
        return ""
    return re.sub(r"\s+", " ", str(text)).strip()


def goal_hash(text: Any) -> str:
    return stable_hash(normalize_goal(text))


def split_for(key: str, *, train_ratio: float, val_ratio: float, seed: int) -> str:
    digest = hashlib.sha1(f"{seed}|{key}".encode("utf-8")).hexdigest()
    x = int(digest[:15], 16) / float(16**15 - 1)
    if x < train_ratio:
        return "train"
    if x < train_ratio + val_ratio:
        return "val"
    return "test"


def tactic_family(tactic: Any) -> str:
    text = str(tactic or "").strip()
    return text.split()[0] if text.split() else ""


def lean_output_from_verification(value: Any) -> str:
    if not isinstance(value, dict):
        return ""
    lean = value.get("lean")
    if isinstance(lean, dict):
        return str(lean.get("stdout") or "") + str(lean.get("stderr") or "")
    return str(value.get("stdout") or "") + str(value.get("stderr") or "")


@dataclass(frozen=True)
class SuccessTransition:
    source: str
    theorem: str
    lean_file: str
    theorem_statement: str
    goal_before: str
    tactic: str
    goal_after: str
    dependencies: tuple[str, ...]
    raw_ref: dict[str, Any]
    node_class: str = "leaf"
    info_kind: str = "tactic"

    @property
    def goal_hash(self) -> str:
        return goal_hash(self.goal_before)

    @property
    def is_leaf_transition(self) -> bool:
        return self.node_class == "leaf"


@dataclass(frozen=True)
class FailureTransition:
    source: str
    theorem: str
    lean_file: str
    theorem_statement: str
    goal_before: str
    failed_tactic: str
    diagnostic: str
    failure_kind: str
    raw_ref: dict[str, Any]

    @property
    def goal_hash(self) -> str:
        return goal_hash(self.goal_before)


def leandojo_successes(path: Path) -> list[SuccessTransition]:
    out: list[SuccessTransition] = []
    for line_no, row in enumerate(iter_jsonl(path), start=1):
        theorem = str(row.get("theoremFullName") or row.get("declaration") or "")
        lean_file = str(row.get("leanFile") or "")
        statement = str(row.get("theoremStatement") or "")
        dependencies = tuple(str(dep) for dep in row.get("dependencies") or [] if isinstance(dep, str))
        for idx, tactic in enumerate(row.get("tactics") or []):
            if not isinstance(tactic, dict):
                continue
            goal_before = normalize_goal(tactic.get("stateBefore"))
            tactic_text = str(tactic.get("tactic") or "").strip()
            goal_after = normalize_goal(tactic.get("stateAfter"))
            if not goal_before or not tactic_text:
                continue
            node_class = str(tactic.get("node_class") or tactic.get("nodeClass") or "leaf")
            if node_class == "aggregate":
                continue
            out.append(
                SuccessTransition(
                    source="leandojo_v2",
                    theorem=theorem,
                    lean_file=lean_file,
                    theorem_statement=statement,
                    goal_before=goal_before,
                    tactic=tactic_text,
                    goal_after=goal_after,
                    dependencies=dependencies,
                    raw_ref={
                        "source_file": row.get("sourceFile") or str(path),
                        "source_line": row.get("sourceLine") or line_no,
                        "tactic_index": idx,
                    },
                    node_class=node_class,
                    info_kind=str(tactic.get("info_kind") or tactic.get("infoKind") or "tactic"),
                )
            )
    return out


def hive_successes(path: Path) -> list[SuccessTransition]:
    out: list[SuccessTransition] = []
    for row in iter_json_docs(path):
        if row.get("schema") != "info_geometry.hive_replay_packet.v1":
            continue
        theorem = str(row.get("generated_theorem_name") or "")
        lean_file = str(row.get("theorem_source_path") or "")
        theorem_statement = str(row.get("theorem_source") or "")
        goal_before = normalize_goal(row.get("proof_state_before"))
        trace = row.get("tactic_trace") or []
        tactic = ""
        goal_after = ""
        if isinstance(trace, list):
            for step in trace:
                if isinstance(step, dict) and step.get("phase") == "proposed":
                    tactic = str(step.get("tactic") or "").strip()
                if isinstance(step, dict) and step.get("phase") == "apply_tactic":
                    goal_after = str(step.get("lean_output") or "")
        if not goal_before or not tactic:
            continue
        out.append(
            SuccessTransition(
                source="hive",
                theorem=theorem,
                lean_file=lean_file,
                theorem_statement=theorem_statement,
                goal_before=goal_before,
                tactic=tactic,
                goal_after=goal_after,
                dependencies=tuple(),
                raw_ref={"source_key": row.get("_key"), "schema": row.get("schema")},
                node_class="leaf",
            )
        )
    return out


def hive_failures(path: Path) -> list[FailureTransition]:
    out: list[FailureTransition] = []
    for row in iter_json_docs(path):
        if row.get("schema") != "info_geometry.hive_deadend.v1":
            continue
        goal_before = normalize_goal(row.get("local_context_slice") or row.get("goal_hash_shape"))
        tactic = str(row.get("attempted_tactic") or "").strip()
        if not tactic:
            continue
        out.append(
            FailureTransition(
                source="hive",
                theorem=str(row.get("const_name") or row.get("goal_key") or ""),
                lean_file="",
                theorem_statement="",
                goal_before=goal_before,
                failed_tactic=tactic,
                diagnostic=str(row.get("verification_output") or ""),
                failure_kind=str(row.get("failure_kind") or "failure"),
                raw_ref={"source_key": row.get("_key"), "schema": row.get("schema")},
            )
        )
    return out


def leantrail_failures(path: Path) -> list[FailureTransition]:
    out: list[FailureTransition] = []
    for line_no, row in enumerate(iter_jsonl(path), start=1):
        src = str(row.get("src") or "")
        dst = str(row.get("dst") or "")
        failure_kind = str(row.get("error_kind") or row.get("kind") or "failure")
        out.append(
            FailureTransition(
                source="leantrail",
                theorem=src,
                lean_file="",
                theorem_statement="",
                goal_before=normalize_goal(row.get("goal_before") or src),
                failed_tactic=str(row.get("tactic") or row.get("attempted_tactic") or row.get("kind") or ""),
                diagnostic=str(row.get("diagnostic") or row.get("error") or f"{failure_kind}: {src} -> {dst}"),
                failure_kind=failure_kind,
                raw_ref={"source_file": str(path), "source_line": line_no, "id": row.get("id")},
            )
        )
    return out


def real_prover_successes(path: Path) -> list[SuccessTransition]:
    out: list[SuccessTransition] = []
    for line_no, row in enumerate(iter_jsonl(path), start=1):
        if row.get("schema") != "info_geometry.real_prover_trace.v1":
            continue
        statement = str(row.get("formal_statement") or "")
        for result_idx, result in enumerate(row.get("collect_results") or []):
            if not isinstance(result, dict):
                continue
            theorem = str(result.get("declaration") or "")
            nodes_by_id = {
                node.get("id"): node
                for node in result.get("nodes") or []
                if isinstance(node, dict)
            }
            for node_idx, node in enumerate(result.get("nodes") or []):
                if not isinstance(node, dict):
                    continue
                tactic = str(node.get("tactic") or "").strip()
                if not tactic:
                    continue
                parent = nodes_by_id.get(node.get("parent"))
                if not isinstance(parent, dict):
                    continue
                parent_state = parent.get("state") or []
                node_state = node.get("state") or []
                goal_before = normalize_goal("\n\n".join(str(x) for x in parent_state))
                goal_after = normalize_goal("\n\n".join(str(x) for x in node_state)) or "no goals"
                if not goal_before:
                    continue
                out.append(
                    SuccessTransition(
                        source="real_prover",
                        theorem=theorem,
                        lean_file="",
                        theorem_statement=statement,
                        goal_before=goal_before,
                        tactic=tactic,
                        goal_after=goal_after,
                        dependencies=tuple(),
                        raw_ref={
                            "source_file": row.get("raw_ref", {}).get("source_file") or str(path),
                            "source_line": row.get("raw_ref", {}).get("source_line") or line_no,
                            "trace_id": row.get("id"),
                            "result_index": result_idx,
                            "node_index": node_idx,
                        },
                        node_class="leaf",
                    )
                )
    return out


def jixia_successes(path: Path) -> list[SuccessTransition]:
    out: list[SuccessTransition] = []
    for line_no, row in enumerate(iter_jsonl(path), start=1):
        if row.get("schema") != "info_geometry.jixia.tactic_transition.v1":
            continue
        node_class = str(row.get("node_class") or "leaf")
        if node_class != "leaf":
            continue
        tactic = str(row.get("tactic_syntax") or "").strip()
        before = row.get("before") or []
        after = row.get("after") or []
        if not tactic or not isinstance(before, list):
            continue
        goal_before = normalize_goal(
            "\n\n".join(
                str(goal.get("pp") or goal.get("type") or "")
                for goal in before
                if isinstance(goal, dict)
            )
        )
        if not goal_before:
            continue
        if isinstance(after, list) and after:
            goal_after = normalize_goal(
                "\n\n".join(
                    str(goal.get("pp") or goal.get("type") or "")
                    for goal in after
                    if isinstance(goal, dict)
                )
            )
        else:
            goal_after = "no goals"
        source_file = str(row.get("source_file") or path)
        out.append(
            SuccessTransition(
                source="jixia",
                theorem=str(row.get("declaration") or source_file),
                lean_file=source_file,
                theorem_statement="",
                goal_before=goal_before,
                tactic=tactic,
                goal_after=goal_after,
                dependencies=tuple(str(ref) for ref in row.get("references") or []),
                raw_ref={
                    "source_file": source_file,
                    "source_line": line_no,
                    "transition_id": row.get("id"),
                    "range": row.get("range"),
                    "node_class": node_class,
                    "info_kind": row.get("info_kind") or "tactic",
                },
                node_class=node_class,
                info_kind=str(row.get("info_kind") or "tactic"),
            )
        )
    return out


def ulam_successes(path: Path) -> list[SuccessTransition]:
    out: list[SuccessTransition] = []
    for line_no, row in enumerate(iter_jsonl(path), start=1):
        if row.get("schema") != "info_geometry.ulam_trace.v1":
            continue
        if not bool(row.get("ok", False)):
            continue
        goal_before = normalize_goal(row.get("goal_before"))
        tactic = str(row.get("tactic") or "").strip()
        if not goal_before or not tactic:
            continue
        goal_after = normalize_goal(row.get("goal_after")) or (
            "no goals" if bool(row.get("solved", False)) else ""
        )
        out.append(
            SuccessTransition(
                source="ulamai",
                theorem=str(row.get("theorem") or row.get("state_key") or ""),
                lean_file=str(row.get("lean_file") or ""),
                theorem_statement="",
                goal_before=goal_before,
                tactic=tactic,
                goal_after=goal_after,
                dependencies=tuple(),
                raw_ref={
                    "source_file": row.get("raw_ref", {}).get("source_file") or str(path),
                    "source_line": row.get("raw_ref", {}).get("source_line") or line_no,
                    "trace_id": row.get("id"),
                },
                node_class="leaf",
                info_kind="tactic",
            )
        )
    return out


def ulam_failures(path: Path) -> list[FailureTransition]:
    out: list[FailureTransition] = []
    for line_no, row in enumerate(iter_jsonl(path), start=1):
        if row.get("schema") != "info_geometry.ulam_trace.v1":
            continue
        if bool(row.get("ok", False)):
            continue
        goal_before = normalize_goal(row.get("goal_before"))
        tactic = str(row.get("tactic") or "").strip()
        if not tactic:
            continue
        out.append(
            FailureTransition(
                source="ulamai",
                theorem=str(row.get("theorem") or row.get("state_key") or ""),
                lean_file=str(row.get("lean_file") or ""),
                theorem_statement="",
                goal_before=goal_before,
                failed_tactic=tactic,
                diagnostic=str(row.get("error") or ""),
                failure_kind=str(row.get("error_kind") or "failure"),
                raw_ref={
                    "source_file": row.get("raw_ref", {}).get("source_file") or str(path),
                    "source_line": row.get("raw_ref", {}).get("source_line") or line_no,
                    "trace_id": row.get("id"),
                },
            )
        )
    return out


def sft_row(success: SuccessTransition, *, seed: int, train_ratio: float, val_ratio: float) -> dict[str, Any]:
    row_id = stable_hash("sft", success.source, success.theorem, success.goal_hash, success.tactic)
    return {
        "schema": SCHEMA_SFT,
        "id": row_id,
        "split": split_for(row_id, train_ratio=train_ratio, val_ratio=val_ratio, seed=seed),
        "source": success.source,
        "theorem": success.theorem,
        "lean_file": success.lean_file,
        "theorem_statement": success.theorem_statement,
        "goal_before": success.goal_before,
        "goal_hash": success.goal_hash,
        "tactic": success.tactic,
        "aesop_tactic_prior": classify_tactic(success.tactic),
        "goal_after": success.goal_after,
        "outcome": "success",
        "info_kind": success.info_kind,
        "node_class": success.node_class,
        "is_leaf_transition": success.is_leaf_transition,
        "context": {
            "dependencies": list(success.dependencies),
            "imports": [],
            "local_context": "",
            "retrieval_context": [],
        },
        "raw_ref": success.raw_ref,
    }


def failure_row(failure: FailureTransition, *, seed: int, train_ratio: float, val_ratio: float) -> dict[str, Any]:
    row_id = stable_hash("failure", failure.source, failure.theorem, failure.goal_hash, failure.failed_tactic, failure.failure_kind)
    return {
        "schema": SCHEMA_FAILURE,
        "id": row_id,
        "split": split_for(row_id, train_ratio=train_ratio, val_ratio=val_ratio, seed=seed),
        "source": failure.source,
        "theorem": failure.theorem,
        "lean_file": failure.lean_file,
        "theorem_statement": failure.theorem_statement,
        "goal_before": failure.goal_before,
        "goal_hash": failure.goal_hash,
        "failed_tactic": failure.failed_tactic,
        "aesop_tactic_prior": classify_tactic(failure.failed_tactic),
        "diagnostic": failure.diagnostic,
        "failure_kind": failure.failure_kind,
        "tactic_family": tactic_family(failure.failed_tactic),
        "context": {},
        "raw_ref": failure.raw_ref,
    }


def dpo_rows(
    successes: list[SuccessTransition],
    failures: list[FailureTransition],
    *,
    seed: int,
    train_ratio: float,
    val_ratio: float,
) -> tuple[list[dict[str, Any]], dict[str, int]]:
    success_by_key: dict[tuple[str, str], list[SuccessTransition]] = defaultdict(list)
    failure_by_key: dict[tuple[str, str], list[FailureTransition]] = defaultdict(list)
    for success in successes:
        success_by_key[(success.theorem, success.goal_hash)].append(success)
    for failure in failures:
        failure_by_key[(failure.theorem, failure.goal_hash)].append(failure)

    rows: list[dict[str, Any]] = []
    paired_success_keys: set[tuple[str, str]] = set()
    paired_failure_keys: set[tuple[str, str]] = set()
    for key in sorted(success_by_key.keys() & failure_by_key.keys()):
        success = success_by_key[key][0]
        failure = failure_by_key[key][0]
        row_id = stable_hash("dpo", key, success.tactic, failure.failed_tactic)
        rows.append(
            {
                "schema": SCHEMA_DPO,
                "id": row_id,
                "split": split_for(row_id, train_ratio=train_ratio, val_ratio=val_ratio, seed=seed),
                "theorem": success.theorem,
                "goal_before": success.goal_before,
                "goal_hash": success.goal_hash,
                "chosen": {
                    "tactic": success.tactic,
                    "aesop_tactic_prior": classify_tactic(success.tactic),
                    "goal_after": success.goal_after,
                    "source": success.source,
                    "raw_ref": success.raw_ref,
                },
                "rejected": {
                    "tactic": failure.failed_tactic,
                    "aesop_tactic_prior": classify_tactic(failure.failed_tactic),
                    "diagnostic": failure.diagnostic,
                    "failure_kind": failure.failure_kind,
                    "source": failure.source,
                    "raw_ref": failure.raw_ref,
                },
                "pairing_reason": "same_theorem_and_goal_hash",
            }
        )
        paired_success_keys.add(key)
        paired_failure_keys.add(key)

    return rows, {
        "same_goal_hash_pairs": len(rows),
        "unpaired_successes": sum(len(v) for k, v in success_by_key.items() if k not in paired_success_keys),
        "unpaired_failures": sum(len(v) for k, v in failure_by_key.items() if k not in paired_failure_keys),
    }


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with path.open("w", encoding="utf-8") as out:
        for row in rows:
            out.write(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n")
            count += 1
    return count


def build_dataset(args: argparse.Namespace) -> dict[str, Any]:
    successes: list[SuccessTransition] = []
    failures: list[FailureTransition] = []
    quality = Counter()
    by_source = Counter()

    if args.leandojo_bridge and args.leandojo_bridge.exists():
        rows = leandojo_successes(args.leandojo_bridge)
        successes.extend(rows)
        by_source["leandojo_v2"] += len(rows)
    if args.hive_attempts and args.hive_attempts.exists():
        success_rows = hive_successes(args.hive_attempts)
        failure_rows = hive_failures(args.hive_attempts)
        successes.extend(success_rows)
        failures.extend(failure_rows)
        by_source["hive"] += len(success_rows) + len(failure_rows)
    if args.leantrail_failures and args.leantrail_failures.exists():
        rows = leantrail_failures(args.leantrail_failures)
        failures.extend(rows)
        by_source["leantrail"] += len(rows)
    if args.real_prover_traces and args.real_prover_traces.exists():
        rows = real_prover_successes(args.real_prover_traces)
        successes.extend(rows)
        by_source["real_prover"] += len(rows)
    if args.jixia_tactics and args.jixia_tactics.exists():
        rows = jixia_successes(args.jixia_tactics)
        successes.extend(rows)
        by_source["jixia"] += len(rows)
    ulam_traces = getattr(args, "ulam_traces", None)
    if ulam_traces and ulam_traces.exists():
        success_rows = ulam_successes(ulam_traces)
        failure_rows = ulam_failures(ulam_traces)
        successes.extend(success_rows)
        failures.extend(failure_rows)
        by_source["ulamai"] += len(success_rows) + len(failure_rows)

    good_successes = []
    for success in successes:
        if not success.goal_before:
            quality["missing_goal_before"] += 1
            continue
        if not success.tactic:
            quality["missing_tactic"] += 1
            continue
        if not success.goal_after:
            quality["missing_goal_after"] += 1
        good_successes.append(success)

    good_failures = []
    for failure in failures:
        if not failure.goal_before:
            quality["failure_missing_goal_before"] += 1
        if not failure.failed_tactic:
            quality["failure_missing_tactic"] += 1
        good_failures.append(failure)

    sft_rows = [sft_row(s, seed=args.seed, train_ratio=args.train_ratio, val_ratio=args.val_ratio) for s in good_successes]
    failure_rows = [failure_row(f, seed=args.seed, train_ratio=args.train_ratio, val_ratio=args.val_ratio) for f in good_failures]
    dpo, dpo_stats = dpo_rows(
        good_successes,
        good_failures,
        seed=args.seed,
        train_ratio=args.train_ratio,
        val_ratio=args.val_ratio,
    )

    sft_count = write_jsonl(args.out_sft, sft_rows)
    dpo_count = write_jsonl(args.out_dpo, dpo)
    failure_count = write_jsonl(args.out_failures, failure_rows)

    stats = {
        "schema": SCHEMA_STATS,
        "inputs": {
            "leandojo_bridge": str(args.leandojo_bridge) if args.leandojo_bridge else None,
            "leantrail_failures": str(args.leantrail_failures) if args.leantrail_failures else None,
            "hive_attempts": str(args.hive_attempts) if args.hive_attempts else None,
            "raw_infotree": str(args.raw_infotree) if args.raw_infotree else None,
            "real_prover_traces": str(args.real_prover_traces) if args.real_prover_traces else None,
            "jixia_tactics": str(args.jixia_tactics) if args.jixia_tactics else None,
            "ulam_traces": str(ulam_traces) if ulam_traces else None,
        },
        "rows": {
            "sft": sft_count,
            "dpo": dpo_count,
            "failures": failure_count,
        },
        "by_source": dict(sorted(by_source.items())),
        "dpo_pairing": dpo_stats,
        "quality": {
            "missing_goal_before": int(quality["missing_goal_before"]),
            "missing_tactic": int(quality["missing_tactic"]),
            "missing_goal_after": int(quality["missing_goal_after"]),
            "failure_missing_goal_before": int(quality["failure_missing_goal_before"]),
            "failure_missing_tactic": int(quality["failure_missing_tactic"]),
            "excluded_unverified_success_claims": 0,
            "raw_infotree_not_implemented": 1 if args.raw_infotree else 0,
        },
    }
    args.stats_out.parent.mkdir(parents=True, exist_ok=True)
    args.stats_out.write_text(json.dumps(stats, indent=2, ensure_ascii=True, sort_keys=True) + "\n", encoding="utf-8")
    return stats


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--leandojo-bridge", type=Path, default=Path("artifacts/leandojo_v2/leandojo_v2_bridge.jsonl"))
    parser.add_argument("--leantrail-failures", type=Path, default=Path("artifacts/leantrail/failed_transitions.jsonl"))
    parser.add_argument("--hive-attempts", type=Path)
    parser.add_argument("--real-prover-traces", type=Path, help="JSONL emitted by real_prover_trace_bridge.py")
    parser.add_argument("--jixia-tactics", type=Path, help="JSONL emitted by jixia_trace_bridge.py")
    parser.add_argument("--ulam-traces", type=Path, help="JSONL emitted by ulam_trace_bridge.py")
    parser.add_argument("--raw-infotree", type=Path, help="Reserved for Phase B2 raw InfoTree adapter")
    parser.add_argument("--out-sft", type=Path, default=Path("reports/training/tactic_sft.jsonl"))
    parser.add_argument("--out-dpo", type=Path, default=Path("reports/training/tactic_dpo.jsonl"))
    parser.add_argument("--out-failures", type=Path, default=Path("reports/training/tactic_failures.jsonl"))
    parser.add_argument("--stats-out", type=Path, default=Path("reports/training/tactic_training_dataset.stats.json"))
    parser.add_argument("--seed", type=int, default=1729)
    parser.add_argument("--train-ratio", type=float, default=0.85)
    parser.add_argument("--val-ratio", type=float, default=0.075)
    args = parser.parse_args()
    stats = build_dataset(args)
    print(json.dumps(stats, indent=2, ensure_ascii=True, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
