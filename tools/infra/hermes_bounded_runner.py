#!/usr/bin/env python3
"""Run one bounded Hermes planning cycle over the research packet queue.

This runner is intentionally conservative:

- it polls the Hermes research packet directory
- it selects one draft packet per invocation
- it asks the configured planner endpoint for a plan
- it writes deterministic artifacts
- it does not invoke Codex, edit Lean files, or promote canonical content

The systemd timer can call this forever because every invocation is bounded.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import textwrap
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
PACKET_DIR = REPO_ROOT / "quarantine" / "hermes_memory" / "research_packets"
ARTIFACT_ROOT = REPO_ROOT / "artifacts" / "hermes_loop"
STATE_PATH = ARTIFACT_ROOT / "state.json"
RUNS_DIR = ARTIFACT_ROOT / "runs"
GRAVITY_DIR = ARTIFACT_ROOT / "gravity_context"
TRUTH_TRANSPORT_DIR = ARTIFACT_ROOT / "truth_transport"
DEFAULT_BASE_URL = "http://127.0.0.1:30000/v1"
DEFAULT_MODEL = "Nemotron-3-Nano-30B-A3B-UD-Q8_K_XL.gguf"
DEFAULT_API_KEY = "token-123"
GRAVITY_TOOL = REPO_ROOT / "tools" / "infra" / "arango_gravity_context.py"


@dataclass(frozen=True)
class Packet:
    path: Path
    data: dict[str, Any]

    @property
    def packet_id(self) -> str:
        return str(self.data.get("packet_id") or self.path.stem)

    @property
    def status(self) -> str:
        return str(self.data.get("status") or "unknown")


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def load_json(path: Path, default: Any) -> Any:
    if not path.exists():
        return default
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    with tmp.open("w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")
    tmp.replace(path)


def discover_packets(packet_dir: Path) -> list[Packet]:
    packets: list[Packet] = []
    for path in sorted(packet_dir.glob("*.json")):
        if path.name.endswith("_manifest.json") or path.name == "leanprogress_manifest.json":
            continue
        try:
            data = load_json(path, {})
        except json.JSONDecodeError as exc:
            print(f"skip invalid packet {path}: {exc}", file=sys.stderr)
            continue
        if isinstance(data, dict) and data.get("packet_id"):
            packets.append(Packet(path=path, data=data))
    return packets


def select_packet(packets: list[Packet], state: dict[str, Any], force: str | None) -> Packet | None:
    if force:
        for packet in packets:
            if packet.packet_id == force:
                return packet
        raise SystemExit(f"packet not found: {force}")

    planned = set(state.get("planned_packet_ids") or [])
    for packet in packets:
        if packet.status == "draft" and packet.packet_id not in planned:
            return packet

    for packet in packets:
        if packet.status == "draft":
            return packet

    return None


def packet_query(packet: Packet) -> str:
    classification = packet.data.get("classification") or {}
    candidates = classification.get("formalization_candidates") or []
    interpretations = classification.get("interpretations") or []
    targets = packet.data.get("formalization_targets") or []
    parts = [
        str(packet.data.get("research_goal") or ""),
        " ".join(str(item) for item in targets[:5]),
        " ".join(str(item) for item in candidates[:5]),
        " ".join(str(item) for item in interpretations[:5]),
    ]
    query = " ".join(part for part in parts if part).strip()
    return re.sub(r"\s+", " ", query)[:1200] or packet.packet_id


def run_gravity_retrieval(
    *,
    packet: Packet,
    query: str,
    output_dir: Path,
    run_id: str,
    top_k: int,
    timeout: int,
    graph_mode: str,
) -> tuple[dict[str, Any] | None, str | None]:
    if top_k <= 0:
        return None, None
    output_dir.mkdir(parents=True, exist_ok=True)
    out_path = output_dir / f"{run_id}.json"
    command = [
        sys.executable,
        str(GRAVITY_TOOL),
        "--source",
        "auto",
        "--query",
        query,
        "--top-k",
        str(top_k),
        "--graph-mode",
        graph_mode,
        "--json-out",
        str(out_path),
        "--repo-root",
        str(REPO_ROOT),
    ]
    try:
        subprocess.run(
            command,
            cwd=REPO_ROOT,
            check=True,
            text=True,
            capture_output=True,
            timeout=timeout,
        )
        context = load_json(out_path, None)
        if isinstance(context, dict):
            context["packet_id"] = packet.packet_id
            write_json(output_dir / "latest.json", context)
        return context, None
    except Exception as exc:  # noqa: BLE001 - retrieval must not break the timer loop
        return None, repr(exc)


def summarize_gravity_context(context: dict[str, Any] | None, max_items: int, max_chars: int) -> str:
    if not context:
        return "No graph context available."

    items = context.get("items") or []
    if not items:
        return (
            "No semantically strong graph neighbors were found in compiled repo declarations. "
            "Do not inject unrelated high-mass nodes; route to proof-local Lean/mathlib investigation instead."
        )
    lines = [
        "Graph-grounded context from already compiled Lean declarations.",
        f"source={context.get('graph_source')} mode={context.get('graph_mode')} "
        f"nodes={context.get('node_count')} edges={context.get('edge_count')} "
        f"seed_sccs={context.get('seed_scc_count')}",
        "Use this as gravitational mass: nearby proven code pulls proof search; it is not proof admission.",
    ]
    for item in items[:max_items]:
        witness = item.get("faithful_witness") or {}
        witness_text = ""
        if witness:
            witness_text = (
                f" raw={witness.get('raw_doc_id')} scc={witness.get('scc_key') or witness.get('scc_id')} "
                f"witness_backed={witness.get('witness_backed')}"
            )
        lines.append(
            f"- {item.get('id')} score={item.get('score')} distance={item.get('distance')} "
            f"scc_distance={item.get('scc_anchor_distance')} module={item.get('module')} "
            f"line={item.get('line')}{witness_text}"
        )
        doc = str(item.get("doc") or "").strip()
        if doc:
            lines.append(f"  doc: {doc[:260]}")
        excerpt = item.get("source_excerpt") or {}
        excerpt_lines = excerpt.get("lines") or []
        if excerpt_lines:
            lean = "\n".join(str(row.get("text") or "") for row in excerpt_lines[:8])
            lines.append("  lean:\n" + textwrap.indent(lean[:1000], "    "))

    summary = "\n".join(lines)
    if len(summary) > max_chars:
        summary = summary[:max_chars].rstrip() + "\n[graph context truncated]"
    return summary


def build_prompt(packet: Packet, gravity_summary: str) -> str:
    evidence = packet.data.get("evidence") or []
    targets = packet.data.get("formalization_targets") or []
    forbidden = packet.data.get("forbidden_moves") or []
    classification = packet.data.get("classification") or {}
    handoff = packet.data.get("handoff") or {}

    return textwrap.dedent(
        f"""
        You are Hermes, bounded orchestrator and steward of the Lean4 repository
        info-geometry-lean. Act under docs/HERMES_OPERATOR_CHARTER.md and
        docs/CANONICAL_AGENT_STACK.md.

        This is one timer-triggered planning cycle. Do not use tools. Do not
        edit files. Do not call Codex. Do not claim theorem closure. Produce a
        concise routing decision only.

        Runtime lanes:
        - Nemotron: planner/orchestration reasoning
        - DeepSeek-Prover-V2-7B: Lean4 proof-specialist lane
        - Goedel: conservative audit lane
        - Codex CLI: execution lane, only if explicitly requested later
        - Lean/lake: final truth authority

        Packet:
        - id: {packet.packet_id}
        - status: {packet.status}
        - goal: {packet.data.get("research_goal", "")}
        - formalization_targets: {json.dumps(targets, ensure_ascii=False)}
        - handoff: {json.dumps(handoff, ensure_ascii=False)}
        - forbidden_moves: {json.dumps(forbidden, ensure_ascii=False)}
        - interpretations: {json.dumps(classification.get("interpretations", []), ensure_ascii=False)}
        - candidates: {json.dumps(classification.get("formalization_candidates", []), ensure_ascii=False)}
        - evidence: {json.dumps(evidence, ensure_ascii=False)}

        Gravitational Lean context:
        {gravity_summary}

        Required output format:
        ROUTE: one of [deepseek_proof, goedel_audit, codex_execution_request, hold]
        EXECUTION_ALLOWED: yes/no
        NEXT_ACTION: one concrete bounded action
        RATIONALE: two to five concise sentences
        GUARDS: list the gates that must pass before canonical mutation

        Rules:
        - Treat graph-grounded compiled Lean context as the strongest planning prior.
        - Do not invent proof context from chat memory when graph context is available.
        - Prefer deepseek_proof for tactic/proof-state investigation.
        - Use codex_execution_request only if the packet explicitly requires
          mutation and the next action is already justified.
        - For draft LeanProgress sample packets, execution should normally be
          disallowed and the next action should be proof-specialist evaluation.
        """
    ).strip()


def call_openai_compatible(
    *,
    base_url: str,
    model: str,
    api_key: str,
    prompt: str,
    timeout: int,
    max_tokens: int,
) -> dict[str, Any]:
    url = base_url.rstrip("/") + "/chat/completions"
    payload = {
        "model": model,
        "messages": [
            {
                "role": "system",
                "content": "You are a bounded theorem-factory orchestrator. Follow the requested output format exactly.",
            },
            {"role": "user", "content": prompt},
        ],
        "temperature": 0.2,
        "max_tokens": max_tokens,
    }
    body = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(
        url,
        data=body,
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"planner HTTP {exc.code}: {detail}") from exc


def extract_text(response: dict[str, Any]) -> str:
    choices = response.get("choices") or []
    if not choices:
        return ""
    message = choices[0].get("message") or {}
    content = message.get("content")
    if isinstance(content, str) and content.strip():
        return content

    # Some local reasoning models served through llama.cpp/vLLM put their whole
    # answer in `reasoning_content` when the completion is token-capped.  Recover
    # the requested route block instead of treating the planner as silent.
    reasoning = message.get("reasoning_content")
    if not isinstance(reasoning, str):
        return ""
    labels = ["ROUTE:", "EXECUTION_ALLOWED:", "NEXT_ACTION:", "RATIONALE:", "GUARDS:"]
    starts = [reasoning.rfind(label) for label in labels]
    if min(starts) >= 0:
        start = starts[0]
        return reasoning[start:].strip()
    return reasoning.strip()


def parse_planner_route(text: str) -> dict[str, str]:
    fields = {
        "route": "",
        "execution_allowed": "",
        "next_action": "",
        "rationale": "",
        "guards": "",
    }
    label_map = {
        "ROUTE": "route",
        "EXECUTION_ALLOWED": "execution_allowed",
        "NEXT_ACTION": "next_action",
        "RATIONALE": "rationale",
        "GUARDS": "guards",
    }
    current: str | None = None
    for raw_line in text.splitlines():
        line = raw_line.strip()
        matched = False
        for label, key in label_map.items():
            prefix = f"{label}:"
            if line.startswith(prefix):
                fields[key] = line.removeprefix(prefix).strip()
                current = key
                matched = True
                break
        if not matched and current and line:
            fields[current] = (fields[current] + " " + line).strip()
    return fields


def build_truth_transport_packet(
    *,
    run_id: str,
    packet: Packet,
    planner_text: str,
    gravity_context: dict[str, Any] | None,
    gravity_path: Path,
) -> dict[str, Any]:
    route = parse_planner_route(planner_text)
    items = []
    for item in (gravity_context or {}).get("items") or []:
        excerpt = item.get("source_excerpt") or {}
        items.append(
            {
                "id": item.get("id"),
                "name": item.get("name"),
                "module": item.get("module"),
                "decl_kind": item.get("decl_kind"),
                "score": item.get("score"),
                "distance": item.get("distance"),
                "source": {
                    "path": excerpt.get("path") or item.get("file"),
                    "line": excerpt.get("line") or item.get("line"),
                    "start": excerpt.get("start"),
                    "end": excerpt.get("end"),
                    "lines": excerpt.get("lines") or [],
                },
            }
        )

    return {
        "schema": "info_geometry.truth_transport.v1",
        "run_id": run_id,
        "packet_id": packet.packet_id,
        "created_at": utc_now(),
        "target": {
            "research_goal": packet.data.get("research_goal"),
            "formalization_targets": packet.data.get("formalization_targets") or [],
        },
        "planner_route": route,
        "handoff_policy": {
            "truth_source": "compiled Lean graph via ArangoDB/LeanTrail plus Lean/lake verification",
            "graph_context_required": True,
            "codex_mutation_allowed": route.get("execution_allowed") == "yes"
            and route.get("route") == "codex_execution_request",
            "canonical_mutation_allowed": False,
            "must_verify_with": ["lean_interact_wrapper.py for probes", "lake build/check before admission"],
        },
        "gravity_context": {
            "path": str(gravity_path),
            "graph_source": (gravity_context or {}).get("graph_source"),
            "node_count": (gravity_context or {}).get("node_count"),
            "edge_count": (gravity_context or {}).get("edge_count"),
            "items": items,
        },
        "next_agent_instruction": (
            "Use the graph_context items as the inherited truth orbit. Any plausible new theorem must be "
            "stated relative to these compiled neighbors, probed in Lean, and kept non-canonical until gates pass."
        ),
    }


def write_truth_transport(path: Path, packet: dict[str, Any]) -> None:
    write_json(path, packet)


def write_markdown(run_path: Path, packet: Packet, prompt: str, text: str) -> None:
    md_path = run_path.with_suffix(".md")
    md_path.write_text(
        "\n".join(
            [
                f"# Hermes Bounded Cycle: {packet.packet_id}",
                "",
                "## Planner Output",
                "",
                text.strip() or "(empty response)",
                "",
                "## Prompt",
                "",
                "```text",
                prompt,
                "```",
                "",
            ]
        ),
        encoding="utf-8",
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet-dir", type=Path, default=PACKET_DIR)
    parser.add_argument("--state", type=Path, default=STATE_PATH)
    parser.add_argument("--runs-dir", type=Path, default=RUNS_DIR)
    parser.add_argument("--base-url", default=os.environ.get("HERMES_LOOP_BASE_URL", DEFAULT_BASE_URL))
    parser.add_argument("--model", default=os.environ.get("HERMES_LOOP_MODEL", DEFAULT_MODEL))
    parser.add_argument("--api-key", default=os.environ.get("HERMES_LOOP_API_KEY", DEFAULT_API_KEY))
    parser.add_argument("--timeout", type=int, default=int(os.environ.get("HERMES_LOOP_TIMEOUT", "120")))
    parser.add_argument("--max-tokens", type=int, default=int(os.environ.get("HERMES_LOOP_MAX_TOKENS", "768")))
    parser.add_argument("--packet-id", help="force a specific packet id")
    parser.add_argument("--dry-run", action="store_true", help="write prompt artifact without calling the model")
    parser.add_argument("--gravity-top-k", type=int, default=int(os.environ.get("HERMES_LOOP_GRAVITY_TOP_K", "5")))
    parser.add_argument("--gravity-timeout", type=int, default=int(os.environ.get("HERMES_LOOP_GRAVITY_TIMEOUT", "30")))
    parser.add_argument("--gravity-max-chars", type=int, default=int(os.environ.get("HERMES_LOOP_GRAVITY_MAX_CHARS", "6000")))
    parser.add_argument(
        "--gravity-graph-mode",
        choices=["compact", "faithful", "hybrid"],
        default=os.environ.get("HERMES_LOOP_GRAVITY_GRAPH_MODE", "compact"),
    )
    parser.add_argument("--no-gravity-context", action="store_true")
    args = parser.parse_args()

    packets = discover_packets(args.packet_dir)
    state = load_json(args.state, {"schema": "hermes_bounded_runner_state.v1", "planned_packet_ids": []})
    selected = select_packet(packets, state, args.packet_id)
    if selected is None:
        print("no draft packets available")
        return 0

    started = utc_now()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    run_id = f"{stamp}-{selected.packet_id}"
    args.runs_dir.mkdir(parents=True, exist_ok=True)
    run_path = args.runs_dir / f"{run_id}.json"

    query = packet_query(selected)
    gravity_context = None
    gravity_error = None
    if not args.no_gravity_context:
        gravity_context, gravity_error = run_gravity_retrieval(
            packet=selected,
            query=query,
            output_dir=GRAVITY_DIR,
            run_id=run_id,
            top_k=args.gravity_top_k,
            timeout=args.gravity_timeout,
            graph_mode=args.gravity_graph_mode,
        )
    gravity_summary = summarize_gravity_context(gravity_context, args.gravity_top_k, args.gravity_max_chars)
    prompt = build_prompt(selected, gravity_summary)
    response: dict[str, Any] | None = None
    planner_text = ""
    error = None

    if args.dry_run:
        planner_text = "DRY_RUN: planner call skipped"
    else:
        try:
            response = call_openai_compatible(
                base_url=args.base_url,
                model=args.model,
                api_key=args.api_key,
                prompt=prompt,
                timeout=args.timeout,
                max_tokens=args.max_tokens,
            )
            planner_text = extract_text(response)
        except Exception as exc:  # noqa: BLE001 - record failures as artifacts
            error = repr(exc)

    run_payload = {
        "schema": "hermes_bounded_cycle.v1",
        "run_id": run_id,
        "started_at": started,
        "finished_at": utc_now(),
        "packet_id": selected.packet_id,
        "packet_path": str(selected.path),
        "planner": {
            "base_url": args.base_url,
            "model": args.model,
            "max_tokens": args.max_tokens,
            "dry_run": args.dry_run,
        },
        "prompt": prompt,
        "gravity": {
            "enabled": not args.no_gravity_context,
            "query": query,
            "top_k": args.gravity_top_k,
            "graph_mode": args.gravity_graph_mode,
            "context_path": str((GRAVITY_DIR / f"{run_id}.json")),
            "error": gravity_error,
        },
        "planner_text": planner_text,
        "raw_response": response,
        "error": error,
        "execution_invoked": False,
        "canonical_mutation_invoked": False,
    }
    truth_transport_path = TRUTH_TRANSPORT_DIR / f"{run_id}.json"
    if planner_text:
        transport_packet = build_truth_transport_packet(
            run_id=run_id,
            packet=selected,
            planner_text=planner_text,
            gravity_context=gravity_context,
            gravity_path=GRAVITY_DIR / f"{run_id}.json",
        )
        write_truth_transport(truth_transport_path, transport_packet)
        write_json(TRUTH_TRANSPORT_DIR / "latest.json", transport_packet)
        run_payload["truth_transport"] = {
            "path": str(truth_transport_path),
            "schema": transport_packet["schema"],
        }
    write_json(run_path, run_payload)
    write_markdown(run_path, selected, prompt, planner_text if not error else error)

    if not args.dry_run:
        planned = list(dict.fromkeys([*(state.get("planned_packet_ids") or []), selected.packet_id]))
        state.update(
            {
                "schema": "hermes_bounded_runner_state.v1",
                "updated_at": utc_now(),
                "last_run_id": run_id,
                "last_packet_id": selected.packet_id,
                "planned_packet_ids": planned,
            }
        )
        write_json(args.state, state)

    if error:
        print(f"run failed: {run_path}")
        print(error)
        return 1

    print(f"planned packet {selected.packet_id}: {run_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
