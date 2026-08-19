#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from tools.alexandria.arango_ingest import db_url, request_json
from tools.infra.arango_env import alexandria_arango_endpoint, arango_password, arango_username, load_repo_arango_env


LEAN_ANCHORS = [
    {
        "name": "InfoGeometry.Krein.KreinSpace.IsJProjection",
        "role": "Krein-side projection predicate anchored by a fundamental symmetry.",
    },
    {
        "name": "InfoGeometry.Krein.KreinSpace.isJSelfAdjoint_iff_kreinInner",
        "role": "Metric readback for J-self-adjointness through the Krein inner product.",
    },
    {
        "name": "InfoGeometry.Krein.KreinSpace.IsJProjection.isDrazinInverse_self",
        "role": "A J-projection is a Drazin inverse of itself.",
    },
    {
        "name": "InfoGeometry.Krein.KreinSpace.IsJProjection.drazinProjection_isStarProjection_of_hilbertSelfAdjoint",
        "role": "Drazin spectral projector becomes a Hilbert star projection only with Hilbert self-adjointness.",
    },
    {
        "name": "InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector_eq_range_starProjection",
        "role": "Moore-Penrose range projector is the orthogonal projection onto range(A).",
    },
    {
        "name": "InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector_eq_kerOrthogonal_starProjection",
        "role": "Moore-Penrose domain projector is the orthogonal projection onto ker(A) orthogonal complement.",
    },
]


def _text(value: Any) -> str:
    return str(value or "").strip()


def execute_aql(
    *,
    aql: str,
    endpoint: str,
    database: str,
    username: str,
    password: str,
    bind_vars: dict[str, Any],
) -> list[dict[str, Any]]:
    payload = {"query": aql, "bindVars": bind_vars, "batchSize": 1000}
    first = request_json("POST", db_url(endpoint, database, "/_api/cursor"), username, password, payload)
    rows = list(first.get("result", []))
    cursor_id = first.get("id")
    has_more = bool(first.get("hasMore"))
    while has_more and cursor_id:
        page = request_json("PUT", db_url(endpoint, database, f"/_api/cursor/{cursor_id}"), username, password)
        rows.extend(page.get("result", []))
        cursor_id = page.get("id")
        has_more = bool(page.get("hasMore"))
    return rows


def flatten_witnesses(results: list[dict[str, Any]], limit: int = 12) -> list[dict[str, Any]]:
    seen: set[tuple[str, str]] = set()
    witnesses: list[dict[str, Any]] = []
    for row in results:
        for witness in row.get("witnesses", []) or []:
            key = (_text(witness.get("scc")), _text(witness.get("chunk")))
            if key in seen:
                continue
            seen.add(key)
            witnesses.append(
                {
                    "scc": key[0],
                    "chunk": key[1],
                    "preview": _text(witness.get("preview")),
                    "terms": witness.get("terms", []),
                }
            )
            if len(witnesses) >= limit:
                return witnesses
    return witnesses


def select_top_path(results: list[dict[str, Any]]) -> dict[str, Any] | None:
    if not results:
        return None
    return max(
        results,
        key=lambda row: (
            int(row.get("depth", 0) or 0),
            float(row.get("conductiveWeight", 0.0) or 0.0),
            len(row.get("witnesses", []) or []),
        ),
    )


def render_prompt(packet: dict[str, Any]) -> str:
    query = _text(packet.get("query")) or ", ".join(packet.get("seedTerms", []))
    top_path = packet.get("topPath") or {}
    path = " -> ".join(top_path.get("path", []) or []) or "(no quotient path returned)"
    terms = ", ".join(top_path.get("pathTerms", []) or []) or "(no terms returned)"

    lines = [
        "# Proof Synthesis Report Prompt",
        "",
        "Write a proof-synthesis report explaining the relation between Moore-Penrose and Drazin projectors in the retrieved Krein-space corridor.",
        "",
        "Authority boundary:",
        "- Lean is proof authority.",
        "- Graph witnesses are language/context/provenance only; they are not proofs.",
        "- Do not promote graph proximity, SCC membership, or De Bruijn flow into unconditional mathematical claims.",
        "- Keep the star-gap explicit: J-self-adjointness in a Krein metric is not Hilbert self-adjointness; Hilbert star-projection conclusions require `star P = P` or a Lean theorem that supplies it.",
        "",
        f"Query: {query}",
        f"Top SCC path: {path}",
        f"Path terms: {terms}",
        "",
        "Lean anchors to cite as formal truth:",
    ]
    for anchor in packet.get("leanAnchors", []):
        lines.append(f"- `{anchor['name']}`: {anchor['role']}")

    lines.extend(["", "Graph witnesses to cite as provenance/context:"])
    for witness in packet.get("witnesses", []):
        preview = witness.get("preview", "").replace("\n", " ")
        terms = ", ".join(witness.get("terms", []) or [])
        lines.append(f"- `{witness.get('scc')}` / `{witness.get('chunk')}` [{terms}]: {preview}")

    lines.extend(
        [
            "",
            "Required report structure:",
            "1. State the formal Lean facts first.",
            "2. Explain Moore-Penrose projectors as metric/star projections: `A*B` projects onto `range A`, and `B*A` projects onto `ker A` orthogonal complement.",
            "3. Explain Drazin projectors as algebraic projectors by default, becoming star projections only under the self-adjoint-base bridge.",
            "4. Explain the Krein bridge through fundamental symmetry and J-projection, without collapsing J-self-adjointness into Hilbert self-adjointness.",
            "5. List which statements are already Lean-backed and which are only candidate theorem-shapes suggested by the graph.",
        ]
    )
    return "\n".join(lines) + "\n"


def build_packet(*, query: str, seed_terms: list[str], results: list[dict[str, Any]]) -> dict[str, Any]:
    top_path = select_top_path(results)
    witnesses = flatten_witnesses(results)
    packet = {
        "query": query,
        "seedTerms": seed_terms,
        "resultCount": len(results),
        "topPath": top_path,
        "witnesses": witnesses,
        "leanAnchors": LEAN_ANCHORS,
    }
    packet["prompt"] = render_prompt(packet)
    return packet


def write_outputs(packet: dict[str, Any], json_out: Path | None, md_out: Path | None) -> None:
    if json_out is not None:
        json_out.parent.mkdir(parents=True, exist_ok=True)
        json_out.write_text(json.dumps(packet, indent=2, ensure_ascii=False), encoding="utf-8")
    if md_out is not None:
        md_out.parent.mkdir(parents=True, exist_ok=True)
        md_out.write_text(packet["prompt"], encoding="utf-8")


def main() -> int:
    load_repo_arango_env(Path.cwd())
    ap = argparse.ArgumentParser(description="Build a witness-backed proof synthesis prompt from Alexandria SCC Deep Discovery")
    ap.add_argument("--aql", type=Path, help="AQL file to execute against Arango")
    ap.add_argument("--input-json", type=Path, help="Previously saved discovery result list or packet")
    ap.add_argument("--seed-term", action="append", default=[])
    ap.add_argument("--query", default="")
    ap.add_argument("--min-member-count", type=int, default=1)
    ap.add_argument("--max-depth", type=int, default=6)
    ap.add_argument("--limit", type=int, default=25)
    ap.add_argument("--endpoint", default=alexandria_arango_endpoint())
    ap.add_argument("--database", default="alexandria")
    ap.add_argument("--username", default=arango_username())
    ap.add_argument("--password", default=arango_password("alexandria_root"))
    ap.add_argument("--json-out", type=Path)
    ap.add_argument("--md-out", type=Path)
    args = ap.parse_args()

    if args.input_json is None and args.aql is None:
        ap.error("provide --input-json or --aql")

    if args.input_json is not None:
        loaded = json.loads(args.input_json.read_text(encoding="utf-8"))
        if isinstance(loaded, dict) and "results" in loaded:
            results = loaded["results"]
        elif isinstance(loaded, list):
            results = loaded
        else:
            results = loaded.get("discoveryResults", []) if isinstance(loaded, dict) else []
    else:
        seed_terms = args.seed_term or ["Krein space", "J-self-adjoint", "Drazin inverse", "Moore-Penrose"]
        bind_vars = {
            "seedTerms": seed_terms,
            "minMemberCount": args.min_member_count,
            "maxDepth": args.max_depth,
            "limit": args.limit,
        }
        results = execute_aql(
            aql=args.aql.read_text(encoding="utf-8"),
            endpoint=args.endpoint,
            database=args.database,
            username=args.username,
            password=args.password,
            bind_vars=bind_vars,
        )

    seed_terms = args.seed_term or ["Krein space", "J-self-adjoint", "Drazin inverse", "Moore-Penrose"]
    query = args.query or " ".join(seed_terms)
    packet = build_packet(query=query, seed_terms=seed_terms, results=results)
    write_outputs(packet, args.json_out, args.md_out)
    if args.json_out is None and args.md_out is None:
        print(packet["prompt"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
