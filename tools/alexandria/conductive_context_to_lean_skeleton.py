#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


DEFAULT_IMPORTS = [
    "InfoGeometry.Canonical.Drazin",
    "InfoGeometry.Canonical.MoorePenrose",
    "InfoGeometry.Canonical.CertifiedInverseKernel",
    "InfoGeometry.Krein.JSelfAdjointProjection",
]


@dataclass(frozen=True)
class LeanCandidate:
    name: str
    kind: str
    source_edge: dict[str, Any]
    entities: list[str]
    statement: str
    obligations: list[str]
    ancestry_hash: str
    ancestry_sources: list[str]


# [lossless-compact] stable_hash folded into igf.common.hashing.stable_hash
from igf.common.hashing import stable_hash


def load_packet(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def sanitize_name(text: str) -> str:
    words = re.findall(r"[A-Za-z][A-Za-z0-9]*", text)
    if not words:
        return "candidate"
    head = words[0].lower()
    tail = "".join(word[:1].upper() + word[1:] for word in words[1:8])
    return head + tail


def edge_terms(edge: dict[str, Any]) -> list[str]:
    terms: list[str] = []
    for symbol in edge.get("overlap_symbols", []) or []:
        if isinstance(symbol, str):
            terms.append(symbol)
    for key in ["fromPreview", "toPreview"]:
        terms.extend(re.findall(r"\b(?:Krein|Drazin|Moore-Penrose|J-self-adjoint|projection|projector|star projection|fundamental symmetry|adjoint|indefinite inner product)\b", str(edge.get(key, "")), flags=re.IGNORECASE))
    return list(dict.fromkeys(term.strip() for term in terms if term.strip()))


def candidate_statement(name: str, terms: list[str]) -> tuple[str, list[str]]:
    lowered = " ".join(terms).lower()
    if "drazin" in lowered and ("projection" in lowered or "projector" in lowered):
        if "j-self-adjoint" in lowered or "krein" in lowered:
            return (
                f"theorem {name}\n"
                "    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]\n"
                "    [InfoGeometry.Krein.KreinSpace H]\n"
                "    {P : H →L[ℝ] H}\n"
                "    (hP : InfoGeometry.Krein.KreinSpace.IsJProjection (H := H) P) :\n"
                "    InfoGeometry.Canonical.Drazin.IsDrazinInverse P P 1",
                [
                    "Reuse `InfoGeometry.Krein.KreinSpace.IsJProjection.isDrazinInverse_self`.",
                    "This proves the Drazin consequence from J-projection idempotence only.",
                ],
            )
        return (
            f"theorem {name}\n"
            "    {R : Type*} [Ring R] [StarRing R]\n"
            "    {A AD : R} {k : Nat}\n"
            "    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse A AD k)\n"
            "    (hA : star A = A) :\n"
            "    IsStarProjection (InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection A AD)",
            [
                "Reuse `InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_isStarProjection_of_selfAdjoint`.",
                "Do not assert Krein-space semantics until a concrete Krein/J-adjoint substrate exists.",
            ],
        )
    if "moore" in lowered or "penrose" in lowered:
        return (
            f"theorem {name}\n"
            "    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]\n"
            "    [InnerProductSpace 𝕜 E] [CompleteSpace E]\n"
            "    {A B : E →L[𝕜] E}\n"
            "    (hMP : InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse A B) :\n"
            "    ∃ (_ : A.range.HasOrthogonalProjection),\n"
            "      InfoGeometry.Canonical.MoorePenrose.rightProjector A B = A.range.starProjection",
            [
                "Reuse `InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector_eq_range_starProjection`.",
                "The MP witness supplies orthogonal projectability; no extra closed-range premise needed at this layer.",
            ],
        )
    if "j-self-adjoint" in lowered or "adjoint" in lowered:
        return (
            f"-- Candidate `{name}` should target\n"
            "-- `InfoGeometry.Krein.KreinSpace.IsJSelfAdjoint` and\n"
            "-- `InfoGeometry.Krein.KreinSpace.isJSelfAdjoint_iff_kreinInner`.",
            [
                "Use `InfoGeometry.Krein.KreinSpace.isJSelfAdjoint_iff_kreinInner` for metric characterization.",
                "Select a concrete operator statement before promoting this prose edge to Lean.",
            ],
        )
    return (
        f"-- Candidate `{name}` needs owner-surface selection before becoming Lean code.",
        ["No safe automatic Lean statement inferred from this activated edge."],
    )


def candidates_from_packet(packet: dict[str, Any], *, limit: int) -> list[LeanCandidate]:
    candidates: list[LeanCandidate] = []
    for index, edge in enumerate(packet.get("activatedEdges", [])[:limit], start=1):
        terms = edge_terms(edge)
        base = sanitize_name(" ".join(terms) or f"activated_edge_{index}")
        name = f"{base}_fromConductivePath_{index}"
        statement, obligations = candidate_statement(name, terms)
        ancestry_sources = [
            str(edge.get("from", "")),
            str(edge.get("to", "")),
            str(edge.get("sourceDocumentKey", "")),
        ]
        candidates.append(
            LeanCandidate(
                name=name,
                kind=str(edge.get("kind", "edge")),
                source_edge=edge,
                entities=terms,
                statement=statement,
                obligations=obligations,
                ancestry_hash=stable_hash(packet.get("query", ""), edge, statement, size=32),
                ancestry_sources=[source for source in ancestry_sources if source],
            )
        )
    return candidates


def render_lean(packet: dict[str, Any], candidates: list[LeanCandidate], *, namespace: str) -> str:
    lines: list[str] = [
        "/-",
        "Generated Lean skeleton packet from an Alexandria conductive context.",
        "",
        "This file is an artifact, not proof authority.",
        "Do not import it into the build without replacing skeletons by real proofs.",
        "",
        f"Query: {packet.get('query', '')}",
        "-/",
        "",
    ]
    lines.extend(f"import {imp}" for imp in DEFAULT_IMPORTS)
    lines.extend(["", f"namespace {namespace}", ""])
    for candidate in candidates:
        comment_start = "/--" if candidate.statement.lstrip().startswith(("theorem ", "structure ")) else "/-"
        lines.extend(
            [
                comment_start,
                f"Conductive candidate from `{candidate.kind}`.",
                "",
                "Entities:",
            ]
        )
        for entity in candidate.entities:
            lines.append(f"- {entity}")
        lines.append("")
        lines.append(f"Ancestry hash: `{candidate.ancestry_hash}`")
        if candidate.ancestry_sources:
            lines.append(f"Ancestry sources: `{', '.join(candidate.ancestry_sources)}`")
        lines.append("")
        lines.append("Proof obligations:")
        for obligation in candidate.obligations:
            lines.append(f"- {obligation}")
        lines.extend(["-/", candidate.statement])
        if candidate.statement.lstrip().startswith("theorem "):
            obligations_text = "\n".join(candidate.obligations)
            if "projection_isStarProjection_of_selfAdjoint" in obligations_text:
                lines.extend(
                    [
                        ":= by",
                        "  -- Conductive path selected an existing repo-rooted theorem.",
                        "  exact InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_isStarProjection_of_selfAdjoint hD hA",
                        "",
                    ]
                )
            elif "IsJProjection.isDrazinInverse_self" in obligations_text:
                lines.extend(
                    [
                        ":= by",
                        "  -- Conductive path selected the repo-native Krein/J-projection bridge.",
                        "  exact InfoGeometry.Krein.KreinSpace.IsJProjection.isDrazinInverse_self hP",
                        "",
                    ]
                )
            else:
                lines.extend(
                    [
                        ":= by",
                        "  -- Skeleton only. Replace with a repo-rooted proof before moving into `lean/`.",
                        "  -- Do not add `sorry` here; keep generated artifacts outside the Lean build.",
                        "  exact by",
                        "    -- proof intentionally omitted in artifact",
                        "    fail_if_success trivial",
                        "",
                    ]
                )
        else:
            lines.append("")
    lines.extend([f"end {namespace}", ""])
    return "\n".join(lines)


def render_markdown(packet: dict[str, Any], candidates: list[LeanCandidate]) -> str:
    lines = [
        "# Conductive Context Lean Skeleton Packet",
        "",
        f"Query: `{packet.get('query', '')}`",
        "",
        "## Activated theorem targets",
        "",
    ]
    for candidate in candidates:
        edge = candidate.source_edge
        lines.extend(
            [
                f"### `{candidate.name}`",
                "",
                f"- edge kind: `{candidate.kind}`",
                f"- conductivity: `{edge.get('conductivity', 1.0)}`",
                f"- weight: `{edge.get('weight', 0.0)}`",
                f"- overlap: `{edge.get('overlap_symbols', [])}`",
                f"- ancestry hash: `{candidate.ancestry_hash}`",
                f"- ancestry sources: `{candidate.ancestry_sources}`",
                "",
                "Statement:",
                "",
                "```lean",
                candidate.statement,
                "```",
                "",
                "Obligations:",
            ]
        )
        for obligation in candidate.obligations:
            lines.append(f"- {obligation}")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def write_json(path: Path, obj: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Convert conductive Alexandria context into reviewable Lean skeleton artifacts.")
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--namespace", default="InfoGeometry.Alexandria.GeneratedSkeleton")
    parser.add_argument("--limit", type=int, default=6)
    args = parser.parse_args()

    packet = load_packet(args.input)
    candidates = candidates_from_packet(packet, limit=args.limit)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir / "conductive_skeleton.lean").write_text(render_lean(packet, candidates, namespace=args.namespace), encoding="utf-8")
    (args.output_dir / "conductive_skeleton.md").write_text(render_markdown(packet, candidates), encoding="utf-8")
    write_json(args.output_dir / "conductive_skeleton_map.json", {"query": packet.get("query", ""), "candidates": [asdict(candidate) for candidate in candidates]})
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
