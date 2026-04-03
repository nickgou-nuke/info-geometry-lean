"""Markdown and JSON report rendering for vacuity planner outputs."""

from __future__ import annotations

import json
from typing import Any, cast

from .common import DIAG_PROVENANCE_WEIGHT, HEAD_SOURCE_WEIGHT, JsonObj, VIOLATION_LEVEL_WEIGHT
from .policy import planner_policy_snapshot


def make_markdown_report(report: JsonObj) -> str:
    lines: list[str] = []
    lines.append("# Vacuity Planner Report")
    lines.append("")
    lines.append("## Boundary")
    lines.append("")
    boundary = report.get("boundary", {})
    lines.append(f"- plannerMode: {boundary.get('plannerMode')}")
    lines.append(f"- mutationSurface: {boundary.get('mutationSurface')}")
    lines.append(f"- automaticReplacement: {boundary.get('automaticReplacement')}")
    lines.append(f"- proofRepair: {boundary.get('proofRepair')}")
    lines.append(f"- strictAdmissibilityPrecheck: {boundary.get('strictAdmissibilityPrecheck')}")
    lines.append("")

    lines.append("## Input Coverage")
    lines.append("")
    inputs = report.get("inputs", {})
    lines.append(f"- theoremSignificanceEntries: {inputs.get('theoremSignificanceEntries', 0)}")
    lines.append(f"- declarationCount: {inputs.get('declarationCount', 0)}")
    lines.append(f"- edgeCount: {inputs.get('edgeCount', 0)}")
    lines.append(f"- ownerEntries: {inputs.get('ownerEntries', 0)}")
    lines.append(f"- bridgePayloadFiles: {inputs.get('bridgePayloadFiles', 0)}")
    lines.append(f"- bridgePayloadObjects: {inputs.get('bridgePayloadObjects', 0)}")
    lines.append("")

    norm = report.get("normalization", {})
    lines.append("## Normalization Snapshot")
    lines.append("")
    lines.append("### Top exprSemantic head groups")
    lines.append("")
    lines.append("| rank | surface | head | count | confidence |")
    lines.append("|---:|---|---|---:|---:|")
    for i, row in enumerate(norm.get("semanticHeadGroups", [])[:10], start=1):
        lines.append(
            f"| {i} | {row.get('surface')} | {row.get('head')} | {row.get('count')} | {row.get('groupConfidence')} |"
        )
    if not norm.get("semanticHeadGroups"):
        lines.append("| - | - | - | 0 | 0.0 |")
    lines.append("")

    lines.append("### Top fingerprint groups")
    lines.append("")
    lines.append("| rank | surface | fingerprint | count | confidence |")
    lines.append("|---:|---|---|---:|---:|")
    for i, row in enumerate(norm.get("fingerprintGroups", [])[:10], start=1):
        lines.append(
            f"| {i} | {row.get('surface')} | {row.get('fingerprint')} | {row.get('count')} | {row.get('groupConfidence')} |"
        )
    if not norm.get("fingerprintGroups"):
        lines.append("| - | - | - | 0 | 0.0 |")
    lines.append("")

    def emit_ranked_table(title: str, rows: list[JsonObj], cols: list[tuple[str, str]]) -> None:
        lines.append(f"## {title}")
        lines.append("")
        header = "| " + " | ".join(label for _, label in cols) + " |"
        sep = "|" + "|".join("---" for _ in cols) + "|"
        lines.append(header)
        lines.append(sep)
        for row in rows[:20]:
            values = [str(row.get(key, "")) for key, _ in cols]
            lines.append("| " + " | ".join(values) + " |")
        if not rows:
            lines.append("| - | - | - | - |")
        lines.append("")

    emit_ranked_table(
        "Ranked Vacuity Candidates",
        report.get("rankedVacuityCandidates", []),
        [("rank", "rank"), ("name", "declaration"), ("score", "score"), ("confidence", "confidence")],
    )
    emit_ranked_table(
        "Ranked Owner Candidates",
        report.get("rankedOwnerCandidates", []),
        [("rank", "rank"), ("ownerFile", "ownerFile"), ("score", "score"), ("confidence", "confidence")],
    )
    emit_ranked_table(
        "Ranked Replacement Candidates",
        report.get("rankedReplacementCandidates", []),
        [("rank", "rank"), ("replacementDecl", "replacementDecl"), ("score", "score"), ("confidence", "confidence")],
    )

    lines.append("## Ranked Fingerprint Corridors")
    lines.append("")
    lines.append("| rank | clusterKey | vacuityCount | replacementCount | score | confidence |")
    lines.append("|---:|---|---:|---:|---:|---:|")
    for row in report.get("rankedFingerprintCorridors", [])[:20]:
        lines.append(
            "| "
            + " | ".join(
                [
                    str(row.get("rank", "")),
                    str(row.get("clusterKey", "")),
                    str(row.get("vacuityCount", 0)),
                    str(row.get("replacementCount", 0)),
                    str(row.get("score", "")),
                    str(row.get("confidence", "")),
                ]
            )
            + " |"
        )
    if not report.get("rankedFingerprintCorridors"):
        lines.append("| - | - | 0 | 0 | 0.0 | 0.0 |")
    lines.append("")

    lines.append("## Ranked Declaration Plans")
    lines.append("")
    lines.append("| rank | candidate | probable_owner | probable_replacement | score | confidence |")
    lines.append("|---:|---|---|---|---:|---:|")
    for row in report.get("rankedDeclarationPlans", [])[:20]:
        owner_any = row.get("probable_owner")
        owner_file = ""
        if isinstance(owner_any, dict):
            owner_file_any = owner_any.get("ownerFile")
            if isinstance(owner_file_any, str):
                owner_file = owner_file_any
        corridor_any = row.get("probable_replacement_corridor")
        repl = ""
        if isinstance(corridor_any, list) and corridor_any:
            first = cast(Any, corridor_any[0])
            if isinstance(first, dict):
                repl = str(first.get("replacementDecl", ""))
        lines.append(
            "| "
            + " | ".join(
                [
                    str(row.get("rank", "")),
                    str(row.get("candidate", "")),
                    str(owner_file),
                    repl,
                    str(row.get("score", "")),
                    str(row.get("confidence", "")),
                ]
            )
            + " |"
        )
    if not report.get("rankedDeclarationPlans"):
        lines.append("| - | - | - | - | - | - |")
    lines.append("")

    lines.append("## Strict Admissibility Pre-checks")
    lines.append("")
    lines.append("| rank | candidate | replacementDecl | status | score | confidence |")
    lines.append("|---:|---|---|---|---:|---:|")
    for row in report.get("rankedAdmissibilityPrechecks", [])[:20]:
        lines.append(
            "| "
            + " | ".join(
                [
                    str(row.get("rank", "")),
                    str(row.get("candidate", "")),
                    str(row.get("replacementDecl", "")),
                    str(row.get("precheckStatus", "")),
                    str(row.get("score", "")),
                    str(row.get("confidence", "")),
                ]
            )
            + " |"
        )
    if not report.get("rankedAdmissibilityPrechecks"):
        lines.append("| - | - | - | - | 0.0 | 0.0 |")
    lines.append("")

    lines.append("## Confidence Provenance Weights")
    lines.append("")
    lines.append("- headSourceWeight: " + json.dumps(HEAD_SOURCE_WEIGHT, sort_keys=True))
    lines.append("- diagnosticProvenanceWeight: " + json.dumps(DIAG_PROVENANCE_WEIGHT, sort_keys=True))
    lines.append("- violationLevelWeight: " + json.dumps(VIOLATION_LEVEL_WEIGHT, sort_keys=True))
    lines.append("")

    lines.append("## Planner Policy")
    lines.append("")
    lines.append("- " + json.dumps(planner_policy_snapshot(), sort_keys=True))
    lines.append("")

    return "\n".join(lines)
