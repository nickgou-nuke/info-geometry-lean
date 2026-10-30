#!/usr/bin/env python3
"""Stage a current InfoTree-to-Git-fossil overlay as an immutable Arango generation.

Exact events already represented by ``evo_commit_files`` are linked through
small generation-scoped fossil-to-commit edges. Only events without a verified
base edge are stored as fallback event documents. Current InfoTree nodes
connect to shared path-fossil documents; historical source trees are never
copied and existing generations are never overwritten.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Iterable, Iterator
from urllib.parse import quote

from tools.infra.arango_env import (
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from tools.infra.arango_raw_infotree_ingest import (
    ArangoTarget,
    CollectionSpec,
    collection_count,
    create_collection,
    db_url,
    ensure_database,
    ensure_index,
    import_accounting_failures,
    list_collections,
    live_count_failures,
    request_json,
)


OVERLAY_SCHEMA = "info_geometry.git_fossil_overlay_manifest.v1"
EVENT_SCHEMA = "info_geometry.git_path_fossil_event.v1"
LINK_SCHEMA = "info_geometry.infotree_node_git_fossil_link.v1"
LINE_FOSSIL_SCHEMA = "info_geometry.git_line_fossil_span.v1"
DECL_LINE_FOSSIL_SCHEMA = "info_geometry.declaration_line_fossil_link.v1"
RECEIPT_COLLECTION = "repo_phylogeny_generation_receipts"
STAGE_SCHEMA = "info_geometry.git_fossil_overlay_generation.v2"


def _jsonl(path: Path) -> Iterator[dict[str, Any]]:
    with path.open("r", encoding="utf-8") as stream:
        for number, line in enumerate(stream, 1):
            if not line.strip():
                continue
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{number}: invalid JSON") from exc
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{number}: expected JSON object")
            yield row


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _path_fossil_id(git_head: str, source_path: str) -> str:
    return hashlib.sha256(f"{git_head}\0{source_path}".encode(
        "utf-8", errors="surrogateescape"
    )).hexdigest()


def _evolution_path_key(path: str) -> str:
    """Use the same raw-path SHA-256 key as tools/infra/evolution_ingest.py."""
    return hashlib.sha256(path.encode("utf-8", errors="surrogateescape")).hexdigest()


def _evolution_commit_file_key(event: dict[str, Any]) -> str:
    """Compute the existing evo_commit_files edge key for an extracted event."""
    path_key = _evolution_path_key(str(event.get("changedPath") or ""))
    stable = f"{event.get('commitSha', '')}:{event.get('changeType', '')}:{path_key}"
    return hashlib.sha256(stable.encode("utf-8")).hexdigest()


def _event_key(event: dict[str, Any], fossil_id: str) -> str:
    stable = "\0".join(str(event.get(field, "")) for field in (
        "historyRevision", "commitSha", "artifactPath", "changeType", "changedPath", "oldPath"
    ))
    return hashlib.sha256(f"{fossil_id}\0{stable}".encode("utf-8")).hexdigest()


def _link_key(link: dict[str, Any], generation_id: str) -> str:
    stable = "\0".join(str(link.get(field, "")) for field in (
        "currentSourcePath", "rootKey", "nodeKey"
    ))
    return hashlib.sha256(f"{generation_id}\0{stable}".encode("utf-8")).hexdigest()


def _line_edge_key(link: dict[str, Any], span_id: str, generation_id: str) -> str:
    stable = "\0".join(str(link.get(field, "")) for field in (
        "currentSourcePath", "rootKey", "nodeKey"
    ))
    return hashlib.sha256(f"{generation_id}\0{stable}\0{span_id}".encode("utf-8")).hexdigest()


def build_stage_plan(overlay_dir: Path, git_path_events: Path,
                     raw_generation_report: Path) -> dict[str, Any]:
    """Validate local artifacts and produce a bounded import plan without DB access."""
    overlay_dir = overlay_dir.resolve()
    manifest = json.loads((overlay_dir / "metadata.json").read_text(encoding="utf-8"))
    if manifest.get("schema") != OVERLAY_SCHEMA:
        raise ValueError(f"expected overlay schema {OVERLAY_SCHEMA}")
    generation_id = str(manifest.get("generationId") or "")
    git_head = str(manifest.get("gitHead") or "")
    if not re.fullmatch(r"[0-9a-f]{64}", generation_id):
        raise ValueError("overlay generationId must be a full SHA-256")
    if not re.fullmatch(r"[0-9a-f]{40,64}", git_head):
        raise ValueError("overlay gitHead must be a full Git object id")
    raw_report = json.loads(raw_generation_report.read_text(encoding="utf-8"))
    raw_generation_id = str(raw_report.get("generation_id") or "")
    if not raw_generation_id or raw_report.get("dry_run") is not False:
        raise ValueError("a completed non-dry-run RawInfoTree generation report is required")
    if not raw_report.get("validation", {}).get("ok"):
        raise ValueError("RawInfoTree generation report lacks successful export validation")
    raw_provenance_rows = raw_report.get("preflight", {}).get("source_provenance")
    if not isinstance(raw_provenance_rows, list):
        raise ValueError("RawInfoTree generation report lacks source provenance")
    raw_provenance = {
        str(row.get("sourcePath")): row for row in raw_provenance_rows
        if isinstance(row, dict) and row.get("sourcePath")
    }
    raw_node_collection = f"raw_infotree_nodes_g_{raw_generation_id}"
    raw_decl_link_collection = f"raw_infotree_decl_links_g_{raw_generation_id}"

    links_path = overlay_dir / "node_fossil_links.jsonl"
    line_fossils_path = overlay_dir / "source_line_fossils.jsonl"
    declaration_links_path = overlay_dir / "declaration_line_fossil_links.jsonl"
    if _sha256_file(links_path) != manifest.get("nodeLinksSha256"):
        raise ValueError("node fossil link file hash differs from overlay manifest")
    line_fossil_sha = _sha256_file(line_fossils_path)
    if line_fossil_sha != manifest.get("sourceLineFossilsSha256"):
        raise ValueError("source line fossil file hash differs from overlay manifest")
    declaration_links_sha = _sha256_file(declaration_links_path)
    if declaration_links_sha != manifest.get("declarationLineFossilLinksSha256"):
        raise ValueError("declaration line fossil link hash differs from overlay manifest")
    lineage_features = manifest.get("sourceLineageFeaturesByPath")
    if not isinstance(lineage_features, dict):
        raise ValueError("overlay manifest lacks source-lineage features")
    lineage_feature_sha = hashlib.sha256(json.dumps(
        lineage_features, sort_keys=True, ensure_ascii=False, separators=(",", ":")
    ).encode("utf-8")).hexdigest()
    if lineage_feature_sha != manifest.get("sourceLineageFeaturesSha256"):
        raise ValueError("source-lineage feature digest differs from overlay manifest")
    if _sha256_file(git_path_events) != manifest.get("gitPathEventsSha256"):
        raise ValueError("Git path event stream hash differs from overlay manifest")

    node_count = 0
    line_fossil_ids: set[str] = set()
    line_fossil_sources: dict[str, tuple[str, str]] = {}
    line_metrics: dict[str, dict[str, Any]] = {}
    line_fossil_count = 0
    for fossil in _jsonl(line_fossils_path):
        span_id = str(fossil.get("lineFossilSpanId") or "")
        source = str(fossil.get("sourcePath") or "")
        if (fossil.get("schema") != LINE_FOSSIL_SCHEMA
                or fossil.get("generationId") != generation_id
                or fossil.get("historyRevision") != git_head
                or not span_id or not source):
            raise ValueError("source line fossil has mismatched schema/generation or lacks identity")
        if span_id in line_fossil_ids:
            raise ValueError(f"duplicate source line fossil span id: {span_id}")
        line_count = fossil.get("lineCount")
        start_line, end_line = fossil.get("startLine"), fossil.get("endLineExclusive")
        origin_start, origin_end = fossil.get("originStartLine"), fossil.get("originEndLine")
        if (isinstance(line_count, bool) or not isinstance(line_count, int) or line_count < 1
                or any(isinstance(value, bool) or not isinstance(value, int)
                       for value in (start_line, end_line, origin_start, origin_end))
                or start_line < 1 or end_line - start_line != line_count
                or origin_start < 1 or origin_end - origin_start != line_count):
            raise ValueError(f"source line fossil has an invalid half-open interval: {source}")
        commit_sha = fossil.get("commitSha")
        origin_status = fossil.get("originStatus")
        if not isinstance(commit_sha, str) or origin_status not in {
                "committed_line_origin", "uncommitted_current_content"}:
            raise ValueError(f"source line fossil has an invalid commit attribution: {source}")
        if ((origin_status == "uncommitted_current_content") != (commit_sha == "0" * 40)):
            raise ValueError(f"source line fossil zero-SHA status mismatch: {source}")
        line_fossil_ids.add(span_id)
        line_fossil_sources[span_id] = (source, str(fossil.get("sourceSha256") or ""))
        metrics = line_metrics.setdefault(source, {
            "attributedLineCount": 0,
            "committedLineCount": 0,
            "currentContentLineCount": 0,
            "commits": set(),
            "originPaths": set(),
        })
        metrics["attributedLineCount"] += line_count
        if origin_status == "committed_line_origin":
            metrics["committedLineCount"] += line_count
            metrics["commits"].add(commit_sha)
            if fossil.get("originPath"):
                metrics["originPaths"].add(fossil["originPath"])
        else:
            metrics["currentContentLineCount"] += line_count
        line_fossil_count += 1
    if line_fossil_count != int(manifest.get("sourceLineFossilSpanCount", -1)):
        raise ValueError("source line fossil span count differs from overlay manifest")

    declaration_link_count = declaration_edge_count = 0
    seen_declaration_links: set[str] = set()
    declaration_link_sources: set[str] = set()
    declaration_metrics: dict[str, dict[str, Any]] = {}
    for declaration_link in _jsonl(declaration_links_path):
        link_key = str(declaration_link.get("linkKey") or "")
        source = str(declaration_link.get("currentSourcePath") or "")
        decl_key = str(declaration_link.get("declKey") or "")
        span_ids = declaration_link.get("lineFossilSpanIds", [])
        if (declaration_link.get("schema") != DECL_LINE_FOSSIL_SCHEMA
                or declaration_link.get("generationId") != generation_id
                or declaration_link.get("historyRevision") != git_head
                or not source or not link_key or not re.fullmatch(r"d_[0-9a-f]{40}", decl_key)
                or not declaration_link.get("declName") or not isinstance(span_ids, list)):
            raise ValueError("declaration line-fossil link has mismatched provenance or lacks identity")
        if link_key in seen_declaration_links:
            raise ValueError(f"duplicate current declaration link key: {link_key}")
        seen_declaration_links.add(link_key)
        declaration_link_sources.add(source)
        decl_stats = declaration_metrics.setdefault(source, {
            "declarationLinkCount": 0,
            "declarationWithLineOriginCount": 0,
            "declarations": set(),
        })
        decl_stats["declarationLinkCount"] += 1
        decl_stats["declarations"].add(decl_key)
        if span_ids:
            decl_stats["declarationWithLineOriginCount"] += 1
        for span_id in span_ids:
            if (span_id not in line_fossil_sources
                    or line_fossil_sources[span_id]
                    != (source, str(declaration_link.get("sourceSha256") or ""))):
                raise ValueError(f"declaration link references an absent or foreign line fossil: {source}")
        declaration_link_count += 1
        declaration_edge_count += len(span_ids)
    if declaration_link_count != int(manifest.get("declarationLineFossilLinkCount", -1)):
        raise ValueError("declaration line-fossil link count differs from overlay manifest")
    if declaration_edge_count != int(manifest.get("declarationLineFossilEdgeCount", -1)):
        raise ValueError("declaration line-fossil edge count differs from overlay manifest")

    links_by_path: dict[str, dict[str, Any]] = {}
    seen_node_keys: set[tuple[str, str, str]] = set()
    for link in _jsonl(links_path):
        if link.get("schema") != LINK_SCHEMA or link.get("historyRevision") != git_head:
            raise ValueError("node link has a mismatched schema or Git revision")
        if link.get("generationId") != generation_id:
            raise ValueError("node link belongs to a different overlay generation")
        source = str(link.get("currentSourcePath") or "")
        node_key, root_key = str(link.get("nodeKey") or ""), str(link.get("rootKey") or "")
        if not source or not node_key or not root_key:
            raise ValueError("node fossil link lacks source, node, or root identity")
        identity = (source, root_key, node_key)
        if identity in seen_node_keys:
            raise ValueError(f"duplicate current InfoTree node link {identity}")
        seen_node_keys.add(identity)
        expected_fossil = _path_fossil_id(git_head, source)
        if link.get("pathFossilId") != expected_fossil:
            raise ValueError(f"node has an invalid shared path fossil id: {source}")
        span_ids = link.get("lineFossilSpanIds", [])
        if not isinstance(span_ids, list) or any(
                span_id not in line_fossil_ids
                or line_fossil_sources[span_id] != (source, str(link.get("sourceSha256") or ""))
                for span_id in span_ids):
            raise ValueError(f"node link references an absent source line fossil span: {source}")
        links_by_path.setdefault(source, {
            "pathFossilId": expected_fossil,
            "sourceSha256": link.get("sourceSha256"),
            "leanContextFingerprint": link.get("leanContextFingerprint"),
            "historyRevision": git_head,
            "fossilEventCount": int(link.get("fossilEventCount", 0)),
            "pathHistoryStatus": link.get("pathHistoryStatus"),
            "relation": "module_path_cohabitation",
            "rawCaptureSha256": link.get("rawCaptureSha256"),
        })
        node_count += 1
    if node_count != int(manifest.get("nodeLinkCount", -1)):
        raise ValueError("node link count differs from overlay manifest")
    if len(links_by_path) != int(manifest.get("sourceCount", -1)):
        raise ValueError("node links do not cover the manifest source count")
    if set(lineage_features) != set(links_by_path):
        raise ValueError("source-lineage features do not cover the InfoTree source paths")
    for source, link_info in links_by_path.items():
        features = lineage_features[source]
        if (not isinstance(features, dict)
                or features.get("schema") != "info_geometry.source_lineage_features.v1"
                or features.get("generationId") != generation_id
                or features.get("historyRevision") != git_head
                or features.get("sourcePath") != source
                or features.get("sourceSha256") != link_info.get("sourceSha256")):
            raise ValueError(f"source-lineage feature provenance differs for {source}")
        line_stats = line_metrics.get(source, {
            "attributedLineCount": 0, "committedLineCount": 0,
            "currentContentLineCount": 0, "commits": set(), "originPaths": set(),
        })
        decl_stats = declaration_metrics.get(source, {
            "declarationLinkCount": 0,
            "declarationWithLineOriginCount": 0,
            "declarations": set(),
        })
        derived = {
            **{field: line_stats[field] for field in (
                "attributedLineCount", "committedLineCount", "currentContentLineCount"
            )},
            "distinctCommitCount": len(line_stats["commits"]),
            "distinctOriginPathCount": len(line_stats["originPaths"]),
            "declarationLinkCount": decl_stats["declarationLinkCount"],
            "declarationWithLineOriginCount": decl_stats[
                "declarationWithLineOriginCount"
            ],
            "distinctDeclarationCount": len(decl_stats["declarations"]),
        }
        if any(features.get(field) != value for field, value in derived.items()):
            raise ValueError(f"source-lineage feature counts disagree with fossil streams: {source}")
        if features.get("lineAttributionStatus") == "complete":
            if features.get("attributedLineCount") != features.get("lineCount"):
                raise ValueError(f"complete line attribution does not cover current source: {source}")
        elif features.get("attributedLineCount") != 0:
            raise ValueError(f"unavailable line attribution has attributed lines: {source}")
    if not declaration_link_sources <= set(links_by_path):
        raise ValueError("declaration line-fossil link references a source outside current InfoTree scope")
    for source, link_info in links_by_path.items():
        provenance = raw_provenance.get(source)
        if (provenance is None
                or provenance.get("sourceSha256") != link_info.get("sourceSha256")
                or provenance.get("leanContextFingerprint") != link_info.get("leanContextFingerprint")):
            raise ValueError(f"RawInfoTree generation provenance differs for {source}")

    event_count = 0
    event_counts_by_path: Counter[str] = Counter()
    seen_events: set[str] = set()
    for event in _jsonl(git_path_events):
        if event.get("schema") != EVENT_SCHEMA or event.get("historyRevision") != git_head:
            raise ValueError("Git path event has a mismatched schema or revision")
        source = str(event.get("artifactPath") or "")
        if source not in links_by_path:
            raise ValueError(f"Git path event is outside the InfoTree capture scope: {source}")
        event_key = _event_key(event, links_by_path[source]["pathFossilId"])
        if event_key in seen_events:
            raise ValueError(f"duplicate Git path fossil event identity: {source}")
        seen_events.add(event_key)
        event_counts_by_path[source] += 1
        event_count += 1
    if event_count != int(manifest.get("gitPathEventCount", -1)):
        raise ValueError("Git path event count differs from overlay manifest")
    for source, link_info in links_by_path.items():
        if event_counts_by_path[source] != link_info["fossilEventCount"]:
            raise ValueError(f"node link fossil event count differs for {source}")

    stage_generation_id = hashlib.sha256(
        f"{generation_id}\0{STAGE_SCHEMA}".encode("utf-8")
    ).hexdigest()
    suffix = stage_generation_id
    collections = {
        "path_fossils": f"repo_path_fossils_g_{suffix}",
        "path_events": f"repo_git_path_events_g_{suffix}",
        "evolution_commit_edges": f"repo_path_fossil_commit_edges_g_{suffix}",
        "node_edges": f"repo_infotree_path_fossil_edges_g_{suffix}",
        "line_fossils": f"repo_source_line_fossils_g_{suffix}",
        "node_line_edges": f"repo_infotree_line_fossil_edges_g_{suffix}",
        "declaration_line_edges": f"repo_declaration_line_fossil_edges_g_{suffix}",
        "raw_nodes": raw_node_collection,
        "raw_decl_links": raw_decl_link_collection,
    }
    return {
        "generationId": stage_generation_id,
        "overlayGenerationId": generation_id,
        "gitHead": git_head,
        "rawInfoTreeGenerationId": raw_generation_id,
        "rawBuildFingerprint": raw_report.get("build_fingerprint"),
        "sourceCount": len(links_by_path),
        "nodeLinkCount": node_count,
        "sourceLineFossilSpanCount": line_fossil_count,
        "declarationLineFossilLinkCount": declaration_link_count,
        "declarationLineFossilEdgeCount": declaration_edge_count,
        "pathEventCount": event_count,
        "collections": collections,
        "sourcePaths": sorted(links_by_path),
        "pathFossils": links_by_path,
        "overlayManifest": manifest,
        "overlayDir": overlay_dir,
        "gitPathEvents": git_path_events.resolve(),
    }


def _iter_path_fossils(plan: dict[str, Any]) -> Iterator[dict[str, Any]]:
    for source, info in sorted(plan["pathFossils"].items()):
        yield {
            "_key": info["pathFossilId"],
            "schema": "info_geometry.git_path_fossil.v1",
            "generationId": plan["generationId"],
            "overlayGenerationId": plan["overlayGenerationId"],
            "sourcePath": source,
            "sourceSha256": info["sourceSha256"],
            "leanContextFingerprint": info["leanContextFingerprint"],
            "historyRevision": plan["gitHead"],
            "eventCount": info["fossilEventCount"],
            "overlayEventRecordCount": info.get(
                "overlayEventRecordCount", info["fossilEventCount"]
            ),
            "reusedEvolutionEventCount": info.get("reusedEvolutionEventCount", 0),
            "pathHistoryStatus": info["pathHistoryStatus"],
            "relationSemantics": "module_path_cohabitation",
            "rawCaptureSha256": info["rawCaptureSha256"],
            "sourceLineageFeatures": plan["overlayManifest"][
                "sourceLineageFeaturesByPath"
            ][source],
            "rawInfoTreeGenerationId": plan["rawInfoTreeGenerationId"],
        }


def _iter_path_events(plan: dict[str, Any]) -> Iterator[dict[str, Any]]:
    reuse = plan.get("evolutionReuse", {})
    reused = reuse.get("reusedEdgeKeys", set())
    for event in _jsonl(plan["gitPathEvents"]):
        fossil_id = _path_fossil_id(plan["gitHead"], str(event["artifactPath"]))
        event_key = _event_key(event, fossil_id)
        edge_key = _evolution_commit_file_key(event)
        if edge_key in reused:
            continue
        if not reuse.get("baseCollectionsAvailable", False):
            reason = "evolution_collections_unavailable"
        elif edge_key not in reused:
            reason = "no_exact_commit_file_edge"
        else:
            reason = "event_not_reused"
        yield {
            "_key": event_key,
            "pathFossilId": fossil_id,
            "fallbackReason": reason,
            **event,
        }


def _iter_evolution_commit_edges(plan: dict[str, Any]) -> Iterator[dict[str, Any]]:
    path_fossils = plan["collections"]["path_fossils"]
    reused = plan.get("evolutionReuse", {}).get("reusedEdgeKeys", set())
    for event in _jsonl(plan["gitPathEvents"]):
        source = str(event["artifactPath"])
        fossil_id = _path_fossil_id(plan["gitHead"], source)
        event_id = _event_key(event, fossil_id)
        edge_key = _evolution_commit_file_key(event)
        if edge_key not in reused:
            continue
        relation_key = hashlib.sha256(
            f"{plan['generationId']}\0{event_id}".encode("utf-8")
        ).hexdigest()
        yield {
            "_key": relation_key,
            "_from": f"{path_fossils}/{fossil_id}",
            "_to": f"evo_commits/{event['commitSha']}",
            "role": "current_path_fossil_commit_event",
            "generationId": plan["generationId"],
            "historyRevision": plan["gitHead"],
            "currentSourcePath": source,
            "commitSha": event["commitSha"],
            "changeType": event["changeType"],
            "changedPath": event["changedPath"],
            "oldPath": event.get("oldPath"),
            "committerTimestamp": event.get("committerTimestamp"),
            "evolutionCommitFileEdgeKey": edge_key,
            "relation": "git_name_status_path_continuity",
            "authority": "captured path event with exact existing evo_commit_files witness",
        }


def _iter_line_fossils(plan: dict[str, Any]) -> Iterator[dict[str, Any]]:
    path = plan["overlayDir"] / "source_line_fossils.jsonl"
    for fossil in _jsonl(path):
        yield {"_key": fossil["lineFossilSpanId"], **fossil}


def _iter_node_edges(plan: dict[str, Any]) -> Iterator[dict[str, Any]]:
    raw_nodes = plan["collections"]["raw_nodes"]
    path_fossils = plan["collections"]["path_fossils"]
    links_path = plan["overlayDir"] / "node_fossil_links.jsonl"
    for link in _jsonl(links_path):
        node_id = f"{raw_nodes}/{link['nodeKey']}"
        path_id = f"{path_fossils}/{link['pathFossilId']}"
        yield {
            "_key": _link_key(link, plan["generationId"]),
            "_from": node_id,
            "_to": path_id,
            "role": "current_infotree_node_path_fossil",
            "generationId": plan["generationId"],
            "currentSourcePath": link["currentSourcePath"],
            "sourceSha256": link["sourceSha256"],
            "leanContextFingerprint": link["leanContextFingerprint"],
            "rawCaptureSha256": link["rawCaptureSha256"],
            "rootKey": link["rootKey"],
            "nodeKey": link["nodeKey"],
            "nodeKind": link.get("nodeKind"),
            "depth": link.get("depth"),
            "currentDeclarationLinks": link.get("currentDeclarationLinks", []),
            "captureLoss": link.get("captureLoss"),
            "relation": "module_path_cohabitation",
            "authority": link.get("authority"),
            "sourceSpan": link.get("sourceSpan"),
            "lineFossilSpanIds": link.get("lineFossilSpanIds", []),
            "lineFossilStatus": link.get("lineFossilStatus"),
        }


def _iter_node_line_edges(plan: dict[str, Any]) -> Iterator[dict[str, Any]]:
    raw_nodes = plan["collections"]["raw_nodes"]
    line_fossils = plan["collections"]["line_fossils"]
    links_path = plan["overlayDir"] / "node_fossil_links.jsonl"
    for link in _jsonl(links_path):
        node_id = f"{raw_nodes}/{link['nodeKey']}"
        for span_id in link.get("lineFossilSpanIds", []):
            yield {
                "_key": _line_edge_key(link, span_id, plan["generationId"]),
                "_from": node_id,
                "_to": f"{line_fossils}/{span_id}",
                "role": "current_infotree_node_line_origin",
                "generationId": plan["generationId"],
                "currentSourcePath": link["currentSourcePath"],
                "rootKey": link["rootKey"],
                "nodeKey": link["nodeKey"],
                "relationAuthority": "current syntax span intersects current-line blame attribution",
            }


def _iter_declaration_line_edges(plan: dict[str, Any]) -> Iterator[dict[str, Any]]:
    declaration_links = plan["collections"]["raw_decl_links"]
    line_fossils = plan["collections"]["line_fossils"]
    links_path = plan["overlayDir"] / "declaration_line_fossil_links.jsonl"
    for link in _jsonl(links_path):
        for span_id in link.get("lineFossilSpanIds", []):
            stable = f"{plan['generationId']}\0{link['linkKey']}\0{span_id}"
            yield {
                "_key": hashlib.sha256(stable.encode("utf-8")).hexdigest(),
                "_from": f"{declaration_links}/{link['linkKey']}",
                "_to": f"{line_fossils}/{span_id}",
                "role": "current_declaration_line_origin",
                "generationId": plan["generationId"],
                "historyRevision": plan["gitHead"],
                "sourcePath": link["currentSourcePath"],
                "declKey": link["declKey"],
                "declName": link["declName"],
                "nodeKey": link["nodeKey"],
                "lineFossilSpanId": span_id,
                "relation": link["relation"],
                "authority": link["authority"],
            }


def _import_immutable(target: ArangoTarget, collection: str,
                      rows: Iterable[dict[str, Any]], batch_size: int) -> dict[str, int]:
    created = errors = total = 0
    batch: list[dict[str, Any]] = []

    def flush() -> None:
        nonlocal created, errors, total, batch
        if not batch:
            return
        response = request_json(
            "POST",
            db_url(target, f"/_api/document/{quote(collection)}?overwriteMode=conflict&silent=false"),
            username=target.username,
            password=target.password,
            payload=batch,
        )
        if isinstance(response, list):
            errors += sum(1 for row in response if isinstance(row, dict) and row.get("error"))
            created += len(response) - sum(1 for row in response if isinstance(row, dict) and row.get("error"))
        elif isinstance(response, dict) and response.get("error"):
            errors += len(batch)
        else:
            created += len(batch)
        total += len(batch)
        batch = []

    for row in rows:
        batch.append(row)
        if len(batch) >= batch_size:
            flush()
    flush()
    return {"created": created, "errors": errors, "total": total}


def _aql(target: ArangoTarget, query: str, bind_vars: dict[str, Any]) -> list[Any]:
    result = request_json("POST", db_url(target, "/_api/cursor"),
                          username=target.username, password=target.password,
                          payload={"query": query, "bindVars": bind_vars})
    return result.get("result", []) if isinstance(result, dict) else []


def _prepare_evolution_reuse(plan: dict[str, Any], target: ArangoTarget,
                             existing: set[str], *, batch_size: int = 500) -> dict[str, Any]:
    """Resolve events against exact live evo edges, retaining unmatched events.

    A matched event gets a generation-scoped path-fossil-to-commit edge whose
    ``evolutionCommitFileEdgeKey`` points to the exact existing file-change
    edge. This event-level relation preserves the captured Git revision and
    cannot pull unrelated branches through a shared historical path vertex.
    """
    if batch_size < 1:
        raise ValueError("evolution reuse batch size must be positive")
    base_available = {"evo_commit_files", "evo_files", "evo_commits"} <= existing
    existing_edge_keys: set[str] = set()
    candidate_batch: dict[str, tuple[str, str, str, str | None]] = {}
    old_paths_by_key: dict[str, str | None] = {}
    conflicting_keys: set[str] = set()

    def resolve_batch() -> None:
        if not candidate_batch or not base_available:
            candidate_batch.clear()
            return
        rows = [
            {"edgeKey": key, "commitSha": values[0], "pathKey": values[1],
             "changeType": values[2], "oldPath": values[3]}
            for key, values in candidate_batch.items()
        ]
        existing_edge_keys.update(_aql(
            target,
            "FOR row IN @rows "
            "LET edge = DOCUMENT(CONCAT('evo_commit_files/', row.edgeKey)) "
            "FILTER edge != null "
            "FILTER edge._from == CONCAT('evo_commits/', row.commitSha) "
            "AND edge._to == CONCAT('evo_files/', row.pathKey) "
            "AND edge.change_type == row.changeType "
            "AND edge.old_path == row.oldPath "
            "AND edge.old_path_base64 == null "
            "AND DOCUMENT(edge._from) != null AND DOCUMENT(edge._to) != null "
            "RETURN row.edgeKey",
            {"rows": rows},
        ))
        candidate_batch.clear()

    for event in _jsonl(plan["gitPathEvents"]):
        if base_available:
            edge_key = _evolution_commit_file_key(event)
            old_path = event.get("oldPath")
            if old_path is not None and not isinstance(old_path, str):
                raise ValueError("fossil oldPath must be a string or null")
            if edge_key in old_paths_by_key and old_paths_by_key[edge_key] != old_path:
                conflicting_keys.add(edge_key)
            old_paths_by_key[edge_key] = old_path
            candidate_batch[edge_key] = (
                str(event.get("commitSha") or ""),
                _evolution_path_key(str(event.get("changedPath") or "")),
                str(event.get("changeType") or ""),
                old_path,
            )
            if len(candidate_batch) >= batch_size:
                resolve_batch()
    resolve_batch()
    # A key excludes the rename source. Conflicting observations cannot both
    # be represented by one base document, including across batch boundaries.
    existing_edge_keys.difference_update(conflicting_keys)

    reused_by_source: Counter[str] = Counter()
    fallback_by_source: Counter[str] = Counter()
    fallback_reason_counts: Counter[str] = Counter()
    event_count = 0
    for event in _jsonl(plan["gitPathEvents"]):
        source = str(event["artifactPath"])
        edge_key = _evolution_commit_file_key(event)
        event_count += 1
        if edge_key in existing_edge_keys:
            reused_by_source[source] += 1
        else:
            fallback_by_source[source] += 1
            if not base_available:
                reason = "evolution_collections_unavailable"
            else:
                reason = "no_exact_commit_file_edge"
            fallback_reason_counts[reason] += 1
    if event_count != plan["pathEventCount"]:
        raise RuntimeError("path event stream changed while resolving evolution reuse")

    for source, info in plan["pathFossils"].items():
        info["reusedEvolutionEventCount"] = reused_by_source[source]
        info["overlayEventRecordCount"] = fallback_by_source[source]
    head_present = False
    if "evo_commits" in existing:
        head_present = bool(_aql(
            target,
            "FOR c IN evo_commits FILTER c._key == @head LIMIT 1 RETURN c._key",
            {"head": plan["gitHead"]},
        ))
    reused_count = sum(reused_by_source.values())
    summary = {
        "schema": "info_geometry.evolution_history_reuse.v1",
        "status": ("exact_reuse" if reused_count == event_count and event_count > 0 else
                   "partial_exact_reuse" if reused_count else
                   "overlay_only_no_exact_reuse"),
        "baseCollectionsAvailable": base_available,
        "snapshotHeadPresentInArango": head_present,
        "totalPathEvents": event_count,
        "reusedPathEvents": reused_count,
        "overlayFallbackEvents": sum(fallback_by_source.values()),
        "distinctReusedCommitFileEdges": len(existing_edge_keys),
        "reusedCommitRelationEdgeCount": reused_count,
        "fallbackReasonCounts": dict(sorted(fallback_reason_counts.items())),
        "reusedEdgeKeys": existing_edge_keys,
    }
    plan["evolutionReuse"] = summary
    return summary


def stage_generation(plan: dict[str, Any], target: ArangoTarget,
                     *, batch_size: int = 1000) -> dict[str, Any]:
    """Create generation-suffixed collections, import, validate, then write receipt."""
    ensure_database(target)
    existing = list_collections(target)
    specs = [
        CollectionSpec(plan["collections"]["path_fossils"], False),
        CollectionSpec(plan["collections"]["path_events"], False),
        CollectionSpec(plan["collections"]["node_edges"], True),
        CollectionSpec(plan["collections"]["line_fossils"], False),
        CollectionSpec(plan["collections"]["node_line_edges"], True),
        CollectionSpec(plan["collections"]["declaration_line_edges"], True),
        CollectionSpec(plan["collections"]["evolution_commit_edges"], True),
    ]
    conflicts = [spec.name for spec in specs if spec.name in existing]
    if conflicts:
        raise RuntimeError("refusing to overwrite existing fossil generation collections: "
                           + ", ".join(conflicts))
    if RECEIPT_COLLECTION in existing:
        duplicate = _aql(target,
                         f"FOR d IN {RECEIPT_COLLECTION} FILTER d._key == @key RETURN d._key",
                         {"key": plan["generationId"]})
        if duplicate:
            raise RuntimeError("fossil overlay generation receipt already exists")

    raw_collection = plan["collections"]["raw_nodes"]
    raw_decl_link_collection = plan["collections"]["raw_decl_links"]
    if raw_collection not in existing:
        raise RuntimeError(f"raw InfoTree generation collection is absent: {raw_collection}")
    if raw_decl_link_collection not in existing:
        raise RuntimeError(
            f"raw InfoTree declaration-link collection is absent: {raw_decl_link_collection}"
        )
    generation_collection = "raw_infotree_generations"
    if generation_collection not in existing:
        raise RuntimeError("raw InfoTree generation receipt collection is absent")
    raw_receipts = _aql(
        target,
        f"FOR g IN {generation_collection} FILTER g._key == @key RETURN "
        "{status:g.status, buildFingerprint:g.buildFingerprint, "
        "collections:g.collections, sourceProvenance:g.sourceProvenance}",
        {"key": plan["rawInfoTreeGenerationId"]},
    )
    if len(raw_receipts) != 1 or raw_receipts[0].get("status") != "complete":
        raise RuntimeError("no unique complete RawInfoTree generation receipt was found")
    raw_receipt = raw_receipts[0]
    if raw_receipt.get("buildFingerprint") != plan.get("rawBuildFingerprint"):
        raise RuntimeError("RawInfoTree build fingerprint differs from local generation report")
    if (raw_receipt.get("collections") or {}).get("raw_infotree_nodes") != raw_collection:
        raise RuntimeError("RawInfoTree receipt points to a different node collection")
    if (raw_receipt.get("collections") or {}).get("raw_infotree_decl_links") != raw_decl_link_collection:
        raise RuntimeError("RawInfoTree receipt points to a different declaration-link collection")
    receipt_sources = {
        str(row.get("sourcePath")): row for row in raw_receipt.get("sourceProvenance", [])
        if isinstance(row, dict) and row.get("sourcePath")
    }
    for source, info in plan["pathFossils"].items():
        source_receipt = receipt_sources.get(source)
        if (source_receipt is None
                or source_receipt.get("sourceSha256") != info.get("sourceSha256")
                or source_receipt.get("leanContextFingerprint") != info.get("leanContextFingerprint")):
            raise RuntimeError(f"Arango RawInfoTree provenance differs for {source}")
    raw_count = collection_count(target, raw_collection)
    raw_expected = int(plan["overlayManifest"]["nodeLinkCount"])
    if raw_count != raw_expected:
        raise RuntimeError(f"raw node collection count mismatch: expected {raw_expected}, found {raw_count}")

    evolution_reuse = _prepare_evolution_reuse(plan, target, set(existing))

    for spec in specs:
        create_collection(target, spec)

    imports = {
        specs[0].name: _import_immutable(target, specs[0].name,
                                        _iter_path_fossils(plan), batch_size),
        specs[1].name: _import_immutable(target, specs[1].name,
                                        _iter_path_events(plan), batch_size),
        specs[2].name: _import_immutable(target, specs[2].name,
                                        _iter_node_edges(plan), batch_size),
        specs[3].name: _import_immutable(target, specs[3].name,
                                        _iter_line_fossils(plan), batch_size),
        specs[4].name: _import_immutable(target, specs[4].name,
                                        _iter_node_line_edges(plan), batch_size),
        specs[5].name: _import_immutable(target, specs[5].name,
                                        _iter_declaration_line_edges(plan), batch_size),
        specs[6].name: _import_immutable(target, specs[6].name,
                                        _iter_evolution_commit_edges(plan), batch_size),
    }
    failures = import_accounting_failures({
        name: {**row, "updated": 0, "error": row["errors"] > 0}
        for name, row in imports.items()
    })
    if failures:
        raise RuntimeError("fossil overlay import accounting failed: " + "; ".join(failures))

    ensure_index(target, specs[0].name, ["sourcePath"], unique=True, sparse=False)
    ensure_index(target, specs[1].name, ["pathFossilId", "commitSha"], sparse=False)
    ensure_index(target, specs[2].name, ["currentSourcePath", "nodeKey"], sparse=False)
    ensure_index(target, specs[3].name, ["sourcePath", "startLine"], sparse=False)
    ensure_index(target, specs[3].name, ["commitSha"], sparse=False)
    ensure_index(target, specs[4].name, ["currentSourcePath", "nodeKey"], sparse=False)
    ensure_index(target, specs[5].name, ["declKey", "sourcePath"], sparse=False)
    ensure_index(target, specs[6].name, ["currentSourcePath", "commitSha"], sparse=False)
    live_counts = {spec.name: collection_count(target, spec.name) for spec in specs}
    expected_counts = {
        specs[0].name: plan["sourceCount"],
        specs[1].name: evolution_reuse["overlayFallbackEvents"],
        specs[2].name: plan["nodeLinkCount"],
        specs[3].name: plan["sourceLineFossilSpanCount"],
        specs[4].name: sum(
            len(link.get("lineFossilSpanIds", []))
            for link in _jsonl(plan["overlayDir"] / "node_fossil_links.jsonl")
        ),
        specs[5].name: plan["declarationLineFossilEdgeCount"],
        specs[6].name: evolution_reuse["reusedCommitRelationEdgeCount"],
    }
    count_failures = live_count_failures(expected_counts, live_counts)
    if count_failures:
        raise RuntimeError("fossil overlay count validation failed: " + "; ".join(count_failures))

    dangling = _aql(
        target,
        f"FOR e IN {specs[2].name} "
        "FILTER DOCUMENT(e._from) == null OR DOCUMENT(e._to) == null "
        "LIMIT 10 RETURN {_key:e._key, from:e._from, to:e._to}",
        {},
    )
    if dangling:
        raise RuntimeError(f"fossil overlay has dangling node/path endpoints: {dangling[:3]}")
    dangling_line = _aql(
        target,
        f"FOR e IN {specs[4].name} "
        "FILTER DOCUMENT(e._from) == null OR DOCUMENT(e._to) == null "
        "LIMIT 10 RETURN {_key:e._key, from:e._from, to:e._to}",
        {},
    )
    if dangling_line:
        raise RuntimeError(f"line-origin overlay has dangling endpoints: {dangling_line[:3]}")
    dangling_declaration = _aql(
        target,
        f"FOR e IN {specs[5].name} "
        "FILTER DOCUMENT(e._from) == null OR DOCUMENT(e._to) == null "
        "LIMIT 10 RETURN {_key:e._key, from:e._from, to:e._to}",
        {},
    )
    if dangling_declaration:
        raise RuntimeError(
            f"declaration line-origin overlay has dangling endpoints: {dangling_declaration[:3]}"
        )
    dangling_evolution = _aql(
        target,
        f"FOR e IN {specs[6].name} "
        "FILTER DOCUMENT(e._from) == null OR DOCUMENT(e._to) == null "
        "LIMIT 10 RETURN {_key:e._key, from:e._from, to:e._to}",
        {},
    )
    if dangling_evolution:
        raise RuntimeError(
            f"evolution commit reuse overlay has dangling endpoints: {dangling_evolution[:3]}"
        )

    if RECEIPT_COLLECTION not in existing:
        create_collection(target, CollectionSpec(RECEIPT_COLLECTION, False))
    receipt = {
        "_key": plan["generationId"],
        "schema": STAGE_SCHEMA,
        "status": "staged_validated",
        "generationId": plan["generationId"],
        "overlayGenerationId": plan["overlayGenerationId"],
        "gitHead": plan["gitHead"],
        "rawInfoTreeGenerationId": plan["rawInfoTreeGenerationId"],
        "collections": plan["collections"],
        "sourceCount": plan["sourceCount"],
        "nodeLinkCount": plan["nodeLinkCount"],
        "pathEventCount": plan["pathEventCount"],
        "storedPathEventCount": evolution_reuse["overlayFallbackEvents"],
        "evolutionHistoryReuse": {
            key: value for key, value in evolution_reuse.items()
            if key != "reusedEdgeKeys"
        },
        "sourceLineFossilSpanCount": plan["sourceLineFossilSpanCount"],
        "declarationLineFossilLinkCount": plan["declarationLineFossilLinkCount"],
        "declarationLineFossilEdgeCount": plan["declarationLineFossilEdgeCount"],
        "imports": imports,
        "liveCounts": live_counts,
        "countFailures": count_failures,
        "danglingEndpoints": 0,
        "relationSemantics": "module_path_cohabitation",
        "authority": "append-only staged current InfoTree/Git path-fossil overlay; not declaration ancestry",
    }
    request_json(
        "POST", db_url(target, f"/_api/document/{RECEIPT_COLLECTION}?waitForSync=true"),
        username=target.username, password=target.password, payload=receipt,
    )
    return receipt


def main() -> int:
    load_repo_arango_env()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("overlay_dir", type=Path)
    parser.add_argument("git_path_events", type=Path)
    parser.add_argument("raw_generation_report", type=Path)
    parser.add_argument("--endpoint", default=arango_endpoint())
    parser.add_argument("--database", default=arango_database())
    parser.add_argument("--username", default=arango_username())
    parser.add_argument("--password", default=arango_password("alexandria_root"))
    parser.add_argument("--batch-size", type=int, default=1000)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    plan = build_stage_plan(args.overlay_dir, args.git_path_events, args.raw_generation_report)
    if args.dry_run:
        print(json.dumps({key: value for key, value in plan.items()
                          if key not in {"pathFossils", "overlayManifest", "overlayDir", "gitPathEvents"}},
                         sort_keys=True))
        return 0
    target = ArangoTarget(str(args.endpoint).rstrip("/"), str(args.database),
                          str(args.username), str(args.password))
    receipt = stage_generation(plan, target, batch_size=max(1, int(args.batch_size)))
    print(json.dumps(receipt, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
