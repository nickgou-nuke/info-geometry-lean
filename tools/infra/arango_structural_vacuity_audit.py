#!/usr/bin/env python3
import argparse
import base64
import json
import os
import re
import sys
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import quote
from urllib.request import Request, urlopen


TRIVIAL_TARGETS = [
    "Eq.refl",
    "rfl",
    "trivial",
    "True.intro",
    "False.elim",
    "id",
    "Eq.ndrec",
    "Eq.rec",
    "Iff.rfl",
    "of_eq_true",
    "Eq.symm",
    "cast",
    "Eq",
    "True",
    "False",
    "HEq.refl",
    "And.intro",
    "And.left",
    "And.right",
    "Or.inl",
    "Or.inr",
    "Iff.intro",
    "Iff.mp",
    "Iff.mpr",
    "Not.intro",
]

FOUNDATIONAL_TARGETS = [
    "Classical.choice",
    "Quot.sound",
    "propext",
    "funext",
]

SUSPICIOUS_TARGETS = [
    "sorryAx",
]

GENERATED_NAME_REGEX = r"\.(eq_|sizeOf_spec|injEq)"


def collection_name(value: str) -> str:
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", value):
        raise argparse.ArgumentTypeError(f"Unsafe Arango collection name: {value!r}")
    return value


def positive_int(value: str) -> int:
    try:
        number = int(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(f"Expected positive integer: {value!r}") from exc
    if number <= 0:
        raise argparse.ArgumentTypeError(f"Expected positive integer: {value!r}")
    return number


def request_json(method, url, username, password, payload=None, timeout=30):
    body = None if payload is None else json.dumps(payload).encode("utf-8")

    req = Request(url, data=body, method=method)

    auth = base64.b64encode(f"{username}:{password}".encode("utf-8")).decode("ascii")
    req.add_header("Authorization", f"Basic {auth}")
    req.add_header("Accept", "application/json")

    if body is not None:
        req.add_header("Content-Type", "application/json")

    try:
        with urlopen(req, timeout=timeout) as resp:
            raw = resp.read().decode("utf-8")
    except HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"HTTP {exc.code} {url}: {detail}") from exc
    except URLError as exc:
        raise RuntimeError(f"Could not connect to ArangoDB at {url}: {exc}") from exc

    data = json.loads(raw) if raw else {}

    if data.get("error"):
        raise RuntimeError(
            f"ArangoDB API error {data.get('code')}: "
            f"{data.get('errorMessage', data)}"
        )

    return data


def run_aql(base_url, database, username, password, query, bind_vars=None, batch_size=1000, fail_on_warning=False):
    base_url = base_url.rstrip("/")
    database = quote(database, safe="")
    cursor_url = f"{base_url}/_db/{database}/_api/cursor"

    payload = {
        "query": query,
        "bindVars": bind_vars or {},
        "batchSize": batch_size,
        "options": {
            "failOnWarning": fail_on_warning,
        },
    }

    data = request_json(
        "POST",
        cursor_url,
        username=username,
        password=password,
        payload=payload,
    )

    results = list(data.get("result", []))
    warnings = list(data.get("extra", {}).get("warnings", []))

    while data.get("hasMore"):
        cursor_id = data.get("id")
        if not cursor_id:
            raise RuntimeError("Arango cursor response had hasMore=true but no cursor id.")

        data = request_json(
            "POST",
            f"{cursor_url}/{quote(str(cursor_id), safe='')}",
            username=username,
            password=password,
        )

        results.extend(data.get("result", []))
        warnings.extend(data.get("extra", {}).get("warnings", []))

    return results, warnings


def build_query(node_collection, edge_collection, direction):
    return f"""
    WITH {node_collection}

    FOR doc IN {node_collection}
      FILTER doc.kind == "theorem"
      FILTER IS_STRING(doc.name)
      FILTER IS_ARRAY(doc.labels) AND @namespace_label IN doc.labels
      FILTER NOT REGEX_TEST(doc.name, @generated_name_regex, false)

      LET deps = (
        FOR v, e, p IN 1..@max_depth {direction} doc {edge_collection}
          FILTER LENGTH(@edge_kinds) == 0
             OR LENGTH(
                  FOR edge IN p.edges
                    FILTER edge.kind IN @edge_kinds
                       OR edge.type IN @edge_kinds
                       OR edge.rel IN @edge_kinds
                       OR edge.label IN @edge_kinds
                       OR (
                            IS_ARRAY(edge.labels)
                            AND LENGTH(INTERSECTION(edge.labels, @edge_kinds)) > 0
                          )
                    RETURN 1
                ) == LENGTH(p.edges)
          FILTER IS_STRING(v.name)
          RETURN DISTINCT v.name
      )

      LET trivial_deps = (
        FOR d IN deps
          FILTER d IN @trivial_targets
          RETURN d
      )
      
      LET foundational_deps = (
        FOR d IN deps
          FILTER d IN @foundational_targets
          RETURN d
      )

      LET suspicious_deps = (
        FOR d IN deps
          FILTER d IN @suspicious_targets
          RETURN d
      )

      LET non_domain_deps = (
        FOR d IN deps
          FILTER d NOT IN @trivial_targets
             AND d NOT IN @foundational_targets
             AND d NOT IN @suspicious_targets
          RETURN d
      )

      LET has_sorry = LENGTH(suspicious_deps) > 0

      LET classification = (
        has_sorry
          ? "admitted_by_sorry"
          : (
              LENGTH(deps) == 0
                ? "dependency_free"
                : (
                    LENGTH(non_domain_deps) == 0 AND LENGTH(foundational_deps) == 0
                      ? "only_trivial_dependencies"
                      : "only_foundational_dependencies"
                  )
            )
      )

      FILTER has_sorry OR LENGTH(non_domain_deps) == 0

      SORT classification, doc.name

      RETURN {{
        id: doc._id,
        key: doc._key,
        name: doc.name,
        classification: classification,
        dep_name_count: LENGTH(deps),
        deps: deps,
        trivial_deps: trivial_deps,
        foundational_deps: foundational_deps,
        suspicious_deps: suspicious_deps,
        non_domain_deps: non_domain_deps
      }}
    """


def make_report(results, warnings):
    counts = Counter(item["classification"] for item in results)

    return {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "status": "findings" if results else "clean",
        "summary": {
            "total_findings": len(results),
            "admitted_by_sorry": counts.get("admitted_by_sorry", 0),
            "dependency_free": counts.get("dependency_free", 0),
            "only_trivial_dependencies": counts.get("only_trivial_dependencies", 0),
            "only_foundational_dependencies": counts.get("only_foundational_dependencies", 0),
            "warnings": len(warnings),
        },
        "warnings": warnings,
        "findings": results,
    }


def write_json(path, report):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def md_code(value):
    text = str(value)
    return "`" + text.replace("`", "\\`") + "`"


def write_markdown(path, report):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)

    lines = [
        "# Structural Vacuity Audit",
        "",
        f"Status: `{report['status']}`",
        "",
        "## Summary",
        "",
        f"- Total findings: {report['summary']['total_findings']}",
        f"- Admitted by `sorryAx`: {report['summary']['admitted_by_sorry']}",
        f"- Dependency-free local theorems: {report['summary']['dependency_free']}",
        f"- Only trivial dependencies: {report['summary']['only_trivial_dependencies']}",
        f"- Only foundational dependencies: {report['summary']['only_foundational_dependencies']}",
        f"- Arango warnings: {report['summary']['warnings']}",
        "",
    ]

    if report["warnings"]:
        lines.extend(["## Arango Warnings", ""])
        for warning in report["warnings"]:
            lines.append(f"- `{warning}`")
        lines.append("")

    lines.extend(["## Findings", ""])

    if not report["findings"]:
        lines.append("No structurally vacuous or admitted local theorems were detected.")
    else:
        for item in report["findings"]:
            deps = ", ".join(md_code(dep) for dep in item["deps"]) or "none"
            lines.extend([
                f"### {md_code(item['name'])}",
                "",
                f"- Classification: {md_code(item['classification'])}",
                f"- Dependency name count: {item['dep_name_count']}",
                f"- Dependencies: {deps}",
                "",
            ])

    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def parse_args():
    parser = argparse.ArgumentParser(
        description=(
            "Audit an ArangoDB InfoTree DAG for local theorems with vacuous, "
            "trivial-only, foundational-only, or admitted proof-dependency structure. "
            "Note: The default mode (max-depth 1) is a one-hop structural screening "
            "rather than semantic vacuity or transitive trust analysis."
        )
    )

    parser.add_argument("--url", default=os.getenv("ARANGO_URL", "http://127.0.0.1:8529"))
    parser.add_argument("--database", default=os.getenv("ARANGO_DATABASE", "infogeometry"))
    parser.add_argument("--username", default=os.getenv("ARANGO_USERNAME", "root"))
    parser.add_argument("--password", default=os.getenv("ARANGO_PASSWORD", ""))

    parser.add_argument("--node-collection", type=collection_name, default="ig_nodes")
    parser.add_argument("--edge-collection", type=collection_name, default="ig_edges")

    parser.add_argument(
        "--direction",
        choices=["OUTBOUND", "INBOUND", "ANY"],
        default="OUTBOUND",
        help=(
            "Traversal direction from theorem node to dependency node. "
            "Use INBOUND if your graph stores dependency -> theorem edges."
        ),
    )

    parser.add_argument(
        "--max-depth",
        type=positive_int,
        default=1,
        help="Maximum depth for dependency traversal.",
    )

    parser.add_argument(
        "--namespace-label",
        default="namespace:local",
        help="Node label used to restrict the audit to local/project theorems.",
    )

    parser.add_argument(
        "--edge-kind",
        action="append",
        default=[],
        help=(
            "Restrict traversal to dependency edges with this kind/type/rel/label. "
            "Repeatable. If omitted, all edges up to max-depth are considered."
        ),
    )

    parser.add_argument(
        "--ignored-target",
        action="append",
        default=[],
        help="Additional dependency target name to ignore as trivial.",
    )

    parser.add_argument("--batch-size", type=positive_int, default=1000)
    parser.add_argument("--output-json")
    parser.add_argument("--output-md")

    parser.add_argument(
        "--fail-on-findings",
        action="store_true",
        help="Exit 1 if any findings are detected.",
    )

    parser.add_argument(
        "--fail-on-warning",
        action="store_true",
        help="Ask ArangoDB to abort the AQL query on warnings.",
    )

    return parser.parse_args()


def main():
    args = parse_args()

    trivial_targets = sorted(set(TRIVIAL_TARGETS + args.ignored_target))

    query = build_query(
        node_collection=args.node_collection,
        edge_collection=args.edge_collection,
        direction=args.direction,
    )

    bind_vars = {
        "namespace_label": args.namespace_label,
        "generated_name_regex": GENERATED_NAME_REGEX,
        "trivial_targets": trivial_targets,
        "foundational_targets": FOUNDATIONAL_TARGETS,
        "suspicious_targets": SUSPICIOUS_TARGETS,
        "edge_kinds": args.edge_kind,
        "max_depth": args.max_depth,
    }

    print("[structural-audit] Querying ArangoDB for structurally vacuous/admitted local theorems...")

    try:
        results, warnings = run_aql(
            base_url=args.url,
            database=args.database,
            username=args.username,
            password=args.password,
            query=query,
            bind_vars=bind_vars,
            batch_size=args.batch_size,
            fail_on_warning=args.fail_on_warning,
        )
    except Exception as exc:
        print(f"[structural-audit] ERROR: {exc}", file=sys.stderr)
        return 2

    report = make_report(results, warnings)

    print(f"[structural-audit] Found {len(results)} findings.")

    for warning in warnings:
        print(f"[structural-audit] Arango warning: {warning}", file=sys.stderr)

    for item in results:
        print(f"- {item['name']} [{item['classification']}] deps={item['deps']}")

    if args.output_json:
        write_json(args.output_json, report)

    if args.output_md:
        write_markdown(args.output_md, report)

    if args.fail_on_findings and results:
        return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
