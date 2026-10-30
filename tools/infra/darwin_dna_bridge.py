#!/usr/bin/env python3
"""
Application-side DNA bridge: darwin_commits <-> infogeometry (port 8530).

Connects commit taxonomy in `darwin_commits` to declaration DNA in
`infogeometry` without cross-database AQL (unsupported between DBs).
Produces:
  - CommitDeclEdge relations (commit -> decl) in JSONL + optional Arango collection
  - Habitat Maps: subsystem -> {change_category: count, churn: sum}
  - explicitly coarse habitat-cohabitation resolution on CommitDeclEdge

The output is written incrementally. The current-declaration index and commit
metadata are materialized in memory, so memory use grows with those inputs.
Arango persistence is opt-in; module matches are habitat cohabitation only.
"""
from __future__ import annotations

import json
import re
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any, Dict, Iterator, List, cast

from arango.client import ArangoClient  # type: ignore
from arango.cursor import Cursor  # type: ignore
from arango.database import StandardDatabase  # type: ignore
from tools.infra.arango_env import (  # type: ignore
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)

load_repo_arango_env(Path(__file__).resolve().parents[2])

DARWIN_DB = "darwin_commits"
INFOGEO_DB = "infogeometry"
USER = arango_username()
PASS = arango_password()


def aql_stream(
    db: StandardDatabase,
    query: str,
    bind_vars: Dict[str, Any] | None = None,
    batch_size: int = 2000,
) -> Iterator[Dict[str, Any]]:
    """
    Типизирана обвивка за python-arango AQL курсори.
    Satisfies Pyright/mypy 100% without needing `# type: ignore`.
    """
    raw_cursor = db.aql.execute(
        query,
        bind_vars=bind_vars or {},
        batch_size=batch_size,
    )
    cursor = cast(Cursor, raw_cursor)
    for doc in cursor:
        yield cast(Dict[str, Any], doc)


def lean_path_to_module_and_subsystem(file_path: str) -> tuple[str, str] | None:
    """
    Convert a changed-file path from commit_nodes into
    (Lean module name, subsystem habitat).

    'lean/InfoGeometry/Graph/DarwinCommitTaxonomy.lean'
        -> ('InfoGeometry.Graph.DarwinCommitTaxonomy', 'Graph')
    'lean/InfoGeometry/Algebra/Basic.lean'
        -> ('InfoGeometry.Algebra.Basic', 'Algebra')
    """
    clean = file_path.strip().replace("\\", "/")
    if not clean.endswith(".lean"):
        return None

    clean_no_ext = clean[:-5]
    parts = [p for p in clean_no_ext.split("/") if p]

    if parts and parts[0].lower() in ("lean", "src", "lib"):
        parts = parts[1:]

    if not parts:
        return None

    module_name = ".".join(parts)

    if len(parts) >= 2 and parts[0] == "InfoGeometry":
        subsystem = parts[1]
    elif len(parts) >= 2:
        subsystem = parts[0]
    else:
        subsystem = "Root"

    return module_name, subsystem


class DarwinInfoGeometryBridge:
    def __init__(
        self,
        darwin_host: str = "http://localhost:8530",
        infogeo_host: str = "http://localhost:8530",
        darwin_db_name: str = DARWIN_DB,
        infogeo_db_name: str = INFOGEO_DB,
        username: str = USER,
        password: str = PASS,
    ):
        self.darwin_client = ArangoClient(hosts=darwin_host)
        self.infogeo_client = ArangoClient(hosts=infogeo_host)
        self.darwin_db = self.darwin_client.db(
            darwin_db_name, username=username, password=password
        )
        self.infogeo_db = self.infogeo_client.db(
            infogeo_db_name, username=username, password=password
        )

    def load_infogeometry_decl_index(
        self,
    ) -> Dict[str, List[Dict[str, Any]]]:
        """
        Load compact index {module_name -> [{_key, name, kind, line, file}]} from infogeometry.decls.
        """
        module_to_decls: Dict[str, List[Dict[str, Any]]] = defaultdict(list)

        aql = """
        FOR d IN decls
            FILTER d.module != null
            RETURN {
                _key: d._key, name: d.name, module: d.module,
                kind: d.kind, line: d.line, file: d.file,
                typeFingerprint: d.typeFingerprint,
                valueFingerprint: d.valueFingerprint,
                canonicalTypeHash: d.canonicalTypeHash,
                canonicalValueHash: d.canonicalValueHash
            }
        """
        for decl in aql_stream(self.infogeo_db, aql, batch_size=5000):
            module_to_decls[decl["module"]].append(decl)

        return module_to_decls

    def build_commit_decl_courtship_stream(
        self,
        output_jsonl: str = "commit_decl_edges.jsonl",
        persist_to_darwin_collection: bool = False,
    ) -> Dict[str, int]:
        """
        Stream commit_nodes from darwin_commits, resolve module paths to Lean
        modules, find matching decls in infogeometry.decls, and write
        CommitDeclEdge relations (commit -> decl) to JSONL and optionally
        to the `commit_decl_edges` collection in darwin_commits.

        Module paths establish habitat cohabitation only. Exact declaration
        edits require historical declaration spans and diff-hunk overlap,
        neither of which is available from this module-level join.
        """
        module_to_decls = self.load_infogeometry_decl_index()

        if persist_to_darwin_collection:
            if self.darwin_db.has_collection("commit_decl_edges"):
                existing = self.darwin_db.collection("commit_decl_edges")
                # Cross-database edge references are unavailable; refuse to
                # delete/replace an existing edge collection implicitly.
                try:
                    props = existing.properties()
                    coll_type = props.get("type", 2) if isinstance(props, dict) else 2
                except Exception:
                    coll_type = 2
                if coll_type == 3:
                    raise RuntimeError(
                        "commit_decl_edges is an edge collection; refusing to "
                        "delete it automatically. Export JSONL or perform an "
                        "explicit, separately reviewed migration."
                    )
            else:
                self.darwin_db.create_collection("commit_decl_edges")

        bridge_col = (
            self.darwin_db.collection("commit_decl_edges")
            if persist_to_darwin_collection
            else None
        )

        aql = """
        FOR cn IN commit_nodes
            FILTER LENGTH(cn.modulePaths) > 0
            LET ec = DOCUMENT(CONCAT('evo_commits/', cn._key))
            RETURN {
                commit_key: cn._key, changeLabels: cn.changeLabels,
                modulePaths: cn.modulePaths,
                churn: ec == null OR ec.diff_stats_status == 'not_collected' OR
                    !IS_NUMBER(ec.insertions) OR !IS_NUMBER(ec.deletions)
                    ? null : ec.insertions + ec.deletions
            }
        """
        cursor = aql_stream(self.darwin_db, aql, batch_size=2000)
        # Materialize all commit docs up front so the Arango cursor doesn't
        # expire while we make per-commit `git show` calls below.
        commit_docs = list(cursor)

        commits_matched = 0
        edges_created = 0
        batch_buffer: List[Dict[str, Any]] = []

        with open(output_jsonl, "w", encoding="utf-8", buffering=1024 * 128) as fout:
            for cn in commit_docs:
                c_key = cn["commit_key"]
                matched_this_commit = False

                for raw_path in cn.get("modulePaths") or []:
                    parsed = lean_path_to_module_and_subsystem(raw_path)
                    if not parsed:
                        continue
                    module_name, subsystem = parsed

                    decls_in_mod = module_to_decls.get(module_name, [])
                    if not decls_in_mod:
                        continue

                    matched_this_commit = True
                    module_decl_count = len(decls_in_mod)
                    per_decl_churn = (cn["churn"] / module_decl_count
                                      if cn.get("churn") is not None and module_decl_count else None)
                    for d in decls_in_mod:
                        edge_doc = {
                            "_key": f"{c_key}__{d['_key']}",
                            "commitHash": c_key,
                            "declKey": d["_key"],
                            "declName": d["name"],
                            "declKind": d.get("kind"),
                            "declLine": d.get("line"),
                            "declFile": d.get("file"),
                            "typeFingerprint": d.get("typeFingerprint"),
                            "valueFingerprint": d.get("valueFingerprint"),
                            "canonicalTypeHash": d.get("canonicalTypeHash"),
                            "canonicalValueHash": d.get("canonicalValueHash"),
                            "moduleName": module_name,
                            "subsystem": subsystem,
                            "changeLabels": cn.get("changeLabels", []),
                            "resolution": "habitat_cohabitation",
                            "exact_match": False,
                            "module_decl_count": module_decl_count,
                            "habitat_churn_share_estimate": per_decl_churn,
                        }
                        fout.write(json.dumps(edge_doc, ensure_ascii=False) + "\n")
                        edges_created += 1

                        if bridge_col is not None:
                            batch_buffer.append(edge_doc)
                            if len(batch_buffer) >= 2000:
                                bridge_col.import_bulk(
                                    batch_buffer, on_duplicate="replace"
                                )
                                batch_buffer.clear()

                if matched_this_commit:
                    commits_matched += 1

            if bridge_col is not None and batch_buffer:
                bridge_col.import_bulk(batch_buffer, on_duplicate="replace")

        return {
            "indexed_infogeometry_modules": len(module_to_decls),
            "commits_with_dna_presence": commits_matched,
            "commit_decl_edges_created": edges_created,
        }

    def compute_habitat_map(self) -> Dict[str, Dict[str, Any]]:
        """
        Join commit_nodes, evo_commits, evo_labels from darwin_commits and
        aggregate by subsystem (habitat):
          subsystem -> {
              "total_churn": sum(insertions + deletions),
              "commits_touched": count,
              "category_distribution": {change_category: count},
              "dominant_category": top_category
          }
        """
        aql = """
        FOR c IN evo_commits
            LET cn = DOCUMENT(CONCAT('commit_nodes/', c.sha))
            LET lbl_doc = DOCUMENT(CONCAT('evo_labels/', c.sha))
            LET category_list = lbl_doc != null
                ? (lbl_doc.labels != null
                    ? lbl_doc.labels[*].category
                    : (lbl_doc.category != null ? [lbl_doc.category] :
                       (lbl_doc.species != null ? [lbl_doc.species] : [])))
                : []
            RETURN {
                commit_key: c._key,
                sha: c.sha,
                subject: c.subject,
                churn: c.diff_stats_status == 'not_collected' OR
                    !IS_NUMBER(c.insertions) OR !IS_NUMBER(c.deletions)
                    ? null : c.insertions + c.deletions,
                categories: category_list,
                modulePaths: cn != null ? cn.modulePaths : []
            }
        """
        cursor = aql_stream(self.darwin_db, aql, batch_size=2000)

        habitats: Dict[str, Dict[str, Any]] = defaultdict(
            lambda: {
                "total_churn": 0,
                "observed_churn_commits": 0,
                "unknown_churn_commits": 0,
                "commits_touched": 0,
                "category_counts": defaultdict(int),
            }
        )

        scope_regex = re.compile(r"^[a-zA-Z]+\(([^)]+)\):")

        for row in cursor:
            subsystems_in_commit: set[str] = set()

            for path in row.get("modulePaths") or []:
                parsed = lean_path_to_module_and_subsystem(path)
                if parsed:
                    _, subsys = parsed
                    subsystems_in_commit.add(subsys)

            if not subsystems_in_commit and row.get("subject"):
                m = scope_regex.match(row["subject"].strip())
                if m:
                    subsystems_in_commit.add(m.group(1))
                else:
                    subsystems_in_commit.add("General")

            category_values = row.get("categories") or []
            if isinstance(category_values, str):  # legacy flat documents
                category_values = [category_values]
            churn = row.get("churn")

            for subsys in subsystems_in_commit:
                h = habitats[subsys]
                if churn is None:
                    h["unknown_churn_commits"] += 1
                else:
                    h["total_churn"] += churn
                    h["observed_churn_commits"] += 1
                h["commits_touched"] += 1
                for category in set(category_values):
                    h["category_counts"][category] += 1

        result: Dict[str, Dict[str, Any]] = {}
        for subsys, data in sorted(
            habitats.items(), key=lambda kv: kv[1]["total_churn"], reverse=True
        ):
            sorted_categories = dict(
                sorted(
                    data["category_counts"].items(), key=lambda kv: kv[1], reverse=True
                )
            )
            dominant = next(iter(sorted_categories.keys()), None)
            result[subsys] = {
                "commits_touched": data["commits_touched"],
                "total_churn": data["total_churn"] if data["observed_churn_commits"] else None,
                "observed_churn_commits": data["observed_churn_commits"],
                "unknown_churn_commits": data["unknown_churn_commits"],
                "dominant_category": dominant,
                "categories": sorted_categories,
            }

        return result


def main() -> int:
    import argparse

    parser = argparse.ArgumentParser(description="Darwin DNA bridge to infogeometry")
    parser.add_argument(
        "--build-edges",
        action="store_true",
        help="Build commit_decl_edges JSONL + optional Arango collection",
    )
    parser.add_argument(
        "--output-jsonl",
        default="commit_decl_edges.jsonl",
        help="Output JSONL path for commit->decl edges",
    )
    parser.add_argument(
        "--no-persist",
        action="store_true",
        help="Deprecated compatibility flag; persistence is disabled by default",
    )
    parser.add_argument(
        "--persist",
        action="store_true",
        help="Explicitly upsert habitat-cohabitation edges into Arango",
    )
    parser.add_argument(
        "--habitat-map",
        action="store_true",
        help="Compute and print habitat map (subsystem -> change categories + churn)",
    )
    args = parser.parse_args()

    bridge = DarwinInfoGeometryBridge()

    if args.build_edges:
        result = bridge.build_commit_decl_courtship_stream(
            output_jsonl=args.output_jsonl,
            persist_to_darwin_collection=args.persist and not args.no_persist,
        )
        print(
            f"[dna_bridge] {result['indexed_infogeometry_modules']} infogeometry modules indexed; "
            f"{result['commits_with_dna_presence']} commits with DNA presence; "
            f"{result['commit_decl_edges_created']} commit_decl_edges created",
            file=sys.stderr,
        )

    if args.habitat_map:
        habitat = bridge.compute_habitat_map()
        print("[dna_bridge] Habitat map (subsystem -> change categories + churn):")
        for subsys, data in habitat.items():
            print(f"  {subsys}: commits={data['commits_touched']}, "
                  f"churn={data['total_churn']}, dominant={data['dominant_category']}")
            for category, cnt in list(data["categories"].items())[:5]:
                print(f"    {category}: {cnt}")

    if not args.build_edges and not args.habitat_map:
        parser.print_help()
        return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
