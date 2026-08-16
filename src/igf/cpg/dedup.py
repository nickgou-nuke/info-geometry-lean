"""
AST AQL Hash-Based Deduplication and Equivalence Clustering Engine for IGF.
Discovers exact and structural AST equivalence classes via ArangoDB graph queries.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from collections import defaultdict
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

if __package__ in (None, ""):
    _REPO_ROOT = Path(__file__).resolve().parents[3]
    sys.path.insert(0, str(_REPO_ROOT / "src"))
    sys.path.insert(0, str(_REPO_ROOT))

from igf.common.hashing import stable_hash
from igf.common.json_io import dump_json, write_jsonl
from igf.common.time_utils import utc_now_iso
from igf.config import arango_database, arango_endpoint, arango_password, arango_username, load_repo_arango_env


@dataclass
class EquivalenceCluster:
    cluster_id: str
    cluster_type: str  # "file_exact", "function_exact", "function_shape", "class_shape"
    hash_value: str
    item_name: str
    cardinality: int
    occurrences: list[dict[str, Any]]
    recommended_target: str = ""


class ArangoCPGDeduplicator:
    """Discovers AST shape, de Bruijn alpha, and exact clones across the codebase using ArangoDB AQL."""

    def __init__(self, endpoint: Optional[str] = None, db_name: Optional[str] = None):
        load_repo_arango_env()
        self.endpoint = endpoint or arango_endpoint()
        self.db_name = db_name or arango_database()
        self.username = arango_username()
        self.password = arango_password()
        self.db = None
        self._connect()

    def _connect(self) -> None:
        try:
            from arango import ArangoClient
            client = ArangoClient(hosts=self.endpoint)
            self.db = client.db(self.db_name, username=self.username, password=self.password)
        except Exception as e:
            print(f"[cpg-dedup] ArangoDB connection error: {e}")
            self.db = None

    def find_exact_file_duplicates(self) -> list[EquivalenceCluster]:
        """Finds identical files with matching full module hashes."""
        if not self.db:
            return []
        q = """
        FOR m IN python_modules
          FILTER m.file != null
          COLLECT hash = m.module_hash INTO group = {file: m.file, lines: m.num_lines}
          LET count = LENGTH(group)
          FILTER count > 1
          SORT count DESC
          RETURN {
            hash: hash,
            count: count,
            occurrences: group
          }
        """
        clusters = []
        for r in self.db.aql.execute(q):
            clusters.append(EquivalenceCluster(
                cluster_id=f"file_exact_{r['hash']}",
                cluster_type="file_exact",
                hash_value=r["hash"],
                item_name="<module>",
                cardinality=r["count"],
                occurrences=r["occurrences"],
            ))
        return clusters

    def find_function_shape_clusters(self, min_count: int = 3, limit: int = 100) -> list[EquivalenceCluster]:
        """Finds FunctionDef clusters with identical AST structural shape hash (pi_shape)."""
        if not self.db:
            return []
        q = f"""
        FOR n IN python_ast_nodes
          FILTER n.node_type == 'FunctionDef' AND n.shape_hash != null
          COLLECT shape = n.shape_hash INTO group = {{
            file: n.file,
            name: n.name,
            lineno: n.lineno,
            exact_hash: n.exact_hash
          }}
          LET count = LENGTH(group)
          FILTER count >= {min_count}
          SORT count DESC
          LIMIT {limit}
          RETURN {{
            shape_hash: shape,
            count: count,
            names: UNIQUE(group[*].name),
            exact_hashes: UNIQUE(group[*].exact_hash),
            occurrences: group
          }}
        """
        clusters = []
        for r in self.db.aql.execute(q):
            primary_name = r["names"][0] if r["names"] else "<anonymous>"
            clusters.append(EquivalenceCluster(
                cluster_id=f"fn_shape_{r['shape_hash']}",
                cluster_type="function_shape",
                hash_value=r["shape_hash"],
                item_name=primary_name,
                cardinality=r["count"],
                occurrences=r["occurrences"],
            ))
        return clusters

    def find_function_exact_clones(self, min_count: int = 2, limit: int = 100) -> list[EquivalenceCluster]:
        """Finds FunctionDef instances with identical exact code body hash."""
        if not self.db:
            return []
        q = f"""
        FOR n IN python_ast_nodes
          FILTER n.node_type == 'FunctionDef' AND n.exact_hash != null
          COLLECT exact = n.exact_hash INTO group = {{
            file: n.file,
            name: n.name,
            lineno: n.lineno,
            shape_hash: n.shape_hash
          }}
          LET count = LENGTH(group)
          FILTER count >= {min_count}
          SORT count DESC
          LIMIT {limit}
          RETURN {{
            exact_hash: exact,
            count: count,
            names: UNIQUE(group[*].name),
            occurrences: group
          }}
        """
        clusters = []
        for r in self.db.aql.execute(q):
            primary_name = r["names"][0] if r["names"] else "<fn>"
            clusters.append(EquivalenceCluster(
                cluster_id=f"fn_exact_{r['exact_hash']}",
                cluster_type="function_exact",
                hash_value=r["exact_hash"],
                item_name=primary_name,
                cardinality=r["count"],
                occurrences=r["occurrences"],
            ))
        return clusters

    def generate_deduplication_manifest(self, out_json: Path = Path("reports/cpg_dedup_report.json")) -> dict[str, Any]:
        """Runs the complete AQL AST deduplication analysis and emits the telemetry manifest."""
        t0 = time.time()
        file_exact = self.find_exact_file_duplicates()
        fn_exact = self.find_function_exact_clones(min_count=2, limit=150)
        fn_shape = self.find_function_shape_clusters(min_count=3, limit=150)
        elapsed = time.time() - t0

        manifest = {
            "schema": "ig.cpg-dedup-report.v1",
            "timestamp_utc": utc_now_iso(),
            "elapsed_seconds": round(elapsed, 4),
            "summary": {
                "exact_file_duplicate_clusters": len(file_exact),
                "exact_function_clone_clusters": len(fn_exact),
                "structural_function_shape_clusters": len(fn_shape),
                "total_duplicated_functions": sum(c.cardinality for c in fn_exact),
            },
            "file_exact_clusters": [asdict(c) for c in file_exact],
            "function_exact_clones": [asdict(c) for c in fn_exact],
            "function_shape_clusters": [asdict(c) for c in fn_shape],
        }

        out_json.parent.mkdir(parents=True, exist_ok=True)
        dump_json(out_json, manifest)
        print(f"[cpg-dedup] Generated deduplication manifest with {len(fn_exact)} exact clone clusters and {len(fn_shape)} shape clusters in {elapsed:.2f}s.")
        return manifest
