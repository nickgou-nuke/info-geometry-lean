"""
AST AQL Hash-Based Deduplication and Equivalence Clustering Engine for IGF.
Discovers exact and structural AST equivalence classes via ArangoDB graph queries.
"""

from __future__ import annotations

import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Optional

if __package__ in (None, ""):
    _REPO_ROOT = Path(__file__).resolve().parents[3]
    sys.path.insert(0, str(_REPO_ROOT / "src"))
    sys.path.insert(0, str(_REPO_ROOT))

from igf.graph.arango_http import ArangoHttpTarget, execute_aql
from igf.common.json_io import dump_json
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
        # Connection/query failures propagate when the common HTTP helper executes.
        self.db = ArangoHttpTarget(self.endpoint, self.db_name, self.username, self.password)

    def _query(self, query: str, bind_vars: dict[str, Any] | None = None) -> list[Any]:
        if self.db is None:
            raise RuntimeError("Arango target unavailable")
        return execute_aql(self.db, query, bind_vars)

    def find_exact_file_duplicates(self, min_count: int = 2, limit: int = 100) -> list[EquivalenceCluster]:
        """Finds identical files with matching full module hashes."""
        if min_count < 2 or limit < 1:
            raise ValueError("min_count must be >= 2 and limit must be positive")
        q = """
        FOR m IN python_modules
          FILTER m.file != null AND IS_STRING(m.module_hash) AND m.module_hash != ""
          COLLECT hash = m.module_hash INTO group = {file: m.file, lines: m.num_lines}
          LET count = LENGTH(group)
          FILTER count >= @min_count
          SORT count DESC, hash ASC
          LIMIT @limit
          RETURN {
            hash: hash,
            count: count,
            occurrences: group
          }
        """
        clusters = []
        for r in self._query(q, {"min_count": min_count, "limit": limit}):
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
        if min_count < 2 or limit < 1:
            raise ValueError("min_count must be >= 2 and limit must be positive")
        q = f"""
        FOR n IN python_ast_nodes
          FILTER n.node_type == 'FunctionDef' AND IS_STRING(n.shape_hash) AND n.shape_hash != ''
          COLLECT shape = n.shape_hash INTO group = {{
            file: n.file,
            name: n.name,
            lineno: n.lineno,
            exact_hash: n.exact_hash
          }}
          LET count = LENGTH(group)
          FILTER count >= @min_count
          SORT count DESC, shape ASC
          LIMIT @limit
          RETURN {{
            shape_hash: shape,
            count: count,
            names: UNIQUE(group[*].name),
            exact_hashes: UNIQUE(group[*].exact_hash),
            occurrences: group
          }}
        """
        clusters = []
        for r in self._query(q, {"min_count": min_count, "limit": limit}):
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
        if min_count < 2 or limit < 1:
            raise ValueError("min_count must be >= 2 and limit must be positive")
        q = f"""
        FOR n IN python_ast_nodes
          FILTER n.node_type == 'FunctionDef' AND IS_STRING(n.exact_hash) AND n.exact_hash != ''
          COLLECT exact = n.exact_hash INTO group = {{
            file: n.file,
            name: n.name,
            lineno: n.lineno,
            shape_hash: n.shape_hash
          }}
          LET count = LENGTH(group)
          FILTER count >= @min_count
          SORT count DESC, exact ASC
          LIMIT @limit
          RETURN {{
            exact_hash: exact,
            count: count,
            names: UNIQUE(group[*].name),
            occurrences: group
          }}
        """
        clusters = []
        for r in self._query(q, {"min_count": min_count, "limit": limit}):
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

    def generate_deduplication_manifest(self, out_json: Path = Path("reports/cpg_dedup_report.json"), *, min_count: int = 2, limit: int = 100) -> dict[str, Any]:
        """Runs the complete AQL AST deduplication analysis and emits the telemetry manifest."""
        t0 = time.time()
        file_exact = self.find_exact_file_duplicates(min_count=min_count, limit=limit)
        fn_exact = self.find_function_exact_clones(min_count=min_count, limit=limit)
        fn_shape = self.find_function_shape_clusters(min_count=min_count, limit=limit)
        elapsed = time.time() - t0

        manifest = {
            "schema": "ig.cpg-dedup-report.v2",
            "evidence_class": "heuristic_hash_candidates_not_semantic_verdict",
            "parameters": {"min_count": min_count, "limit": limit},
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
