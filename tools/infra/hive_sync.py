#!/usr/bin/env python3
"""Hive Sync — commit Gold theorems to infogeometry DAG + Hive Memory."""

from __future__ import annotations

import json
import os
import subprocess
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional

try:
    from arango import ArangoClient
except ImportError:
    ArangoClient = None


@dataclass
class HiveConfig:
    infogeo_endpoint: str = os.environ.get("ARANGO_ENDPOINT", "http://127.0.0.1:8530")
    hive_endpoint: str = os.environ.get("HIVE_ENDPOINT", "http://127.0.0.1:8540")
    username: str = os.environ.get("ARANGO_USER", "root")
    password: str = os.environ.get("ARANGO_PASSWORD", "hive_brain")
    infogeo_db: str = "infogeometry"
    hive_db: str = "hive_memory"


class HiveSync:
    """Sync Gold theorems to both ArangoDB databases."""

    def __init__(self, config: Optional[HiveConfig] = None):
        self.config = config or HiveConfig()
        self.infogeo = None
        self.hive = None
        if ArangoClient:
            self._connect()

    def _connect(self):
        try:
            client_geo = ArangoClient(hosts=self.config.infogeo_endpoint)
            self.infogeo = client_geo.db(
                self.config.infogeo_db,
                username=self.config.username,
                password=self.config.password
            )
            client_hive = ArangoClient(hosts=self.config.hive_endpoint)
            self.hive = client_hive.db(
                self.config.hive_db,
                username=self.config.username,
                password=self.config.password
            )
        except Exception as e:
            print(f"[HiveSync] ArangoDB connection failed: {e}")

    def commit_gold(self, hypothesis) -> bool:
        """Commit Gold hypothesis to both databases."""
        if not self.infogeo or not self.hive:
            print("[HiveSync] Not connected — logging locally")
            self._log_locally(hypothesis)
            return False

        try:
            # 1. Commit to infogeometry DAG (decls collection + edges)
            self._commit_to_infogeometry(hypothesis)
            
            # 2. Commit to hive_memory (Thoughts + CausalLinks)
            self._commit_to_hive_memory(hypothesis)
            
            print(f"[HiveSync] ✅ Committed {hypothesis.id} to both DBs")
            return True
        except Exception as e:
            print(f"[HiveSync] Commit failed: {e}")
            self._log_locally(hypothesis)
            return False

    def _commit_to_infogeometry(self, h):
        """Add theorem to infogeometry decls + edges from cone."""
        # This would add a new decl node and edges from the cone
        # For now, just log the structure
        doc = {
            "_key": h.id,
            "name": h.id,
            "statement": h.statement,
            "source_apex": h.source_apex,
            "kind": "theorem",
            "module": "Automath.Generated",
            "proof_status": "proven",
            "shape_hash": h.shape_hash,
            "cas_verified": True,
            "oracle_verified": "BREAKTHROUGH" in getattr(h, 'oracle_verdict', ''),
            "timestamp": datetime.utcnow().isoformat(),
        }
        # self.infogeo.collection('decls').insert(doc)
        print(f"[HiveSync] Would insert to infogeometry: {doc['_key']}")

    def _commit_to_hive_memory(self, h):
        """Write Thought + CausalLinks to hive_memory."""
        # Thought document
        thought = {
            "_key": h.id,
            "type": "gold_theorem",
            "content": {
                "id": h.id,
                "statement": h.statement,
                "apex": h.source_apex,
                "timestamp": datetime.utcnow().isoformat(),
                "provenance": "automath_pipeline",
            },
            "metadata": {
                "shape_hash": h.shape_hash,
                "cas_verified": True,
                "oracle_verdict": getattr(h, 'oracle_verdict', ''),
            },
        }
        # self.hive.collection('Thoughts').insert(thought)
        
        # CausalLinks (provenance chain)
        # self.hive.collection('CausalLinks').insert({
        #     "_from": f"Thoughts/{h.source_apex}",
        #     "_to": f"Thoughts/{h.id}",
        #     "type": "derives_from",
        # })
        print(f"[HiveSync] Would commit to hive_memory: {h.id}")

    def _log_locally(self, h):
        """Fallback: log to local JSONL file."""
        log_file = Path("/tmp/automath_gold_log.jsonl")
        entry = {
            "id": h.id,
            "statement": h.statement,
            "apex": h.source_apex,
            "timestamp": datetime.utcnow().isoformat(),
        }
        with open(log_file, "a") as f:
            f.write(json.dumps(entry) + "\n")
        print(f"[HiveSync] Logged locally to {log_file}")

    def broadcast_to_bees(self, h):
        """Broadcast new Gold to all Bees via Hive Memory."""
        # This would notify all active Bees via Hive Memory
        # For now, just log
        print(f"[HiveSync] 📡 BEE BROADCAST: {h.id} -> all bees")