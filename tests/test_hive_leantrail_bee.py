import argparse
from pathlib import Path
import sys


REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from tools.infra import hive_leantrail_bee as lane


def _ns(**kwargs):
    defaults = {
        "hive_endpoint": "http://127.0.0.1:8540",
        "hive_database": "hive_live",
        "hive_username": "root",
        "hive_password": "alexandria_root",
        "queue_name": "proof-search",
        "worker_id": "hive-leantrail-bee-001",
        "lease_seconds": 600,
        "model_base_url": "http://127.0.0.1:8001/v1",
        "model_name": "deepseek-prover-v2-7b",
        "api_key": "***",
        "backend_kind": None,
        "backend_identity": None,
        "subscription_backed": False,
        "backend_capability": "proof_tactic_proposal",
        "hermes_role": "hive_proof_bee",
        "allow_direct_provider_api": False,
        "timeout": 120,
        "tactic_override": None,
        "task_kind": "proof.search.leantrail",
        "leansearch_num_results": 8,
        "once": True,
        "poll_interval": 1,
    }
    defaults.update(kwargs)
    return argparse.Namespace(**defaults)


def test_leantrail_lane_defaults() -> None:
    cfg = lane.config_from_args(_ns())
    assert cfg.retrieval_strategy == "leantrail"
    assert cfg.task_kind == "proof.search.leantrail"


def test_leantrail_lane_runs_one_cycle(monkeypatch) -> None:
    monkeypatch.setattr(lane, "parse_args", lambda: _ns())
    monkeypatch.setattr(lane.hive_bee, "run_one", lambda cfg: {"status": "idle", "retrieval_strategy": cfg.retrieval_strategy})

    rc = lane.main()
    assert rc == 0
