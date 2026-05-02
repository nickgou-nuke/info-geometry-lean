#!/usr/bin/env python3
"""LeanSearch-backed Hive proof bee lane.

Alternative retrieval lane for Hive that keeps the same Lean verification/fossilization
pipeline but uses LeanSearch semantic retrieval instead of Arango gravity retrieval.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

try:
    from tools.infra import hive_bee
except ModuleNotFoundError:
    repo_root = Path(__file__).resolve().parents[2]
    if str(repo_root) not in sys.path:
        sys.path.insert(0, str(repo_root))
    from tools.infra import hive_bee


DEFAULT_TASK_KIND = "proof.search.leansearch"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hive-endpoint", default=hive_bee.DEFAULT_HIVE_ENDPOINT)
    parser.add_argument("--hive-database", default=hive_bee.DEFAULT_HIVE_DATABASE)
    parser.add_argument("--hive-username", default=hive_bee.DEFAULT_HIVE_USERNAME)
    parser.add_argument("--hive-password", default=hive_bee.DEFAULT_HIVE_PASSWORD)
    parser.add_argument("--queue-name", default=hive_bee.DEFAULT_QUEUE)
    parser.add_argument("--worker-id", default="hive-leansearch-bee-001")
    parser.add_argument("--lease-seconds", type=int, default=hive_bee.DEFAULT_LEASE_SECONDS)
    parser.add_argument("--model-base-url", default=hive_bee.DEFAULT_MODEL_BASE_URL)
    parser.add_argument("--model-name", default=hive_bee.DEFAULT_MODEL)
    parser.add_argument("--api-key", default=hive_bee.DEFAULT_API_KEY)
    parser.add_argument("--backend-kind", default=None)
    parser.add_argument("--backend-identity", default=None)
    parser.add_argument("--subscription-backed", action="store_true")
    parser.add_argument("--backend-capability", default=hive_bee.DEFAULT_BACKEND_CAPABILITY)
    parser.add_argument("--hermes-role", default=hive_bee.DEFAULT_HERMES_ROLE)
    parser.add_argument("--allow-direct-provider-api", action="store_true")
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--tactic-override", default=None)
    parser.add_argument("--task-kind", default=DEFAULT_TASK_KIND)
    parser.add_argument("--leansearch-base-url", default=hive_bee.DEFAULT_LEANSEARCH_BASE_URL)
    parser.add_argument("--leansearch-num-results", type=int, default=hive_bee.DEFAULT_LEANSEARCH_NUM_RESULTS)
    parser.add_argument("--once", action="store_true")
    parser.add_argument("--poll-interval", type=int, default=15)
    return parser.parse_args()


def config_from_args(args: argparse.Namespace) -> hive_bee.BeeConfig:
    backend_kind = hive_bee.infer_backend_kind(args)
    return hive_bee.BeeConfig(
        hive_endpoint=str(args.hive_endpoint).rstrip("/"),
        hive_database=str(args.hive_database),
        hive_username=str(args.hive_username),
        hive_password=str(args.hive_password),
        queue_name=str(args.queue_name),
        worker_id=str(args.worker_id),
        lease_seconds=int(args.lease_seconds),
        gravity_base_url=hive_bee.DEFAULT_GRAVITY_BASE_URL,
        gravity_database=hive_bee.DEFAULT_GRAVITY_DATABASE,
        gravity_top_k=int(hive_bee.DEFAULT_TOP_K),
        model_base_url=str(args.model_base_url).rstrip("/"),
        model_name=str(args.model_name),
        api_key=str(args.api_key),
        backend_kind=backend_kind,
        backend_identity=str(args.backend_identity or args.model_base_url).rstrip("/"),
        subscription_backed=bool(args.subscription_backed),
        backend_capability=str(args.backend_capability),
        hermes_role=str(args.hermes_role),
        allow_direct_provider_api=bool(args.allow_direct_provider_api),
        timeout=int(args.timeout),
        tactic_override=str(args.tactic_override).strip() if args.tactic_override else None,
        retrieval_strategy="leansearch",
        task_kind=str(args.task_kind),
        leansearch_base_url=str(args.leansearch_base_url).rstrip("/"),
        leansearch_num_results=max(1, int(args.leansearch_num_results)),
    )


def main() -> int:
    args = parse_args()
    config = config_from_args(args)
    while True:
        result = hive_bee.run_one(config)
        print(json.dumps(result, indent=2, ensure_ascii=False, sort_keys=True))
        if args.once:
            return 0
        time.sleep(max(1, int(args.poll_interval)))


if __name__ == "__main__":
    raise SystemExit(main())
