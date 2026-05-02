from __future__ import annotations

import json
from dataclasses import asdict

import requests

from igf.config.env_aliases import first_present_name
from igf.config.loader import load_arango_config


def run_preflight() -> dict:
    cfg = load_arango_config()
    checks = {
        "endpoint_reachable": False,
        "database_reachable": False,
        "credentials_present": bool(cfg.user and cfg.password),
        "endpoint": cfg.endpoint,
        "database": cfg.database,
        "credential_sources": {
            "user": first_present_name("ARANGO_USER", "ARANGO_USERNAME"),
            "password": first_present_name("ARANGO_PASS", "ARANGO_PASSWORD"),
        },
    }

    if not checks["credentials_present"]:
        return {"ok": False, "checks": checks, "error": "missing_credentials"}

    try:
        r = requests.get(f"{cfg.endpoint}/_api/version", timeout=15)
        checks["endpoint_reachable"] = r.ok
    except Exception as exc:
        return {"ok": False, "checks": checks, "error": f"endpoint_unreachable: {exc}"}

    try:
        r = requests.get(
            f"{cfg.endpoint}/_db/{cfg.database}/_api/version",
            auth=(cfg.user, cfg.password),
            timeout=15,
        )
        checks["database_reachable"] = r.ok
    except Exception as exc:
        return {"ok": False, "checks": checks, "error": f"database_unreachable: {exc}"}

    ok = checks["endpoint_reachable"] and checks["database_reachable"]
    return {"ok": ok, "checks": checks}


def print_preflight_json() -> int:
    result = run_preflight()
    print(json.dumps(result, ensure_ascii=False))
    return 0 if result.get("ok") else 1
