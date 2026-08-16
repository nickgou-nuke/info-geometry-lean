"""
Unified UTC Time utilities for IGF.
Canonical deduplicated implementation for all timestamps across telemetry and audits.
"""

from __future__ import annotations

import time
from datetime import datetime, timezone


from typing import Optional


def utc_now() -> datetime:
    """Returns the current UTC datetime."""
    return datetime.now(timezone.utc)


def utc_now_iso() -> str:
    """Returns standard ISO 8601 UTC timestamp format: YYYY-MM-DDTHH:MM:SSZ."""
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def now_iso() -> str:
    """Alias for utc_now_iso()."""
    return utc_now_iso()


def now_tag() -> str:
    """Returns compact timestamp tag format: YYYYMMDD_HHMMSS."""
    return time.strftime("%Y%m%d_%H%M%S", time.gmtime())


def today_utc() -> str:
    """Returns UTC date string: YYYY-MM-DD."""
    return time.strftime("%Y-%m-%d", time.gmtime())


def now_sec() -> float:
    """Returns current UNIX epoch timestamp in seconds."""
    return time.time()


def timestamp_utc() -> str:
    """Alias for utc_now_iso()."""
    return utc_now_iso()


def parse_iso_timestamp(iso_str: str) -> Optional[datetime]:
    """Parses an ISO 8601 timestamp string into datetime."""
    try:
        clean = iso_str.replace("Z", "+00:00")
        return datetime.fromisoformat(clean)
    except Exception:
        return None
