"""Repository paths and integrity checks for the public numerical fixtures.

Only standard-library modules are imported, so the exact interval evaluator
can use this module without NumPy or Matplotlib.
"""
from __future__ import annotations

from decimal import Decimal
import hashlib
import json
from pathlib import Path

TOOLS_DIR = Path(__file__).resolve().parent
REPO_ROOT = TOOLS_DIR.parents[1]
DATA_DIR = REPO_ROOT / "data" / "spectral_table_bridge"
DEFAULT_OUTPUT_DIR = REPO_ROOT / "artifacts" / "spectral_table_bridge"

DECIMAL_SHA = "30a4bc1781ebade1636f74fe3703faea04d5584d72b4a178cc84f4bd11e6fa6d"
ROUNDED_ORIGINAL_SHA = "882b6799b2787041c86e07b36c7fe892ee1e7807756e05273227ac73b9411754"
ROUNDED_FIXTURE_SHA = "eb8443cf5f2fd3f0e802f261465667c9725278529de72e9242b99291cf84445d"
REFERENCE_HASHES = {
    "prior_five_line_balancing_results.json":
        "10952b810563eb5c5a2bfc316fd399644a971960868951df438a72022cb1db72",
    "prior_two_line_bounds_audit.json":
        "9daea254028b0ceb811913fec8bc4c99efa617d5e8ce223eae99a08968cd517c",
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def public_path(path):
    """A repository-relative label, or a basename for an external destination."""
    path = Path(path).resolve()
    try:
        return path.relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return path.name


def read_reference(path, expected_name):
    if sha(path) != REFERENCE_HASHES[expected_name]:
        raise ValueError("numerical reference hash changed: " + expected_name)
    return json.loads(Path(path).read_text(encoding="utf-8"))


def read_rounded_fixture(path):
    """Verify the compact fixture and recover exact Decimal-valued records.

    The original text fingerprint records extraction provenance. It does not
    imply that the omitted text is available or independently re-extracted at
    runtime. The fixture bytes, schema, units, and exact conversions are checked.
    """
    if sha(path) != ROUNDED_FIXTURE_SHA:
        raise ValueError("rounded two-line fixture hash changed")
    fixture = json.loads(Path(path).read_text(encoding="utf-8"))
    if fixture["schema"] != "spectral-rounded-two-line-v1":
        raise ValueError("unsupported rounded fixture schema")
    if fixture["original_source"]["sha256"] != ROUNDED_ORIGINAL_SHA:
        raise ValueError("rounded fixture original-source fingerprint changed")
    if fixture["channel_order"] != ["352", "609"]:
        raise ValueError("unexpected rounded fixture channels")
    if [row["cartridge"] for row in fixture["records"]] != list(range(1, 10)):
        raise ValueError("expected exactly cartridges 1 through 9 in order")
    records = []
    for row in fixture["records"]:
        real = Decimal(row["real_seconds"])
        live = Decimal(row["live_seconds"])
        if real != Decimal(row["real_minutes_source"]) * 60:
            raise ValueError("real-time unit conversion changed")
        if live != Decimal(row["live_minutes_source"]) * 60:
            raise ValueError("live-time unit conversion changed")
        areas = {channel: Decimal(row["areas"][channel]) for channel in ["352", "609"]}
        if not (real >= live > 0 and all(value > 0 for value in areas.values())):
            raise ValueError("nonpositive area or inconsistent acquisition time")
        records.append({
            "cartridge": row["cartridge"], "start_time": row["start_time"],
            "real_seconds": real, "live_seconds": live,
            "elapsed_seconds": Decimal(row["elapsed_seconds"]), "areas": areas,
        })
    lam = Decimal(fixture["lambda_per_second"])
    if lam <= 0:
        raise ValueError("decay constant must be positive")
    provenance = {
        "filename": Path(path).name, "sha256": ROUNDED_FIXTURE_SHA,
        "original_source_sha256": ROUNDED_ORIGINAL_SHA,
        "schema": fixture["schema"],
        "mapping": "See data/spectral_table_bridge/PROVENANCE.json.",
    }
    return records, lam, provenance
