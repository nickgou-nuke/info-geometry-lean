"""Opaque-box 4-tier E2E verification helpers for Drive 13ED & AI Studio 1v8J epistemic compilation."""

from __future__ import annotations

import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

DEFAULT_REPORTS_DIR = REPO_ROOT / "scratch" / "epistemic_compilation_e2e" / "reports"
DEFAULT_PROBES_DIR = REPO_ROOT / "scratch" / "epistemic_compilation_e2e" / "probes"
DEFAULT_BUILD_LOCK_PATH = Path("/tmp/info-geometry-build.lock")

# Source A (Google Drive 13ED) invariants
SOURCE_A_ID = "13ED-2v91xEP9x9u84ihl07or3EchY1Pl"
SOURCE_A_REL = "cached/drive_docs/13ED-2v91xEP9x9u84ihl07or3EchY1Pl.md"
SOURCE_A_ALT_RELS = (
    "cached/drive_13ED.txt",
    "cached/aistudio_attachment_13ED-2v91xEP9x9u84ihl07or3EchY1Pl.txt",
)
SOURCE_A_BYTES = 36955
SOURCE_A_LINES = 288
SOURCE_A_SHA256 = "3e0658a30059abebe68372006d39c1d83601cb002458bbcea476a466df909fa0"

# Source B (Google AI Studio 1v8J) invariants
SOURCE_B_ID = "1v8Jj30jF2ytMHunuZq_FXEBjWcNFyw0O"
SOURCE_B_REL = "cached/aistudio_prompt_1v8Jj30jF2ytMHunuZq_FXEBjWcNFyw0O.json"
SOURCE_B_EXTRACT_DIR_REL = "cached/aistudio_extracts/aistudio_prompt_1v8Jj30jF2ytMHunuZq_FXEBjWcNFyw0O"
SOURCE_B_BASELINE45_CHUNKS = 45
SOURCE_B_BASELINE45_BYTES = 1393195
SOURCE_B_BASELINE45_SHA256 = "8ac03ba57fcd4cb65fd6df0b5d47a2c460ce967e40be20989b8efee78a90c555"
SOURCE_B_LIVE84_MIN_CHUNKS = 84
SOURCE_B_LIVE84_BYTES = 2131625
SOURCE_B_LIVE84_SHA256_PREFIX = "d56a5f"

# Additional Sources C, D, E (F10 / M1b)
SOURCE_C_ID = "12bAWYfzcbkBbfdgf1yBXXT3DYYZx1a3x"  # Google Drive file 2
SOURCE_D_ID = "1VUSK6QHOIV1jN0AbU_9oPGHY1CR78n_R"  # Google AI Studio prompt 2
SOURCE_E_ID = "1wzqgM89NscGs-oGdwK4iKBIccNqfQfJT"  # Google Drive file 3

ADDITIONAL_SOURCES = (
    {"label": "C", "id": SOURCE_C_ID, "kind": "drive", "url": f"https://drive.google.com/file/d/{SOURCE_C_ID}/view"},
    {"label": "D", "id": SOURCE_D_ID, "kind": "aistudio", "url": f"https://aistudio.google.com/app/prompts?state=%7B%22ids%22:%5B%22{SOURCE_D_ID}%22%5D"},
    {"label": "E", "id": SOURCE_E_ID, "kind": "drive", "url": f"https://drive.google.com/file/d/{SOURCE_E_ID}/view"},
)

ALL_FIVE_SOURCE_IDS = (SOURCE_A_ID, SOURCE_B_ID, SOURCE_C_ID, SOURCE_D_ID, SOURCE_E_ID)

# Exact 5-line Lean copyright header required at byte 0
REQUIRED_LEAN_COPYRIGHT_HEADER = (
    "/-\n"
    "Copyright (c) 2026 InfoGeometry Authors. All rights reserved.\n"
    "Released under Apache 2.0 license as described in the file LICENSE.\n"
    "Authors: InfoGeometry Engine Contributors\n"
    "-/\n"
)

PERMITTED_FOUNDATIONAL_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

VALID_RESULT_LABELS = (
    "[kernel_verified]",
    "[accepted_limited_scope]",
    "[bucket_2_conditional]",
    "[bucket_3_open_debt]",
    "[countermodel_found]",
    "[documentation_only]",
)

VALID_BUCKETS = ("BUCKET 1", "BUCKET 2", "BUCKET 3")

BUCKET_ALLOWED_LABELS = {
    "BUCKET 1": frozenset({"[kernel_verified]", "[accepted_limited_scope]"}),
    "BUCKET 2": frozenset({"[bucket_2_conditional]"}),
    "BUCKET 3": frozenset({"[bucket_3_open_debt]", "[countermodel_found]", "[documentation_only]"}),
}

REQUIRED_INTENT_ENVELOPE_KEYS = (
    "schema",
    "concept_id",
    "source_text",
    "intake_classification",
    "classification",
    "mathematical_domain",
    "target_status",
    "risk_level",
    "allowed_imports",
    "non_theorem_claims",
    "formal_objects",
    "acceptance_theorems",
)

FORBIDDEN_CONCURRENT_DRAFTS = (
    "InfoGeometry.OperatorAlgebra.PeirceSpine.ReciprocalTotalityAporiaPoset",
    "InfoGeometry.OperatorAlgebra.ParabolicJordanTrichotomyAndMannheimVMetric",
)

FORBIDDEN_RIEMANN_MASULLO_IMPORTS = (
    "RiemannMasullo.Ch05",
    "RiemannMasullo.Ch06",
    "RiemannMasullo.Ch07",
    "RiemannMasullo.Ch08",
    "RiemannMasullo.Ch09",
    "RiemannMasullo.Ch10",
    "RiemannMasullo.Ch11",
    "RiemannMasullo.Ch12",
    "RiemannMasullo.Challenge",
    "RiemannMasullo.Main",
)

BASELINE_COMPILATION_DOC_REL = "docs/DRIVE_13ED_AISTUDIO_1v8J_EPISTEMIC_COMPILATION.md"
BASELINE_INTENT_ENVELOPE_REL = "artifacts/qms/DRIVE-AISTUDIO-20261118-intent_envelope.json"
BASELINE_AUDIT_REPORT_REL = "artifacts/qms/DRIVE-AISTUDIO-20261118-audit_report.json"
BASELINE_QA_REPORT_REL = "artifacts/qms/DRIVE-AISTUDIO-20261118-qa_report.md"
BASELINE_SMOKE_LEAN_REL = "lean/InfoGeometry/Canonical/SouriauKillingLipschitzBridge.lean"

KNOWN_COUNTERMODEL_IDS = ("SA-18", "SB-17", "SB-35")


@dataclass
class CheckOutcome:
    """Structured result for a single Tier 1-4 check."""

    check_id: str
    tier: int
    feature: str
    status: str  # "PASS", "FAIL", "SKIP"
    summary: str
    details: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)
