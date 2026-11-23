#!/usr/bin/env python3
"""Opaque-box 4-tier E2E runner for the Real Polarized Z/2-Graded Operator Algebra Framework."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
SUITE_DIR = REPO_ROOT / "tests" / "polarized_z2_e2e"
LEAN_SRC_ROOT = REPO_ROOT / "lean"
OLEAN_ROOT = REPO_ROOT / ".lake" / "build" / "lib" / "lean"
BUILD_LOCK_PATH = Path("/tmp/info-geometry-build.lock")
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.quality.audit_constructivity import strip_comments
from tools.quality.proof_proxy_staged_gate import (
    REQUIRED_LEAN_COPYRIGHT_HEADER,
    aggregate_prop_constructors,
)

TIER_EXPECTED_FILES: dict[str, list[str]] = {
    "1": ["Tier1_R1.lean", "Tier1_R2.lean", "Tier1_R3.lean", "Tier1_R4.lean"],
    "2": ["Tier2_R1.lean", "Tier2_R2.lean", "Tier2_R3.lean", "Tier2_R4.lean"],
    "3": ["Tier3_CrossFeature.lean"],
    "4": ["Tier4_Applications.lean"],
}

TIER_FILE_THRESHOLDS: dict[str, dict[str, Any]] = {
    "Tier1_R1.lean": {"kind": "per_feature", "prefix_fmt": "t1_f{n}_", "features": [1, 2, 3, 4, 5], "min_each": 5},
    "Tier1_R2.lean": {"kind": "per_feature", "prefix_fmt": "t1_f{n}_", "features": [6, 7, 8], "min_each": 5},
    "Tier1_R3.lean": {"kind": "per_feature", "prefix_fmt": "t1_f{n}_", "features": [9, 10, 11, 12], "min_each": 5},
    "Tier1_R4.lean": {"kind": "per_feature", "prefix_fmt": "t1_f{n}_", "features": [13, 14, 15, 16], "min_each": 5},
    "Tier2_R1.lean": {"kind": "per_feature", "prefix_fmt": "t2_f{n}_", "features": [1, 2, 3, 4, 5], "min_each": 5},
    "Tier2_R2.lean": {"kind": "per_feature", "prefix_fmt": "t2_f{n}_", "features": [6, 7, 8], "min_each": 5},
    "Tier2_R3.lean": {"kind": "per_feature", "prefix_fmt": "t2_f{n}_", "features": [9, 10, 11, 12], "min_each": 5},
    "Tier2_R4.lean": {"kind": "per_feature", "prefix_fmt": "t2_f{n}_", "features": [13, 14, 15, 16], "min_each": 5},
    "Tier3_CrossFeature.lean": {"kind": "total_prefix", "prefix": "t3_", "min_total": 16},
    "Tier4_Applications.lean": {"kind": "total_prefix", "prefix": "t4_", "min_total": 8},
}

EXTENDED_OWNER_CONTRACTS: dict[str, list[str]] = {
    "InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport": [
        "graded_split_flat_cartan_equations",
        "SolderingOneForm",
        "gaugeForm_product_general_separation",
    ],
    "InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv": [
        "cliffordTensorEquivMatrix",
    ],
    "InfoGeometry.Core.OperatorCliffordDouble": [
        "blockMatrixAlgEquiv",
    ],
    "InfoGeometry.Canonical.BostConnesColimitKMSBridge": [
        "CliffordTowerKMSBridgeSystem",
    ],
}

PEIRCE_SPECTRAL_MODULE_PAIR = (
    "InfoGeometry.NCG.OppositePeirceRealMetric",
    "InfoGeometry.NCG.PeirceProjectorSpectralBounds",
)
PEIRCE_SPECTRAL_CONTRACTS: list[str] = [
    "indefinite_vs_positive_adjoint_blocks",
    "orthogonalProjector_F_sq_le_quarter",
    "orthogonalProjector_one_sub_F_sq_ge_three_quarters",
    "unilateral_nilpotent_F_sq_zero",
    "hyperbolicPlane_kreinSelfAdjoint_sq_neg_one",
]

BASELINE_STASH_ANCHOR = "pre-fold-main-working-tree-20261123"
BASELINE_STASH_ALLOWED = {
    "On (no branch): pre-fold-main-working-tree-20261123",
    "On main: WIP before PR 323-356 integration sweep",
    "WIP on hermes/raw-infotree-stabilization: 8258b7889 infra: add RawInfoTree-ExprArango bridge validator",
    "filter-branch: rewrite",
}
BASELINE_STASH_MAX_COUNT = 4

PR426_FILE = "lean/InfoGeometry/Canonical/ConnesSpectralTripleBridge.lean"
PR426_BASELINE_HASH = "112305a7a88aa1109b970c5525b073a27bbadee9"

CLEAN_PROTECTED_FILES = [
    PR426_FILE,
    "lakefile.lean",
    "lean-toolchain",
    "lake-manifest.json",
]

PRESERVED_BASELINE_BLOBS: dict[str, str] = {
    "PREREQUISITES.md": "e2a945a8b2994e356397899041dfa9de51f4adf1",
    "lean/InfoGeometry/Clifford/All.lean": "9fa8ae879704987893ef560fc89d3860af1f2df6",
    "lean/InfoGeometry/Canonical/RealDoubledChiralKreinBridge.lean": "651cc3d2fd5fedeb94ca132070f46fb901105c77",
}

DECL_RE = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]]*\]\s*)*(?:(?P<priv>private)\s+)?"
    r"(?:(?:protected|noncomputable)\s+)*(?:theorem|lemma)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.«»]*)\b"
)
E2E_AUDIT_SECTION_RE = re.compile(
    r"(?ms)^[ \t]*section\s+E2EAxiomAudit\b.*?^[ \t]*end\s+E2EAxiomAudit\b"
)


@dataclass
class CheckResult:
    name: str
    tier: str
    file: str | None
    status: str  # PASS | FAIL | PENDING_IMPL | SKIPPED
    duration_s: float
    summary: str
    details: dict[str, Any] = field(default_factory=dict)


def _run(cmd: list[str], timeout: int = 120) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=timeout,
        check=False,
    )


def _rel_posix(path: Path) -> str:
    return path.resolve().relative_to(REPO_ROOT.resolve()).as_posix()


def _extract_leading_json_list(stdout: str) -> list[dict[str, Any]]:
    decoder = json.JSONDecoder()
    pos = 0
    while True:
        idx = stdout.find("[", pos)
        if idx == -1:
            break
        try:
            data, _ = decoder.raw_decode(stdout, idx)
        except json.JSONDecodeError:
            pos = idx + 1
            continue
        if isinstance(data, list) and all(isinstance(item, dict) for item in data):
            return data
        pos = idx + 1
    raise ValueError(f"Could not locate JSON list in stdout: {stdout[:300]!r}")


def _parse_imports(path: Path) -> list[str]:
    """Parse Lean header imports using comment-stripped lines."""
    found: list[str] = []
    seen: set[str] = set()
    depth = 0
    with path.open(encoding="utf-8") as handle:
        for line in handle:
            visible: list[str] = []
            for token in re.split(r"(/-|-/|--)", line):
                if token == "/-":
                    depth += 1
                elif token == "-/" and depth:
                    depth -= 1
                elif token == "--" and not depth:
                    break
                elif not depth:
                    visible.append(token)
            stripped = "".join(visible).strip()
            if not stripped or stripped in {"module", "prelude"}:
                continue
            match = re.fullmatch(r"(?:(?:public|private)\s+)?import\s+(.+)", stripped)
            if not match:
                break
            for raw_mod in match.group(1).split():
                mod = raw_mod.replace("«", "").replace("»", "")
                if mod not in seen:
                    seen.add(mod)
                    found.append(mod)
    return found


def _module_to_lean(mod: str) -> Path:
    return LEAN_SRC_ROOT.joinpath(*mod.split(".")).with_suffix(".lean")


def _module_to_olean(mod: str) -> Path:
    return OLEAN_ROOT.joinpath(*mod.split(".")).with_suffix(".olean")


def _symbol_declared_in_source(source: str, symbol: str) -> bool:
    cleaned = strip_comments(source, strip_strings=True, strip_quoted_identifiers=False)
    pattern = re.compile(
        rf"\b(?:theorem|lemma|def|abbrev|structure|class|inductive|opaque|instance)\s+(?:[^\n]*\.)?(?:«)?{re.escape(symbol)}(?:»)?\b"
    )
    if pattern.search(cleaned):
        return True
    return re.search(rf"\b{re.escape(symbol)}\b", cleaned) is not None


def _check_module_readiness(imports: list[str]) -> dict[str, Any]:
    info_mods = [m for m in imports if m == "InfoGeometry" or m.startswith("InfoGeometry.")]
    missing_lean: list[str] = []
    missing_olean: list[str] = []
    missing_contracts: dict[str, list[str]] = {}
    ready_modules: list[str] = []

    for mod in info_mods:
        lean_file = _module_to_lean(mod)
        olean_file = _module_to_olean(mod)
        mod_ok = True
        if not lean_file.is_file():
            missing_lean.append(mod)
            mod_ok = False
        if not olean_file.is_file():
            missing_olean.append(mod)
            mod_ok = False

        if lean_file.is_file() and mod in EXTENDED_OWNER_CONTRACTS:
            src = lean_file.read_text(encoding="utf-8")
            absent = [sym for sym in EXTENDED_OWNER_CONTRACTS[mod] if not _symbol_declared_in_source(src, sym)]
            if absent:
                missing_contracts[mod] = absent
                mod_ok = False

        if mod in PEIRCE_SPECTRAL_MODULE_PAIR:
            pair_sources: list[str] = []
            for pair_mod in PEIRCE_SPECTRAL_MODULE_PAIR:
                pair_file = _module_to_lean(pair_mod)
                if pair_file.is_file():
                    pair_sources.append(pair_file.read_text(encoding="utf-8"))
            combined = "\n".join(pair_sources)
            absent = [sym for sym in PEIRCE_SPECTRAL_CONTRACTS if not _symbol_declared_in_source(combined, sym)]
            if absent:
                missing_contracts[mod] = absent
                mod_ok = False

        if mod_ok:
            ready_modules.append(mod)

    is_ready = not (missing_lean or missing_olean or missing_contracts)
    return {
        "info_geometry_imports": info_mods,
        "ready_modules": ready_modules,
        "missing_lean": missing_lean,
        "missing_olean": missing_olean,
        "missing_contracts": missing_contracts,
        "is_ready": is_ready,
    }


def _file_tier(filename: str) -> str:
    for tier in ("1", "2", "3", "4"):
        if filename.startswith(f"Tier{tier}_"):
            return tier
    return "infra"


def _discover_targets(selected_tier: str, allow_pending_impl: bool) -> tuple[list[Path], list[CheckResult]]:
    tiers = ["1", "2", "3", "4"] if selected_tier == "all" else [selected_tier]
    discovered: list[Path] = []
    seen: set[Path] = set()
    presence_checks: list[CheckResult] = []

    for tier in tiers:
        for fname in TIER_EXPECTED_FILES[tier]:
            path = SUITE_DIR / fname
            if path.is_file():
                discovered.append(path)
                seen.add(path.resolve())
            else:
                status = "PENDING_IMPL" if allow_pending_impl else "FAIL"
                presence_checks.append(
                    CheckResult(
                        name="tier_file_presence",
                        tier=tier,
                        file=f"tests/polarized_z2_e2e/{fname}",
                        status=status,
                        duration_s=0.0,
                        summary=f"Missing expected tier file tests/polarized_z2_e2e/{fname}",
                        details={"expected_file": f"tests/polarized_z2_e2e/{fname}"},
                    )
                )
        for extra in sorted(SUITE_DIR.glob(f"Tier{tier}_*.lean")):
            if extra.resolve() not in seen:
                discovered.append(extra)
                seen.add(extra.resolve())

    helper = SUITE_DIR / "AxiomAuditHelper.lean"
    if helper.is_file():
        if helper.resolve() not in seen:
            discovered.append(helper)
            seen.add(helper.resolve())
    else:
        presence_checks.append(
            CheckResult(
                name="tier_file_presence",
                tier="infra",
                file="tests/polarized_z2_e2e/AxiomAuditHelper.lean",
                status="FAIL",
                duration_s=0.0,
                summary="Missing required helper tests/polarized_z2_e2e/AxiomAuditHelper.lean",
                details={"expected_file": "tests/polarized_z2_e2e/AxiomAuditHelper.lean"},
            )
        )

    return discovered, presence_checks


def run_hygiene_checks() -> list[CheckResult]:
    """F17 repository, branch, stash, and baseline-preservation checks."""
    checks: list[CheckResult] = []
    t0 = time.monotonic()

    # 1. Current branch is main
    branch_proc = _run(["git", "rev-parse", "--abbrev-ref", "HEAD"], timeout=30)
    current_branch = branch_proc.stdout.strip()
    checks.append(
        CheckResult(
            name="f17_current_branch_main",
            tier="hygiene",
            file=None,
            status="PASS" if (branch_proc.returncode == 0 and current_branch == "main") else "FAIL",
            duration_s=round(time.monotonic() - t0, 3),
            summary=f"HEAD branch={current_branch!r}",
            details={"branch": current_branch, "stderr": branch_proc.stderr.strip()},
        )
    )

    # 2. No extra local branches
    t1 = time.monotonic()
    refs_proc = _run(["git", "for-each-ref", "--format=%(refname:short)", "refs/heads"], timeout=30)
    branches = [ln.strip() for ln in refs_proc.stdout.splitlines() if ln.strip()]
    checks.append(
        CheckResult(
            name="f17_no_extra_local_branches",
            tier="hygiene",
            file=None,
            status="PASS" if (refs_proc.returncode == 0 and branches == ["main"]) else "FAIL",
            duration_s=round(time.monotonic() - t1, 3),
            summary=f"local_branches={branches}",
            details={"local_branches": branches},
        )
    )

    # 3. Stashes: <= 4 and no new stash beyond baseline
    t2 = time.monotonic()
    stash_proc = _run(["git", "stash", "list"], timeout=30)
    stash_lines = [ln.strip() for ln in stash_proc.stdout.splitlines() if ln.strip()]
    stash_subjects = [ln.split(": ", 1)[1] if ": " in ln else ln for ln in stash_lines]
    unexpected_stashes = [s for s in stash_subjects if s not in BASELINE_STASH_ALLOWED]
    anchor_ok = (len(stash_lines) < BASELINE_STASH_MAX_COUNT) or (
        len(stash_lines) == BASELINE_STASH_MAX_COUNT
        and bool(stash_lines)
        and BASELINE_STASH_ANCHOR in stash_lines[0]
    )
    stash_ok = (
        stash_proc.returncode == 0
        and len(stash_lines) <= BASELINE_STASH_MAX_COUNT
        and not unexpected_stashes
        and anchor_ok
    )
    checks.append(
        CheckResult(
            name="f17_no_new_stashes",
            tier="hygiene",
            file=None,
            status="PASS" if stash_ok else "FAIL",
            duration_s=round(time.monotonic() - t2, 3),
            summary=f"stash_count={len(stash_lines)} (baseline <= {BASELINE_STASH_MAX_COUNT})",
            details={
                "stash_count": len(stash_lines),
                "stashes": stash_lines,
                "unexpected_stashes": unexpected_stashes,
                "anchor_ok": anchor_ok,
            },
        )
    )

    # 4. PR #426 + lakefile.lean + lean-toolchain + lake-manifest.json clean vs HEAD
    t3 = time.monotonic()
    dirty_protected: dict[str, str] = {}
    pr426_hash_actual: str | None = None
    for rel in CLEAN_PROTECTED_FILES:
        st = _run(["git", "status", "--porcelain", "--", rel], timeout=30)
        df = _run(["git", "diff", "HEAD", "--", rel], timeout=30)
        if st.returncode != 0 or st.stdout.strip() or df.stdout.strip():
            dirty_protected[rel] = st.stdout.strip() or "diff against HEAD non-empty"
        if rel == PR426_FILE:
            ho = _run(["git", "hash-object", rel], timeout=30)
            pr426_hash_actual = ho.stdout.strip()
            if ho.returncode != 0 or pr426_hash_actual != PR426_BASELINE_HASH:
                dirty_protected[rel] = (
                    f"blob hash mismatch: got {pr426_hash_actual}, expected {PR426_BASELINE_HASH}"
                )
    checks.append(
        CheckResult(
            name="f17_protected_clean_files",
            tier="hygiene",
            file=None,
            status="PASS" if not dirty_protected else "FAIL",
            duration_s=round(time.monotonic() - t3, 3),
            summary="PR #426 and Lake/toolchain config untouched"
            if not dirty_protected
            else f"Modified protected files: {sorted(dirty_protected)}",
            details={
                "checked": CLEAN_PROTECTED_FILES,
                "pr426_hash": pr426_hash_actual,
                "pr426_expected_hash": PR426_BASELINE_HASH,
                "violations": dirty_protected,
            },
        )
    )

    # 5. Pre-existing baseline worktree blobs preserved intact
    t4 = time.monotonic()
    baseline_mismatches: dict[str, Any] = {}
    observed_hashes: dict[str, str] = {}
    for rel, expected_hash in PRESERVED_BASELINE_BLOBS.items():
        full = REPO_ROOT / rel
        if not full.is_file() or full.stat().st_size == 0:
            baseline_mismatches[rel] = "missing or empty"
            continue
        ho = _run(["git", "hash-object", rel], timeout=30)
        actual = ho.stdout.strip()
        observed_hashes[rel] = actual
        if ho.returncode != 0 or actual != expected_hash:
            baseline_mismatches[rel] = {"actual": actual, "expected": expected_hash}
    checks.append(
        CheckResult(
            name="f17_preserved_baseline_files",
            tier="hygiene",
            file=None,
            status="PASS" if not baseline_mismatches else "FAIL",
            duration_s=round(time.monotonic() - t4, 3),
            summary="Pre-existing baseline files match recorded hashes"
            if not baseline_mismatches
            else f"Baseline drift in: {sorted(baseline_mismatches)}",
            details={"observed_hashes": observed_hashes, "mismatches": baseline_mismatches},
        )
    )

    return checks


def _check_headers_and_local_scans(files: list[Path]) -> list[CheckResult]:
    results: list[CheckResult] = []
    native_re = re.compile(r"\bnative_decide\b")
    for path in files:
        rel = _rel_posix(path)
        tier = _file_tier(path.name)
        t0 = time.monotonic()
        source = path.read_text(encoding="utf-8")

        header_ok = source.startswith(REQUIRED_LEAN_COPYRIGHT_HEADER)
        results.append(
            CheckResult(
                name="apache_header_byte0",
                tier=tier,
                file=rel,
                status="PASS" if header_ok else "FAIL",
                duration_s=round(time.monotonic() - t0, 3),
                summary="Byte-0 Apache 2.0 2026 header present"
                if header_ok
                else "Missing or malformed byte-0 REQUIRED_LEAN_COPYRIGHT_HEADER",
            )
        )

        t1 = time.monotonic()
        prop_findings = aggregate_prop_constructors(source)
        results.append(
            CheckResult(
                name="aggregate_prop_constructors",
                tier=tier,
                file=rel,
                status="PASS" if not prop_findings else "FAIL",
                duration_s=round(time.monotonic() - t1, 3),
                summary="No aggregate Prop constructor wrappers"
                if not prop_findings
                else f"Found {len(prop_findings)} Prop wrapper(s)",
                details={"findings": prop_findings},
            )
        )

        t2 = time.monotonic()
        cleaned = strip_comments(source, strip_strings=True, strip_quoted_identifiers=True)
        hits: list[str] = []
        for lineno, line in enumerate(cleaned.splitlines(), start=1):
            if native_re.search(line):
                hits.append(f"{rel}:{lineno}")
        results.append(
            CheckResult(
                name="native_decide_scan",
                tier=tier,
                file=rel,
                status="PASS" if not hits else "FAIL",
                duration_s=round(time.monotonic() - t2, 3),
                summary="Zero native_decide usages" if not hits else f"native_decide hits: {hits}",
                details={"hits": hits},
            )
        )
    return results


def _check_test_counts(files: list[Path]) -> list[CheckResult]:
    results: list[CheckResult] = []
    for path in files:
        spec = TIER_FILE_THRESHOLDS.get(path.name)
        if spec is None:
            continue
        rel = _rel_posix(path)
        tier = _file_tier(path.name)
        t0 = time.monotonic()
        source = path.read_text(encoding="utf-8")
        cleaned = strip_comments(source, strip_strings=True, strip_quoted_identifiers=False)
        cleaned = E2E_AUDIT_SECTION_RE.sub("", cleaned)

        decls = [
            m.group("name").replace("«", "").replace("»", "")
            for m in DECL_RE.finditer(cleaned)
            if not m.group("priv")
        ]

        if spec["kind"] == "per_feature":
            counts: dict[str, int] = {}
            deficits: dict[str, str] = {}
            total_matching = 0
            for feat in spec["features"]:
                prefix = spec["prefix_fmt"].format(n=feat)
                matched = [d for d in decls if d.startswith(prefix)]
                counts[f"F{feat}"] = len(matched)
                total_matching += len(matched)
                if len(matched) < spec["min_each"]:
                    deficits[f"F{feat}"] = f"{len(matched)} < {spec['min_each']} ({prefix}*)"
            passed = not deficits
            summary = (
                f"total={total_matching}, per_feature={counts}"
                if passed
                else f"Feature coverage below threshold: {deficits}"
            )
            details = {"counts": counts, "deficits": deficits, "total_matching": total_matching}
        else:
            prefix = spec["prefix"]
            matched = [d for d in decls if d.startswith(prefix)]
            passed = len(matched) >= spec["min_total"]
            summary = f"count={len(matched)} (min {spec['min_total']} {prefix}*)"
            details = {"count": len(matched), "min_total": spec["min_total"], "prefix": prefix}

        results.append(
            CheckResult(
                name="test_count_thresholds",
                tier=tier,
                file=rel,
                status="PASS" if passed else "FAIL",
                duration_s=round(time.monotonic() - t0, 3),
                summary=summary,
                details=details,
            )
        )
    return results


def _run_quality_tools(files: list[Path], allow_pending_impl: bool, timeout: int) -> list[CheckResult]:
    if not files:
        return []
    rel_files = [_rel_posix(p) for p in files]
    results: list[CheckResult] = []

    # 1. opengauss_screener.py --strict --json (NEVER --quarantine)
    t0 = time.monotonic()
    og = _run([sys.executable, "tools/infra/opengauss_screener.py", "--strict", "--json", *rel_files], timeout=timeout)
    try:
        og_data = json.loads(og.stdout) if og.stdout.strip() else {}
    except json.JSONDecodeError:
        og_data = {"raw_stdout": og.stdout}
    violations = og_data.get("violations", {}) if isinstance(og_data, dict) else {}
    v_count = sum(len(v) for v in violations.values()) if isinstance(violations, dict) else -1
    results.append(
        CheckResult(
            name="opengauss_screener_strict",
            tier="quality",
            file=None,
            status="PASS" if (og.returncode == 0 and v_count == 0) else "FAIL",
            duration_s=round(time.monotonic() - t0, 3),
            summary=f"violations={v_count}",
            details={"files": rel_files, "violations": violations, "stderr": og.stderr.strip()},
        )
    )

    # 2. placeholder_audit.py --strict --format json
    t1 = time.monotonic()
    pa = _run([sys.executable, "tools/quality/placeholder_audit.py", "--strict", "--format", "json", *rel_files], timeout=timeout)
    try:
        pa_data = json.loads(pa.stdout) if pa.stdout.strip() else {}
    except json.JSONDecodeError:
        pa_data = {"raw_stdout": pa.stdout}
    pa_summary = pa_data.get("summary", {}) if isinstance(pa_data, dict) else {}
    hard = int(pa_summary.get("hard_count", pa_summary.get("provenance", {}).get("hard_failures", -1)))
    results.append(
        CheckResult(
            name="placeholder_audit_strict",
            tier="quality",
            file=None,
            status="PASS" if (pa.returncode == 0 and hard == 0) else "FAIL",
            duration_s=round(time.monotonic() - t1, 3),
            summary=f"hard_count={hard}",
            details=pa_data,
        )
    )

    # 3. axiom_audit.py --fail-on-gaps --format json
    t2 = time.monotonic()
    aa = _run([sys.executable, "tools/infra/axiom_audit.py", "--fail-on-gaps", "--format", "json", *rel_files], timeout=timeout)
    try:
        aa_data = json.loads(aa.stdout) if aa.stdout.strip() else {}
    except json.JSONDecodeError:
        aa_data = {"raw_stdout": aa.stdout}
    gaps = int(aa_data.get("total_open_gaps", -1)) if isinstance(aa_data, dict) else -1
    results.append(
        CheckResult(
            name="axiom_audit_static",
            tier="quality",
            file=None,
            status="PASS" if (aa.returncode == 0 and gaps == 0) else "FAIL",
            duration_s=round(time.monotonic() - t2, 3),
            summary=f"total_open_gaps={gaps}",
            details=aa_data,
        )
    )

    # 4. detect_hollow_theorems.py --strict
    t3 = time.monotonic()
    ht = _run([sys.executable, "tools/quality/detect_hollow_theorems.py", "--strict", *rel_files], timeout=timeout)
    results.append(
        CheckResult(
            name="detect_hollow_theorems_strict",
            tier="quality",
            file=None,
            status="PASS" if ht.returncode == 0 else "FAIL",
            duration_s=round(time.monotonic() - t3, 3),
            summary=(ht.stdout.strip() or ht.stderr.strip() or "ok")[:220],
            details={"stdout": ht.stdout, "stderr": ht.stderr},
        )
    )

    # 5. semantic_vacuity_gate.py --fail-on error
    t4 = time.monotonic()
    sv = _run([sys.executable, "tools/quality/semantic_vacuity_gate.py", "--fail-on", "error", *rel_files], timeout=timeout)
    results.append(
        CheckResult(
            name="semantic_vacuity_gate",
            tier="quality",
            file=None,
            status="PASS" if sv.returncode == 0 else "FAIL",
            duration_s=round(time.monotonic() - t4, 3),
            summary=(sv.stdout.strip() or sv.stderr.strip() or "ok")[:220],
            details={"stdout": sv.stdout, "stderr": sv.stderr},
        )
    )

    # 6. Staged status classification + proof_proxy_staged_gate.py --strict
    t5 = time.monotonic()
    cached_proc = _run(["git", "diff", "--cached", "--name-only", "-z", "--", *rel_files], timeout=30)
    staged_set = {
        item for item in cached_proc.stdout.split("\0") if item
    } if cached_proc.returncode == 0 else set()
    porcelain_proc = _run(["git", "status", "--porcelain", "--", *rel_files], timeout=30)
    file_git_states: dict[str, str] = {}
    unstaged_deltas: list[str] = []
    porcelain_map: dict[str, str] = {}
    for line in porcelain_proc.stdout.splitlines():
        if len(line) >= 4:
            code = line[:2]
            p = line[3:].strip()
            porcelain_map[p] = code
    for rf in rel_files:
        code = porcelain_map.get(rf)
        if code is None:
            file_git_states[rf] = "clean_tracked"
        elif code == "??":
            file_git_states[rf] = "untracked"
        elif rf in staged_set:
            if code[1] != " ":
                file_git_states[rf] = "staged_with_unstaged_edits"
                unstaged_deltas.append(rf)
            else:
                file_git_states[rf] = "staged"
        else:
            file_git_states[rf] = f"unstaged({code.strip()})"

    staged_targets = [rf for rf in rel_files if rf in staged_set]
    gate_proc = _run(
        [sys.executable, "tools/quality/proof_proxy_staged_gate.py", "--strict", *rel_files],
        timeout=timeout,
    )
    gate_output = (gate_proc.stdout + "\n" + gate_proc.stderr).strip()
    if gate_proc.returncode == 0:
        if staged_targets and not unstaged_deltas:
            gate_status = "PASS"
            gate_summary = f"staged={len(staged_targets)} passed; unstaged_or_clean={len(rel_files) - len(staged_targets)} checked on disk"
        elif unstaged_deltas:
            gate_status = "FAIL" if not allow_pending_impl else "PASS"
            gate_summary = f"staged files have unstaged worktree edits: {unstaged_deltas}"
        else:
            gate_status = "PASS"
            gate_summary = f"no staged targets in {len(rel_files)} file(s); on-disk quality gates enforced directly"
    else:
        only_import_mismatch = (
            allow_pending_impl
            and "imported Lean source is not a consistent active-index snapshot" in gate_output
            and "OpenGauss" not in gate_output
            and "copyright" not in gate_output
            and "Prop structure" not in gate_output
        )
        gate_status = "PENDING_IMPL" if only_import_mismatch else "FAIL"
        gate_summary = f"proof_proxy_staged_gate exited {gate_proc.returncode}"

    results.append(
        CheckResult(
            name="proof_proxy_staged_gate_strict",
            tier="quality",
            file=None,
            status=gate_status,
            duration_s=round(time.monotonic() - t5, 3),
            summary=gate_summary,
            details={
                "file_git_states": file_git_states,
                "staged_targets": staged_targets,
                "unstaged_deltas": unstaged_deltas,
                "returncode": gate_proc.returncode,
                "output": gate_output[:2000],
            },
        )
    )

    return results


def _run_lean_and_axiom_checks(
    files: list[Path],
    *,
    allow_pending_impl: bool,
    wait_for_build_lock: bool,
    timeout: int,
) -> list[CheckResult]:
    results: list[CheckResult] = []
    wait_flag = "--wait-for-build-lock" if wait_for_build_lock else "--no-wait-for-build-lock"
    all_owner_modules: list[str] = []
    seen_owners: set[str] = set()
    ready_tier_files: list[Path] = []

    for path in files:
        rel = _rel_posix(path)
        tier = _file_tier(path.name)
        imports = _parse_imports(path)
        readiness = _check_module_readiness(imports)

        for mod in readiness["info_geometry_imports"]:
            if mod not in seen_owners:
                seen_owners.add(mod)
                all_owner_modules.append(mod)

        if not readiness["is_ready"]:
            status = "PENDING_IMPL" if allow_pending_impl else "FAIL"
            results.append(
                CheckResult(
                    name="lean_elaboration",
                    tier=tier,
                    file=rel,
                    status=status,
                    duration_s=0.0,
                    summary="Pending or missing InfoGeometry imports/contracts",
                    details=readiness,
                )
            )
            results.append(
                CheckResult(
                    name="tier_file_axiom_audit",
                    tier=tier,
                    file=rel,
                    status=status,
                    duration_s=0.0,
                    summary="Skipped test axiom audit because imports/contracts are pending",
                    details=readiness,
                )
            )
            continue

        # Elaboration via run_locked_lean.py
        t0 = time.monotonic()
        try:
            proc = _run(
                [sys.executable, "tools/infra/run_locked_lean.py", wait_flag, rel],
                timeout=timeout,
            )
            combined = proc.stdout + "\n" + proc.stderr
            has_inline_audit = "section E2EAxiomAudit" in strip_comments(
                path.read_text(encoding="utf-8"), strip_strings=True, strip_quoted_identifiers=False
            )
            audit_marker_ok = (not has_inline_audit) or ("E2E_AXIOM_AUDIT_PASS" in combined)
            elab_ok = proc.returncode == 0 and audit_marker_ok
            summary = "Elaboration passed" if elab_ok else (
                "Missing E2E_AXIOM_AUDIT_PASS output"
                if proc.returncode == 0 and not audit_marker_ok
                else f"Lean elaboration failed (exit {proc.returncode})"
            )
            results.append(
                CheckResult(
                    name="lean_elaboration",
                    tier=tier,
                    file=rel,
                    status="PASS" if elab_ok else "FAIL",
                    duration_s=round(time.monotonic() - t0, 3),
                    summary=summary,
                    details={
                        "returncode": proc.returncode,
                        "has_inline_audit": has_inline_audit,
                        "audit_marker_ok": audit_marker_ok,
                        "stdout": proc.stdout[-2000:],
                        "stderr": proc.stderr[-2000:],
                    },
                )
            )
            if elab_ok and path.name.startswith("Tier"):
                ready_tier_files.append(path)
        except subprocess.TimeoutExpired:
            results.append(
                CheckResult(
                    name="lean_elaboration",
                    tier=tier,
                    file=rel,
                    status="FAIL",
                    duration_s=round(time.monotonic() - t0, 3),
                    summary=f"Timed out after {timeout}s",
                )
            )

    # Owner module kernel axiom audit (NEVER hold an outer build lock around axiom_check.py!)
    if all_owner_modules:
        ready_mods = [m for m in all_owner_modules if _module_to_olean(m).is_file()]
        missing_oleans = [m for m in all_owner_modules if not _module_to_olean(m).is_file()]
        if missing_oleans and not allow_pending_impl:
            results.append(
                CheckResult(
                    name="owner_modules_axiom_audit",
                    tier="axiom",
                    file=None,
                    status="FAIL",
                    duration_s=0.0,
                    summary=f"Missing .olean for imported owner modules: {missing_oleans}",
                    details={"missing_oleans": missing_oleans, "ready_modules": ready_mods},
                )
            )
        if ready_mods:
            t_ax = time.monotonic()
            try:
                ax_proc = _run(
                    [sys.executable, "tools/infra/axiom_check.py", "--batch-size", "4", "--quiet", "--json", *ready_mods],
                    timeout=timeout,
                )
                entries = _extract_leading_json_list(ax_proc.stdout) if ax_proc.stdout.strip() else []
                failed_mods = [e for e in entries if not bool(e.get("passed"))]
                ax_ok = (
                    ax_proc.returncode == 0
                    and len(entries) == len(ready_mods)
                    and not failed_mods
                )
                status = "PASS" if ax_ok else "FAIL"
                if ax_ok and missing_oleans and allow_pending_impl:
                    status = "PENDING_IMPL"
                results.append(
                    CheckResult(
                        name="owner_modules_axiom_audit",
                        tier="axiom",
                        file=None,
                        status=status,
                        duration_s=round(time.monotonic() - t_ax, 3),
                        summary=f"audited={len(entries)}/{len(ready_mods)}, failed={len(failed_mods)}, pending_olean={len(missing_oleans)}",
                        details={
                            "modules": ready_mods,
                            "missing_oleans": missing_oleans,
                            "failed": failed_mods,
                            "entries": entries,
                        },
                    )
                )
            except (subprocess.TimeoutExpired, ValueError) as exc:
                results.append(
                    CheckResult(
                        name="owner_modules_axiom_audit",
                        tier="axiom",
                        file=None,
                        status="FAIL",
                        duration_s=round(time.monotonic() - t_ax, 3),
                        summary=f"axiom_check.py error: {exc}",
                    )
                )
        elif missing_oleans and allow_pending_impl:
            results.append(
                CheckResult(
                    name="owner_modules_axiom_audit",
                    tier="axiom",
                    file=None,
                    status="PENDING_IMPL",
                    duration_s=0.0,
                    summary=f"Pending .olean builds for {len(missing_oleans)} owner module(s)",
                    details={"missing_oleans": missing_oleans},
                )
            )

    # Test file .olean replay audit in TemporaryDirectory
    for path in ready_tier_files:
        rel = _rel_posix(path)
        tier = _file_tier(path.name)
        t_tmp = time.monotonic()
        try:
            with tempfile.TemporaryDirectory(prefix="polarized_z2_e2e_olean_") as tmp_dir:
                tmp_olean = Path(tmp_dir) / f"{path.stem}.olean"
                compile_proc = _run(
                    [sys.executable, "tools/infra/run_locked_lean.py", wait_flag, rel, "-o", str(tmp_olean)],
                    timeout=timeout,
                )
                if compile_proc.returncode != 0 or not tmp_olean.is_file():
                    results.append(
                        CheckResult(
                            name="tier_file_axiom_audit",
                            tier=tier,
                            file=rel,
                            status="FAIL",
                            duration_s=round(time.monotonic() - t_tmp, 3),
                            summary=f"Failed to compile temporary .olean (exit {compile_proc.returncode})",
                            details={"stdout": compile_proc.stdout[-1500:], "stderr": compile_proc.stderr[-1500:]},
                        )
                    )
                    continue
                replay_proc = _run(
                    [
                        "flock",
                        "-x",
                        str(BUILD_LOCK_PATH),
                        "lake",
                        "env",
                        "lean",
                        "--run",
                        "tools/infra/axiom_check.lean",
                        str(tmp_olean),
                    ],
                    timeout=timeout,
                )
                pass_marker = f"MODULE_RESULT:{tmp_olean}:PASS"
                replay_ok = replay_proc.returncode == 0 and pass_marker in replay_proc.stdout
                results.append(
                    CheckResult(
                        name="tier_file_axiom_audit",
                        tier=tier,
                        file=rel,
                        status="PASS" if replay_ok else "FAIL",
                        duration_s=round(time.monotonic() - t_tmp, 3),
                        summary="Temp .olean kernel axiom audit PASS"
                        if replay_ok
                        else f"Temp .olean kernel axiom audit FAIL (exit {replay_proc.returncode})",
                        details={
                            "stdout": replay_proc.stdout[-1500:],
                            "stderr": replay_proc.stderr[-1500:],
                        },
                    )
                )
        except subprocess.TimeoutExpired:
            results.append(
                CheckResult(
                    name="tier_file_axiom_audit",
                    tier=tier,
                    file=rel,
                    status="FAIL",
                    duration_s=round(time.monotonic() - t_tmp, 3),
                    summary=f"Temp .olean audit timed out after {timeout}s",
                )
            )

    return results


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Opaque-box 4-tier E2E runner for tests/polarized_z2_e2e/."
    )
    parser.add_argument(
        "--tier",
        choices=("1", "2", "3", "4", "all"),
        default="all",
        help="Select E2E tier to run (default: all).",
    )
    parser.add_argument(
        "--allow-pending-impl",
        "--syntax-lint",
        dest="allow_pending_impl",
        action="store_true",
        help="Pre-M6 mode: missing tier files / unbuilt M1-M5 imports report PENDING_IMPL instead of FAIL.",
    )
    parser.add_argument(
        "--skip-lean",
        action="store_true",
        help="Skip Lean elaboration and kernel axiom audits; run quality, count, and F17 hygiene gates only.",
    )
    parser.add_argument(
        "--check-hygiene-only",
        action="store_true",
        help="Run only F17 repository, branch, stash, and protected-file hygiene checks.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit a single JSON report object on stdout.",
    )
    parser.add_argument(
        "--wait-for-build-lock",
        dest="wait_for_build_lock",
        action="store_true",
        default=True,
        help="Wait for the repository build lock when invoking run_locked_lean.py (default).",
    )
    parser.add_argument(
        "--no-wait-for-build-lock",
        dest="wait_for_build_lock",
        action="store_false",
        help="Fail immediately if the build lock is held.",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=900,
        help="Timeout in seconds per Lean/tool subprocess (default: 900).",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    if args.timeout < 1:
        print("--timeout must be >= 1", file=sys.stderr)
        return 2

    t_start = time.monotonic()
    checks: list[CheckResult] = []

    # Check (d): F17 Repo & Branch Hygiene always runs
    checks.extend(run_hygiene_checks())

    discovered_files: list[Path] = []
    if not args.check_hygiene_only:
        discovered_files, presence_checks = _discover_targets(args.tier, args.allow_pending_impl)
        checks.extend(presence_checks)

        if discovered_files:
            # Check (c): Header + local static scans + quality tools + staged gate
            checks.extend(_check_headers_and_local_scans(discovered_files))
            checks.extend(_check_test_counts(discovered_files))
            checks.extend(_run_quality_tools(discovered_files, args.allow_pending_impl, args.timeout))

            # Checks (a) & (b): Lean elaboration + kernel axiom audits
            if args.skip_lean:
                for p in discovered_files:
                    checks.append(
                        CheckResult(
                            name="lean_elaboration",
                            tier=_file_tier(p.name),
                            file=_rel_posix(p),
                            status="SKIPPED",
                            duration_s=0.0,
                            summary="Skipped via --skip-lean",
                        )
                    )
            else:
                checks.extend(
                    _run_lean_and_axiom_checks(
                        discovered_files,
                        allow_pending_impl=args.allow_pending_impl,
                        wait_for_build_lock=args.wait_for_build_lock,
                        timeout=args.timeout,
                    )
                )

    counts = {
        "PASS": sum(1 for c in checks if c.status == "PASS"),
        "FAIL": sum(1 for c in checks if c.status == "FAIL"),
        "PENDING_IMPL": sum(1 for c in checks if c.status == "PENDING_IMPL"),
        "SKIPPED": sum(1 for c in checks if c.status == "SKIPPED"),
    }
    overall_passed = counts["FAIL"] == 0

    report = {
        "suite": "polarized_z2_e2e",
        "mode": "hygiene-only" if args.check_hygiene_only else ("allow-pending-impl" if args.allow_pending_impl else "strict"),
        "tier": args.tier,
        "skip_lean": args.skip_lean,
        "passed": overall_passed,
        "duration_s": round(time.monotonic() - t_start, 3),
        "discovered_files": [_rel_posix(p) for p in discovered_files],
        "counts": counts,
        "checks": [asdict(c) for c in checks],
    }

    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(
            f"[polarized_z2_e2e] mode={report['mode']} tier={args.tier} "
            f"passed={overall_passed} counts={counts}"
        )
        for chk in checks:
            loc = f" ({chk.file})" if chk.file else ""
            print(f"  [{chk.status}] {chk.name}{loc}: {chk.summary}")

    return 0 if overall_passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
