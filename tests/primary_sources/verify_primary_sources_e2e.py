#!/usr/bin/env python3
"""Standalone pure-stdlib E2E verification runner for Primary-Source Foundations (Tiers 1-4)."""

from __future__ import annotations

import argparse
import json
import sys
import time
from dataclasses import asdict
from pathlib import Path
from typing import Any

# Ensure REPO_ROOT is importable when invoked directly as `python3 tests/primary_sources/verify_primary_sources_e2e.py`
_THIS_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_THIS_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_THIS_REPO_ROOT))

from tests.primary_sources import (  # noqa: E402
    ANCHOR_MODULES,
    BRIDGE_FILE_REL,
    FEATURE_SPECS,
    MILESTONES,
    PILLARS,
    PRIMARY_LEAN_FILES,
    REPORTS_DIR,
    REPO_ROOT,
    TARGET_MODULES,
)
from tests.primary_sources.lean_audit import (  # noqa: E402
    check_cross_pillar_bridge,
    check_traceability_kernel,
    lean_path_to_module,
    run_batched_lake_build,
    run_olean_axiom_audits,
    run_print_axioms_probe,
    run_r3_kernel_probe,
)
from tests.primary_sources.manifest_checker import (  # noqa: E402
    CheckOutcome,
    TraceabilityRow,
    check_papers_git_hygiene,
    validate_archetypes_doc,
    validate_manifest,
)
from tests.primary_sources.quality_and_r3 import (  # noqa: E402
    check_apache_header_byte0,
    check_feature_lean_presence,
    check_forbidden_tokens_and_prop_wrappers,
    check_r3_compliance,
    check_repo_lean_invariants,
    run_scoped_quality_tools,
)
from tools.build_lock import BuildLock, DEFAULT_BUILD_LOCK_PATH  # noqa: E402


def classify_milestone_states(repo_root: Path) -> dict[str, dict[str, Any]]:
    """Classify each milestone M1..M6 as PRESENT, HALF_STARTED, or ABSENT."""
    states: dict[str, dict[str, Any]] = {}
    for mid, spec in MILESTONES.items():
        req_files = list(spec["required_files"])  # type: ignore[arg-type]
        req_dirs = list(spec["required_dirs"])  # type: ignore[arg-type]
        present_files = [f for f in req_files if (repo_root / f).is_file()]
        missing_files = [f for f in req_files if not (repo_root / f).is_file()]
        present_dirs = [d for d in req_dirs if (repo_root / d).is_dir()]
        missing_dirs = [d for d in req_dirs if not (repo_root / d).is_dir()]
        dir_has_content = any(
            (repo_root / d).is_dir() and any((repo_root / d).iterdir()) for d in req_dirs
        )

        any_present = bool(present_files) or dir_has_content
        all_present = not missing_files and not missing_dirs

        if all_present:
            state = "PRESENT"
        elif any_present:
            state = "HALF_STARTED"
        else:
            state = "ABSENT"

        states[mid] = {
            "state": state,
            "pillar": spec["pillar"],
            "features": spec["features"],
            "present_files": present_files,
            "missing_files": missing_files,
            "present_dirs": present_dirs,
            "missing_dirs": missing_dirs,
        }
    return states


def _pillar_matches(
    item_pillar: str,
    pillar_filter: str,
    *,
    include_cross_pillar: bool = False,
) -> bool:
    if pillar_filter == "all":
        return True
    if item_pillar == "all":
        return include_cross_pillar
    return item_pillar == pillar_filter


def _milestone_files_for_pillar(pillar_filter: str, *, include_cross_pillar: bool = False) -> list[str]:
    files: list[str] = []
    for mid in ("M2", "M3", "M4", "M5", "M6"):
        spec = MILESTONES[mid]
        if _pillar_matches(str(spec["pillar"]), pillar_filter, include_cross_pillar=include_cross_pillar):
            files.extend(spec["required_files"])  # type: ignore[arg-type]
    return list(dict.fromkeys(files))


def _olean_exists(repo_root: Path, module: str) -> bool:
    parts = module.split(".")
    olean = repo_root / ".lake" / "build" / "lib" / "lean" / Path(*parts).with_suffix(".olean")
    return olean.is_file()


def _wait_for_settled_oleans() -> None:
    """Wait until any concurrent exclusive lake build releases the shared build lock."""
    with BuildLock(DEFAULT_BUILD_LOCK_PATH, "primary_sources_e2e_olean_scan", block=True, shared=True):
        pass


def run_suite(
    *,
    repo_root: Path = REPO_ROOT,
    tier: str = "all",
    mode: str = "strict",
    pillar: str = "all",
    check_id: str | None = None,
    include_anchors: bool = False,
    include_cross_pillar: bool = False,
    deep_replay: bool = False,
    run_lean_commands: bool = True,
) -> dict[str, Any]:
    """Execute selected E2E tiers and return structured report dictionary."""
    t0 = time.monotonic()
    selected_tiers = {1, 2, 3, 4} if tier == "all" else {int(tier)}
    m_states = classify_milestone_states(repo_root)
    outcomes: list[CheckOutcome] = []

    def _want(cid: str) -> bool:
        return check_id is None or check_id == cid

    def _want_any(cids: set[str]) -> bool:
        return check_id is None or check_id in cids

    def _emit_missing_milestone(cid: str, tier_num: int, mid: str, p_tag: str, missing: list[str]) -> None:
        if mode == "strict":
            outcomes.append(
                CheckOutcome(
                    check_id=cid,
                    tier=tier_num,
                    milestone=mid,
                    pillar=p_tag,
                    status="FAIL",
                    summary=f"MISSING_FAIL ({mid} absent in strict mode): missing {missing}",
                    details={"missing": missing, "milestone_state": "ABSENT"},
                )
            )
        else:
            outcomes.append(
                CheckOutcome(
                    check_id=cid,
                    tier=tier_num,
                    milestone=mid,
                    pillar=p_tag,
                    status="PENDING_MISSING",
                    summary=f"PENDING_MISSING ({mid} absent in partial mode): awaiting {missing}",
                    details={"missing": missing, "milestone_state": "ABSENT"},
                )
            )

    # Tier 2: enforce .papers/ git hygiene & zero .lean files in tests/primary_sources/
    if 2 in selected_tiers and _want("T2-GIT-HYGIENE"):
        outcomes.append(check_papers_git_hygiene(repo_root))

    # Pre-check M1 data if present or half-started (needed by Tier 1 and Tier 3)
    m1_info = m_states["M1"]
    m1_state = str(m1_info["state"])
    manifest_data: dict[str, Any] | None = None
    trace_rows: list[TraceabilityRow] = []

    if 1 in selected_tiers and m1_state == "HALF_STARTED" and _want("T1-M1-HALF-STARTED"):
        # Half-started milestone ALWAYS fails on missing sibling files, even in partial mode
        missing = list(m1_info["missing_files"]) + list(m1_info["missing_dirs"])
        outcomes.append(
            CheckOutcome(
                check_id="T1-M1-HALF-STARTED",
                tier=1,
                milestone="M1",
                pillar=pillar,
                status="FAIL",
                summary=f"M1 is half-started (present={m1_info['present_files']}, missing={missing})",
                details=m1_info,
            )
        )

    need_m1_data = (1 in selected_tiers and _want_any({"T1-M1-MANIFEST", "T1-M1-ARCHETYPES-DOC"})) or (
        3 in selected_tiers and _want("T3-TRACEABILITY-KERNEL")
    )
    if m1_state in {"PRESENT", "HALF_STARTED"} and need_m1_data:
        m_out, manifest_data = validate_manifest(repo_root, pillar_filter=pillar)
        d_out, trace_rows = validate_archetypes_doc(repo_root, manifest=manifest_data, pillar_filter=pillar)
        if 1 in selected_tiers:
            if _want(m_out.check_id):
                outcomes.append(m_out)
            if _want(d_out.check_id):
                outcomes.append(d_out)
    elif 1 in selected_tiers and m1_state == "ABSENT" and _want("T1-M1-PRIMARY-SOURCES"):
        _emit_missing_milestone(
            "T1-M1-PRIMARY-SOURCES",
            1,
            "M1",
            pillar,
            list(m1_info["missing_files"]) + list(m1_info["missing_dirs"]),
        )

    # Tier 1: Milestone completeness checks for M2..M6 (half-started fails even in partial mode)
    if 1 in selected_tiers:
        for mid in ("M2", "M3", "M4", "M5", "M6"):
            info = m_states[mid]
            if not _pillar_matches(str(info["pillar"]), pillar, include_cross_pillar=include_cross_pillar):
                continue
            if info["state"] == "HALF_STARTED" and _want(f"T1-{mid}-HALF-STARTED"):
                outcomes.append(
                    CheckOutcome(
                        check_id=f"T1-{mid}-HALF-STARTED",
                        tier=1,
                        milestone=mid,
                        pillar=str(info["pillar"]),
                        status="FAIL",
                        summary=f"{mid} is half-started (present={info['present_files']}, missing={info['missing_files']})",
                        details=info,
                    )
                )

    # Tier 1: Feature #3..#23 Lean module & concept presence
    if 1 in selected_tiers:
        for fspec in FEATURE_SPECS:
            if fspec.milestone == "M1":
                continue
            if not _pillar_matches(fspec.pillar, pillar, include_cross_pillar=include_cross_pillar):
                continue
            cid = f"T1-F{fspec.feature_id:02d}"
            if not _want(cid):
                continue
            m_state = str(m_states[fspec.milestone]["state"])
            if m_state == "ABSENT":
                _emit_missing_milestone(
                    cid,
                    1,
                    fspec.milestone,
                    fspec.pillar,
                    [fspec.owner_file],
                )
            else:
                outcomes.append(check_feature_lean_presence(fspec.feature_id, repo_root))

    # Determine present M2..M6 files matching pillar filter
    target_files = _milestone_files_for_pillar(pillar, include_cross_pillar=include_cross_pillar)
    present_primary_files = [f for f in target_files if (repo_root / f).is_file()]

    # Tier 2: Headers, scoped quality gates, R3 architectural checks
    if 2 in selected_tiers:
        if present_primary_files:
            if _want("T2-APACHE-HEADER"):
                outcomes.append(check_apache_header_byte0(present_primary_files, repo_root))
            if _want("T2-FORBIDDEN-SCAN"):
                outcomes.append(check_forbidden_tokens_and_prop_wrappers(present_primary_files, repo_root))
            if _want_any({"T2-PLACEHOLDER-AUDIT", "T2-AXIOM-AUDIT-SCAN", "T2-HOLLOW-THEOREMS", "T2-SEMANTIC-VACUITY", "T2-OPENGAUSS-SCREENER"}):
                outcomes.extend(run_scoped_quality_tools(present_primary_files, repo_root, strict_placeholder_names=True))
            if _want_any({"T2-R3.1-KREIN-SEPARATION", "T2-R3.2-METRIC-BASIS-FREE", "T2-R3.3-KOSZUL-Z2-GRADING", "T2-R3.4-LIE-PEIRCE-DIAMONDS"}):
                outcomes.extend(check_r3_compliance(present_primary_files, repo_root, pillar_filter=pillar))
            if run_lean_commands and _want("T2-R3-KERNEL-INSPECTION"):
                _wait_for_settled_oleans()
                built_mods = [
                    lean_path_to_module(f)
                    for f in present_primary_files
                    if _olean_exists(repo_root, lean_path_to_module(f))
                ]
                if built_mods:
                    outcomes.append(run_r3_kernel_probe(built_mods, repo_root=repo_root))
        elif _want("T2-PRIMARY-FILES"):
            if mode == "strict":
                outcomes.append(
                    CheckOutcome(
                        check_id="T2-PRIMARY-FILES",
                        tier=2,
                        milestone="M2-M6",
                        pillar=pillar,
                        status="FAIL",
                        summary="MISSING_FAIL: zero M2-M6 Lean files present in strict mode",
                        details={"expected": target_files},
                    )
                )
            else:
                outcomes.append(
                    CheckOutcome(
                        check_id="T2-PRIMARY-FILES",
                        tier=2,
                        milestone="M2-M6",
                        pillar=pillar,
                        status="PENDING_MISSING",
                        summary="PENDING_MISSING: no M2-M6 Lean files present yet in partial mode",
                        details={"expected": target_files},
                    )
                )

        if include_anchors:
            anchor_files = [
                a["path"]
                for a in ANCHOR_MODULES
                if _pillar_matches(a["pillar"], pillar, include_cross_pillar=True) and (repo_root / a["path"]).is_file()
            ]
            if anchor_files:
                if _want("T2-ANCHOR-APACHE-HEADER"):
                    hdr = check_apache_header_byte0(anchor_files, repo_root, allow_anchor_exempt=True)
                    outcomes.append(
                        CheckOutcome(
                            check_id="T2-ANCHOR-APACHE-HEADER",
                            tier=2,
                            milestone="ANCHOR",
                            pillar=pillar,
                            status=hdr.status,
                            summary=hdr.summary,
                            details={"anchors": anchor_files},
                        )
                    )
                if _want("T2-ANCHOR-FORBIDDEN-SCAN"):
                    fb = check_forbidden_tokens_and_prop_wrappers(anchor_files, repo_root)
                    fb.check_id = "T2-ANCHOR-FORBIDDEN-SCAN"
                    fb.milestone = "ANCHOR"
                    outcomes.append(fb)
                if _want_any({
                    "T2-ANCHOR-PLACEHOLDER-AUDIT",
                    "T2-ANCHOR-AXIOM-AUDIT-SCAN",
                    "T2-ANCHOR-HOLLOW-THEOREMS",
                    "T2-ANCHOR-SEMANTIC-VACUITY",
                    "T2-ANCHOR-OPENGAUSS-SCREENER",
                }):
                    for q in run_scoped_quality_tools(anchor_files, repo_root, strict_placeholder_names=False):
                        q.check_id = q.check_id.replace("T2-", "T2-ANCHOR-")
                        q.milestone = "ANCHOR"
                        outcomes.append(q)
                if _want_any({
                    "T2-ANCHOR-R3.1-KREIN-SEPARATION",
                    "T2-ANCHOR-R3.2-METRIC-BASIS-FREE",
                    "T2-ANCHOR-R3.3-KOSZUL-Z2-GRADING",
                    "T2-ANCHOR-R3.4-LIE-PEIRCE-DIAMONDS",
                }):
                    for r3 in check_r3_compliance(anchor_files, repo_root, pillar_filter=pillar):
                        r3.check_id = r3.check_id.replace("T2-", "T2-ANCHOR-")
                        r3.milestone = "ANCHOR"
                        outcomes.append(r3)
                if run_lean_commands and _want("T2-ANCHOR-R3-KERNEL"):
                    _wait_for_settled_oleans()
                    built_anchors = [
                        lean_path_to_module(f)
                        for f in anchor_files
                        if _olean_exists(repo_root, lean_path_to_module(f))
                    ]
                    if built_anchors:
                        outcomes.append(
                            run_r3_kernel_probe(
                                built_anchors,
                                repo_root=repo_root,
                                check_id="T2-ANCHOR-R3-KERNEL",
                            )
                        )

    # Tier 3: Cross-pillar integration & Source-to-Declaration traceability kernel probe
    if 3 in selected_tiers:
        if (pillar == "all" or include_cross_pillar) and _want("T3-FOUR-PILLAR-BRIDGE"):
            m6_state = str(m_states["M6"]["state"])
            if m6_state == "ABSENT":
                _emit_missing_milestone("T3-FOUR-PILLAR-BRIDGE", 3, "M6", "all", [BRIDGE_FILE_REL])
            else:
                outcomes.append(check_cross_pillar_bridge(repo_root))

        if _want("T3-TRACEABILITY-KERNEL"):
            if m1_state == "ABSENT":
                _emit_missing_milestone("T3-TRACEABILITY-KERNEL", 3, "M6", pillar, list(m1_info["missing_files"]))
            else:
                outcomes.append(
                    check_traceability_kernel(
                        trace_rows,
                        manifest_data,
                        repo_root=repo_root,
                        pillar_filter=pillar,
                        run_lean_kernel=run_lean_commands,
                        allow_planned=(mode == "partial"),
                        include_cross_pillar=include_cross_pillar,
                        incremental_partial=(mode == "partial"),
                    )
                )

    # Tier 4: Batched Lake build, .olean axiom audits, #print axioms probe, repo invariant
    if 4 in selected_tiers:
        if _want("T4-REPO-LEAN-INVARIANT"):
            outcomes.append(
                check_repo_lean_invariants(
                    repo_root,
                    require_m6_in_all=(m_states["M6"]["state"] == "PRESENT" and (pillar == "all" or include_cross_pillar)),
                )
            )
        present_target_mods = [lean_path_to_module(f) for f in present_primary_files]
        if m_states["M6"]["state"] == "PRESENT" and (pillar == "all" or include_cross_pillar):
            for extra_mod in ("InfoGeometry.Canonical.R1R2R3UnifiedTriangleBridge", "InfoGeometry.Canonical.All"):
                if extra_mod not in present_target_mods:
                    present_target_mods.append(extra_mod)

        need_t4_build = _want_any({"T4-LAKE-BUILD", "T4-OLEAN-AXIOM-INDEX", "T4-OLEAN-AXIOM-CHECK", "T4-PRINT-AXIOMS-PROBE"})
        if present_primary_files:
            if run_lean_commands and need_t4_build:
                build_res = run_batched_lake_build(present_target_mods, repo_root=repo_root)
                if _want("T4-LAKE-BUILD"):
                    outcomes.append(build_res)
                if build_res.status == "PASS":
                    if _want_any({"T4-OLEAN-AXIOM-INDEX", "T4-OLEAN-AXIOM-CHECK"}):
                        outcomes.extend(
                            run_olean_axiom_audits(
                                present_target_mods,
                                repo_root=repo_root,
                                deep_replay=deep_replay,
                            )
                        )
                    if _want("T4-PRINT-AXIOMS-PROBE"):
                        outcomes.append(run_print_axioms_probe(present_primary_files, repo_root=repo_root))
        elif _want("T4-LAKE-BUILD"):
            if mode == "strict":
                outcomes.append(
                    CheckOutcome(
                        check_id="T4-LAKE-BUILD",
                        tier=4,
                        milestone="M2-M6",
                        pillar=pillar,
                        status="FAIL",
                        summary="MISSING_FAIL: no M2-M6 Lean modules present for strict Tier 4 build/axiom audit",
                        details={"expected_modules": list(TARGET_MODULES)},
                    )
                )
            else:
                outcomes.append(
                    CheckOutcome(
                        check_id="T4-LAKE-BUILD",
                        tier=4,
                        milestone="M2-M6",
                        pillar=pillar,
                        status="PENDING_MISSING",
                        summary="PENDING_MISSING: no M2-M6 Lean modules present yet in partial mode",
                        details={"expected_modules": list(TARGET_MODULES)},
                    )
                )

        if include_anchors and run_lean_commands and _want_any({"T4-ANCHOR-OLEAN-AXIOM-INDEX", "T4-ANCHOR-OLEAN-AXIOM-CHECK", "T4-ANCHOR-PRINT-AXIOMS"}):
            _wait_for_settled_oleans()
            built_anchor_mods = [
                a["module"]
                for a in ANCHOR_MODULES
                if _pillar_matches(a["pillar"], pillar, include_cross_pillar=True) and _olean_exists(repo_root, a["module"])
            ]
            if built_anchor_mods:
                if _want_any({"T4-ANCHOR-OLEAN-AXIOM-INDEX", "T4-ANCHOR-OLEAN-AXIOM-CHECK"}):
                    for ao in run_olean_axiom_audits(
                        built_anchor_mods,
                        repo_root=repo_root,
                        deep_replay=deep_replay,
                    ):
                        ao.check_id = ao.check_id.replace("T4-", "T4-ANCHOR-")
                        ao.milestone = "ANCHOR"
                        outcomes.append(ao)
                if _want("T4-ANCHOR-PRINT-AXIOMS"):
                    smoke_file = "lean/InfoGeometry/Canonical/R1R2R3UnifiedTriangleBridge.lean"
                    if (repo_root / smoke_file).is_file():
                        pa = run_print_axioms_probe([smoke_file], repo_root=repo_root)
                        pa.check_id = "T4-ANCHOR-PRINT-AXIOMS"
                        pa.milestone = "ANCHOR"
                        outcomes.append(pa)

    if check_id:
        outcomes = [o for o in outcomes if o.check_id == check_id]
        if not outcomes:
            return {
                "error": f"No check matched --check-id {check_id!r}",
                "exit_code": 2,
                "mode": mode,
                "tier": tier,
                "pillar": pillar,
                "outcomes": [],
                "summary": {"passed": 0, "failed": 0, "pending": 0, "skipped": 0, "executed": 0},
                "milestone_states": m_states,
            }

    passed = sum(1 for o in outcomes if o.status == "PASS")
    failed = sum(1 for o in outcomes if o.status == "FAIL")
    pending = sum(1 for o in outcomes if o.status == "PENDING_MISSING")
    skipped = sum(1 for o in outcomes if o.status == "SKIPPED")
    executed = len(outcomes)

    if mode == "strict":
        exit_code = 0 if (failed == 0 and pending == 0 and executed > 0) else 1
    else:
        exit_code = 0 if failed == 0 else 1

    return {
        "suite": "primary_sources_e2e",
        "mode": mode,
        "tier": tier,
        "pillar": pillar,
        "include_anchors": include_anchors,
        "duration_s": round(time.monotonic() - t0, 3),
        "exit_code": exit_code,
        "partial_banner": (mode == "partial" or pending > 0),
        "milestone_states": m_states,
        "summary": {
            "passed": passed,
            "failed": failed,
            "pending": pending,
            "skipped": skipped,
            "executed": executed,
        },
        "outcomes": [asdict(o) for o in outcomes],
    }


def render_markdown_report(report: dict[str, Any]) -> str:
    s = report["summary"]
    lines = [
        "# Primary-Source Mathematical Foundations E2E Report",
        "",
        f"- **Mode**: `{report['mode']}`",
        f"- **Tier**: `{report['tier']}`",
        f"- **Pillar**: `{report['pillar']}`",
        f"- **Exit Code**: `{report['exit_code']}`",
        f"- **Duration**: `{report.get('duration_s', 0)}s`",
        f"- **Counts**: `passed={s['passed']}`, `failed={s['failed']}`, `pending={s['pending']}`, `executed={s['executed']}`",
        "",
    ]
    if report.get("partial_banner"):
        lines.extend(
            [
                "> **[PARTIAL REPO STATE — NOT FULL ACCEPTANCE]** Missing unstarted milestones are flagged `PENDING_MISSING`; run `--mode strict` for full M1–M6 acceptance.",
                "",
            ]
        )
    lines.extend(["## Milestone States", "", "| Milestone | State | Present Files | Missing Files |", "|---|---|---|---|"])
    for mid, st in report["milestone_states"].items():
        lines.append(
            f"| {mid} | `{st['state']}` | {len(st['present_files'])} | {len(st['missing_files']) + len(st['missing_dirs'])} |"
        )
    lines.extend(["", "## Check Outcomes", "", "| Check ID | Tier | Milestone | Pillar | Status | Summary |", "|---|---|---|---|---|---|"])
    for o in report["outcomes"]:
        summ = str(o["summary"]).replace("|", "\\|").replace("\n", " ")
        lines.append(f"| `{o['check_id']}` | {o['tier']} | {o['milestone']} | {o['pillar']} | `{o['status']}` | {summ} |")
    lines.append("")
    return "\n".join(lines)


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="E2E verification suite for Primary-Source Mathematical Foundations (info-geometry-lean)."
    )
    parser.add_argument(
        "--tier",
        choices=("1", "2", "3", "4", "all"),
        default="all",
        help="Verification tier to execute (default: all)",
    )
    parser.add_argument(
        "--mode",
        choices=("strict", "partial"),
        default=None,
        help="Strict requires full M1-M6 closure; partial marks completely absent milestones PENDING_MISSING (default: strict)",
    )
    parser.add_argument(
        "--partial-ok",
        "--allow-missing-milestones",
        dest="partial_ok",
        action="store_true",
        help="Alias for --mode partial (cannot be combined with --mode strict)",
    )
    parser.add_argument(
        "--pillar",
        choices=(*PILLARS, "all"),
        default="all",
        help="Filter checks by mathematical pillar (default: all)",
    )
    parser.add_argument(
        "--include-cross-pillar",
        action="store_true",
        help="Include M6 cross-pillar checks when filtering by a single --pillar",
    )
    parser.add_argument(
        "--check-id",
        default=None,
        help="Run/filter to a single check ID",
    )
    parser.add_argument(
        "--include-anchors",
        action="store_true",
        help="Also run quality, R3, and axiom checks on existing repo anchor modules",
    )
    parser.add_argument(
        "--deep-replay",
        action="store_true",
        help="Also run slow per-module axiom_check.py replay in addition to fast compiled axiom_index.py",
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        default=None,
        help="Path to write JSON report (defaults under scratch/primary_sources_e2e/reports/)",
    )
    parser.add_argument(
        "--md-out",
        type=Path,
        default=None,
        help="Path to write Markdown report (defaults under scratch/primary_sources_e2e/reports/)",
    )
    parser.add_argument(
        "--no-reports",
        action="store_true",
        help="Skip writing JSON and Markdown reports",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=REPO_ROOT,
        help="Repository root path (default: current checkout)",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_arg_parser()
    args = parser.parse_args(argv)
    if args.partial_ok and args.mode == "strict":
        print(
            "[primary_sources_e2e] ERROR: --mode strict and --partial-ok are mutually exclusive",
            file=sys.stderr,
        )
        return 2
    mode = "partial" if args.partial_ok else (args.mode or "strict")
    repo_root = args.repo_root.resolve()

    report = run_suite(
        repo_root=repo_root,
        tier=args.tier,
        mode=mode,
        pillar=args.pillar,
        check_id=args.check_id,
        include_anchors=args.include_anchors,
        include_cross_pillar=args.include_cross_pillar,
        deep_replay=args.deep_replay,
    )

    if report.get("error"):
        print(f"[primary_sources_e2e] ERROR: {report['error']}", file=sys.stderr)
        return int(report["exit_code"])

    if not args.no_reports:
        reports_dir = repo_root / "scratch" / "primary_sources_e2e" / "reports"
        reports_dir.mkdir(parents=True, exist_ok=True)
        json_out = args.json_out or (reports_dir / f"e2e_report_tier_{args.tier}_{mode}.json")
        md_out = args.md_out or (reports_dir / f"e2e_report_tier_{args.tier}_{mode}.md")
        json_out.parent.mkdir(parents=True, exist_ok=True)
        md_out.parent.mkdir(parents=True, exist_ok=True)
        json_out.write_text(json.dumps(report, indent=2), encoding="utf-8")
        md_out.write_text(render_markdown_report(report), encoding="utf-8")

    s = report["summary"]
    if report["partial_banner"]:
        print("[PARTIAL REPO STATE — NOT FULL ACCEPTANCE]")
    for o in report["outcomes"]:
        print(f"[{o['status']}] {o['check_id']} ({o['milestone']}/{o['pillar']}): {o['summary']}")
    print(
        f"[primary_sources_e2e] mode={mode} tier={args.tier} pillar={args.pillar} "
        f"passed={s['passed']} failed={s['failed']} pending={s['pending']} exit={report['exit_code']}"
    )
    return int(report["exit_code"])


if __name__ == "__main__":
    raise SystemExit(main())
