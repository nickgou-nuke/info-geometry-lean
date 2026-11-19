"""Execution engine & standalone CLI for the 218-check R1/R2/R3 E2E suite."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

from tests.reconciliation_e2e import REPO_ROOT, REPORTS_DIR, VALID_MODES, get_mode
from tests.reconciliation_e2e.lean_probes import (
    ProbeResult,
    discover_candidate_owners,
    run_milestone_contract_probe,
    run_r1_baseline_probe,
    run_r2_r1r2_baseline_probe,
    run_r3_baseline_probe,
)
from tests.reconciliation_e2e.manifest import (
    ALL_BASELINE_OWNER_FILES,
    CHECKS,
    F2_5_BASELINE_ALL,
    F2_5_ERLANGEN_PROGRAM_MODULES,
    M1_OWNER_FILES,
    M2_OWNER_FILES,
    M3_OWNER_FILES,
    CheckSpec,
    get_summary_counts,
    is_active_for_mode,
)
from tests.reconciliation_e2e.quality_runner import (
    ToolResult,
    assert_quality_bundle_passed,
    check_apache_headers,
    check_native_decide,
    check_prop_wrappers,
    lean_path_to_module,
    run_axiom_audit,
    run_axiom_check,
    run_axiom_index,
    run_detect_hollow_theorems,
    run_opengauss_screener,
    run_placeholder_audit,
    run_quality_bundle,
    run_repo_lean_scope_audit,
    run_semantic_content_audit,
    run_semantic_vacuity_gate,
    run_unified_gate,
    prewarm_axiom_index,
)
from tests.reconciliation_e2e.rubric_checker import (
    check_dual_lake_targets,
    check_duplicate_onsager_types,
    check_infogeometry_barrel_imports,
    check_monodromy_vacuity,
    check_src_parity_ncg,
    detect_bucket3_overclaims_in_text,
    find_master_spec_docs,
    verify_baseline_rubric_coverage,
    verify_doc_symbols,
    verify_erlangen_1872_primary_source,
    verify_klein_grassmann_plucker_docs,
    verify_no_bucket3_overclaims,
    verify_spec_docs_present,
)


@dataclass
class CheckOutcome:
    check_id: str
    tier: int
    feature: str
    gate: str
    bucket: str
    status: str  # "PASS" | "FAIL" | "SKIPPED"
    duration_s: float
    summary: str
    details: dict[str, Any]


def _run_probe_by_name(name: str) -> ProbeResult:
    if name == "r1_baseline":
        return run_r1_baseline_probe()
    if name == "r3_baseline":
        return run_r3_baseline_probe()
    if name == "r2_r1r2_baseline":
        return run_r2_r1r2_baseline_probe()
    raise ValueError(f"Unknown baseline probe: {name!r}")


def _collect_m1_m2_m3_files() -> list[str]:
    base = (
        list(M1_OWNER_FILES)
        + list(M2_OWNER_FILES)
        + list(M3_OWNER_FILES)
        + list(F2_5_BASELINE_ALL)
        + [
            "lean/InfoGeometry/OperatorAlgebra/ErlangenDoubleCylinderSymmetryInvariants.lean",
            "lean/InfoGeometry/Topology/CliffordMobiusDeRhamMonodromy.lean",
        ]
    )
    extra = discover_candidate_owners(
        (),
        (
            "DerivationExteriorCalculus",
            "MaurerCartanTower",
            "CoordinateLessCliffordInvariance",
            "SplitCliffordTowerUnification",
            "PluckerGrassmann",
            "GrassmannSubspace",
            "SmoothPrincipalCartan",
            "GrassmannPluckerKleinFunctorialBridges",
            "ErlangenProgram",
            "KleinErlangen",
            "Erlangen20OperatorGeometry",
        ),
    )
    # Keep only files that actually exist on disk
    all_files = [f for f in dict.fromkeys(base + extra) if (REPO_ROOT / f).is_file()]
    return all_files


def _check_test_default_lean_sources_invariant() -> tuple[bool, str]:
    """Verify no undeclared .lean files exist under tests/ matching test_default_lean_sources.py."""
    config = (REPO_ROOT / "lakefile.lean").read_text(encoding="utf-8")
    suite_match = re.search(
        r"lean_lib InfoGeometryTestSuite where\n(.*?)(?=^\S|\Z)", config, re.M | re.S
    )
    if suite_match is None:
        return False, "InfoGeometryTestSuite not found in lakefile.lean"
    suite_declared = set(re.findall(r"`([\w.]+)", suite_match.group(1)))
    opt_in: set[str] = set()
    for lib_name, lib_body in re.findall(
        r"^lean_lib (\w+) where\n(.*?)(?=^\S|\Z)", config, re.M | re.S
    ):
        if lib_name != "InfoGeometryTestSuite" and 'srcDir := "../tests"' in lib_body:
            opt_in.update(re.findall(r"`([\w.]+)", lib_body))
    existing = {
        ".".join(path.relative_to(REPO_ROOT / "tests").with_suffix("").parts)
        for path in (REPO_ROOT / "tests").rglob("*.lean")
    }
    declared = suite_declared | opt_in
    if declared != existing:
        return False, f"declared != existing: extra={sorted(existing - declared)}, missing={sorted(declared - existing)}"
    return True, f"declared == existing ({len(existing)} Lean test files)"


def _run_quality_split_opengauss(
    targets: list[str],
    opengauss_targets: list[str] | None,
    tag: str,
    strict_headers: bool,
) -> dict[str, ToolResult]:
    if not opengauss_targets or set(opengauss_targets) == set(targets):
        return run_quality_bundle(targets, tag, strict_headers=strict_headers)
    # Run standard bundle and replace opengauss_screener with scoped subset
    res = {
        "placeholder_audit": run_placeholder_audit(targets),
        "axiom_audit": run_axiom_audit(targets),
        "detect_hollow_theorems": run_detect_hollow_theorems(targets),
        "semantic_vacuity_gate": run_semantic_vacuity_gate(targets),
        "repo_lean_scope_audit": run_repo_lean_scope_audit(targets),
        "opengauss_screener": run_opengauss_screener(opengauss_targets),
        "apache_header_byte0": check_apache_headers(targets, strict_all=strict_headers),
        "native_decide_scan": check_native_decide(targets),
        "aggregate_prop_constructors": check_prop_wrappers(targets),
        "unified_gate": run_unified_gate(targets),
    }
    return res


_PREWARMED_MODES: set[str] = set()


def _ensure_axiom_index_prewarmed(mode: str) -> None:
    if mode in _PREWARMED_MODES:
        return
    _PREWARMED_MODES.add(mode)
    mods: list[str] = []
    for c in CHECKS:
        if is_active_for_mode(c, mode) and c.spec.get("kind") == "axiom_audit_modules":
            mods.extend(c.spec.get("modules", []))
    if mods:
        prewarm_axiom_index(mods)


def execute_check(check: CheckSpec, mode: str) -> CheckOutcome:
    t0 = time.monotonic()
    if not is_active_for_mode(check, mode):
        return CheckOutcome(
            check_id=check.check_id,
            tier=check.tier,
            feature=check.feature,
            gate=check.gate,
            bucket=check.bucket,
            status="SKIPPED",
            duration_s=0.0,
            summary=f"Gated on {check.gate}; skipped in mode={mode}",
            details={},
        )

    spec = check.spec
    kind = spec["kind"]
    try:
        if kind == "quality_and_probe":
            targets = list(spec["targets"])
            og_targets = spec.get("opengauss_targets")
            strict_headers = bool(spec.get("strict_headers", False))
            qres = _run_quality_split_opengauss(targets, og_targets, check.check_id, strict_headers)
            assert_quality_bundle_passed(qres, check.check_id)
            probe = _run_probe_by_name(spec["probe"])
            if not probe.passed:
                raise AssertionError(f"Probe {probe.probe_id} failed: {probe.summary}")
            summary = f"quality ok ({len(targets)} files) + {probe.probe_id} ok"
            details = {"quality": {k: v.summary for k, v in qres.items()}, "probe": probe.probe_path}

        elif kind == "axiom_audit_modules":
            _ensure_axiom_index_prewarmed(mode)
            modules = list(spec["modules"])
            ai = run_axiom_index(modules)
            if not ai.passed:
                raise AssertionError(f"axiom_index failed: {ai.summary}")
            probe = _run_probe_by_name(spec["probe"])
            if not probe.passed:
                raise AssertionError(f"Probe {probe.probe_id} failed: {probe.summary}")
            summary = f"axiom_index({len(modules)}) + {probe.probe_id} ok"
            details = {"axiom_index": ai.summary, "probe": probe.probe_path}

        elif kind == "baseline_probe":
            verify_file = REPO_ROOT / spec["verify_file"]
            if not verify_file.is_file():
                raise AssertionError(f"Missing baseline file: {spec['verify_file']}")
            txt = verify_file.read_text(encoding="utf-8", errors="replace")
            if not re.search(rf"\b{re.escape(spec['symbol'])}\b", txt):
                raise AssertionError(f"Symbol {spec['symbol']!r} missing from {spec['verify_file']}")
            probe = _run_probe_by_name(spec["probe"])
            if not probe.passed:
                raise AssertionError(f"Probe {probe.probe_id} failed: {probe.summary}")
            summary = f"{spec['symbol']} verified + {probe.probe_id} ok"
            details = {"verify_file": spec["verify_file"], "probe": probe.probe_path}

        elif kind == "baseline_wide_hygiene":
            targets = list(spec["targets"])
            pa = run_placeholder_audit(targets)
            aa = run_axiom_audit(targets)
            dh = run_detect_hollow_theorems(targets)
            sv = run_semantic_vacuity_gate(targets)
            nd = check_native_decide(targets)
            pw = check_prop_wrappers(targets)
            rc = verify_baseline_rubric_coverage()
            for r in (pa, aa, dh, sv, nd, pw):
                if not r.passed:
                    raise AssertionError(f"{r.name} failed: {r.summary}")
            if not rc["passed"]:
                raise AssertionError(f"Baseline rubric coverage failed: {rc}")
            summary = f"60 baseline owners clean; {rc['checked_items']} rubric items mapped"
            details = {"placeholder": pa.summary, "axiom_audit": aa.summary, "rubric_items": rc["checked_items"]}

        elif kind == "src_parity_ncg":
            parity = check_src_parity_ncg()
            if spec.get("expect_synced") and not parity["in_sync"]:
                raise AssertionError(f"src/ NCG parity out of sync: {parity}")
            if not (REPO_ROOT / "lean/InfoGeometry/NCG/NoncommutativeConnectionCurvature.lean").is_file():
                raise AssertionError("lean/ NCG/NoncommutativeConnectionCurvature.lean missing")
            summary = f"in_sync={parity['in_sync']}, missing_in_src={parity['missing_in_src']}"
            details = parity

        elif kind == "doc_symbol_exists" or kind == "file_symbol_exists":
            p = REPO_ROOT / spec["file"]
            if not p.is_file():
                raise AssertionError(f"Missing file: {spec['file']}")
            txt = p.read_text(encoding="utf-8", errors="replace")
            if not re.search(rf"\b{re.escape(spec['symbol'])}\b", txt):
                raise AssertionError(f"Symbol {spec['symbol']!r} not found in {spec['file']}")
            summary = f"verified `{spec['symbol']}` in {spec['file']}"
            details = {"file": spec["file"], "symbol": spec["symbol"]}

        elif kind == "default_lean_sources_clean":
            ok, msg = _check_test_default_lean_sources_invariant()
            if not ok:
                raise AssertionError(msg)
            summary = msg
            details = {}

        elif kind == "dual_mode_probe":
            probe = _run_probe_by_name(spec["phase0_probe"])
            if not probe.passed:
                raise AssertionError(f"Phase-0 probe {probe.probe_id} failed: {probe.summary}")
            if mode == "full" or mode.upper() == str(spec.get("full_gate", "")).upper():
                mprobe = run_milestone_contract_probe(check.check_id, spec)
                if not mprobe.passed:
                    raise AssertionError(f"Milestone contract failed: {mprobe.summary}")
                summary = f"{probe.probe_id} ok + milestone contract ok"
            else:
                summary = f"{probe.probe_id} ok (milestone portion gated on {spec.get('full_gate')})"
            details = {"phase0_probe": probe.probe_path}

        elif kind == "dual_mode_certification":
            for pname in ("r1_baseline", "r3_baseline", "r2_r1r2_baseline"):
                pr = _run_probe_by_name(pname)
                if not pr.passed:
                    raise AssertionError(f"Baseline probe {pname} failed: {pr.summary}")
            ok, msg = _check_test_default_lean_sources_invariant()
            if not ok:
                raise AssertionError(msg)
            if mode == "full":
                files = _collect_m1_m2_m3_files()
                mods = [lean_path_to_module(f) for f in files]
                bld = subprocess.run(
                    [sys.executable, "tools/infra/run_locked_lake_build.py", "--wait-for-build-lock", *mods],
                    cwd=REPO_ROOT,
                    capture_output=True,
                    text=True,
                    timeout=900,
                    check=False,
                )
                if bld.returncode != 0:
                    raise AssertionError(f"Locked lake build failed: {(bld.stderr or bld.stdout)[-400:]}")
                ac = run_axiom_check(mods)
                if not ac.passed:
                    raise AssertionError(f"axiom_check failed: {ac.summary}")
                summary = f"Full M4 build & axiom certification ok ({len(mods)} modules)"
            else:
                summary = f"Phase-0 probes (3/3) + {msg}"
            details = {"mode": mode}

        elif kind == "milestone_quality_and_probe":
            # M1/M2/M3 strict quality + contract probe
            probe = run_milestone_contract_probe(check.check_id, spec)
            if not probe.passed:
                raise AssertionError(probe.summary)
            raw_targets = list(spec.get("required_files", [])) + list(spec.get("candidate_files", [])) + list(probe.matched_files)
            targets = [f for f in dict.fromkeys(raw_targets) if (REPO_ROOT / f).is_file()]
            if targets:
                qres = run_quality_bundle(targets, check.check_id, strict_headers=True, include_sca=True)
                assert_quality_bundle_passed(qres, check.check_id)
                mods = [lean_path_to_module(f) for f in targets]
                ac = run_axiom_check(mods)
                ai = run_axiom_index(mods)
                if not ac.passed or not ai.passed:
                    raise AssertionError(f"Axiom closure failed: check={ac.summary}, index={ai.summary}")
            if spec.get("verify_erlangen_1872_docs"):
                erl = verify_erlangen_1872_primary_source(find_master_spec_docs())
                if not erl["passed"]:
                    raise AssertionError(f"Erlangen 1872 (ABN7632.0001.001) primary-source check failed: {erl}")
            summary = f"milestone quality + axiom + probe ok ({probe.probe_path})"
            details = {"probe": probe.probe_path}

        elif kind in ("contract_probe", "e2e_scenario"):
            probe = run_milestone_contract_probe(check.check_id, spec)
            if not probe.passed:
                raise AssertionError(probe.summary)
            summary = f"contract probe passed ({probe.probe_path})"
            details = {"probe": probe.probe_path}

        elif kind == "onsager_consolidation":
            targets = list(spec["targets"])
            qres = run_quality_bundle(targets, check.check_id, strict_headers=True)
            assert_quality_bundle_passed(qres, check.check_id)
            dups = check_duplicate_onsager_types()
            if not dups["passed"]:
                raise AssertionError(f"Duplicate TransportTensor/TimeReversal definitions remain: {dups['duplicates']}")
            summary = "Onsager headers clean & zero duplicate TransportTensor/TimeReversal"
            details = dups

        elif kind == "onsager_no_duplicates":
            dups = check_duplicate_onsager_types()
            if not dups["passed"]:
                raise AssertionError(f"Duplicate TransportTensor/TimeReversal definitions: {dups['duplicates']}")
            summary = f"Unique canonical owners: {dups['owners']}"
            details = dups

        elif kind == "monodromy_non_vacuous":
            mv = check_monodromy_vacuity()
            if not mv["passed"]:
                raise AssertionError(f"Vacuous rfl conjunctions remain in CliffordMobiusDeRhamMonodromy: {mv['vacuous_matches']}")
            summary = "Zero vacuous `(clsplit_succ_equiv n) = (clsplit_succ_equiv n) ∧` conjunctions"
            details = mv

        elif kind == "bucket3_honesty":
            has_bucket3_marker = False
            overclaim_findings: list[str] = []
            for rel in spec["files"]:
                full = REPO_ROOT / rel
                if not full.is_file():
                    raise AssertionError(f"Missing file: {rel}")
                txt = full.read_text(encoding="utf-8", errors="replace")
                overclaim_findings.extend(detect_bucket3_overclaims_in_text(rel, txt))
                if re.search(r"BUCKET\s*1\b[^\n]{0,120}(?:internal\s+Kasparov\s+product|C\*-correspondence\s+proved)|(?:internal\s+Kasparov\s+product|C\*-correspondence\s+proved)[^\n]{0,120}\[?\s*`?BUCKET\s*1\b`?\s*\]?", txt, re.I):
                    overclaim_findings.append(f"{rel}: falsely promotes BUCKET 3 Kasparov product / C*-correspondence to BUCKET 1")
                if re.search(r"\bBUCKET\s*3\b", txt, re.I):
                    has_bucket3_marker = True
            if overclaim_findings:
                raise AssertionError(f"BUCKET 3 overclaim(s): {overclaim_findings}")
            if not has_bucket3_marker:
                raise AssertionError(f"Missing explicit BUCKET 3 boundary marker in {spec['files']}")
            summary = "Right-B-module & Kasparov product BUCKET 3 boundaries honestly preserved"
            details = {"files": spec["files"], "has_bucket3_marker": has_bucket3_marker}

        elif kind == "rubric_spec_docs_present":
            res = verify_spec_docs_present(require_m1=True, require_m2=True, require_m3=True)
            if not res["passed"]:
                raise AssertionError(f"Spec docs check failed: {res}")
            erl = verify_erlangen_1872_primary_source(res["present"])
            if not erl["passed"]:
                raise AssertionError(f"Erlangen 1872 (ABN7632.0001.001) primary-source check failed: {erl}")
            kgp = verify_klein_grassmann_plucker_docs(res["present"])
            if not kgp["passed"]:
                raise AssertionError(f"Klein-Grassmann-Plucker Bridges A/B/C spec check failed: {kgp}")
            summary = f"Spec docs present, BUCKET-tagged, Erlangen 1872 & Grassmann/Plucker cited: {res['present']}"
            details = {"docs": res, "erlangen_1872": erl, "klein_grassmann_plucker": kgp}

        elif kind == "barrel_and_src_sync":
            mods = [lean_path_to_module(f) for f in _collect_m1_m2_m3_files()]
            bar = check_infogeometry_barrel_imports(mods)
            if not bar["passed"]:
                raise AssertionError(f"InfoGeometry.lean missing barrel imports: {bar['missing']}")
            parity = check_src_parity_ncg()
            if not parity["in_sync"]:
                raise AssertionError(f"src/ NCG parity still lagging: {parity['missing_in_src']}")
            summary = f"Barrel imports ({bar['imported_count']}) & src/ NCG parity synced"
            details = {"barrel": bar, "parity": parity}

        elif kind == "m1_m2_m3_axiom_closure":
            files = _collect_m1_m2_m3_files()
            mods = [lean_path_to_module(f) for f in files]
            ac = run_axiom_check(mods)
            ai = run_axiom_index(mods)
            if not ac.passed:
                raise AssertionError(f"axiom_check failed: {ac.summary}")
            if not ai.passed:
                raise AssertionError(f"axiom_index failed: {ai.summary}")
            summary = f"axiom_check & axiom_index clean across {len(mods)} modules"
            details = {"axiom_check": ac.summary, "axiom_index": ai.summary}

        elif kind == "m1_m2_m3_strict_quality":
            files = _collect_m1_m2_m3_files()
            qres = run_quality_bundle(files, check.check_id, strict_headers=True, include_sca=True)
            assert_quality_bundle_passed(qres, check.check_id)
            summary = f"Strict quality + SCA + byte-0 Apache headers passed across {len(files)} files"
            details = {k: v.summary for k, v in qres.items()}

        elif kind == "rubric_doc_symbol_fidelity":
            docs = find_master_spec_docs()
            if not docs:
                raise AssertionError("No M1/M2/M3 reconciliation spec docs found under docs/")
            res = verify_doc_symbols(docs)
            if not res["passed"]:
                raise AssertionError(f"Doc symbol fidelity failed: {res}")
            summary = f"Verified doc symbols across {len(res['checked_docs'])} spec docs"
            details = res

        elif kind == "rubric_no_bucket3_overclaims":
            docs = find_master_spec_docs() + [
                "docs/ERLANGEN_2_THEOREM_HONEST_MANIFEST.md",
                "docs/OPEN_DEBT_PROBLEMS.md",
                "docs/KASPAROV_KREIN_RECONCILIATION_PLAN.md",
            ]
            lean_files = _collect_m1_m2_m3_files()
            res = verify_no_bucket3_overclaims(docs, lean_files)
            if not res["passed"]:
                raise AssertionError(f"BUCKET 3 overclaim(s) detected: {res['findings']}")
            summary = f"Zero BUCKET 3 overclaims across {len(docs)} docs and {len(lean_files)} Lean files"
            details = res

        elif kind == "dual_lake_targets":
            mods = [lean_path_to_module(f) for f in _collect_m1_m2_m3_files()]
            res = check_dual_lake_targets(mods)
            if not res["passed"]:
                raise AssertionError(f"Dual-lane Lake target check failed: {res}")
            summary = f"Dual-lane targets resolved ({len(mods)} modules)"
            details = res

        elif kind == "full_rubric_audit":
            b_cov = verify_baseline_rubric_coverage()
            s_pres = verify_spec_docs_present(require_m1=True, require_m2=True, require_m3=True)
            docs = find_master_spec_docs()
            sym = verify_doc_symbols(docs) if docs else {"passed": False, "error": "no spec docs"}
            honest = verify_no_bucket3_overclaims(docs)
            erl = verify_erlangen_1872_primary_source(docs)
            kgp = verify_klein_grassmann_plucker_docs(docs)
            if not b_cov["passed"]:
                raise AssertionError(f"Rubric owner coverage failed: {b_cov}")
            if not s_pres["passed"]:
                raise AssertionError(f"Spec docs check failed: {s_pres}")
            if not sym["passed"]:
                raise AssertionError(f"Doc symbol fidelity failed: {sym}")
            if not honest["passed"]:
                raise AssertionError(f"BUCKET 3 overclaim failed: {honest}")
            if not erl["passed"]:
                raise AssertionError(f"Erlangen 1872 (ABN7632.0001.001) primary-source check failed: {erl}")
            if not kgp["passed"]:
                raise AssertionError(f"Klein-Grassmann-Plucker Bridges A/B/C check failed: {kgp}")
            summary = f"All {b_cov['checked_items']} rubric items verified with BUCKET 1/2/3, Erlangen 1872 & Grassmann/Plucker honesty"
            details = {"rubric": b_cov, "docs": s_pres, "symbols": sym, "erlangen_1872": erl, "klein_grassmann_plucker": kgp}

        elif kind == "f25_baseline_hygiene":
            targets = list(spec["targets"])
            compiled_targets = list(spec["compiled_targets"])
            missing_disk = [f for f in targets if not (REPO_ROOT / f).is_file()]
            if missing_disk:
                raise AssertionError(f"Missing F2.5 Grassmann/Plucker files: {missing_disk}")
            pa = run_placeholder_audit(targets)
            aa = run_axiom_audit(targets)
            nd = check_native_decide(targets)
            hdr = check_apache_headers(targets, strict_all=False)
            for r in (pa, aa, nd, hdr):
                if not r.passed:
                    raise AssertionError(f"{r.name} failed on F2.5 files: {r.summary}")
            missing_oleans = [
                f for f in compiled_targets
                if not (REPO_ROOT / ".lake/build/lib/lean" / Path(f).relative_to("lean").with_suffix(".olean")).is_file()
            ]
            if missing_oleans:
                raise AssertionError(f"Expected baseline compiled F2.5 .oleans missing: {missing_oleans}")
            summary = f"{len(targets)} Grassmann/Plucker files clean; {len(compiled_targets)} compiled .oleans verified"
            details = {"placeholder": pa.summary, "axiom_audit": aa.summary, "headers": hdr.summary}

        elif kind == "f25_grassmann_1862_baseline":
            doc = REPO_ROOT / "docs/GRASSMANN_AUSDEHNUNGSLEHRE_1862_ENDMATTER_EPISTEMIC_COMPILATION.md"
            if not doc.is_file():
                raise AssertionError("Missing docs/GRASSMANN_AUSDEHNUNGSLEHRE_1862_ENDMATTER_EPISTEMIC_COMPILATION.md")
            core = [
                "lean/InfoGeometry/Projective/KleinQuadric.lean",
                "lean/InfoGeometry/Projective/KleinQuadricPlucker.lean",
                "lean/InfoGeometry/Projective/GrassmannAusdehnungslehreRegressiveShadow.lean",
                "lean/InfoGeometry/Canonical/GrassmannPfaffianDarbouxAlgebra.lean",
            ]
            pa = run_placeholder_audit(core)
            aa = run_axiom_audit(core)
            if not pa.passed or not aa.passed:
                raise AssertionError(f"Core F2.5 baseline hygiene failed: {pa.summary}; {aa.summary}")
            summary = f"Grassmann 1862 doc + 4 core .olean owners clean ({pa.summary})"
            details = {"doc": doc.name, "placeholder": pa.summary, "axiom_audit": aa.summary}

        elif kind == "rubric_f25_grassmann_citations":
            docs = find_master_spec_docs()
            res = verify_klein_grassmann_plucker_docs(docs)
            if not res["passed"]:
                raise AssertionError(f"Klein 1872 Grassmann [6,7,8] / Bridges A-C check failed: {res}")
            summary = f"Klein 1872 Grassmann [6,7,8] & Bridges A/B/C verified in {res['checked_docs']}"
            details = res

        elif kind == "f25_all_oleans_compiled":
            targets = list(spec["targets"])
            missing_oleans = [
                f for f in targets
                if not (REPO_ROOT / ".lake/build/lib/lean" / Path(f).relative_to("lean").with_suffix(".olean")).is_file()
            ]
            if missing_oleans:
                raise AssertionError(f"Uncompiled F2.5 Grassmann/Plucker/ErlangenProgram modules: {missing_oleans}")
            og = run_opengauss_screener(targets)
            if not og.passed:
                raise AssertionError(f"opengauss_screener failed on F2.5 modules: {og.summary}")
            mods = [lean_path_to_module(f) for f in targets]
            ac = run_axiom_check(mods)
            ai = run_axiom_index(mods)
            if not ac.passed or not ai.passed:
                raise AssertionError(f"Axiom closure failed on F2.5 modules: check={ac.summary}, index={ai.summary}")
            summary = f"All {len(targets)} F2.5 Grassmann/Plucker/ErlangenProgram .oleans compiled, OpenGauss & axiom-clean"
            details = {"opengauss": og.summary, "axiom_check": ac.summary, "axiom_index": ai.summary}

        else:
            raise ValueError(f"Unknown check kind: {kind!r}")

        return CheckOutcome(
            check_id=check.check_id,
            tier=check.tier,
            feature=check.feature,
            gate=check.gate,
            bucket=check.bucket,
            status="PASS",
            duration_s=round(time.monotonic() - t0, 3),
            summary=summary,
            details=details,
        )
    except Exception as exc:
        return CheckOutcome(
            check_id=check.check_id,
            tier=check.tier,
            feature=check.feature,
            gate=check.gate,
            bucket=check.bucket,
            status="FAIL",
            duration_s=round(time.monotonic() - t0, 3),
            summary=str(exc),
            details={"error": str(exc)},
        )


def run_suite(
    mode: str = "baseline",
    *,
    tier_filter: int | None = None,
    check_id_filter: str | None = None,
    write_reports: bool = True,
) -> dict[str, Any]:
    mode = get_mode(mode)
    selected = [
        c
        for c in CHECKS
        if (tier_filter is None or c.tier == tier_filter)
        and (check_id_filter is None or c.check_id == check_id_filter)
    ]
    outcomes = [execute_check(c, mode) for c in selected]
    passed = sum(1 for o in outcomes if o.status == "PASS")
    failed = sum(1 for o in outcomes if o.status == "FAIL")
    skipped = sum(1 for o in outcomes if o.status == "SKIPPED")

    report = {
        "mode": mode,
        "manifest_counts": get_summary_counts(),
        "executed": len(outcomes),
        "passed": passed,
        "failed": failed,
        "skipped": skipped,
        "outcomes": [asdict(o) for o in outcomes],
    }

    if write_reports:
        REPORTS_DIR.mkdir(parents=True, exist_ok=True)
        json_path = REPORTS_DIR / f"e2e_report_{mode}.json"
        md_path = REPORTS_DIR / f"e2e_report_{mode}.md"
        json_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

        lines = [
            f"# Reconciliation E2E Report (`mode={mode}`)",
            "",
            f"- **Manifest Totals**: {report['manifest_counts']}",
            f"- **Executed**: {len(outcomes)} | **PASS**: {passed} | **FAIL**: {failed} | **SKIPPED (gated)**: {skipped}",
            "",
            "| Check ID | Tier | Feature | Gate | Bucket | Status | Duration (s) | Summary |",
            "|---|---|---|---|---|---|---:|---|",
        ]
        for o in outcomes:
            short_sum = o.summary.replace("\n", " ")[:120]
            lines.append(
                f"| `{o.check_id}` | {o.tier} | `{o.feature}` | `{o.gate}` | `{o.bucket}` | **{o.status}** | {o.duration_s:.2f} | {short_sum} |"
            )
        md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run R1/R2/R3 reconciliation E2E suite")
    parser.add_argument("--mode", choices=VALID_MODES, default="baseline")
    parser.add_argument("--tier", type=int, choices=(1, 2, 3, 4), default=None)
    parser.add_argument("--check-id", type=str, default=None)
    args = parser.parse_args(argv)

    report = run_suite(
        args.mode,
        tier_filter=args.tier,
        check_id_filter=args.check_id,
        write_reports=True,
    )
    print(
        f"[reconciliation_e2e] mode={report['mode']} total={report['executed']} "
        f"pass={report['passed']} fail={report['failed']} skipped={report['skipped']}"
    )
    if report["failed"] > 0:
        for o in report["outcomes"]:
            if o["status"] == "FAIL":
                print(f"  FAIL {o['check_id']}: {o['summary']}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
