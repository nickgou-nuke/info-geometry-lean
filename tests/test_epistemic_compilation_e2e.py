#!/usr/bin/env python3
"""Pure-stdlib 4-tier opaque-box E2E acceptance suite for Drive 13ED/12bA/1wzq & AI Studio 1v8J/1VUS epistemic compilation."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import unittest
import unittest.mock
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

# Bootstrap repo root on sys.path for direct script execution
_THIS_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_THIS_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_THIS_REPO_ROOT))

from tests.epistemic_compilation_e2e import (  # noqa: E402
    BASELINE_COMPILATION_DOC_REL,
    BASELINE_SMOKE_LEAN_REL,
    CheckOutcome,
    DEFAULT_REPORTS_DIR,
    REPO_ROOT,
    REQUIRED_LEAN_COPYRIGHT_HEADER,
    SOURCE_A_ID,
    SOURCE_B_ID,
    SOURCE_C_ID,
    SOURCE_D_ID,
    SOURCE_E_ID,
)
from tests.epistemic_compilation_e2e.epistemic_checks import (  # noqa: E402
    DiscoveredArtifacts,
    ParsedClaimRow,
    _split_markdown_table_row,
    check_t1_ec_01_claim_ledger,
    check_t1_ec_04_causal_poset_dag,
    check_t1_ec_05_intent_envelope_schema,
    discover_artifacts,
    kahn_topological_sort,
    parse_claim_ledgers,
    parse_mermaid_dag,
    run_tier1_epistemic_checks,
)
from tests.epistemic_compilation_e2e.intake_checks import (  # noqa: E402
    _has_explicit_blocker_report,
    check_t1_intake_01_source_a,
    check_t1_intake_02_source_b,
    check_t1_intake_06_access_blocker_note,
    check_t1_intake_07_additional_sources_f10,
    resolve_effective_source_b_mode,
    run_tier1_intake_checks,
)
from tests.epistemic_compilation_e2e.lean_checks import (  # noqa: E402
    ResolvedTarget,
    _classify_suffices_prop_detail,
    _find_decl_return_type_and_split,
    _has_concrete_model_args,
    _subst_lean_expr_capture_avoiding,
    check_t1_lean_01_copyright_header,
    check_t1_lean_02_style_and_module_doc,
    check_t1_lean_03_theorem_lint,
    check_t1_lean_04_placeholder_and_vacuity,
    check_t1_lean_05_workspace_and_declarations,
    extract_non_opaque_lean_declarations,
    lean_short_name,
    resolve_targets,
    run_tier1_lean_checks,
    scan_native_decide_and_vacuous_true,
    scan_parameterized_prop_bundlers,
    split_lean_qual_ident,
    strip_lean_comments_and_strings,
)
from tests.epistemic_compilation_e2e.tier2_tier3_tier4 import (  # noqa: E402
    _extract_obj_module_stems,
    _porcelain_path,
    build_tier4_commands,
    check_t2_bnd_01_turn10_drive_attachment,
    check_t2_bnd_02_turn24_indented_fence,
    check_t2_bnd_03_turn_delta_separation,
    check_t2_bnd_04_riemann_masullo_quarantine,
    check_t2_bnd_05_colimit_rh_bucket3_enforcement,
    check_t2_bnd_06_countermodel_quarantine,
    check_t2_bnd_07_bucket_label_disjointness,
    check_t3_cons_02_contracts_to_lean_declarations,
    check_t3_cons_03_imports_isolation,
    check_t3_cons_05_audit_report_hashes,
    parse_axiom_check_json_output,
    run_tier2_checks,
    run_tier3_checks,
    run_tier4_checks,
    validate_axiom_check_entries,
)


def _extract_expected_decls_from_artifacts(artifacts: DiscoveredArtifacts) -> dict[str, list[str]]:
    expected: dict[str, list[str]] = {}
    for env_path in artifacts.intent_envelopes:
        data = json.loads(env_path.read_text(encoding="utf-8"))
        formal_objs = data.get("formal_objects", {})
        acc_thms = data.get("acceptance_theorems", {})
        mod_map: dict[str, str] = {}
        for art in data.get("owner_search", {}).get("target_artifacts", []):
            if isinstance(art, str) and art.startswith("lean/") and art.endswith(".lean"):
                mod = art.removeprefix("lean/").removesuffix(".lean").replace("/", ".")
                mod_map[Path(art).stem] = mod
        known_stems = set(mod_map.keys())
        for lane, thms in acc_thms.items():
            if not isinstance(thms, list) or not thms:
                continue
            objs = formal_objs.get(lane, [])
            stems = _extract_obj_module_stems(objs if isinstance(objs, list) else [], known_stems)
            lane_mods = [mod_map[s] for s in stems if s in mod_map]
            if lane_mods:
                key = lane_mods[0] if len(lane_mods) == 1 else ",".join(lane_mods)
                bucket = expected.setdefault(key, [])
                for t in thms:
                    if t not in bucket:
                        bucket.append(t)
    for c_path in artifacts.contract_jsons:
        data = json.loads(c_path.read_text(encoding="utf-8"))
        tmod = data.get("target_module")
        tthms = data.get("acceptance_theorems")
        if isinstance(tmod, str) and tmod.startswith("InfoGeometry.") and isinstance(tthms, list) and tthms:
            bucket = expected.setdefault(tmod, [])
            for t in tthms:
                if t not in bucket:
                    bucket.append(t)
    return expected


def run_acceptance_pipeline(
    *,
    repo_root: Path = REPO_ROOT,
    tier: str = "all",
    source_b_mode: str = "auto",
    raw_targets: list[str] | None = None,
    manifest_args: list[str] | None = None,
    dry_run: bool = False,
    all_sources: bool = False,
) -> dict[str, Any]:
    """Execute Tiers 1-4 opaque-box checks and return structured report dict."""
    artifacts, manifest_errors = discover_artifacts(
        repo_root,
        manifest_args,
        baseline_only=(source_b_mode == "baseline45" and not manifest_args),
        raw_targets=raw_targets,
    )
    if manifest_errors:
        return {
            "error": "; ".join(manifest_errors),
            "exit_code": 2,
            "outcomes": [],
            "summary": {"passed": 0, "failed": 0, "skipped": 0},
        }

    effective_mode = resolve_effective_source_b_mode(repo_root, source_b_mode)
    raw_target_list = list(raw_targets or [])
    if not raw_target_list:
        if artifacts.explicit_targets:
            raw_target_list = list(artifacts.explicit_targets)
        elif dry_run or effective_mode == "baseline45":
            raw_target_list = [BASELINE_SMOKE_LEAN_REL]

    targets, target_errors = resolve_targets(repo_root, raw_target_list)
    if target_errors:
        return {
            "error": "; ".join(target_errors),
            "exit_code": 2,
            "outcomes": [],
            "summary": {"passed": 0, "failed": 0, "skipped": 0},
        }

    need_tier4_live = (tier in ("4", "all")) and not dry_run
    if need_tier4_live:
        if not targets:
            return {
                "error": "Live Tier 4 mode requires --targets or manifest target_artifacts",
                "exit_code": 2,
                "outcomes": [],
                "summary": {"passed": 0, "failed": 0, "skipped": 0},
            }
        missing = [t.rel_path for t in targets if not t.exists]
        if missing:
            return {
                "error": f"Live Tier 4 target file(s) missing on disk: {missing}",
                "exit_code": 2,
                "outcomes": [],
                "summary": {"passed": 0, "failed": 0, "skipped": 0},
            }

    strict_live = (effective_mode == "live84") or need_tier4_live

    outcomes: list[CheckOutcome] = []
    rows: list[ParsedClaimRow] = []

    if tier in ("1", "2", "3", "all"):
        ec_outcomes, rows = run_tier1_epistemic_checks(repo_root, artifacts, effective_mode)
    else:
        ec_outcomes = []

    if tier in ("1", "all"):
        outcomes.extend(
            run_tier1_intake_checks(
                repo_root,
                artifacts.compilation_docs,
                effective_mode,
                manifest_paths=artifacts.manifest_paths,
                require_all_sources=all_sources,
            )
        )
        outcomes.extend(ec_outcomes)
        expected_decls = _extract_expected_decls_from_artifacts(artifacts)
        outcomes.extend(
            run_tier1_lean_checks(
                repo_root,
                targets,
                strict_live=strict_live,
                expected_decls_by_module=expected_decls,
            )
        )

    if tier in ("2", "all"):
        outcomes.extend(run_tier2_checks(repo_root, artifacts, rows, targets, effective_mode))

    if tier in ("3", "all"):
        outcomes.extend(run_tier3_checks(repo_root, artifacts, rows, targets, effective_mode))

    if tier in ("4", "all"):
        outcomes.extend(run_tier4_checks(repo_root, targets, dry_run=dry_run))

    passed = sum(1 for o in outcomes if o.status == "PASS")
    failed = sum(1 for o in outcomes if o.status == "FAIL")
    skipped = sum(1 for o in outcomes if o.status == "SKIP")
    exit_code = 1 if failed > 0 else 0
    return {
        "generated_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "tier": tier,
        "requested_source_b_mode": source_b_mode,
        "effective_source_b_mode": effective_mode,
        "dry_run": dry_run,
        "all_sources": all_sources,
        "targets": [t.rel_path for t in targets],
        "outcomes": [o.to_dict() for o in outcomes],
        "summary": {"passed": passed, "failed": failed, "skipped": skipped, "total": len(outcomes)},
        "exit_code": exit_code,
    }


def render_markdown_report(report: dict[str, Any]) -> str:
    s = report["summary"]
    lines = [
        "# Epistemic Compilation E2E Verification Report",
        "",
        f"- Generated at: `{report.get('generated_at')}`",
        f"- Tier: `{report.get('tier')}` | Source B mode: `{report.get('effective_source_b_mode')}` | Dry-run: `{report.get('dry_run')}`",
        f"- Targets: `{len(report.get('targets', []))}`",
        f"- Result: **passed={s['passed']}**, **failed={s['failed']}**, **skipped={s['skipped']}** (exit `{report['exit_code']}`)",
        "",
        "| Check ID | Tier | Feature | Status | Summary |",
        "|---|---:|---|---|---|",
    ]
    for o in report.get("outcomes", []):
        lines.append(f"| `{o['check_id']}` | {o['tier']} | {o['feature']} | **{o['status']}** | {o['summary']} |")
    lines.append("")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Pure-stdlib unittest.TestCase Suite (--self-test & unittest/pytest discovery)
# ---------------------------------------------------------------------------


class TestEpistemicCompilationE2E(unittest.TestCase):
    """Self-contained baseline + synthetic negative/boundary E2E tests (zero lake build)."""

    def test_zero_lean_files_under_tests_epistemic_package(self) -> None:
        pkg_dir = Path(__file__).resolve().parent / "epistemic_compilation_e2e"
        self.assertTrue(pkg_dir.is_dir())
        self.assertEqual(list(pkg_dir.rglob("*.lean")), [])

    def test_tier1_baseline_intake_and_f10_five_source_synthetic(self) -> None:
        artifacts, errs = discover_artifacts(REPO_ROOT, baseline_only=True)
        self.assertEqual(errs, [])
        outcomes = run_tier1_intake_checks(
            REPO_ROOT,
            artifacts.compilation_docs,
            "baseline45",
            manifest_paths=artifacts.manifest_paths,
            require_all_sources=False,
        )
        for o in outcomes:
            self.assertEqual(o.status, "PASS", msg=f"{o.check_id}: {o.summary}")

        # Negative test: corrupted Source A SHA256/bytes fails T1-INTAKE-01
        with tempfile.TemporaryDirectory(prefix="ec_neg_src_a_") as td:
            root = Path(td)
            p = root / "cached" / "drive_docs" / f"{SOURCE_A_ID}.md"
            p.parent.mkdir(parents=True)
            p.write_text("corrupted\n", encoding="utf-8")
            bad_a = check_t1_intake_01_source_a(root)
            self.assertEqual(bad_a.status, "FAIL")

        # Negative test: missing Sign-In blocker fails T1-INTAKE-06
        with tempfile.TemporaryDirectory(prefix="ec_neg_blk_") as td:
            doc = Path(td) / "comp.md"
            doc.write_text("No access notes here.\n", encoding="utf-8")
            bad_blk = check_t1_intake_06_access_blocker_note(Path(td), [doc], "live84")
            self.assertEqual(bad_blk.status, "FAIL")

        # F10 5-source synthetic test: accessible Drive C + AI Studio D + blocker-reported E
        with tempfile.TemporaryDirectory(prefix="ec_f10_ok_") as td:
            root = Path(td)
            c_bytes = b"Drive source C content\nline 2\n"
            c_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            c_path.parent.mkdir(parents=True)
            c_path.write_bytes(c_bytes)
            c_sha = hashlib.sha256(c_bytes).hexdigest()

            d_payload = {
                "runSettings": {},
                "systemInstruction": {},
                "chunkedPrompt": {
                    "chunks": [
                        {"role": "user", "text": "Hello $x^2$", "createTime": "2026-11-22T10:00:00Z"},
                        {"role": "model", "text": "Reply $y=1$", "createTime": "2026-11-22T10:01:00Z"},
                    ]
                },
            }
            d_bytes = json.dumps(d_payload).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            extract_out = root / "cached" / "aistudio_extracts"
            extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
            proc = subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(extract_out)],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            self.assertEqual(proc.returncode, 0)

            m1b_doc = root / "docs" / "M1B_COMPILATION.md"
            m1b_doc.parent.mkdir(parents=True)
            m1b_doc.write_text(
                f"# M1b Provenance\n"
                f"- Source C `{SOURCE_C_ID}`: {len(c_bytes)} bytes, 2 lines, sha256 `{c_sha}`\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 2 chunks, sha256 `{d_sha}`\n"
                f"- Source E `{SOURCE_E_ID}`: HTTP 403 / Google Accounts sign-in HTML blocker (inaccessible without browser session)\n\n"
                f"| Claim ID | Source Provenance | Candidate Statement | Carrier | Classification & Bucket | Notes |\n"
                f"|---|---|---|---|---|---|\n"
                f"| `CDE-01` | Source C/D | Sample finite identity | `Ring R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                f"| `CDE-02` | Source D | Unbounded continuum debt | `Infinite` | `[bucket_3_open_debt]` (`BUCKET 3`) | open debt |\n",
                encoding="utf-8",
            )
            ok_f10 = check_t1_intake_07_additional_sources_f10(
                root,
                [m1b_doc],
                [],
                "live84",
                require_all_sources=True,
                extract_script_override=extract_script,
            )
            self.assertEqual(ok_f10.status, "PASS", msg=ok_f10.summary)

            # Negative: HTML Google Sign-In saved for Source E without blocker note MUST FAIL
            e_html = root / "cached" / f"download_{SOURCE_E_ID}.md"
            e_html.write_text("<!DOCTYPE html><html><title>Google Accounts Sign in</title></html>", encoding="utf-8")
            m1b_doc.write_text(
                f"- Source C `{SOURCE_C_ID}`: {len(c_bytes)} bytes, 2 lines, sha256 `{c_sha}`\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 2 chunks, sha256 `{d_sha}`\n",
                encoding="utf-8",
            )
            bad_f10 = check_t1_intake_07_additional_sources_f10(
                root,
                [m1b_doc],
                [],
                "live84",
                require_all_sources=True,
                extract_script_override=extract_script,
            )
            self.assertEqual(bad_f10.status, "FAIL")

    def test_tier1_baseline_epistemic_compilation_and_negatives(self) -> None:
        artifacts, errs = discover_artifacts(REPO_ROOT, baseline_only=True)
        self.assertEqual(errs, [])
        outcomes, rows = run_tier1_epistemic_checks(REPO_ROOT, artifacts, "baseline45")
        for o in outcomes:
            self.assertEqual(o.status, "PASS", msg=f"{o.check_id}: {o.summary}")
        self.assertGreaterEqual(len(rows), 74)

        with tempfile.TemporaryDirectory(prefix="ec_neg_ec_") as td:
            root = Path(td)
            # Negative: cycle in Mermaid DAG fails T1-EC-04
            cyc_doc = root / "cyc.md"
            cyc_doc.write_text("```mermaid\nflowchart TD\n  A --> B\n  B --> A\n```\n", encoding="utf-8")
            self.assertEqual(check_t1_ec_04_causal_poset_dag([cyc_doc]).status, "FAIL")

            # Negative: missing label fails T1-EC-01
            bad_ledger = root / "ledger.md"
            bad_ledger.write_text(
                "| Claim ID | Source Provenance | Candidate Statement | Carrier | Kind | Classification | Notes |\n"
                "|---|---|---|---|---|---|---|\n"
                "| `SX-01` | Turn 1 | x = x | Ring | thm | BUCKET 1 | missing label |\n",
                encoding="utf-8",
            )
            ec01, _ = check_t1_ec_01_claim_ledger(root, [bad_ledger])
            self.assertEqual(ec01.status, "FAIL")

            # Negative: intent envelope missing acceptance_theorems fails T1-EC-05
            bad_env = root / "env.json"
            bad_env.write_text(json.dumps({"schema": "info_geometry.qms.intent_envelope.v1", "concept_id": "X"}), encoding="utf-8")
            art_bad = DiscoveredArtifacts([], [bad_env], [], [], [], [], [])
            self.assertEqual(check_t1_ec_05_intent_envelope_schema(art_bad).status, "FAIL")

    def test_tier1_lean_gates_synthetic_valid_and_broken_fixtures(self) -> None:
        with tempfile.TemporaryDirectory(prefix="ec_lean_fix_") as td:
            root = Path(td)
            valid_lean = root / "ValidSample.lean"
            valid_lean.write_text(
                REQUIRED_LEAN_COPYRIGHT_HEADER
                + "\n/-!\n# Sample Module\n\n## i. Overview\nok\n\n## ii. Key results\nok\n\n## iii. Table of contents\nok\n\n## iv. References\nok\n-/\n"
                + "\n/-- Honest lemma docstring -/\nlemma sample_add (n : Nat) : n + 0 = n := by\n  simp\n",
                encoding="utf-8",
            )
            rt_valid = ResolvedTarget(path=valid_lean, rel_path="ValidSample.lean", module=None, exists=True)
            self.assertEqual(check_t1_lean_01_copyright_header([rt_valid]).status, "PASS")
            self.assertEqual(check_t1_lean_02_style_and_module_doc(REPO_ROOT, [rt_valid], strict_live=True).status, "PASS")
            self.assertEqual(check_t1_lean_03_theorem_lint(REPO_ROOT, [rt_valid], strict_live=True).status, "PASS")
            self.assertEqual(check_t1_lean_04_placeholder_and_vacuity(REPO_ROOT, [rt_valid], strict_live=True).status, "PASS")

            # 1. Missing copyright header
            no_hdr = root / "NoHdr.lean"
            no_hdr.write_text("lemma a : 1 = 1 := rfl\n", encoding="utf-8")
            self.assertEqual(check_t1_lean_01_copyright_header([ResolvedTarget(no_hdr, "NoHdr.lean", None, True)]).status, "FAIL")

            # 2. Missing 4-section module doc
            no_doc = root / "NoDoc.lean"
            no_doc.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\nlemma a : 1 = 1 := rfl\n", encoding="utf-8")
            self.assertEqual(
                check_t1_lean_02_style_and_module_doc(REPO_ROOT, [ResolvedTarget(no_doc, "NoDoc.lean", None, True)], strict_live=True).status,
                "FAIL",
            )

            # 3. Unexempted / undocumented theorem fails theorem_lint.py
            bad_thm = root / "BadThm.lean"
            bad_thm.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\ntheorem unexempted : 1 = 1 := rfl\n", encoding="utf-8")
            self.assertEqual(
                check_t1_lean_03_theorem_lint(REPO_ROOT, [ResolvedTarget(bad_thm, "BadThm.lean", None, True)], strict_live=True).status,
                "FAIL",
            )

            # 4. Placeholder / vacuity / native_decide / Prop wrapper failures
            for name, body in (
                ("HasSorry.lean", "lemma bad : 1 = 2 := by sorry\n"),
                ("HasAdmit.lean", "lemma bad : 1 = 2 := by admit\n"),
                ("HasAxiom.lean", "axiom fake_ax : False\n"),
                ("HasNativeDecide.lean", "lemma bad : 1 = 1 := by native_decide\n"),
                ("HasTrueWrap.lean", "lemma bad : True := by trivial\n"),
                (
                    "HasPropBundler.lean",
                    "structure Bundle : Prop where\n  p1 : 1 = 1\n  p2 : 2 = 2\n"
                    "lemma wrap (h1 : 1 = 1) (h2 : 2 = 2) : Bundle := ⟨h1, h2⟩\n",
                ),
            ):
                fp = root / name
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, name, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{name} unexpectedly passed: {res.summary}")

    def test_tier2_baseline_boundaries_and_negative_injections(self) -> None:
        artifacts, _ = discover_artifacts(REPO_ROOT, baseline_only=True)
        _, rows = check_t1_ec_01_claim_ledger(REPO_ROOT, artifacts.compilation_docs)
        targets, _ = resolve_targets(REPO_ROOT, [BASELINE_SMOKE_LEAN_REL])
        for o in run_tier2_checks(REPO_ROOT, artifacts, rows, targets, "baseline45"):
            self.assertEqual(o.status, "PASS", msg=f"{o.check_id}: {o.summary}")

        # Negative tests for Tier 2 boundaries
        with tempfile.TemporaryDirectory(prefix="ec_neg_t2_") as td:
            bad_imp = Path(td) / "BadRM.lean"
            bad_imp.write_text("import RiemannMasullo.Ch05_ThetaZSpaces.Sec1\n", encoding="utf-8")
            self.assertEqual(
                check_t2_bnd_04_riemann_masullo_quarantine(
                    REPO_ROOT, [ResolvedTarget(bad_imp, "BadRM.lean", None, True)], [], "baseline45"
                ).status,
                "FAIL",
            )

            rh_row = ParsedClaimRow(
                "d.md", 10, "SB-99", "Turn 50", "Global W >= 0 <-> RH", "Zeta", "thm",
                "[kernel_verified] (BUCKET 1)", "", ["[kernel_verified]"], ["BUCKET 1"], "BUCKET 1",
            )
            self.assertEqual(check_t2_bnd_05_colimit_rh_bucket3_enforcement([rh_row], artifacts).status, "FAIL")

            cm_doc = Path(td) / "cm.md"
            cm_doc.write_text("```mermaid\nflowchart TD\n  SA-18 --> M2_1\n```\n", encoding="utf-8")
            cm_row = ParsedClaimRow(
                "cm.md", 1, "SA-18", "13ED:229", "False deriv", "R", "thm",
                "[countermodel_found] (BUCKET 3)", "", ["[countermodel_found]"], ["BUCKET 3"], "BUCKET 3",
            )
            self.assertEqual(check_t2_bnd_06_countermodel_quarantine([cm_doc], [cm_row]).status, "FAIL")

            mismatch_row = ParsedClaimRow(
                "d.md", 1, "SX-2", "Turn 1", "stmt", "R", "thm",
                "[bucket_2_conditional] (BUCKET 1)", "", ["[bucket_2_conditional]"], ["BUCKET 1"], "BUCKET 1",
            )
            self.assertEqual(check_t2_bnd_07_bucket_label_disjointness([mismatch_row]).status, "FAIL")

    def test_tier3_baseline_consistency_and_stale_hash_detection(self) -> None:
        artifacts, _ = discover_artifacts(REPO_ROOT, baseline_only=True)
        _, rows = check_t1_ec_01_claim_ledger(REPO_ROOT, artifacts.compilation_docs)
        targets, _ = resolve_targets(REPO_ROOT, [BASELINE_SMOKE_LEAN_REL])
        for o in run_tier3_checks(REPO_ROOT, artifacts, rows, targets, "baseline45"):
            self.assertEqual(o.status, "PASS", msg=f"{o.check_id}: {o.summary}")

        # Negative test: stale hash in audit_report.json
        with tempfile.TemporaryDirectory(prefix="ec_neg_t3_") as td:
            rep = Path(td) / "audit_report.json"
            rep.write_text(
                json.dumps({"artifact_hashes": {BASELINE_COMPILATION_DOC_REL: "sha256:0000000000000000"}}),
                encoding="utf-8",
            )
            art = DiscoveredArtifacts([], [], [], [rep], [], [], [])
            self.assertEqual(check_t3_cons_05_audit_report_hashes(REPO_ROOT, art).status, "FAIL")

    def test_tier4_axiom_check_json_parser_and_disallowed_axioms(self) -> None:
        raw_stdout = (
            "Checking 1 module(s)...\n"
            "  InfoGeometry.Canonical.Demo: OK\n"
            '[{"module": "InfoGeometry.Canonical.Demo", "passed": true, "axioms": ["propext", "Classical.choice"]}]\n'
            "Axiom check summary: 1 passed, 0 failed.\n"
        )
        entries = parse_axiom_check_json_output(raw_stdout)
        ok, issues = validate_axiom_check_entries(entries, ["InfoGeometry.Canonical.Demo"])
        self.assertTrue(ok, msg=str(issues))

        # Disallowed axioms / partial / unsafe / passed=False
        for bad_entry in (
            {"module": "InfoGeometry.Canonical.Demo", "passed": False, "error": "native axiom checker failed"},
            {"module": "InfoGeometry.Canonical.Demo", "passed": True, "axioms": ["propext", "sorryAx"]},
            {"module": "InfoGeometry.Canonical.Demo", "passed": True, "axioms": ["Lean.ofReduceBool"]},
            {"module": "InfoGeometry.Canonical.Demo", "passed": True, "isPartial": True},
            {"module": "InfoGeometry.Canonical.Demo", "passed": True, "isUnsafe": True},
        ):
            ok_b, _ = validate_axiom_check_entries([bad_entry], ["InfoGeometry.Canonical.Demo"])
            self.assertFalse(ok_b)

    def test_cli_help_dry_run_and_exit_codes(self) -> None:
        script = Path(__file__).resolve()
        p_help = subprocess.run([sys.executable, str(script), "--help"], cwd=REPO_ROOT, capture_output=True, text=True)
        self.assertEqual(p_help.returncode, 0)
        self.assertIn("--self-test", p_help.stdout)
        self.assertIn("--dry-run", p_help.stdout)

        p_dry = subprocess.run(
            [
                sys.executable,
                str(script),
                "--dry-run",
                "--source-b-mode",
                "baseline45",
                "--targets",
                BASELINE_SMOKE_LEAN_REL,
                "--no-reports",
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
        )
        self.assertEqual(p_dry.returncode, 0, msg=p_dry.stdout + p_dry.stderr)
        self.assertIn("T4-E2E-DRY-RUN", p_dry.stdout)

        # Missing manifest -> exit code 2
        p_bad_man = subprocess.run(
            [sys.executable, str(script), "--dry-run", "--manifest", "docs/DOES_NOT_EXIST_12345.json", "--no-reports"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
        )
        self.assertEqual(p_bad_man.returncode, 2)

        # Missing live Tier 4 target -> exit code 2
        p_bad_tgt = subprocess.run(
            [sys.executable, str(script), "--tier", "4", "--targets", "lean/InfoGeometry/DoesNotExist999.lean", "--no-reports"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
        )
        self.assertEqual(p_bad_tgt.returncode, 2)

        # Repeatable --targets A --targets B retains both targets
        p_rep = subprocess.run(
            [
                sys.executable,
                str(script),
                "--dry-run",
                "--source-b-mode",
                "baseline45",
                "--targets",
                "lean/InfoGeometry/Canonical/SouriauKillingLipschitzBridge.lean",
                "--targets",
                "lean/InfoGeometry/Canonical/KleinBottleBipartiteKasteleynBridge.lean",
                "--no-reports",
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
        )
        self.assertEqual(p_rep.returncode, 0, msg=p_rep.stdout + p_rep.stderr)
        self.assertIn("InfoGeometry.Canonical.SouriauKillingLipschitzBridge", p_rep.stdout)
        self.assertIn("InfoGeometry.Canonical.KleinBottleBipartiteKasteleynBridge", p_rep.stdout)

    def test_regression_multi_file_lane_attribution_and_dotted_formal_objects(self) -> None:
        with tempfile.TemporaryDirectory(prefix="ec_reg_lane_") as td:
            root = Path(td)
            mod_a = root / "lean" / "InfoGeometry" / "Canonical" / "ModA.lean"
            mod_b = root / "lean" / "InfoGeometry" / "Canonical" / "ModB.lean"
            mod_a_aud = root / "lean" / "InfoGeometry" / "Canonical" / "ModAAudit.lean"
            mod_a.parent.mkdir(parents=True)
            mod_a.write_text("import Mathlib\ntheorem thm_a : 1 = 1 := rfl\n", encoding="utf-8")
            mod_b.write_text("import Mathlib\ntheorem thm_b : 2 = 2 := rfl\n", encoding="utf-8")
            mod_a_aud.write_text("import InfoGeometry.Canonical.ModA\n#print axioms thm_a\n", encoding="utf-8")
            env_path = root / "artifacts" / "qms" / "env.json"
            env_path.parent.mkdir(parents=True)
            env_path.write_text(
                json.dumps(
                    {
                        "schema": "info_geometry.qms.intent_envelope.v1",
                        "owner_search": {
                            "target_artifacts": [
                                "lean/InfoGeometry/Canonical/ModA.lean",
                                "lean/InfoGeometry/Canonical/ModB.lean",
                            ]
                        },
                        "formal_objects": {
                            "M2": [
                                "InfoGeometry.Canonical.ModA.objA",
                                "InfoGeometry.Canonical.ModB.objB",
                            ]
                        },
                        "acceptance_theorems": {"M2": ["thm_a", "thm_b"]},
                        "allowed_imports": {"M2": ["Mathlib"]},
                    }
                ),
                encoding="utf-8",
            )
            arts = DiscoveredArtifacts([], [env_path], [], [], [], [env_path], [])
            expected = _extract_expected_decls_from_artifacts(arts)
            self.assertIn("InfoGeometry.Canonical.ModA,InfoGeometry.Canonical.ModB", expected)
            rt_a = ResolvedTarget(mod_a, "lean/InfoGeometry/Canonical/ModA.lean", "InfoGeometry.Canonical.ModA", True)
            rt_b = ResolvedTarget(mod_b, "lean/InfoGeometry/Canonical/ModB.lean", "InfoGeometry.Canonical.ModB", True)

            # Fails workspace check in temp dir if .lake absent, so test T3-CONS-02 and T3-CONS-03 directly
            mod_b_aud = root / "lean" / "InfoGeometry" / "Canonical" / "ModBAudit.lean"
            mod_b_aud.write_text("import InfoGeometry.Canonical.ModB\n#print axioms thm_b\n", encoding="utf-8")
            c3_2 = check_t3_cons_02_contracts_to_lean_declarations(
                root, arts, [rt_a, rt_b], require_all_envelope_targets=True
            )
            self.assertEqual(c3_2.status, "PASS", msg=c3_2.summary)
            c3_3 = check_t3_cons_03_imports_isolation(root, arts, [rt_a, rt_b])
            self.assertEqual(c3_3.status, "PASS", msg=c3_3.summary)

            # Negative: opaque decl + commented #print axioms MUST FAIL T3-CONS-02
            mod_b.write_text("import Mathlib\nopaque thm_b : Prop\n", encoding="utf-8")
            mod_b_aud.write_text("-- #print axioms thm_b\n", encoding="utf-8")
            c3_2_bad = check_t3_cons_02_contracts_to_lean_declarations(
                root, arts, [rt_a, rt_b], require_all_envelope_targets=True
            )
            self.assertEqual(c3_2_bad.status, "FAIL")

            # Negative: v1 contract missing source_path fails when require_all_envelope_targets=True
            c_json = root / "docs" / "contracts" / "c.json"
            c_json.parent.mkdir(parents=True)
            c_json.write_text(
                json.dumps(
                    {
                        "schema": "info_geometry.opengauss.ground_truth_theorem_contract.v1",
                        "owner_declarations": [
                            {"qualified_name": "InfoGeometry.Canonical.Missing.foo", "source_path": "lean/InfoGeometry/Canonical/Missing.lean"}
                        ],
                    }
                ),
                encoding="utf-8",
            )
            arts_c = DiscoveredArtifacts([], [], [c_json], [], [], [c_json], [])
            self.assertEqual(
                check_t3_cons_02_contracts_to_lean_declarations(root, arts_c, [], require_all_envelope_targets=True).status,
                "FAIL",
            )

    def test_regression_latex_pipe_table_and_mermaid_edge_variants(self) -> None:
        with tempfile.TemporaryDirectory(prefix="ec_reg_md_") as td:
            root = Path(td)
            doc = root / "ledger.md"
            doc.write_text(
                "| Claim ID | Source Provenance | Candidate Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `SB-41` | C46 | Norm $\\|\\beta\\|_g = (k_B T)^{-1}$ on $(M, g)$ | Curved $(M, g)$ | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
                "| `D14.1` | T14 | Second-order Leibniz defect | `Ring A` | `[kernel_verified]` (`BUCKET 1`) | ok |\n",
                encoding="utf-8",
            )
            rows = parse_claim_ledgers([doc], root)
            self.assertEqual([r.claim_id for r in rows], ["SB-41", "D14.1"])
            self.assertEqual(rows[0].labels, ["[bucket_3_open_debt]"])
            self.assertEqual(rows[0].explicit_buckets, ["BUCKET 3"])
            self.assertIn("\\|\\beta\\|_g", rows[0].statement)

            for bad_mermaid in (
                "flowchart TD\n  SB-41 --> SB-42\n  SB-42 --> SB-41\n",
                "flowchart TD\n  A --> B --> A\n",
                "flowchart TD\n  A -- implies --> B\n  B -. dep .-> A\n",
                "flowchart TD\n  A & B -->|lbl| C\n  C --> A\n",
            ):
                nodes, edges = parse_mermaid_dag(bad_mermaid)
                acyclic, _order, _iso = kahn_topological_sort(nodes, edges)
                self.assertFalse(acyclic, msg=f"Cycle missed in:\n{bad_mermaid}")

            # Labels containing '->' and '&' inside brackets MUST NOT create bogus edges
            clean_mermaid = 'flowchart TD\n  N1["A & B -> C"] --> N2["Done"]\n'
            nodes_ok, edges_ok = parse_mermaid_dag(clean_mermaid)
            self.assertEqual(nodes_ok, {"N1", "N2"})
            self.assertEqual(edges_ok, [("N1", "N2")])

    def test_regression_f10_html_json_traps_binary_drive_and_4031_bytes(self) -> None:
        with tempfile.TemporaryDirectory(prefix="ec_reg_f10_") as td:
            root = Path(td)
            (root / "cached" / "drive_docs").mkdir(parents=True)
            doc = root / "docs" / "M1B.md"
            doc.parent.mkdir(parents=True)

            # 1. Disguised >4KB HTML with leading comment + hyphenated sign-in MUST FAIL
            e_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.md"
            e_path.write_text(
                "<!-- Redirect -->\n<html><head><title>Sign-in required</title></head>"
                + (" " * 4500)
                + '<form action="https://accounts.google.com/ServiceLogin"></form></html>\n',
                encoding="utf-8",
            )
            # "4031 bytes" MUST NOT count as an HTTP 403 blocker report
            c_bytes = b"%PDF-1.4\n\xff\xfe\x00\x01binary pdf content"
            c_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.pdf"
            c_path.write_bytes(c_bytes)
            c_sha = hashlib.sha256(c_bytes).hexdigest()

            d_payload = {
                "runSettings": {},
                "systemInstruction": {},
                "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
            }
            d_bytes = json.dumps(d_payload).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )

            doc.write_text(
                f"- Source C `{SOURCE_C_ID}`: {len(c_bytes)} bytes, sha256 `{c_sha}`\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                f"- Source E `{SOURCE_E_ID}`: saved locally, 4031 bytes, sha256 deadbeef1234\n\n"
                f"| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                f"|---|---|---|---|---|---|\n"
                f"| `CDE-1` | C/D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                f"| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n",
                encoding="utf-8",
            )
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(root, [doc], [], "live84", require_all_sources=True, extract_script_override=extract_script).status,
                "FAIL",
            )

            # 2. Binary PDF for C + explicit blocker for E -> PASS
            doc.write_text(
                f"- Source C `{SOURCE_C_ID}`: {len(c_bytes)} bytes, sha256 `{c_sha}`\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                f"- Source E `{SOURCE_E_ID}`: HTTP 403 / Sign-in required (access blocker)\n\n"
                f"| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                f"|---|---|---|---|---|---|\n"
                f"| `CDE-1` | C/D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                f"| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n",
                encoding="utf-8",
            )
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(root, [doc], [], "live84", require_all_sources=True, extract_script_override=extract_script).status,
                "PASS",
            )

            # 3. JSON API error payload masquerading as Drive C -> FAIL
            c_err = json.dumps({"error": {"code": 403, "message": "Access denied"}}).encode("utf-8")
            c_path.unlink()
            c_json_err = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.json"
            c_json_err.write_bytes(c_err)
            doc.write_text(
                f"- Source C `{SOURCE_C_ID}`: {len(c_err)} bytes, 1 lines, sha256 `{hashlib.sha256(c_err).hexdigest()}`\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                f"- Source E `{SOURCE_E_ID}`: HTTP 403 access blocker\n\n"
                f"| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                f"|---|---|---|---|---|---|\n"
                f"| `CDE-1` | C/D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                f"| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n",
                encoding="utf-8",
            )
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(root, [doc], [], "live84", require_all_sources=True, extract_script_override=extract_script).status,
                "FAIL",
            )

            # 4. Truncated Source D JSON without runSettings/role/createTime -> FAIL even in baseline45
            d_path.write_text(json.dumps({"chunkedPrompt": {"chunks": [{"text": "truncated"}]}}), encoding="utf-8")
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(root, [doc], [], "baseline45", require_all_sources=False, extract_script_override=extract_script).status,
                "FAIL",
            )

    def test_regression_riemann_masullo_imports_vacuity_prop_bundler_and_tier2_tier3_traps(self) -> None:
        with tempfile.TemporaryDirectory(prefix="ec_reg_lean_") as td:
            root = Path(td)
            # 1. Nested RiemannMasullo import, public import, and guillemets all fail T2-BND-04
            for fname, imp_line in (
                ("Nested.lean", "import InfoGeometry.Arithmetic.RiemannMasullo.Ch05_ThetaZSpaces.Sec1\n"),
                ("PubImp.lean", "public import RiemannMasullo.Ch05\n"),
                ("GuilImp.lean", "import «RiemannMasullo».Ch12\n"),
            ):
                p = root / fname
                p.write_text(imp_line, encoding="utf-8")
                self.assertEqual(
                    check_t2_bnd_04_riemann_masullo_quarantine(
                        REPO_ROOT, [ResolvedTarget(p, fname, None, True)], [], "baseline45"
                    ).status,
                    "FAIL",
                    msg=f"{fname} bypassed T2-BND-04",
                )

            # 2. Multiline : True wrappers and parameterized Prop bundler fail T1-LEAN-04
            for fname, body in (
                ("MultiEx.lean", "example\n  (n : Nat)\n  : True := by\n  trivial\n"),
                ("TrueSimp.lean", "theorem t : True := by\n  simp\n"),
                ("TrueDecide.lean", "theorem t : True := by decide\n"),
                ("TrueCtor.lean", "theorem t : True := ⟨⟩\n"),
                (
                    "ParamBundle.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
            ):
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 3. T2-BND-05 LaTeX / prose variants & T2-BND-06 underscore alias & scope
            artifacts, _ = discover_artifacts(REPO_ROOT, baseline_only=True)
            for stmt in (
                r"$\mathrm{RH} \iff \mathcal{W}(f,f) \ge 0$",
                r"All Li coefficients $\lambda_n \ge 0$ for all $n \ge 1$",
                r"Inductive colimit as $N \to \infty$ of $D_N$",
                r"Bost-Connes C*-algebra KMS_beta state classification",
                r"Zero simplicity $\zeta'(\rho) \neq 0$",
            ):
                bad_row = ParsedClaimRow(
                    "d.md", 1, "SB-99", "Turn 60", stmt, "C", "", "[kernel_verified] (BUCKET 1)", "", ["[kernel_verified]"], ["BUCKET 1"], "BUCKET 1"
                )
                self.assertEqual(check_t2_bnd_05_colimit_rh_bucket3_enforcement([bad_row], artifacts).status, "FAIL", msg=stmt)

            cm_alias_doc = root / "cm_alias.md"
            cm_alias_doc.write_text("```mermaid\nflowchart TD\n  SA_18[False] --> M2_1\n```\n", encoding="utf-8")
            cm_row = ParsedClaimRow(
                "cm_alias.md", 1, "SA-18", "13ED:229", "False", "R", "", "[countermodel_found] (BUCKET 3)", "", ["[countermodel_found]"], ["BUCKET 3"], "BUCKET 3"
            )
            self.assertEqual(check_t2_bnd_06_countermodel_quarantine([cm_alias_doc], [cm_row]).status, "FAIL")

            # Turn 46-84-only rows do NOT false-fail T2-BND-06 for missing SA-18/SB-17/SB-35
            cm_ok_doc = root / "cm_ok.md"
            cm_ok_doc.write_text("# Clean Turn 46-84 Doc\n", encoding="utf-8")
            t46_row = ParsedClaimRow(
                "docs/TURNS46_84.md", 1, "SB-70", "T62", "F8", "Mat", "", "[countermodel_found] (BUCKET 3)", "", ["[countermodel_found]"], ["BUCKET 3"], "BUCKET 3"
            )
            self.assertEqual(check_t2_bnd_06_countermodel_quarantine([cm_ok_doc], [t46_row]).status, "PASS")

            # 4. axiom_check JSON [INFO] prefix, null axioms, missing axioms+returncode, and axiom_usage
            entries = parse_axiom_check_json_output(
                '[INFO] loading .olean\n[{"module": "InfoGeometry.Demo", "passed": true, "returncode": 0}]\n'
            )
            ok_native, _ = validate_axiom_check_entries(entries, ["InfoGeometry.Demo"])
            self.assertTrue(ok_native)
            for bad_entry in (
                {"module": "InfoGeometry.Demo", "passed": True},
                {"module": "InfoGeometry.Demo", "passed": True, "axioms": None},
                {"module": "InfoGeometry.Demo", "passed": True, "axioms": ["propext"], "axiom_usage": {"bad": ["sorryAx"]}},
            ):
                ok_bad, _ = validate_axiom_check_entries([bad_entry], ["InfoGeometry.Demo"])
                self.assertFalse(ok_bad, msg=f"bad_entry passed: {bad_entry}")

            # 5. discover_artifacts with --manifest still discovers audit_report & excludes qa_report.md from compilation_docs
            (root / "docs").mkdir(exist_ok=True)
            (root / "artifacts" / "qms").mkdir(parents=True)
            m_doc = root / "docs" / "M.md"
            m_doc.write_text("# Doc\n", encoding="utf-8")
            qa_md = root / "artifacts" / "qms" / "DRIVE-qa_report.md"
            qa_md.write_text(f"| [M.md](../../docs/M.md) | `{'0' * 64}` |\n", encoding="utf-8")
            aud_json = root / "artifacts" / "qms" / "DRIVE-audit_report.json"
            aud_json.write_text(json.dumps({"schema": "info_geometry.qms.audit_report.v1", "artifact_hashes": {}}), encoding="utf-8")
            arts_man, errs_man = discover_artifacts(root, [str(m_doc), str(qa_md)])
            self.assertEqual(errs_man, [])
            self.assertEqual(arts_man.compilation_docs, [m_doc])
            self.assertIn(aud_json, arts_man.audit_reports)
            self.assertEqual(check_t3_cons_05_audit_report_hashes(root, arts_man).status, "FAIL")

    def test_regression_r3_intake_bleed_bom_createtime_and_corrupt_pdf(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        with tempfile.TemporaryDirectory(prefix="ec_reg_r3_intake_") as td:
            root = Path(td)
            (root / "cached" / "drive_docs").mkdir(parents=True)
            (root / "docs").mkdir(parents=True)

            d_payload = {
                "runSettings": {},
                "systemInstruction": {},
                "chunkedPrompt": {
                    "chunks": [
                        {"role": "user", "text": "hi", "createTime": "2026-11-22T10:00:00Z"},
                    ]
                },
            }
            d_bytes = json.dumps(d_payload).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )

            # 1. Cross-source blocker window bleed (P1e): C has 403 JSON, E 2 lines below has HTTP 403 -> MUST FAIL
            c_err = json.dumps({"error": {"code": 403, "message": "Access denied"}}).encode("utf-8")
            c_err_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.json"
            c_err_path.write_bytes(c_err)
            e_err_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"
            e_err_path.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            doc = root / "docs" / "M1B.md"
            doc.write_text(
                f"- Source C `{SOURCE_C_ID}`: {len(c_err)} bytes, 1 lines, sha256 `{hashlib.sha256(c_err).hexdigest()}`\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                f"- Source E `{SOURCE_E_ID}`: HTTP 403 access blocker\n\n"
                "| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n",
                encoding="utf-8",
            )
            res_bleed = check_t1_intake_07_additional_sources_f10(
                root, [doc], [], "live84", require_all_sources=True, extract_script_override=extract_script
            )
            self.assertEqual(res_bleed.status, "FAIL", msg=res_bleed.summary)

            # 2. UTF-8 BOM before HTML comment + sign-in (P1g): MUST FAIL even with valid C
            c_err_path.unlink()
            c_ok = b"%PDF-1.4\nvalid pdf"
            c_pdf = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.pdf"
            c_pdf.write_bytes(c_ok)
            c_sha = hashlib.sha256(c_ok).hexdigest()
            e_err_path.unlink()
            e_bom = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.md"
            e_bom.write_bytes(b"\xef\xbb\xbf<!-- bom --><html><title>Sign-in</title></html>")
            doc.write_text(
                f"- Source C `{SOURCE_C_ID}`: {len(c_ok)} bytes, sha256 `{c_sha}`\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                f"- Source E `{SOURCE_E_ID}`: accessible locally\n\n"
                "| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | C/D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n",
                encoding="utf-8",
            )
            res_bom = check_t1_intake_07_additional_sources_f10(
                root, [doc], [], "live84", require_all_sources=True, extract_script_override=extract_script
            )
            self.assertEqual(res_bom.status, "FAIL", msg=res_bom.summary)

            # 3. Corrupt .pdf Drive file without %PDF- magic header (P1f_new): MUST FAIL
            e_bom.unlink()
            c_bad_pdf = b"\xff\xfe\x00\x01corrupt_not_a_pdf"
            c_pdf.write_bytes(c_bad_pdf)
            doc.write_text(
                f"- Source C `{SOURCE_C_ID}`: {len(c_bad_pdf)} bytes, sha256 `{hashlib.sha256(c_bad_pdf).hexdigest()}`\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                f"- Source E `{SOURCE_E_ID}`: HTTP 403 access blocker\n",
                encoding="utf-8",
            )
            res_pdf = check_t1_intake_07_additional_sources_f10(
                root, [doc], [], "baseline45", require_all_sources=False, extract_script_override=extract_script
            )
            self.assertEqual(res_pdf.status, "FAIL", msg=res_pdf.summary)

            # 4. Mixed createTime types (int + str) in Source D (P1h): returns FAIL cleanly, no TypeError
            c_pdf.write_bytes(c_ok)
            d_mixed = {
                "runSettings": {},
                "systemInstruction": {},
                "chunkedPrompt": {
                    "chunks": [
                        {"role": "user", "text": "a", "createTime": 100},
                        {"role": "model", "text": "b", "createTime": "2026-11-22T10:00:00Z"},
                    ]
                },
            }
            d_path.write_text(json.dumps(d_mixed), encoding="utf-8")
            res_mixed = check_t1_intake_07_additional_sources_f10(
                root, [doc], [], "baseline45", require_all_sources=False, extract_script_override=extract_script
            )
            self.assertEqual(res_mixed.status, "FAIL", msg=res_mixed.summary)

    def test_regression_r3_lean_bundlers_vacuity_and_t2_t3_t4_hardening(self) -> None:
        with tempfile.TemporaryDirectory(prefix="ec_reg_r3_lean_") as td:
            root = Path(td)
            # 1. Is* param Prop bundler, multiline header, by constructor, And.intro, (True : Prop), def/abbrev : True (P4b13..17)
            for fname, body in (
                (
                    "IsParamBundle.lean",
                    "structure IsPackagedBundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : IsPackagedBundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "MultilineHdrBundle.lean",
                    "structure Bundle\n  (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "ByCtorBundle.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := by\n  constructor\n  · rfl\n  · exact Nat.add_zero n\n",
                ),
                ("TruePropAscribed.lean", "theorem t : (True : Prop) := trivial\n"),
                ("DefTrueWrap.lean", "def sneak_def : True := trivial\n"),
                ("AbbrevTrueWrap.lean", "abbrev sneak_abbrev : True := trivial\n"),
            ):
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04: {res.summary}")

            # 2. Broadened T2-BND-05 LaTeX / paraphrase variants (P3c..P3g)
            artifacts, _ = discover_artifacts(REPO_ROOT, baseline_only=True)
            for stmt in (
                r"Global Weil positivity $\mathcal{W}(f,f) \ge 0$ for all test functions $f$",
                r"Li sequence satisfies $\lambda_n \geq 0$ for every $n \geq 1$",
                r"Operator limit as $N \rightarrow \infty$ yields global spectral realization",
                r"Bost-Connes $KMS_{\beta}$ state simplex at $\beta > 1$",
                r"Every critical zero $\rho$ has $\zeta'(\rho) \ne 0$",
                r"All nontrivial zeros of $\zeta(s)$ have $\operatorname{Re}(s) = 1/2$",
            ):
                bad_row = ParsedClaimRow(
                    "d.md", 1, "SB-99", "Turn 60", stmt, "C", "", "[kernel_verified] (BUCKET 1)", "", ["[kernel_verified]"], ["BUCKET 1"], "BUCKET 1"
                )
                self.assertEqual(check_t2_bnd_05_colimit_rh_bucket3_enforcement([bad_row], artifacts).status, "FAIL", msg=stmt)

            # 3. parse_axiom_check_json_output ignores trailing [1, 2] and validate_axiom_check_entries rejects nonzero returncode (P5f, P5g)
            parsed = parse_axiom_check_json_output(
                '[{"module": "InfoGeometry.Demo", "passed": true, "axioms": ["propext"]}]\n[1, 2]\n'
            )
            ok_p, issues_p = validate_axiom_check_entries(parsed, ["InfoGeometry.Demo"])
            self.assertTrue(ok_p, msg=str(issues_p))
            ok_rc, _ = validate_axiom_check_entries(
                [{"module": "InfoGeometry.Demo", "passed": True, "axioms": ["propext"], "returncode": 1}],
                ["InfoGeometry.Demo"],
            )
            self.assertFalse(ok_rc)

            # 4. T3-CONS-02 declared vs optional *Audit.lean (P6c5)
            mod_a = root / "lean" / "InfoGeometry" / "Canonical" / "DemoMod.lean"
            mod_a.parent.mkdir(parents=True)
            mod_a.write_text("import Mathlib\ntheorem acc_thm : 1 = 1 := rfl\n", encoding="utf-8")
            (root / "artifacts" / "qms").mkdir(parents=True)
            env_decl = root / "artifacts" / "qms" / "env_decl.json"
            env_decl.write_text(
                json.dumps(
                    {
                        "schema": "info_geometry.qms.intent_envelope.v1",
                        "owner_search": {
                            "target_artifacts": [
                                "lean/InfoGeometry/Canonical/DemoMod.lean",
                                "lean/InfoGeometry/Canonical/DemoModAudit.lean",
                            ]
                        },
                        "formal_objects": {"M2": ["DemoMod.obj"]},
                        "acceptance_theorems": {"M2": ["acc_thm"]},
                    }
                ),
                encoding="utf-8",
            )
            rt_a = ResolvedTarget(mod_a, "lean/InfoGeometry/Canonical/DemoMod.lean", "InfoGeometry.Canonical.DemoMod", True)
            self.assertEqual(
                check_t3_cons_02_contracts_to_lean_declarations(
                    root, DiscoveredArtifacts([], [env_decl], [], [], [], [env_decl], []), [rt_a], require_all_envelope_targets=True
                ).status,
                "FAIL",
            )
            env_opt = root / "artifacts" / "qms" / "env_opt.json"
            env_opt.write_text(
                json.dumps(
                    {
                        "schema": "info_geometry.qms.intent_envelope.v1",
                        "owner_search": {"target_artifacts": ["lean/InfoGeometry/Canonical/DemoMod.lean"]},
                        "formal_objects": {"M2": ["DemoMod.obj"]},
                        "acceptance_theorems": {"M2": ["acc_thm"]},
                    }
                ),
                encoding="utf-8",
            )
            self.assertEqual(
                check_t3_cons_02_contracts_to_lean_declarations(
                    root, DiscoveredArtifacts([], [env_opt], [], [], [], [env_opt], []), [rt_a], require_all_envelope_targets=True
                ).status,
                "PASS",
            )

            # 5. Full-repo --manifest discovers manifest-linked custom audit_report.json & cached/ in qa_report.md (P6b4, P6b5)
            (root / "lean" / "InfoGeometry.lean").write_text("-- root\n", encoding="utf-8")
            (root / "docs").mkdir(exist_ok=True)
            (root / "cached" / "drive_docs").mkdir(parents=True)
            m2_doc = root / "docs" / "M2.md"
            m2_doc.write_text("# M2\n", encoding="utf-8")
            cached_src = root / "cached" / "drive_docs" / "src.txt"
            cached_src.write_text("cached content\n", encoding="utf-8")
            m2_aud = root / "artifacts" / "qms" / "M2-audit_report.json"
            m2_aud.write_text(
                json.dumps({"schema": "info_geometry.qms.audit_report.v1", "artifact_hashes": {"docs/M2.md": "sha256:" + "0" * 64}}),
                encoding="utf-8",
            )
            unrelated_aud = root / "artifacts" / "qms" / "zorn-unrelated-audit_report.json"
            unrelated_aud.write_text(
                json.dumps({"schema": "info_geometry.qms.audit_report.v1", "artifact_hashes": {"docs/Other.md": "sha256:" + "0" * 64}}),
                encoding="utf-8",
            )
            arts_full, errs_full = discover_artifacts(root, [str(m2_doc)])
            self.assertEqual(errs_full, [])
            self.assertIn(m2_aud, arts_full.audit_reports)
            self.assertNotIn(unrelated_aud, arts_full.audit_reports)
            self.assertEqual(check_t3_cons_05_audit_report_hashes(root, arts_full).status, "FAIL")

            qa_cached = root / "artifacts" / "qms" / "M2-qa_report.md"
            qa_cached.write_text(f"| `cached/drive_docs/src.txt` | `{'0' * 64}` |\n", encoding="utf-8")
            self.assertEqual(
                check_t3_cons_05_audit_report_hashes(root, DiscoveredArtifacts([], [], [], [], [qa_cached], [], [])).status,
                "FAIL",
            )

            # 6. No-space Mermaid edges (P2f), inline-code backslash table row, and T4-E2E-05 porcelain prefix
            nodes_ns, edges_ns = parse_mermaid_dag("flowchart TD\n  SB-41-->SB-42\n  SB-42-->SB-41\n")
            self.assertEqual(nodes_ns, {"SB-41", "SB-42"})
            self.assertEqual(edges_ns, [("SB-41", "SB-42"), ("SB-42", "SB-41")])
            acyclic_ns, _, _ = kahn_topological_sort(nodes_ns, edges_ns)
            self.assertFalse(acyclic_ns)

            cells_bt = _split_markdown_table_row(r"| `\` | `second` |")
            self.assertEqual(cells_bt, [r"`\`", "`second`"])

            self.assertTrue(_porcelain_path("?? scratch/epistemic_compilation_e2e/reports/r.json").startswith("scratch/"))
            self.assertFalse(_porcelain_path("?? tests/scratch/x.py").startswith("scratch/"))

    def test_regression_r4_mermaid_char_null_chunked_vacuity_t17_and_consistency(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        with tempfile.TemporaryDirectory(prefix="ec_reg_r4_") as td:
            root = Path(td)

            # 1. No-space dotted Mermaid edges (A-.->B, SB-41-.->SB-42, A-. dep .->B)
            nodes_d1, edges_d1 = parse_mermaid_dag("flowchart TD\n  A-.->B\n  B-.->A\n")
            self.assertEqual(nodes_d1, {"A", "B"})
            self.assertEqual(edges_d1, [("A", "B"), ("B", "A")])
            self.assertFalse(kahn_topological_sort(nodes_d1, edges_d1)[0])

            nodes_d2, edges_d2 = parse_mermaid_dag("flowchart TD\n  SB-41-.->SB-42\n  SB-42-.->SB-41\n")
            self.assertEqual(nodes_d2, {"SB-41", "SB-42"})
            self.assertEqual(edges_d2, [("SB-41", "SB-42"), ("SB-42", "SB-41")])

            nodes_d3, edges_d3 = parse_mermaid_dag("flowchart TD\n  A-. dep .->B\n  B-->A\n")
            self.assertEqual(nodes_d3, {"A", "B"})
            self.assertEqual(edges_d3, [("A", "B"), ("B", "A")])
            self.assertFalse(kahn_topological_sort(nodes_d3, edges_d3)[0])

            # 2. Lean Char literal '"' must NOT blind strip_lean_comments_and_strings, while primes stay intact
            char_src = (
                REQUIRED_LEAN_COPYRIGHT_HEADER
                + "\ndef q : Char := '\"'\n"
                + "def q_esc : Char := '\\\"'\n"
                + "theorem sneak : True := by native_decide\n"
            )
            char_fp = root / "CharQuote.lean"
            char_fp.write_text(char_src, encoding="utf-8")
            self.assertEqual(
                check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(char_fp, "CharQuote.lean", None, True)], strict_live=True
                ).status,
                "FAIL",
            )
            prime_src = "def deriv_ok (x' f'' ζ' a'b : Nat) : Nat := x' + f'' + ζ' + a'b\n"
            self.assertEqual(strip_lean_comments_and_strings(prime_src), prime_src)

            # 3. Null and non-dict chunkedPrompt return FAIL cleanly (no AttributeError)
            (root / "cached" / "drive_docs").mkdir(parents=True)
            (root / "docs").mkdir(parents=True)
            src_b_null = root / "cached" / "aistudio_prompt_1v8Jj30jF2ytMHunuZq_FXEBjWcNFyw0O.json"
            for bad_cp in (None, [], "bad"):
                src_b_null.write_text(
                    json.dumps({"runSettings": {}, "systemInstruction": {}, "chunkedPrompt": bad_cp}),
                    encoding="utf-8",
                )
                self.assertEqual(resolve_effective_source_b_mode(root, "auto"), "baseline45")
                self.assertEqual(check_t1_intake_02_source_b(root, "live84").status, "FAIL")

            d_null = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_null.write_text(
                json.dumps({"runSettings": {}, "systemInstruction": {}, "chunkedPrompt": None}),
                encoding="utf-8",
            )
            c_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            c_ok_bytes = b"Source C valid text\n"
            c_ok_path.write_bytes(c_ok_bytes)
            m1b_doc = root / "docs" / "M1B.md"
            m1b_doc.write_text(
                f"- Source C `{SOURCE_C_ID}`: {len(c_ok_bytes)} bytes, 1 lines, sha256 `{hashlib.sha256(c_ok_bytes).hexdigest()}`\n"
                f"- Source E `{SOURCE_E_ID}`: HTTP 403 access blocker\n",
                encoding="utf-8",
            )
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b_doc], [], "baseline45", require_all_sources=False, extract_script_override=extract_script
                ).status,
                "FAIL",
            )

            # 4. Same-line multi-source blocker isolation (N3) & nested sub-bullet blocker (Rev2 Minor 2)
            d_valid_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_null.write_bytes(d_valid_bytes)
            d_sha = hashlib.sha256(d_valid_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_null), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            c_ok_path.unlink()
            c_err_json = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.json"
            c_err_json.write_text(json.dumps({"error": {"code": 403, "message": "Access denied"}}), encoding="utf-8")
            e_html = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")

            m1b_doc.write_text(
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally, E blocked by HTTP 403\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_valid_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n\n"
                "| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n",
                encoding="utf-8",
            )
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b_doc], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "FAIL",
            )

            # Nested sub-bullet for E with valid C -> PASS
            c_err_json.unlink()
            c_ok_path.write_bytes(c_ok_bytes)
            m1b_doc.write_text(
                f"- Source C `{SOURCE_C_ID}`: {len(c_ok_bytes)} bytes, 1 lines, sha256 `{hashlib.sha256(c_ok_bytes).hexdigest()}`\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_valid_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                f"- Source E (`{SOURCE_E_ID}`):\n"
                "  - Status: HTTP 403 Access Denied\n\n"
                "| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | C/D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n",
                encoding="utf-8",
            )
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b_doc], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "PASS",
            )

            # 5. N6a..N6e Prop bundlers and N7a..N7c + ((True) : Prop) vacuity wrappers MUST FAIL T1-LEAN-04
            for fname, body in (
                (
                    "N6aForall.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok : ∀ n : Nat, Bundle n := fun n => ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "N6bArrow.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok : Nat → Bundle 0 := fun _ => ⟨rfl, rfl⟩\n",
                ),
                (
                    "N6cDotMk.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := .mk rfl (Nat.add_zero n)\n",
                ),
                (
                    "N6dAssign.lean",
                    "structure Bundle (n : Nat) : Prop := mk ::\n  (p1 : n = n)\n  (p2 : n + 0 = n)\n"
                    "lemma ok (n : Nat) : Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "N6eNsQual.lean",
                    "namespace Ns\nstructure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\nend Ns\n"
                    "lemma ok (n : Nat) : Ns.Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                ("N7aForallTrue.lean", "theorem t : ∀ (_ : Nat), True := fun _ => trivial\n"),
                ("N7bArrowTrue.lean", "theorem t : Nat → True := fun _ => trivial\n"),
                ("N7cInstanceTrue.lean", "instance : True := trivial\n"),
                ("NestedParensTrue.lean", "theorem t : ((True) : Prop) := trivial\n"),
            ):
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 6. Trap-T17-compliant witness-bearing : Prop predicates MUST NOT be false-flagged
            t17_consumed = (
                "structure WeylPair (s d : Nat) : Prop where\n  sq : s * s = s\n  conj : s * d = d\n"
                "theorem weylPair_witness : WeylPair 1 0 := ⟨rfl, rfl⟩\n"
                "theorem use_weylPair (s d : Nat) (h : WeylPair s d) : s * d = d := h.conj\n"
            )
            self.assertEqual(scan_parameterized_prop_bundlers(t17_consumed), [])

            t17_standalone = (
                "structure CausalPair (a b : Nat) : Prop where\n  h1 : a + b = b + a\n  h2 : a * b = b * a\n"
                "theorem causalPair_witness (a : Nat) : CausalPair a 0 := by\n"
                "  induction a with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ k ih => constructor <;> simp [Nat.add_comm]\n"
            )
            self.assertEqual(scan_parameterized_prop_bundlers(t17_standalone), [])
            self.assertEqual(scan_native_decide_and_vacuous_true("theorem iff_true (p : Prop) : p ↔ True := sorry\n"), [])

            # 7. T2-BND-05: \mathrm{KMS}_{\beta}, \text{KMS}_{\beta}, Riemann Hypothesis is proved
            artifacts, _ = discover_artifacts(REPO_ROOT, baseline_only=True)
            for stmt in (
                r"Bost-Connes $\mathrm{KMS}_{\beta}$ state classification",
                r"Bost-Connes $\text{KMS}_{\beta}$ state classification",
                r"The Riemann Hypothesis is proved for $\zeta(s)$",
            ):
                bad_row = ParsedClaimRow(
                    "d.md", 1, "SB-99", "Turn 60", stmt, "C", "", "[kernel_verified] (BUCKET 1)", "", ["[kernel_verified]"], ["BUCKET 1"], "BUCKET 1"
                )
                self.assertEqual(check_t2_bnd_05_colimit_rh_bucket3_enforcement([bad_row], artifacts).status, "FAIL", msg=stmt)

            # 8. T3-CONS-05: plain cached/*.pdf & cached/*.jsonl in qa_report.md + --manifest <.md> --targets <.lean>
            (root / "lean" / "InfoGeometry" / "Canonical").mkdir(parents=True)
            (root / "lean" / "InfoGeometry.lean").write_text("-- root\n", encoding="utf-8")
            m2_mod = root / "lean" / "InfoGeometry" / "Canonical" / "M2Mod.lean"
            m2_mod.write_text("namespace MyNs\ntheorem acc_thm : 1 = 1 := rfl\nend MyNs\n", encoding="utf-8")
            (root / "artifacts" / "qms").mkdir(parents=True)
            m2_doc = root / "docs" / "M2.md"
            m2_doc.write_text("# M2\n", encoding="utf-8")
            aud_tgt = root / "artifacts" / "qms" / "20261122-audit_report.json"
            aud_tgt.write_text(
                json.dumps(
                    {
                        "schema": "info_geometry.qms.audit_report.v1",
                        "artifact_hashes": {"lean/InfoGeometry/Canonical/M2Mod.lean": "sha256:" + "0" * 64},
                    }
                ),
                encoding="utf-8",
            )
            arts_tgt, errs_tgt = discover_artifacts(
                root, [str(m2_doc)], raw_targets=["lean/InfoGeometry/Canonical/M2Mod.lean"]
            )
            self.assertEqual(errs_tgt, [])
            self.assertIn(aud_tgt, arts_tgt.audit_reports)
            self.assertEqual(check_t3_cons_05_audit_report_hashes(root, arts_tgt).status, "FAIL")

            pdf_file = root / "cached" / "drive_docs" / "doc.pdf"
            pdf_file.write_bytes(b"%PDF-1.4\nbody")
            jsonl_file = root / "cached" / "aistudio_extracts" / "fences.jsonl"
            jsonl_file.parent.mkdir(parents=True, exist_ok=True)
            jsonl_file.write_text("{}\n", encoding="utf-8")
            qa_pdf = root / "artifacts" / "qms" / "M2-qa_report.md"
            qa_pdf.write_text(
                f"| `cached/drive_docs/doc.pdf` | `{'0' * 64}` |\n"
                f"| `cached/aistudio_extracts/fences.jsonl` | `{'0' * 64}` |\n",
                encoding="utf-8",
            )
            res_qa_pdf = check_t3_cons_05_audit_report_hashes(root, DiscoveredArtifacts([], [], [], [], [qa_pdf], [], []))
            self.assertEqual(res_qa_pdf.status, "FAIL")
            self.assertEqual(res_qa_pdf.details["checked"], 2)

            # 9. T3-CONS-02: dotted acceptance_theorems ("MyNs.acc_thm") matches extracted `acc_thm`
            env_dot = root / "artifacts" / "qms" / "env_dot.json"
            env_dot.write_text(
                json.dumps(
                    {
                        "schema": "info_geometry.qms.intent_envelope.v1",
                        "owner_search": {"target_artifacts": ["lean/InfoGeometry/Canonical/M2Mod.lean"]},
                        "formal_objects": {"M2": ["M2Mod.obj"]},
                        "acceptance_theorems": {"M2": ["MyNs.acc_thm"]},
                    }
                ),
                encoding="utf-8",
            )
            rt_m2 = ResolvedTarget(m2_mod, "lean/InfoGeometry/Canonical/M2Mod.lean", "InfoGeometry.Canonical.M2Mod", True)
            self.assertEqual(
                check_t3_cons_02_contracts_to_lean_declarations(
                    root, DiscoveredArtifacts([], [env_dot], [], [], [], [env_dot], []), [rt_m2], require_all_envelope_targets=True
                ).status,
                "PASS",
            )

    def test_regression_r5_prop_bundler_vacuity_intake_bleed_and_discovery(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        with tempfile.TemporaryDirectory(prefix="ec_reg_r5_") as td:
            root = Path(td)

            # 1. Unparenthesized ∀, nested ∀, equation-style `| _ =>`, and `: Sort 0`
            for fname, body in (
                ("B1ForallUnparenTrue.lean", "theorem t : ∀ x : Nat, True := fun _ => trivial\n"),
                ("B4NestedForallUnparen.lean", "theorem t : ∀ (x : Nat), ∀ y : Nat, True := fun _ _ => trivial\n"),
                ("B2PatternMatchTrue.lean", "theorem t : Nat → True\n  | _ => trivial\n"),
            ):
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertTrue(scan_native_decide_and_vacuous_true(body), msg=f"{fname} missed by scan_nv")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 2. N6a (direct scan_parameterized_prop_bundlers), Sort 0, Rule 1 ascription, Rule 3 Bundle.ok,
            #    dead `have` (ring/cases), trivial `by omega`, `by simp [...]`, and bare-var `by ring`
            bundler_cases = (
                (
                    "N6aForallDirect.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok : ∀ n : Nat, Bundle n := fun n => ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "A4Sort0.lean",
                    "structure Bundle (n : Nat) : Sort 0 where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "A1TypeAscriptionCtor.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := (⟨rfl, Nat.add_zero n⟩ : Bundle n)\n",
                ),
                (
                    "A2BundleDotOkName.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma Bundle.ok (n : Nat) : Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "DeadHaveRing.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := by\n  have _ : 0 = 0 := by ring\n  exact ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "DeadHaveCases.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := by\n  have _ : n = n := by\n    cases n with\n    | zero => rfl\n    | succ _ => rfl\n  exact ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "TrivialOmega.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := ⟨rfl, by omega⟩\n",
                ),
                (
                    "A6bSimpBrackets.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := by simp [Nat.add_zero]; exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "BareVarRing.lean",
                    "structure CausalPair (a b : Nat) : Prop where\n  h1 : a + b = b + a\n  h2 : a * b = b * a\n"
                    "theorem causalPair_witness (a b : Nat) : CausalPair a b := by\n  constructor\n  · ring\n  · ring\n",
                ),
            )
            for fname, body in bundler_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertTrue(scan_parameterized_prop_bundlers(body), msg=f"{fname} missed by scan_parameterized_prop_bundlers")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # Genuine Trap-T17 concrete model witness + goal-level induction remain clean
            t17_concrete = (
                "structure ModelPred (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                "theorem modelPred_std : ModelPred (1 + 1) := by\n  constructor <;> norm_num\n"
            )
            self.assertEqual(scan_parameterized_prop_bundlers(t17_concrete), [])

            # 3. Sub-bullet short-label bleed (C1, C2), multi-source header + sub-bullets, & shared-predicate C3
            (root / "cached" / "drive_docs").mkdir(parents=True)
            (root / "docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            c_err = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.json"
            c_err.write_text(json.dumps({"error": {"code": 403, "message": "Access denied"}}), encoding="utf-8")
            e_html = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            m1b = root / "docs" / "M1B.md"
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )

            # C1: indented bullet mentioning Source E without ID must NOT satisfy C
            m1b.write_text(
                f"- Source C (`{SOURCE_C_ID}`): saved locally\n"
                "  - Sibling status: Source E hit HTTP 403 access blocker\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                f"- Source E (`{SOURCE_E_ID}`): HTTP 403 access blocker\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "FAIL",
            )

            # C2: indented non-bullet continuation mentioning Source E without ID must NOT satisfy C
            m1b.write_text(
                f"- Source C (`{SOURCE_C_ID}`): saved locally\n"
                "  Sibling status: Source E hit HTTP 403 access blocker\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                f"- Source E (`{SOURCE_E_ID}`): HTTP 403 access blocker\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "FAIL",
            )

            # Multi-source header + indented per-label sub-bullets: C saved locally, E HTTP 403 -> C is NOT blocked -> FAIL
            m1b.write_text(
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`):\n"
                "  - C: saved locally\n"
                "  - E: HTTP 403\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "FAIL",
            )

            # Multi-source header + indented sub-bullets with E first and C genuinely blocked -> PASS
            m1b.write_text(
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`):\n"
                "  - E: HTTP 403\n"
                "  - C: HTTP 403\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "PASS",
            )

            # C3: shared predicate on single line (`Sources C & E are both blocked by HTTP 403`) -> PASS
            m1b.write_text(
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`) are both blocked by HTTP 403\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "PASS",
            )

            # 4. Defensive null/non-dict chunk guards in intake_checks.py & tier2_tier3_tier4.py (no AttributeError)
            null_chunks = [None] * 84
            src_b_null = root / "cached" / "aistudio_prompt_1v8Jj30jF2ytMHunuZq_FXEBjWcNFyw0O.json"
            src_b_null.write_text(
                json.dumps({"runSettings": {}, "systemInstruction": {}, "chunkedPrompt": {"chunks": null_chunks}}),
                encoding="utf-8",
            )
            extract_dir_b = root / "cached" / "aistudio_extracts" / "aistudio_prompt_1v8Jj30jF2ytMHunuZq_FXEBjWcNFyw0O"
            extract_dir_b.mkdir(parents=True, exist_ok=True)
            (extract_dir_b / "manifest.json").write_text("{}", encoding="utf-8")
            (extract_dir_b / "transcript.md").write_text("", encoding="utf-8")
            self.assertEqual(check_t1_intake_02_source_b(root, "baseline45").status, "FAIL")
            self.assertEqual(check_t2_bnd_01_turn10_drive_attachment(root, [m1b]).status, "FAIL")
            self.assertEqual(check_t2_bnd_02_turn24_indented_fence(root, [m1b]).status, "FAIL")
            self.assertEqual(check_t2_bnd_03_turn_delta_separation(root, [m1b], [], "baseline45").status, "FAIL")
            self.assertEqual(check_t2_bnd_03_turn_delta_separation(root, [m1b], [], "live84").status, "FAIL")

            # 5. Auto-discovery --targets without --manifest, B5 (.lean -> dotted target_module), B6 (*-qa.md), & Mermaid spaces
            (root / "lean" / "InfoGeometry" / "Canonical").mkdir(parents=True)
            (root / "lean" / "InfoGeometry.lean").write_text("-- root\n", encoding="utf-8")
            (root / "lean" / "InfoGeometry" / "Canonical" / "M2Mod.lean").write_text("theorem x : 1 = 1 := rfl\n", encoding="utf-8")
            (root / "artifacts" / "qms").mkdir(parents=True)
            aud_dotted = root / "artifacts" / "qms" / "20261122-audit_report.json"
            aud_dotted.write_text(
                json.dumps(
                    {
                        "schema": "info_geometry.qms.audit_report.v1",
                        "target_module": "InfoGeometry.Canonical.M2Mod",
                        "artifact_hashes": {"lean/InfoGeometry/Canonical/M2Mod.lean": "sha256:" + "0" * 64},
                    }
                ),
                encoding="utf-8",
            )
            qa_dash = root / "artifacts" / "qms" / "20261122-M2Mod-qa.md"
            qa_dash.write_text("# QA\n", encoding="utf-8")
            arts_auto, errs_auto = discover_artifacts(
                root, manifest_args=None, baseline_only=False, raw_targets=["lean/InfoGeometry/Canonical/M2Mod.lean"]
            )
            self.assertEqual(errs_auto, [])
            self.assertIn(aud_dotted, arts_auto.audit_reports)
            self.assertIn(qa_dash, arts_auto.qa_reports)
            self.assertEqual(check_t3_cons_05_audit_report_hashes(root, arts_auto).status, "FAIL")

            nodes_sp, edges_sp = parse_mermaid_dag("flowchart TD\n  A -.-> |ok| B\n  B --> |ok| A\n")
            self.assertEqual(nodes_sp, {"A", "B"})
            self.assertEqual(edges_sp, [("A", "B"), ("B", "A")])
            self.assertFalse(kahn_topological_sort(nodes_sp, edges_sp)[0])

    def test_regression_r6_unicode_bullets_suffices_binders_and_intake_article(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        with tempfile.TemporaryDirectory(prefix="ec_reg_r6_") as td:
            root = Path(td)

            # 1. Unicode Lean identifiers & `#print axioms` boundary (Finding 1)
            cz_real = REPO_ROOT / "lean" / "InfoGeometry" / "Arithmetic" / "CompletedZetaApollonianV4Bridge.lean"
            if cz_real.is_file():
                cz_decls = extract_non_opaque_lean_declarations(cz_real.read_text(encoding="utf-8"))
                self.assertIn("completedRiemannZeta₀_conj", cz_decls)

            (root / "lean" / "InfoGeometry" / "Arithmetic").mkdir(parents=True)
            (root / "lean" / "InfoGeometry.lean").write_text("-- root\n", encoding="utf-8")
            (root / "artifacts" / "qms").mkdir(parents=True)
            cz_mod = root / "lean" / "InfoGeometry" / "Arithmetic" / "CompletedZetaDemo.lean"
            cz_mod.write_text(
                "namespace InfoGeometry.Arithmetic\n"
                "lemma completedRiemannZeta₀_conj (s : Nat) : s = s := rfl\n"
                "lemma α_bridge⁺ (s : Nat) : s = s := rfl\n"
                "end InfoGeometry.Arithmetic\n",
                encoding="utf-8",
            )
            cz_aud = root / "lean" / "InfoGeometry" / "Arithmetic" / "CompletedZetaDemoAudit.lean"
            cz_aud.write_text(
                "#print axioms InfoGeometry.Arithmetic.completedRiemannZeta₀_conj\n"
                "#print axioms InfoGeometry.Arithmetic.α_bridge⁺\n",
                encoding="utf-8",
            )
            env_u = root / "artifacts" / "qms" / "env_u.json"
            env_u.write_text(
                json.dumps(
                    {
                        "schema": "info_geometry.qms.intent_envelope.v1",
                        "owner_search": {"target_artifacts": ["lean/InfoGeometry/Arithmetic/CompletedZetaDemo.lean"]},
                        "formal_objects": {"M3": ["CompletedZetaDemo.obj"]},
                        "acceptance_theorems": {"M3": ["completedRiemannZeta₀_conj", "α_bridge⁺"]},
                    }
                ),
                encoding="utf-8",
            )
            rt_cz = ResolvedTarget(
                cz_mod, "lean/InfoGeometry/Arithmetic/CompletedZetaDemo.lean", "InfoGeometry.Arithmetic.CompletedZetaDemo", True
            )
            self.assertEqual(
                check_t3_cons_02_contracts_to_lean_declarations(
                    root, DiscoveredArtifacts([], [env_u], [], [], [], [env_u], []), [rt_cz], require_all_envelope_targets=True
                ).status,
                "PASS",
            )
            # Negative: unrelated prefix/suffix in `#print axioms` must NOT satisfy `completedRiemannZeta₀_conj`
            cz_aud.write_text(
                "#print axioms other_completedRiemannZeta₀_conj\n"
                "#print axioms InfoGeometry.Arithmetic.α_bridge⁺₂\n",
                encoding="utf-8",
            )
            self.assertEqual(
                check_t3_cons_02_contracts_to_lean_declarations(
                    root, DiscoveredArtifacts([], [env_u], [], [], [], [env_u], []), [rt_cz], require_all_envelope_targets=True
                ).status,
                "FAIL",
            )

            # 2. Bulleted `have`/`let`, `suffices` aux branches, Rule 1 proof-body ascriptions,
            #    nested-paren binders, binder-derived expressions, and col-0 equation arms (Findings 2-5)
            bypass_cases = (
                (
                    "BulletHaveCases.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := by\n  constructor\n"
                    "  · have _ : n = n := by\n      cases n with\n      | zero => rfl\n      | succ _ => rfl\n    rfl\n"
                    "  · exact Nat.add_zero n\n",
                ),
                (
                    "BulletLetCases.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := by\n  constructor\n"
                    "  · let _ := by\n      cases n with\n      | zero => exact rfl\n      | succ _ => exact rfl\n    rfl\n"
                    "  · exact Nat.add_zero n\n",
                ),
                (
                    "CaseArmHaveCases.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok : ∀ n : Nat, Bundle n\n  | n => by\n    have _ : n = n := by\n      cases n with\n      | zero => rfl\n      | succ _ => rfl\n    exact ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "SufficesDeadCases.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := by\n"
                    "  suffices _ : n = n by exact ⟨rfl, Nat.add_zero n⟩\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => rfl\n",
                ),
                (
                    "BulletSufficesDeadCases.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := by\n  constructor\n"
                    "  · suffices _ : n = n by rfl\n    cases n with\n    | zero => rfl\n    | succ _ => rfl\n"
                    "  · exact Nat.add_zero n\n",
                ),
                (
                    "Rule1ProofBodyVarAscr.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := let h := ⟨rfl, Nat.add_zero n⟩; (h : Bundle n)\n",
                ),
                (
                    "Rule1ProofBodyCallAscr.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok1 (n : Nat) : Bundle n := ⟨rfl, Nat.add_zero n⟩\n"
                    "lemma ok2 (n : Nat) : Bundle n := (ok1 n : Bundle n)\n",
                ),
                (
                    "Rule1ProofBodyFunAscr.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := (fun (h : Bundle n) => h) ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "NestedParenBinder.lean",
                    "structure Bundle (M : Matrix (Fin 2) (Fin 2) Nat) : Prop where\n  p1 : M = M\n  p2 : M + 0 = M\n"
                    "lemma ok (n : Nat) (M : Matrix (Fin 2) (Fin 2) Nat) : Bundle M := by\n  constructor\n  · rfl\n  · simp [Nat.add_zero]\n",
                ),
                (
                    "BinderExprOmega.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle (n + 0) := ⟨rfl, by omega⟩\n",
                ),
                (
                    "BinderIdRing.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle (id n) := by\n  constructor\n  · rfl\n  · ring\n",
                ),
                (
                    "VariableBinderExprOmega.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "variable (n : Nat)\n"
                    "lemma bundle_ok : Bundle (n + 0) := ⟨rfl, by omega⟩\n",
                ),
                (
                    "Col0EqStyleBundler.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok : ∀ n : Nat, Bundle n\n| 0 => ⟨rfl, rfl⟩\n| _ => ⟨rfl, Nat.add_zero _⟩\n",
                ),
            )
            for fname, body in bypass_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertTrue(
                    scan_parameterized_prop_bundlers(body),
                    msg=f"{fname} missed by scan_parameterized_prop_bundlers",
                )
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # Authentic proofs MUST NOT be masked or false-flagged
            self.assertFalse(
                _has_concrete_model_args(
                    "Bundle M",
                    "ok (n : Nat) (M : Matrix (Fin 2) (Fin 2) Nat) : Bundle M :=",
                    "Bundle M",
                    "",
                )
            )
            suffices_real_cases = (
                "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                "lemma bundle_ok (n : Nat) : Bundle n := by\n"
                "  suffices _ : n = n by\n    cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                "  rfl\n"
            )
            self.assertEqual(scan_parameterized_prop_bundlers(suffices_real_cases), [])
            calc_binder_expr = (
                "structure IsOrtho (P Q : Nat) : Prop where\n  h1 : P + Q = Q + P\n  h2 : Q + P = P + Q\n"
                "theorem ortho_shell (P G : Nat) : IsOrtho P (G - P) := by\n"
                "  refine ⟨?_, ?_⟩\n  · calc P + (G - P) = (G - P) + P := by omega\n  · calc (G - P) + P = P + (G - P) := by omega\n"
            )
            self.assertEqual(scan_parameterized_prop_bundlers(calc_binder_expr), [])
            concrete_tag_rw = (
                "structure RootData (τ : Tag) (K : Type*) : Prop where\n  c1 : τ = τ\n  c2 : K = K\n"
                "theorem root_g2 (K : Type*) : RootData .G2 K := by\n  constructor <;> rw [eq_self_iff_true]\n"
            )
            self.assertEqual(scan_parameterized_prop_bundlers(concrete_tag_rw), [])

            # `<|` and unparenthesized `match ... with` return types
            ret_lp, split_lp, _ = _find_decl_return_type_and_split("theorem lp : P <| fun x => Q x := by sorry", 7)
            self.assertEqual(ret_lp, "P <| fun x => Q x")
            self.assertIsNotNone(split_lp)
            ret_mt, split_mt, _ = _find_decl_return_type_and_split(
                "theorem mt (n : Nat) : match n with | 0 => True | _ => True := by sorry", 7
            )
            self.assertEqual(ret_mt, "match n with | 0 => True | _ => True")
            self.assertIsNotNone(split_mt)

            # 3. English indefinite article "A" must NOT false-trigger Source A bleed (Finding 6)
            (root / "cached" / "drive_docs").mkdir(parents=True)
            (root / "docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            (root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.json").write_text(
                json.dumps({"error": {"code": 403, "message": "Access denied"}}), encoding="utf-8"
            )
            (root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html").write_text(
                "<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8"
            )
            m1b = root / "docs" / "M1B.md"
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )
            for phrase in (
                "A blocked HTTP 403 download was recorded.",
                "A failed HTTP 403 response occurred.",
                "A is an inaccessible Drive URL (HTTP 403).",
            ):
                m1b.write_text(
                    f"- Source C (`{SOURCE_C_ID}`): {phrase}\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    f"- Source E (`{SOURCE_E_ID}`): HTTP 403 access blocker\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "PASS",
                    msg=f"False Source A bleed on: {phrase}",
                )
            # Negative: an indented `- A: HTTP 403` sub-bullet still must NOT satisfy Source C
            m1b.write_text(
                f"- Source C (`{SOURCE_C_ID}`): saved locally\n"
                "  - A: HTTP 403 access blocker\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                f"- Source E (`{SOURCE_E_ID}`): HTTP 403 access blocker\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "FAIL",
            )

    def test_regression_r7_intake_guillemets_subblocks_rules_and_binders(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        with tempfile.TemporaryDirectory(prefix="ec_reg_r7_") as td:
            root = Path(td)

            # 1. Intake multi-source clause attribution, IS4, header propagation, reverse bleed & nested sub-bullets
            (root / "cached" / "drive_docs").mkdir(parents=True)
            (root / "docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            c_err_json = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.json"
            c_err_json.write_text(json.dumps({"error": {"code": 403, "message": "Access denied"}}), encoding="utf-8")
            e_html = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            m1b = root / "docs" / "M1B.md"
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )

            # 1a. Sources C & A: C saved locally, A blocked by HTTP 403 -> A blocker found, C MUST FAIL
            m1b.write_text(
                f"- Sources C (`{SOURCE_C_ID}`) & A (`{SOURCE_A_ID}`): C saved locally, A blocked by HTTP 403\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                f"- Source E (`{SOURCE_E_ID}`): HTTP 403 access blocker\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_A_ID))
            self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID))
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "FAIL",
            )

            # 1b. IS4: C saved locally and A blocked by HTTP 403 -> MUST FAIL for C
            m1b.write_text(
                f"- Source C (`{SOURCE_C_ID}`): C saved locally and A blocked by HTTP 403\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                f"- Source E (`{SOURCE_E_ID}`): HTTP 403 access blocker\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID))
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "FAIL",
            )

            # 1c. Sources A & C: A blocked, C saved -> A blocker found, C MUST FAIL
            m1b.write_text(
                f"- Sources A (`{SOURCE_A_ID}`) & C (`{SOURCE_C_ID}`): A blocked by HTTP 403, C saved locally\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                f"- Source E (`{SOURCE_E_ID}`): HTTP 403 access blocker\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_A_ID))
            self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID))
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "FAIL",
            )

            # 1d. Source C: HTTP 403 blocked, whereas E is accessible (valid E -> PASS; invalid E reverse bleed -> FAIL)
            e_html.unlink()
            e_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.md"
            e_ok_bytes = b"Source E valid markdown\n"
            e_ok_path.write_bytes(e_ok_bytes)
            e_sha = hashlib.sha256(e_ok_bytes).hexdigest()
            m1b.write_text(
                f"- Source C (`{SOURCE_C_ID}`): HTTP 403 blocked, whereas E is accessible\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_C_ID))
            self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_E_ID))
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "PASS",
            )
            # Reverse bleed guard: if E is actually HTML sign-in, E MUST NOT steal C's HTTP 403
            e_ok_path.unlink()
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            c_err_json.unlink()
            c_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            c_ok_bytes = b"Source C valid markdown\n"
            c_ok_path.write_bytes(c_ok_bytes)
            c_sha = hashlib.sha256(c_ok_bytes).hexdigest()
            m1b.write_text(
                f"- Source C (`{SOURCE_C_ID}`): HTTP 403 blocked, whereas E is accessible\n"
                f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_E_ID))
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "FAIL",
            )

            # 1e. Multi-source header with nested continuation under Source E sub-bullet MUST NOT bleed into C
            c_ok_path.unlink()
            c_err_json.write_text(json.dumps({"error": {"code": 403, "message": "Access denied"}}), encoding="utf-8")
            m1b.write_text(
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`):\n"
                f"  - Source E (`{SOURCE_E_ID}`):\n"
                "    HTTP 403 Access Denied\n"
                f"  - Source C (`{SOURCE_C_ID}`): saved locally\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID))
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "FAIL",
            )

            # 2. Dotted guillemet identifiers & `#print axioms` namespace/universe boundaries
            self.assertEqual(split_lean_qual_ident("Ns.«foo.bar»"), ["Ns", "«foo.bar»"])
            self.assertEqual(lean_short_name("Ns.«foo.bar»"), "«foo.bar»")

            (root / "lean" / "InfoGeometry" / "Arithmetic").mkdir(parents=True)
            (root / "lean" / "InfoGeometry.lean").write_text("-- root\n", encoding="utf-8")
            (root / "artifacts" / "qms").mkdir(parents=True)
            guil_mod = root / "lean" / "InfoGeometry" / "Arithmetic" / "GuilDot.lean"
            guil_mod.write_text(
                "namespace Ns\nlemma «foo.bar» : 1 = 1 := rfl\nend Ns\n"
                "namespace RightNs\nlemma foo : 1 = 1 := rfl\nend RightNs\n"
                "namespace InfoGeometry.Arithmetic\nlemma bar.{u} : 1 = 1 := rfl\nend InfoGeometry.Arithmetic\n",
                encoding="utf-8",
            )
            guil_aud = root / "lean" / "InfoGeometry" / "Arithmetic" / "GuilDotAudit.lean"
            guil_aud.write_text(
                "#print axioms Ns.«foo.bar»\n"
                "#print axioms RightNs.foo\n"
                "#print axioms InfoGeometry.Arithmetic.bar.{0}\n",
                encoding="utf-8",
            )
            env_g = root / "artifacts" / "qms" / "env_guil.json"
            env_g.write_text(
                json.dumps(
                    {
                        "schema": "info_geometry.qms.intent_envelope.v1",
                        "owner_search": {"target_artifacts": ["lean/InfoGeometry/Arithmetic/GuilDot.lean"]},
                        "formal_objects": {"M3": ["GuilDot.obj"]},
                        "acceptance_theorems": {"M3": ["Ns.«foo.bar»", "RightNs.foo", "bar"]},
                    }
                ),
                encoding="utf-8",
            )
            rt_g = ResolvedTarget(guil_mod, "lean/InfoGeometry/Arithmetic/GuilDot.lean", "InfoGeometry.Arithmetic.GuilDot", True)
            self.assertEqual(
                check_t3_cons_02_contracts_to_lean_declarations(
                    root, DiscoveredArtifacts([], [env_g], [], [], [], [env_g], []), [rt_g], require_all_envelope_targets=True
                ).status,
                "PASS",
            )
            # T1-LEAN-05 declaration extraction also passes for `Ns.«foo.bar»`
            expected_g = _extract_expected_decls_from_artifacts(DiscoveredArtifacts([], [env_g], [], [], [], [env_g], []))
            self.assertEqual(expected_g, {"InfoGeometry.Arithmetic.GuilDot": ["Ns.«foo.bar»", "RightNs.foo", "bar"]})
            with unittest.mock.patch("tools.infra.build._validate_lake_workspace_integrity", return_value=None):
                c1_5_g = check_t1_lean_05_workspace_and_declarations(root, [rt_g], expected_g)
                self.assertEqual(c1_5_g.status, "PASS", msg=c1_5_g.summary)
                c1_5_g_bad = check_t1_lean_05_workspace_and_declarations(
                    root, [rt_g], {"InfoGeometry.Arithmetic.GuilDot": ["Ns.«missing.decl»"]}
                )
                self.assertEqual(c1_5_g_bad.status, "FAIL", msg=c1_5_g_bad.summary)
            # WrongNs.foo MUST FAIL for RightNs.foo
            guil_aud.write_text(
                "#print axioms Ns.«foo.bar»\n"
                "#print axioms WrongNs.foo\n"
                "#print axioms InfoGeometry.Arithmetic.bar.{0}\n",
                encoding="utf-8",
            )
            self.assertEqual(
                check_t3_cons_02_contracts_to_lean_declarations(
                    root, DiscoveredArtifacts([], [env_g], [], [], [], [env_g], []), [rt_g], require_all_envelope_targets=True
                ).status,
                "FAIL",
            )

            # 3. Sub-blocks (`A1`–`A6`, `<;> have`, `r6_2` Minor 1), `A14` inline or-pattern, Rules 2/4 (`A7`–`A9b`),
            #    Pi-arrows & auto-implicits (`A10`–`A11b`, `Gap3`), Unicode fields (`A12`, `A13`, `Minor2`)
            bypass_cases = (
                (
                    "A1SkipSemicolonHave.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := by\n"
                    "  skip; have _ : n = n := by\n    cases n with\n    | zero => rfl\n    | succ _ => rfl\n"
                    "  exact ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "A1InlineByHave.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := by have _ : n = n := by\n    cases n with\n    | zero => rfl\n    | succ _ => rfl\n"
                    "  exact ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "A2BraceHave.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := by\n"
                    "  { have _ : n = n := by\n      cases n with\n      | zero => rfl\n      | succ _ => rfl\n    exact ⟨rfl, Nat.add_zero n⟩ }\n",
                ),
                (
                    "A3SufficesNestedHave.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := by\n"
                    "  suffices _ : n = n by\n    have _ : n = n := by\n      cases n with\n      | zero => rfl\n      | succ _ => rfl\n    exact ⟨rfl, Nat.add_zero n⟩\n  rfl\n",
                ),
                (
                    "A4SufficesNestedCalc.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle (n + 0) := by\n"
                    "  suffices _ : 1 = 1 by\n    have _ : 1 = 1 := by\n      calc 1 = 1 := rfl\n    exact ⟨rfl, by omega⟩\n  rfl\n",
                ),
                (
                    "A5NextArrowHave.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := by\n"
                    "  next => have _ : n = n := by\n    cases n with\n    | zero => rfl\n    | succ _ => rfl\n  exact ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "A6BulletCaseHave.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := by\n  constructor\n"
                    "  · case _ => have _ : n = n := by\n      cases n with\n      | zero => rfl\n      | succ _ => rfl\n    rfl\n"
                    "  · exact Nat.add_zero n\n",
                ),
                (
                    "SemicolonSeqHave.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := by\n"
                    "  constructor <;> have _ : n = n := by\n    cases n with\n    | zero => rfl\n    | succ _ => rfl\n"
                    "  · rfl\n  · exact Nat.add_zero n\n",
                ),
                (
                    "R6Minor1CaseP2Have.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := by\n  constructor\n"
                    "  case p1 => rfl\n"
                    "  case p2 => have _ : n = n := by\n      cases n with\n      | zero => rfl\n      | succ _ => rfl\n    exact Nat.add_zero n\n",
                ),
                (
                    "R6Minor1CaseP2Suffices.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := by\n  constructor\n"
                    "  case p1 => rfl\n"
                    "  case p2 => suffices _ : n = n by exact Nat.add_zero n\n      cases n with\n      | zero => rfl\n      | succ _ => rfl\n",
                ),
                (
                    "R6Minor1SemiSuffices.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := by\n"
                    "  refine ⟨rfl, ?_⟩; suffices _ : n = n by exact Nat.add_zero n; cases n with\n"
                    "  | zero => rfl\n  | succ _ => rfl\n",
                ),
                (
                    "A7WhereAnon.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n :=\n  h\nwhere\n  h : Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "A7WhereBrace.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n :=\n  h\nwhere\n  h : Bundle n := { p1 := rfl, p2 := Nat.add_zero n }\n",
                ),
                (
                    "A7WhereMk.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n :=\n  h\nwhere\n  h : Bundle n := .mk rfl (Nat.add_zero n)\n",
                ),
                (
                    "A8IndentedLetRule2.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := by\n  let\n    h : Bundle n := ⟨rfl, Nat.add_zero n⟩\n  exact h\n",
                ),
                (
                    "A9Rule4InnerArrow.lean",
                    "structure Bundle (T : Type) : Prop where\n  p1 : T = T\n  p2 : True\n"
                    "lemma ok : Bundle (Nat → Nat) := ⟨rfl, trivial⟩\n",
                ),
                (
                    "A9bRule4InnerAnd.lean",
                    "structure Bundle (P : Prop) : Prop where\n  p1 : P = P\n  p2 : True\n"
                    "lemma ok : Bundle (True ∧ True) := ⟨rfl, trivial⟩\n",
                ),
                (
                    "A10PiArrowBinder.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok : (n : Nat) → Bundle (n + 0) := fun n => ⟨rfl, by omega⟩\n",
                ),
                (
                    "A11AutoImplicitUnrelated.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (unused : Nat) : Bundle n := ⟨rfl, by omega⟩\n",
                ),
                (
                    "A11bAutoImplicitExpr.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok : Bundle (n + 0) := ⟨rfl, by omega⟩\n",
                ),
                (
                    "A12UnicodeBraceFields.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p₁ : n = n\n  p₂ : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := { p₁ := rfl, p₂ := Nat.add_zero n }\n",
                ),
                (
                    "A13UnicodeWhereFields.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p₁ : n = n\n  p₂ : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n where\n  p₁ := rfl\n  p₂ := Nat.add_zero n\n",
                ),
                (
                    "Gap3MixedTagBinderExpr.lean",
                    "structure Bundle (tag : Tag) (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle .G2 (n + 0) := ⟨rfl, by omega⟩\n",
                ),
                (
                    "Minor2SpacelessLe.lean",
                    "structure Bundle (P : Prop) : Prop where\n  p1 : P = P\n  p2 : True\n"
                    "lemma bundle_ok (n : Nat) : Bundle (n≤n) := ⟨rfl, by omega⟩\n",
                ),
            )
            for fname, body in bypass_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertTrue(
                    scan_parameterized_prop_bundlers(body),
                    msg=f"{fname} missed by scan_parameterized_prop_bundlers",
                )
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # A14 inline or-pattern vacuous `: True`
            a14_src = "theorem t : Nat → True | 0 | 1 => trivial | _ => trivial\n"
            self.assertTrue(scan_native_decide_and_vacuous_true(a14_src))
            a14_fp = root / "A14OrPatternTrue.lean"
            a14_fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + a14_src, encoding="utf-8")
            self.assertEqual(
                check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(a14_fp, "A14OrPatternTrue.lean", None, True)], strict_live=True
                ).status,
                "FAIL",
            )

            # Positive controls MUST NOT false-trigger
            a15_named = (
                "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                "lemma bundle_ok (n : Nat) : Bundle n := by\n"
                "  suffices h : n + 0 = n by exact ⟨rfl, h⟩\n"
                "  cases n with\n  | zero => rfl\n  | succ k => simp [Nat.add_zero]\n"
            )
            a15_this = (
                "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                "lemma bundle_ok (n : Nat) : Bundle n := by\n"
                "  suffices n + 0 = n by exact ⟨rfl, this⟩\n"
                "  cases n with\n  | zero => rfl\n  | succ k => simp [Nat.add_zero]\n"
            )
            self.assertEqual(scan_parameterized_prop_bundlers(a15_named), [])
            self.assertEqual(scan_parameterized_prop_bundlers(a15_this), [])
            for p_name, p_body in (("A15Named.lean", a15_named), ("A15This.lean", a15_this)):
                p_fp = root / p_name
                p_fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + p_body, encoding="utf-8")
                self.assertEqual(
                    check_t1_lean_04_placeholder_and_vacuity(
                        REPO_ROOT, [ResolvedTarget(p_fp, p_name, None, True)], strict_live=True
                    ).status,
                    "PASS",
                    msg=f"{p_name} false-failed T1-LEAN-04",
                )

            abs_fun_src = "theorem abs_fun : |x| = 0 → (fun y => y) 0 = 0 := by sorry\n"
            ret_abs, split_abs, _ = _find_decl_return_type_and_split(abs_fun_src, 7)
            self.assertEqual(ret_abs, "|x| = 0 → (fun y => y) 0 = 0")
            self.assertIsNotNone(split_abs)
            self.assertEqual(scan_native_decide_and_vacuous_true(abs_fun_src), [])

            minor3_ind = (
                "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                "inductive Holder : Type where\n| mk (h : Bundle 0) : Holder\n"
                "lemma bundle_ok : Bundle 0 := ⟨rfl, rfl⟩\n"
            )
            self.assertEqual(scan_parameterized_prop_bundlers(minor3_ind), [])

            rule2_struct = (
                "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                "structure Outer (n : Nat) : Prop where\n  sub : Bundle n\n"
                "lemma bundle_ok (n : Nat) : Bundle n := ⟨rfl, Nat.add_zero n⟩\n"
            )
            self.assertEqual(scan_parameterized_prop_bundlers(rule2_struct), [])

            rule4_and = (
                "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                "theorem use_b (n : Nat) : Bundle n ∧ n = n := ⟨⟨rfl, Nat.add_zero n⟩, rfl⟩\n"
            )
            self.assertEqual(scan_parameterized_prop_bundlers(rule4_and), [])

            g2_rw = (
                "structure RootData (τ : Tag) (K : Type*) : Prop where\n  c1 : τ = τ\n  c2 : K = K\n"
                "theorem root_g2 (K : Type*) : RootData .G2 K := by\n  constructor <;> rw [eq_self_iff_true]\n"
            )
            self.assertEqual(scan_parameterized_prop_bundlers(g2_rw), [])

            calc_mg = (
                "structure IsOrtho (P Q : Nat) : Prop where\n  h1 : P + Q = Q + P\n  h2 : Q + P = P + Q\n"
                "theorem ortho_shell (P G M : Nat) : IsOrtho P (M - G) := by\n"
                "  refine ⟨?_, ?_⟩\n  · calc P + (M - G) = (M - G) + P := by omega\n  · calc (M - G) + P = P + (M - G) := by omega\n"
            )
            self.assertEqual(scan_parameterized_prop_bundlers(calc_mg), [])

            calc_mixed = (
                "structure Bundle (tag : Tag) (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                "lemma bundle_ok (n : Nat) : Bundle .G2 (n + 0) := by\n"
                "  refine ⟨rfl, ?_⟩\n  calc n + 0 + 0 = n + 0 := by omega\n"
            )
            self.assertEqual(scan_parameterized_prop_bundlers(calc_mixed), [])

    def test_regression_r8_rule4b_combinators_suffices_unicode_and_intake_isolation(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        with tempfile.TemporaryDirectory(prefix="ec_reg_r8_") as td:
            root = Path(td)

            # 1. Lean Findings 1-7: Rule 4b, unparam := mk ::, tactic combinators & parens,
            #    parenthesized (match ... with ...) before eq arms, Rule 3 .mk.{u}, dead suffices simp_all, Unicode ops
            lean_bypass_cases = (
                (
                    "Rule4bFullBypass.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := ⟨rfl, Nat.add_zero n⟩\n"
                    "theorem wrapper (n : Nat) : n = n ∧ n = n → Bundle n := fun _ => ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "Rule4bForallAndBypass.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_ok (n : Nat) : Bundle n := ⟨rfl, Nat.add_zero n⟩\n"
                    "theorem wrapper : ∀ n : Nat, n = n ∧ n = n → Bundle n := fun _ _ => ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "UnparamAssignColon.lean",
                    "structure Bundle : Prop := mk ::\n  (p1 : 1 = 1)\n  (p2 : 2 = 2)\n"
                    "theorem ok : Bundle := by cases (0 : Nat) <;> exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "AllGoalsHave.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := by\n  all_goals have _ : n = n := by\n"
                    "    cases n with\n    | zero => rfl\n    | succ _ => rfl\n  exact ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "TryHave.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := by\n  try have _ : n = n := by\n"
                    "    cases n with\n    | zero => rfl\n    | succ _ => rfl\n  exact ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "FocusHave.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := by\n  focus have _ : n = n := by\n"
                    "    cases n with\n    | zero => rfl\n    | succ _ => rfl\n  exact ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "RepeatHave.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := by\n  repeat have _ : n = n := by\n"
                    "    cases n with\n    | zero => rfl\n    | succ _ => rfl\n  exact ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "FirstPipeHave.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := by\n  first | have _ : n = n := by\n"
                    "    cases n with\n    | zero => rfl\n    | succ _ => rfl\n  | exact ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "ParenHaveMultiline.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := by\n  (have _ : n = n := by\n"
                    "    cases n with\n    | zero => rfl\n    | succ _ => rfl)\n  exact ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "Rule3MkUniv.lean",
                    "structure Bundle (α : Type u) : Prop where\n  p1 : α = α\n  p2 : True\n"
                    "lemma ok (α : Type u) : Bundle α := Bundle.mk.{u} rfl trivial\n",
                ),
                (
                    "DeadSufficesSimpAll.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := by\n  suffices _ : n = n by constructor <;> simp_all\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => rfl\n",
                ),
                (
                    "UnicodeInfMixed.lean",
                    "structure Bundle (tag : Tag) (P : Prop) : Prop where\n  p1 : P = P\n  p2 : True\n"
                    "lemma ok (n : Nat) : Bundle .G2 (n⊓n) := ⟨rfl, by omega⟩\n",
                ),
                (
                    "UnicodeHeqMixed.lean",
                    "structure Bundle (tag : Tag) (P : Prop) : Prop where\n  p1 : P = P\n  p2 : True\n"
                    "lemma ok (n : Nat) : Bundle .G2 (n≍n) := ⟨rfl, by omega⟩\n",
                ),
            )
            for fname, body in lean_bypass_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertTrue(scan_parameterized_prop_bundlers(body), msg=f"{fname} missed by bundler scanner")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # Parenthesized (match ... with ...) in return type before eq-arms
            match_ret_vac = (
                "theorem vac (n : Nat) : (match n with | 0 => Nat | _ => Nat) → True\n"
                "  | 0 => trivial\n  | _ => trivial\n"
            )
            self.assertTrue(scan_native_decide_and_vacuous_true(match_ret_vac))
            mr_fp = root / "MatchRetBeforeEqArm.lean"
            mr_fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + match_ret_vac, encoding="utf-8")
            self.assertEqual(
                check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(mr_fp, "MatchRetBeforeEqArm.lean", None, True)], strict_live=True
                ).status,
                "FAIL",
            )

            # Positive controls: suffices with assumption / simp_all / simp [*], plus real owners DetectorFoundationalCopula & CuntzSubsystem
            suff_pos_cases = (
                (
                    "SufficesAssumption.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := by\n  suffices h : n + 0 = n by\n"
                    "    constructor\n    · rfl\n    · assumption\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => exact Nat.add_zero _\n",
                ),
                (
                    "SufficesSimpAll.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := by\n  suffices h : n + 0 = n by constructor <;> simp_all\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => exact Nat.add_zero _\n",
                ),
                (
                    "SufficesSimpStar.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := by\n  suffices h : n + 0 = n by constructor <;> simp [*]\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => exact Nat.add_zero _\n",
                ),
            )
            for fname, body in suff_pos_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertEqual(scan_parameterized_prop_bundlers(body), [], msg=f"{fname} false-flagged")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "PASS", msg=f"{fname} false-failed T1-LEAN-04: {res.summary}")

            for rel_owner in (
                "lean/InfoGeometry/Probability/DetectorFoundationalCopula.lean",
                "lean/InfoGeometry/Canonical/ConcreteCuntzKCommutationZornCapstone.lean",
            ):
                owner_path = REPO_ROOT / rel_owner
                if owner_path.is_file():
                    self.assertEqual(
                        scan_parameterized_prop_bundlers(owner_path.read_text(encoding="utf-8")),
                        [],
                        msg=f"Positive owner {rel_owner} false-flagged",
                    )

            # 2. Intake Findings 8-10: expanded B-E verbs/punctuation, skip_other_indent / self_bullet_indent,
            #    parenthetical colon guard `(note: C saved locally)`, and English "A ..." preservation
            (root / "cached" / "drive_docs").mkdir(parents=True)
            (root / "docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )
            c_err_json = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.json"
            c_err_json.write_text(json.dumps({"error": {"code": 403, "message": "Access denied"}}), encoding="utf-8")
            e_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.md"
            e_ok_bytes = b"Source E valid markdown\n"
            e_ok_path.write_bytes(e_ok_bytes)
            e_sha = hashlib.sha256(e_ok_bytes).hexdigest()
            m1b = root / "docs" / "M1B.md"

            for bad_line in (
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally, E returned HTTP 403",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally, E — HTTP 403",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally, E = HTTP 403",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally, E requires sign-in (HTTP 403)",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`):\n  - E returned HTTP 403\n  - C saved locally",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`):\n  - Source E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied\n  - Source C (`{SOURCE_C_ID}`): saved locally",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`):\n  - C saved locally\n  E returned HTTP 403",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`):\n  - C saved locally\nHTTP 403 Access Denied",
            ):
                m1b.write_text(
                    bad_line + "\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"C bleed on:\n{bad_line}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Unexpected PASS on:\n{bad_line}",
                )

            # Parenthetical colon `(note: C saved locally)` preserves Source E blocker and denies C bleed;
            # English "A ..." phrases remain clean
            c_err_json.unlink()
            c_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            c_ok_bytes = b"Source C valid markdown\n"
            c_ok_path.write_bytes(c_ok_bytes)
            c_sha = hashlib.sha256(c_ok_bytes).hexdigest()
            e_ok_path.unlink()
            e_html = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")

            m1b.write_text(
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): E blocked by HTTP 403 (note: C saved locally)\n"
                f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID))
            self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID))
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "PASS",
            )
            # English "A ..." negative control on Case 2a-4 ("and a blocked") & "A sign-in page"
            c_ok_path.unlink()
            c_err_json.write_text(json.dumps({"error": {"code": 403, "message": "Access denied"}}), encoding="utf-8")
            for eng in (
                "saved locally and a blocked HTTP 403 page was seen",
                "A sign-in page (HTTP 403) was returned by Google Drive.",
            ):
                m1b.write_text(
                    f"- Source C (`{SOURCE_C_ID}`): {eng}\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    f"- Source E (`{SOURCE_E_ID}`): HTTP 403 access blocker\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                # Neither lowercase "and a blocked" nor English article "A sign-in page" should trigger Source A attribution
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_A_ID), msg=f"False Source A bleed on: {eng}")
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"Lost Source C attribution on: {eng}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "PASS",
                    msg=f"Unexpected result for {eng}",
                )

    def test_regression_r9_all_iteration8_findings(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        with tempfile.TemporaryDirectory(prefix="ec_reg_r9_") as td:
            root = Path(td)

            # 1-7: Lean static checks (Findings 1-7)
            lean_fail_cases = (
                (
                    "ParamWhereNlPriv.lean",
                    "structure Bundle (n : Nat) : Prop where\n  private mk ::\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "AdvRule4bForallHypAnd.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem bundle_ok (n : Nat) : Bundle n := by\n  induction n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ k _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    "theorem wrapper (n : Nat) : ∀ h : n = n ∧ n = n, Bundle n := fun _ => ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "AdvRule4bForallHypExists.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem bundle_ok (n : Nat) : Bundle n := by\n  induction n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ k _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    "theorem wrapper (n : Nat) : ∀ h : ∃ x : Nat, x = n, Bundle n := fun _ => ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "AdvRule4bForallHypIff.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem bundle_ok (n : Nat) : Bundle n := by\n  induction n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ k _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    "theorem wrapper (n : Nat) : ∀ h : n = n ↔ n = n, Bundle n := fun _ => ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "AdvAssignPiFieldUnparam.lean",
                    "structure Bundle : Prop :=\n  p1 : (x : Nat) → x = x\n  p2 : 2 = 2\n"
                    "theorem ok : Bundle := by cases (0 : Nat) <;> exact ⟨fun _ => rfl, rfl⟩\n",
                ),
                (
                    "AdvAssignImplFieldParam.lean",
                    "structure Bundle (n : Nat) : Prop :=\n  p1 : {x : Nat} → x = x\n  p2 : n = n\n"
                    "lemma ok (n : Nat) : Bundle n := ⟨fun {_} => rfl, rfl⟩\n",
                ),
                (
                    "AdvAnonCtorInlineByHave.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := ⟨by have _ : n = n := by\n    cases n with\n    | zero => rfl\n"
                    "    | succ _ => rfl\n  rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "AdvRepeatPrimeHave.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := by\n  repeat' have _ : n = n := by\n    cases n with\n"
                    "    | zero => rfl\n    | succ _ => rfl\n  exact ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "AdvIterateHave.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := by\n  iterate 1 have _ : n = n := by\n    cases n with\n"
                    "    | zero => rfl\n    | succ _ => rfl\n  exact ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "AdvWithReducibleHave.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := by\n  with_reducible have _ : n = n := by\n    cases n with\n"
                    "    | zero => rfl\n    | succ _ => rfl\n  exact ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "AdvSufficesInlineRefineSemi.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n  suffices _ : n = n by { refine ⟨rfl, Nat.add_zero n⟩ }; cases n <;> rfl\n",
                ),
                (
                    "AdvSufficesInlineConstructorSemi.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n  suffices _ : n = n by { constructor <;> first | rfl | exact Nat.add_zero n }; cases n <;> rfl\n",
                ),
                (
                    "AdvDeadHaveInSuffices.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := by\n  suffices h : n = n by\n    have dead : n = n := h\n"
                    "    exact ⟨rfl, Nat.add_zero n⟩\n  cases n with\n  | zero => rfl\n  | succ _ => rfl\n",
                ),
                (
                    "ClassInstWitnessed.lean",
                    "class Bundle (n : Nat) : Prop where\n  p1 : n * 1 = n\n  p2 : n + 0 = n\n"
                    "lemma bundle_one : Bundle 1 := ⟨by omega, by omega⟩\n"
                    "instance (n : Nat) : Bundle n := ⟨Nat.mul_one n, Nat.add_zero n⟩\n",
                ),
                (
                    "ScopedLemmaWitnessed.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "scoped lemma ok (n : Nat) : Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "LocalLemmaWitnessed.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "local lemma ok (n : Nat) : Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "AdvCustomCtorRule3.lean",
                    "structure Bundle (n : Nat) : Prop := myMk ::\n  (p1 : n = n)\n  (p2 : n + 0 = n)\n"
                    "lemma ok (n : Nat) : Bundle n := Bundle.myMk rfl (Nat.add_zero n)\n",
                ),
                (
                    "AdvCustomCtorWhereRule3.lean",
                    "structure Bundle (n : Nat) : Prop where myMk ::\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := Bundle.myMk rfl (Nat.add_zero n)\n",
                ),
                (
                    "AdvUnicodeSqsubsetMixed.lean",
                    "structure Bundle (tag : Tag) (P : Prop) : Prop where\n  p1 : P = P\n  p2 : True\n"
                    "lemma ok (n : Nat) : Bundle .G2 (n⊑n) := ⟨rfl, by omega⟩\n",
                ),
                (
                    "AdvUnicodeDirectsumMixed.lean",
                    "structure Bundle (tag : Tag) (P : Prop) : Prop where\n  p1 : P = P\n  p2 : True\n"
                    "lemma ok (n : Nat) : Bundle .G2 (n⨁n) := ⟨rfl, by omega⟩\n",
                ),
                (
                    "AdvUnicodeEmbedMixed.lean",
                    "structure Bundle (tag : Tag) (P : Prop) : Prop where\n  p1 : P = P\n  p2 : True\n"
                    "lemma ok (n : Nat) : Bundle .G2 (n↪n) := ⟨rfl, by omega⟩\n",
                ),
            )
            for fname, body in lean_fail_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                hits = scan_parameterized_prop_bundlers(body)
                self.assertTrue(hits, msg=f"{fname} missed by bundler scanner")
                if fname.startswith("AdvRule4bForallHyp"):
                    self.assertTrue(
                        any("wrapper" in h[1] for h in hits),
                        msg=f"{fname} did not flag wrapper: {hits}",
                    )
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            for fname, body in (
                (
                    "VacMatchPrime.lean",
                    "theorem vac : Nat → match' 0 = 0 → with' 0 = 0 → True\n"
                    "  | 0 => fun _ _ => trivial\n  | _ => fun _ _ => trivial\n",
                ),
                (
                    "AdvGuillemetColonVacuous.lean",
                    "theorem «foo:bar» : True := trivial\n",
                ),
            ):
                self.assertTrue(scan_native_decide_and_vacuous_true(body), msg=f"{fname} missed by vacuous scanner")
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            lean_pass_cases = (
                (
                    "WhereNewlineMkSingleField.lean",
                    "structure SingleField : Prop where\n  mk ::\n  p1 : 1 = 1\n"
                    "theorem ok_single : SingleField := by constructor; rfl\n",
                ),
                (
                    "FPBundleAndImp.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma witness : Bundle 0 := ⟨rfl, rfl⟩\n"
                    "theorem ok (n : Nat) : (n = n → n = n) ∧ Bundle n := ⟨fun h => h, ⟨rfl, Nat.add_zero n⟩⟩\n",
                ),
                (
                    "FPBundleImpAnd.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma witness : Bundle 0 := ⟨rfl, rfl⟩\n"
                    "theorem ok (n : Nat) : Bundle n ∧ (n = n → n = n) := ⟨⟨rfl, Nat.add_zero n⟩, fun h => h⟩\n",
                ),
                (
                    "FPExistsBundle.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma witness : Bundle 0 := ⟨rfl, rfl⟩\n"
                    "theorem ok (n : Nat) : ∃ x : Nat, Bundle x := ⟨n, ⟨rfl, Nat.add_zero n⟩⟩\n",
                ),
                (
                    "FPRule4bCompoundInnerArrow.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma witness : Bundle 0 := ⟨rfl, rfl⟩\n"
                    "theorem ok (n : Nat) : ∀ k : Nat, (k = k → k = k) ∧ Bundle n := fun _ => ⟨fun h => h, ⟨rfl, Nat.add_zero n⟩⟩\n",
                ),
                (
                    "AdvFPSufficesUsedViaHave.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n = n + 0\n"
                    "lemma ok (n : Nat) : Bundle n := by\n  suffices h : n + 0 = n by\n"
                    "    have h2 : n = n + 0 := h.symm\n    exact ⟨rfl, h2⟩\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => exact Nat.add_zero _\n",
                ),
                (
                    "AdvFPSufficesOmega.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "lemma ok (n : Nat) : Bundle n := by\n  suffices h : n + 0 = n by\n"
                    "    constructor\n    · rfl\n    · omega\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => exact Nat.add_zero _\n",
                ),
                (
                    "CustomCtorWithProjection.lean",
                    "structure Bundle (n : Nat) : Prop := myMk ::\n  (p1 : n = n)\n  (p2 : n + 0 = n)\n"
                    "lemma witness : Bundle 0 := Bundle.myMk rfl rfl\n"
                    "lemma ok (n : Nat) : Bundle n := Bundle.myMk rfl (Nat.add_zero n)\n"
                    "lemma proj (n : Nat) (h : Bundle n) : n = n := Bundle.p1 h\n",
                ),
            )
            for fname, body in lean_pass_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertEqual(scan_parameterized_prop_bundlers(body), [], msg=f"{fname} false-flagged")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "PASS", msg=f"{fname} false-failed T1-LEAN-04: {res.summary}")

            # 7d: T3-CONS-02 `#print axioms @Ns.ok`
            lean_dir = root / "lean" / "InfoGeometry" / "Test"
            lean_dir.mkdir(parents=True)
            target_lf = lean_dir / "AtMod.lean"
            target_lf.write_text("namespace Ns\ntheorem ok : 1 = 1 := rfl\nend Ns\n", encoding="utf-8")
            audit_lf = lean_dir / "AtModAudit.lean"
            audit_lf.write_text("#print axioms @Ns.ok\n", encoding="utf-8")
            env_at = root / "env_at.json"
            env_at.write_text(
                json.dumps(
                    {
                        "owner_search": {"target_artifacts": ["lean/InfoGeometry/Test/AtMod.lean", "lean/InfoGeometry/Test/AtModAudit.lean"]},
                        "formal_objects": {"lane_at": ["AtMod.obj"]},
                        "acceptance_theorems": {"lane_at": ["Ns.ok"]},
                    }
                ),
                encoding="utf-8",
            )
            res_cons2 = check_t3_cons_02_contracts_to_lean_declarations(
                root,
                DiscoveredArtifacts([], [env_at], [], [], [], [env_at], []),
                [ResolvedTarget(target_lf, "lean/InfoGeometry/Test/AtMod.lean", "InfoGeometry.Test.AtMod", True)],
                require_all_envelope_targets=True,
            )
            self.assertEqual(res_cons2.status, "PASS", msg=res_cons2.summary)
            self.assertEqual(res_cons2.details, {"checked_theorems": 1, "checked_audits": 1})

            audit_lf.write_text("#print axioms @Ns.other\n", encoding="utf-8")
            res_cons2_bad = check_t3_cons_02_contracts_to_lean_declarations(
                root,
                DiscoveredArtifacts([], [env_at], [], [], [], [env_at], []),
                [ResolvedTarget(target_lf, "lean/InfoGeometry/Test/AtMod.lean", "InfoGeometry.Test.AtMod", True)],
                require_all_envelope_targets=True,
            )
            self.assertEqual(res_cons2_bad.status, "FAIL", msg=res_cons2_bad.summary)

            # 8-10: Intake Findings 8-10
            (root / "cached" / "drive_docs").mkdir(parents=True)
            (root / "docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )
            c_err_json = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.json"
            c_err_json.write_text(json.dumps({"error": {"code": 403, "message": "Access denied"}}), encoding="utf-8")
            e_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.md"
            e_ok_bytes = b"Source E valid markdown\n"
            e_ok_path.write_bytes(e_ok_bytes)
            e_sha = hashlib.sha256(e_ok_bytes).hexdigest()
            m1b = root / "docs" / "M1B.md"

            for bad_note in (
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally, while E still requires sign-in (HTTP 403)",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally, E redirected to ServiceLogin (HTTP 403)",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally, E also returned HTTP 403",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally, E couldn't be fetched (HTTP 403)",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally, E appears inaccessible (HTTP 403)",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`):\n  - C saved locally\n  - E blocked\nHTTP 403 was returned for the inaccessible item above.",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally, E:\n  HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`):\n  - C saved locally\n  - Note: HTTP 403 seen on other URL",
            ):
                m1b.write_text(
                    bad_note + "\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"C bleed on:\n{bad_note}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Unexpected PASS on:\n{bad_note}",
                )

            c_err_json.unlink()
            c_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            c_ok_bytes = b"Source C valid markdown\n"
            c_ok_path.write_bytes(c_ok_bytes)
            c_sha = hashlib.sha256(c_ok_bytes).hexdigest()
            e_ok_path.unlink()
            e_html = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")

            for good_e_note in (
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): [E](https://drive.google.com/file/d/{SOURCE_E_ID}/view) blocked by HTTP 403, [C](https://drive.google.com/file/d/{SOURCE_C_ID}/view) saved locally",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): E blocked by HTTP 403 [note: C saved locally]",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`) [note: C saved locally]: E blocked by HTTP 403",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`) (note (Drive): C saved locally): E blocked by HTTP 403",
            ):
                m1b.write_text(
                    good_e_note + "\n"
                    f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"Lost E blocker on:\n{good_e_note}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"False C blocker on:\n{good_e_note}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "PASS",
                    msg=f"Unexpected FAIL on:\n{good_e_note}",
                )

            c_ok_path.unlink()
            c_html = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.html"
            c_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            m1b.write_text(
                f"- Sources C (`{SOURCE_C_ID}`, Drive 2) & E (`{SOURCE_E_ID}`, Drive 3): C blocked by HTTP 403\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                f"- Source E (`{SOURCE_E_ID}`): HTTP 403 access blocker\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_C_ID))
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "PASS",
            )

            m1b.write_text(
                f"- Sources C (`{SOURCE_C_ID}`, Drive 2) & E (`{SOURCE_E_ID}`, Drive 3): HTTP 403 Access Denied\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_C_ID))
            self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID))
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "PASS",
            )

            # 11: T3-CONS-05 skips external http(s):// links (including HTTPS://, <...>, titles) and checks real hashes
            sample_doc = root / "docs" / "sample.md"
            sample_bytes = b"verified artifact\n"
            sample_doc.write_bytes(sample_bytes)
            sample_sha = hashlib.sha256(sample_bytes).hexdigest()
            qa_rep = root / "sample-qa.md"
            for qa_line in (
                f"| [Drive](https://drive.google.com/file/d/123) | docs/sample.md | `{sample_sha}` |\n",
                f"| [Drive](HTTPS://drive.google.com/file/d/123) | docs/sample.md | `{sample_sha}` |\n",
                f"| [Drive](<https://drive.google.com/file/d/123>) | docs/sample.md | `{sample_sha}` |\n",
                f"| [Doc](<docs/sample.md>) | `{sample_sha}` |\n",
                f'| [Doc](docs/sample.md "verified") | `{sample_sha}` |\n',
                f"| [Doc](<docs/sample.md> 'verified') | `{sample_sha}` |\n",
            ):
                qa_rep.write_text(qa_line, encoding="utf-8")
                res_cons5 = check_t3_cons_05_audit_report_hashes(
                    root,
                    DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]),
                )
                self.assertEqual(res_cons5.status, "PASS", msg=f"{qa_line.strip()} -> {res_cons5.summary}")
                self.assertIn("(1/1 files)", res_cons5.summary, msg=res_cons5.summary)

            qa_rep.write_text(
                f"| [Drive](HTTPS://drive.google.com/file/d/123) | docs/sample.md | `{'0' * 64}` |\n",
                encoding="utf-8",
            )
            res_cons5_bad = check_t3_cons_05_audit_report_hashes(
                root,
                DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]),
            )
            self.assertEqual(res_cons5_bad.status, "FAIL", msg=res_cons5_bad.summary)
            self.assertEqual(res_cons5_bad.details.get("checked"), 1, msg=res_cons5_bad.details)

    def test_regression_r10_consolidated_fixes(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        with tempfile.TemporaryDirectory(prefix="ec_reg_r10_") as td:
            root = Path(td)

            # 1. Lean Fail Cases (all lean --stdin valid): nested ∀/∃/Σ' Rule 4b,
            #    multi-field & mixed :=/where structures, shadowed have/let in suffices,
            #    parenthesized/braced dead suffices aux branches
            r10_lean_fail_cases = (
                (
                    "R10Rule4bForallExistsOnly.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem wrapper (n : Nat) : ∀ h : ∃ x : Nat, x = n, Bundle n := fun _ => ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "R10Rule4bForallForallWrapper.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem bundle_ok (n : Nat) : Bundle n := by\n  induction n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ k _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    "theorem wrapper (n : Nat) : ∀ h : ∀ x : Nat, x = x, Bundle n := fun _ => ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "R10Rule4bForallSigmaWrapper.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem bundle_ok (n : Nat) : Bundle n := by\n  induction n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ k _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    "theorem wrapper (n : Nat) : ∀ _ : Σ' y : Nat, y = n ∧ n = n, Bundle n := fun _ => ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "R10StructAssignParenMulti.lean",
                    "structure Bundle (n : Nat) : Prop := (p1 p2 : n = n)\n"
                    "theorem ok (n : Nat) : Bundle n := ⟨rfl, rfl⟩\n",
                ),
                (
                    "R10StructWhereParenMulti.lean",
                    "structure Bundle (n : Nat) : Prop where\n  (p1 p2 : n = n)\n"
                    "theorem ok (n : Nat) : Bundle n := ⟨rfl, rfl⟩\n",
                ),
                (
                    "R10StructAssignMixed.lean",
                    "structure Bundle (n : Nat) : Prop := mk ::\n  (p1 : n = n)\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "R10StructWhereMixed.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  (p2 : n + 0 = n)\n"
                    "theorem ok (n : Nat) : Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "R10SufficesShadowedHave.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n  suffices h : n + 0 = n by\n"
                    "    have h : n + 0 = n := Nat.add_zero n\n    exact ⟨rfl, h⟩\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => rfl\n",
                ),
                (
                    "R10SufficesShadowedLet.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n  suffices h : n + 0 = n by\n"
                    "    let h : n + 0 = n := Nat.add_zero n\n    exact ⟨rfl, h⟩\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => rfl\n",
                ),
                (
                    "R10SufficesNestedShadowedChain.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n  suffices h : n + 0 = n by\n"
                    "    have h : n + 0 = n := Nat.add_zero n\n    have h2 : n = n + 0 := h.symm\n    exact ⟨rfl, h2.symm⟩\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => rfl\n",
                ),
                (
                    "R10SufficesParenDead.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n  (suffices _ : n = n by exact ⟨rfl, Nat.add_zero n⟩)\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => rfl\n",
                ),
                (
                    "R10SufficesParenInlineSemiDead.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n  (suffices _ : n = n by exact ⟨rfl, Nat.add_zero n⟩); cases n <;> rfl\n",
                ),
                (
                    "R10SufficesBracedInlineSemiDead.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n  suffices _ : n = n by { exact ⟨rfl, Nat.add_zero n⟩ }; cases n <;> rfl\n",
                ),
            )
            for fname, body in r10_lean_fail_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                hits = scan_parameterized_prop_bundlers(body)
                self.assertTrue(hits, msg=f"{fname} missed by bundler scanner")
                if "Wrapper" in fname or "Only" in fname:
                    self.assertTrue(any("wrapper" in h[1] for h in hits), msg=f"{fname} missed wrapper: {hits}")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 2. Vacuous `: True` fail cases with nested `∀`/`∃`
            for fname, body in (
                (
                    "R10VacForallExistsTrue.lean",
                    "theorem vac (n : Nat) : ∀ h : ∃ x : Nat, x = n, True := fun _ => trivial\n",
                ),
                (
                    "R10VacForallForallTrue.lean",
                    "theorem vac : ∀ h : ∀ x : Nat, x = x, True := fun _ => trivial\n",
                ),
            ):
                self.assertTrue(scan_native_decide_and_vacuous_true(body), msg=f"{fname} missed by vacuous scanner")
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 3. Lean Pass Cases (positive controls, all lean --stdin valid)
            r10_lean_pass_cases = (
                (
                    "R10FPSufficesCtorSemiAssumption.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n  suffices h : n + 0 = n by constructor; rfl; assumption\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => exact Nat.add_zero _\n",
                ),
                (
                    "R10FPSufficesRefineOmega.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n  suffices h : n + 0 = n by refine ⟨rfl, ?_⟩; omega\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => exact Nat.add_zero _\n",
                ),
                (
                    "R10FPSufficesCtorSimpAll.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n  suffices h : n + 0 = n by constructor; rfl; simp_all\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => exact Nat.add_zero _\n",
                ),
                (
                    "R10FPParenHaveBySemi.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n  suffices h : n + 0 = n by\n"
                    "    (have h2 : n + 0 = n := by exact h); exact ⟨rfl, h2⟩\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => exact Nat.add_zero _\n",
                ),
                (
                    "R10FPBracedHaveBySemi.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n  suffices h : n + 0 = n by\n"
                    "    have h2 : n + 0 = n := by { exact h }; exact ⟨rfl, h2⟩\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => exact Nat.add_zero _\n",
                ),
                (
                    "R10FPBracedSufficesCtorSemi.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n  suffices h : n + 0 = n by { constructor; rfl; assumption }; cases n with\n"
                    "  | zero => rfl\n  | succ _ => exact Nat.add_zero _\n",
                ),
                (
                    "R10FPParenSufficesRefineOmega.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n  (suffices h : n + 0 = n by refine ⟨rfl, ?_⟩; omega); cases n with\n"
                    "  | zero => rfl\n  | succ _ => exact Nat.add_zero _\n",
                ),
                (
                    "R10FPSufficesHaveSelfSymm.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n  suffices h : n + 0 = n by\n"
                    "    have h : n = n + 0 := h.symm\n    exact ⟨rfl, h.symm⟩\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => exact Nat.add_zero _\n",
                ),
                (
                    "R10FPMultiBulletHaveShadow.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n  suffices h : n + 0 = n by\n"
                    "    constructor\n    · have h : 1 = 1 := rfl; exact rfl\n    · exact h\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => exact Nat.add_zero _\n",
                ),
                (
                    "R10FPSingleFieldPiMultilineT2.lean",
                    "structure SinglePi : Prop where\n  p1 :\n    (x : Nat) → x = x\n"
                    "theorem ok : SinglePi := ⟨fun _ => rfl⟩\n",
                ),
                (
                    "R10FPSingleFieldPiMultilineT6.lean",
                    "structure SinglePi2 : Prop where\n  p1 : (x : Nat) →\n  (y : Nat) → x = y → x = y\n"
                    "theorem ok : SinglePi2 := ⟨fun _ _ h => h⟩\n",
                ),
            )
            for fname, body in r10_lean_pass_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertEqual(scan_parameterized_prop_bundlers(body), [], msg=f"{fname} false-flagged")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "PASS", msg=f"{fname} false-failed T1-LEAN-04: {res.summary}")

            # 4. Intake R10 regression cases: stacked markdown links, possessives (ASCII + U+2019),
            #    inner sub-headers, parenthetical status in `other_only`, and Source A header/article safety
            (root / "cached" / "drive_docs").mkdir(parents=True)
            (root / "docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )
            m1b = root / "docs" / "M1B.md"
            c_ok_bytes = b"Source C valid markdown\n"
            c_sha = hashlib.sha256(c_ok_bytes).hexdigest()
            e_ok_bytes = b"Source E valid markdown\n"
            e_sha = hashlib.sha256(e_ok_bytes).hexdigest()
            c_err_json = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.json"
            c_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            e_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.md"
            e_html = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"

            r10_ce_cases = (
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): [**C**](https://drive.google.com/file/d/{SOURCE_C_ID}/view) saved locally, [**E**](https://drive.google.com/file/d/{SOURCE_E_ID}/view) blocked by HTTP 403",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): [`C`](https://drive.google.com/file/d/{SOURCE_C_ID}/view) saved locally, [`E`](https://drive.google.com/file/d/{SOURCE_E_ID}/view) blocked by HTTP 403",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): **[C](https://drive.google.com/file/d/{SOURCE_C_ID}/view)** saved locally, **[E](https://drive.google.com/file/d/{SOURCE_E_ID}/view)** blocked by HTTP 403",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): *[C](https://drive.google.com/file/d/{SOURCE_C_ID}/view)* saved locally, *[E](https://drive.google.com/file/d/{SOURCE_E_ID}/view)* blocked by HTTP 403",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): **[Source C](https://drive.google.com/file/d/{SOURCE_C_ID}/view)** saved locally, **[Source E](https://drive.google.com/file/d/{SOURCE_E_ID}/view)** blocked by HTTP 403",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C's link saved locally, E's link returned HTTP 403",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C’s link saved locally, E’s link returned HTTP 403",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): E: HTTP 403 Access Denied, C: saved locally",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): E: HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): E: HTTP 403 (note: C saved locally), C: ok",
                f"- **Sources C** (`{SOURCE_C_ID}`) & **E** (`{SOURCE_E_ID}`): C saved locally, E blocked (HTTP 403)",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): HTTP 403 returned, C saved locally, E blocked (HTTP 403)",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): HTTP 403 returned, C saved locally, Source E blocked (HTTP 403)",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): HTTP 403 returned, C saved locally, E (HTTP 403)",
            )
            # Negative: C=403 JSON, E=valid -> FAIL (C must NOT bleed from E)
            c_err_json.write_text(json.dumps({"error": {"code": 403, "message": "Access denied"}}), encoding="utf-8")
            e_ok_path.write_bytes(e_ok_bytes)
            for line in r10_ce_cases:
                m1b.write_text(
                    line + "\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"C bleed on:\n{line}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Unexpected PASS when C=403 JSON on:\n{line}",
                )

            # Positive: C=valid, E=HTML -> PASS for lines that also assert C is saved (or with explicit C metadata line)
            c_err_json.unlink()
            e_ok_path.unlink()
            c_ok_path.write_bytes(c_ok_bytes)
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            for line in r10_ce_cases:
                m1b.write_text(
                    line + "\n"
                    f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"Lost E blocker on:\n{line}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"False C blocker on:\n{line}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "PASS",
                    msg=f"Unexpected FAIL on:\n{line}",
                )

            # Shared predicate with bare `Source E (1wzq...) & Source C (12bA...), HTTP 403 Access Denied` -> PASS when both blocked
            c_ok_path.unlink()
            c_html = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.html"
            c_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            m1b.write_text(
                f"- Source E (`{SOURCE_E_ID}`) & Source C (`{SOURCE_C_ID}`), HTTP 403 Access Denied\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_C_ID))
            self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID))
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "PASS",
            )
            c_html.unlink()

            # Source A inner sub-header isolation & possessive vs preserved English article
            for a_line, expect_a, expect_c in (
                (
                    f"- Sources A (`{SOURCE_A_ID}`) & C (`{SOURCE_C_ID}`): A: HTTP 403 Access Denied, C: saved locally",
                    True,
                    False,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`) & C (`{SOURCE_C_ID}`): A's link returned HTTP 403, C saved locally",
                    True,
                    False,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`) & C (`{SOURCE_C_ID}`): A’s link returned HTTP 403, C saved locally",
                    True,
                    False,
                ),
                (
                    f"- Source C (`{SOURCE_C_ID}`): saved locally and a blocked HTTP 403 page was seen",
                    False,
                    True,
                ),
                (
                    f"- Source C (`{SOURCE_C_ID}`): A sign-in page (HTTP 403) was returned by Google Drive.",
                    False,
                    True,
                ),
                (
                    f"- Source C (`{SOURCE_C_ID}`): N/A: HTTP 403",
                    False,
                    True,
                ),
            ):
                m1b.write_text(a_line + "\n", encoding="utf-8")
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), expect_a, msg=a_line)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_C_ID), expect_c, msg=a_line)

    def test_regression_r11_challenger_r10_fixes(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        with tempfile.TemporaryDirectory(prefix="ec_reg_r11_") as td:
            root = Path(td)

            # 1. Lean vacuous `: True` fail cases (F1a-c, F1e-f, F2a)
            r11_vac_fail_cases = (
                ("R11F1aLetRetTrue.lean", "theorem vac : let _ := 0; True := trivial\n"),
                ("R11F1bHaveRetTrue.lean", "theorem vac : have _ := 0; True := trivial\n"),
                ("R11F1cForallLetTrue.lean", "theorem vac : ∀ h : let x := 0; x = 0, True := fun _ => trivial\n"),
                ("R11F1eParenLetTrue.lean", "theorem vac : (let _ := 0; True) := trivial\n"),
                ("R11F1fMultilineLetTrue.lean", "theorem vac :\n    let _ := 0\n    True := trivial\n"),
                ("R11F2aAsciiExistsTrue.lean", "theorem vac : ∀ h : exists x : Nat, x = 0, True := fun _ => trivial\n"),
            )
            for fname, body in r11_vac_fail_cases:
                self.assertTrue(scan_native_decide_and_vacuous_true(body), msg=f"{fname} missed by vacuous scanner")
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 2. Lean bundler fail cases (F1d, F2b, F3a-c, F4a, F6, F7a-c)
            r11_bundler_fail_cases = (
                (
                    "R11F1dLetRetBundler.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem bypass (n : Nat) : let _ := 0; Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "R11F2bAsciiExistsBundler.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem wrapper (n : Nat) : ∀ h : exists x : Nat, x = n, Bundle n := fun _ => ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "R11F3aFirstPipeDeadSuffices.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n"
                    "  first | suffices _ : n = n by exact ⟨rfl, Nat.add_zero n⟩ | exact ⟨rfl, Nat.add_zero n⟩\n"
                    "  cases n <;> rfl\n",
                ),
                (
                    "R11F3bFocusDeadSuffices.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n"
                    "  focus suffices _ : n = n by exact ⟨rfl, Nat.add_zero n⟩\n"
                    "  cases n <;> rfl\n",
                ),
                (
                    "R11F3cTryDeadSuffices.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n"
                    "  try suffices _ : n = n by exact ⟨rfl, Nat.add_zero n⟩\n"
                    "  cases n <;> rfl\n",
                ),
                (
                    "R11F4aSimpOnlySemiBypass.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem bypass : Bundle 0 := by\n"
                    "  suffices _ : 0 = 0 by simp only [Nat.add_zero] at *; exact ⟨rfl, rfl⟩\n"
                    "  rfl\n",
                ),
                (
                    "R11F6HaveBinderArgShadowThis.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n"
                    "  suffices n + 0 = n by\n"
                    "    have (x : Nat) : n + 0 = n := Nat.add_zero n\n"
                    "    exact ⟨rfl, this 0⟩\n"
                    "  cases n <;> rfl\n",
                ),
                (
                    "R11F7aStructExtendsAfterProp.lean",
                    "structure Base (n : Nat) : Prop where\n  p1 : n = n\n"
                    "structure SubExt (n : Nat) : Prop extends Base n where\n  p2 : n + 0 = n\n  p3 : n = n\n"
                    "theorem ok (n : Nat) : SubExt n := ⟨⟨rfl⟩, Nat.add_zero n, rfl⟩\n",
                ),
                (
                    "R11F7bStructPrivParenMulti.lean",
                    "structure Bundle (n : Nat) : Prop where\n  private (p1 p2 : n = n)\n  p3 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := ⟨rfl, rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "R11F7cStructGuillemetColon.lean",
                    "structure Bundle (n : Nat) : Prop where\n  («a:b» : n = n)\n  (p2 : n + 0 = n)\n"
                    "theorem ok (n : Nat) : Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
            )
            for fname, body in r11_bundler_fail_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                hits = scan_parameterized_prop_bundlers(body)
                self.assertTrue(hits, msg=f"{fname} missed by bundler scanner")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 3. Lean positive controls (F1 non-True let, F3 multi-arm/bullet, F4b simp; exact h, F5a trivial, F5b simpa)
            r11_lean_pass_cases = (
                ("R11F1PosLetEq.lean", "theorem ok : let x := 0; x = 0 := rfl\n"),
                (
                    "R11F3PosFirstMultiArm.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n"
                    "  first\n"
                    "  | suffices _ : 0 = 1 by exact ⟨rfl, Nat.add_zero n⟩\n"
                    "    cases (0 : Nat) <;> exact absurd rfl (by decide)\n"
                    "  | cases n with\n"
                    "    | zero => exact ⟨rfl, rfl⟩\n"
                    "    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R11F3PosBulletTry.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n"
                    "  constructor\n"
                    "  · try suffices _ : 1 = 1 by rfl\n"
                    "    exact rfl\n"
                    "  · cases n with\n"
                    "    | zero => rfl\n"
                    "    | succ _ => exact Nat.add_zero _\n",
                ),
                (
                    "R11F4bSimpSemiThenH.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle (n + 0) := by\n"
                    "  suffices h : n = n + 0 by simp only [Nat.add_zero]; exact ⟨rfl, h.symm⟩\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => exact (Nat.add_zero _).symm\n",
                ),
                (
                    "R11F5aSufficesTrivial.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n"
                    "  suffices h : n + 0 = n by constructor; rfl; trivial\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => exact Nat.add_zero _\n",
                ),
                (
                    "R11F5bSufficesSimpa.lean",
                    "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : Bundle n := by\n"
                    "  suffices h : n + 0 = n by constructor; rfl; simpa\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => exact Nat.add_zero _\n",
                ),
            )
            for fname, body in r11_lean_pass_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertEqual(scan_native_decide_and_vacuous_true(body), [], msg=f"{fname} false vacuous hit")
                self.assertEqual(scan_parameterized_prop_bundlers(body), [], msg=f"{fname} false bundler hit")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "PASS", msg=f"{fname} false-failed T1-LEAN-04: {res.summary}")

            # 4. F8: T3-CONS-02 prefix-spoof rejection & namespace-scoped #print axioms
            lean_dir = root / "lean" / "InfoGeometry" / "Test"
            lean_dir.mkdir(parents=True)
            ns_mod = lean_dir / "NsMod.lean"
            ns_mod.write_text("namespace Ns\ntheorem ok : 1 = 1 := rfl\nend Ns\n", encoding="utf-8")
            ns_aud = lean_dir / "NsModAudit.lean"
            env_ns = root / "env_ns.json"
            env_ns.write_text(
                json.dumps(
                    {
                        "owner_search": {
                            "target_artifacts": [
                                "lean/InfoGeometry/Test/NsMod.lean",
                                "lean/InfoGeometry/Test/NsModAudit.lean",
                            ]
                        },
                        "formal_objects": {"lane_ns": ["NsMod.obj"]},
                        "acceptance_theorems": {"lane_ns": ["Ns.ok"]},
                    }
                ),
                encoding="utf-8",
            )
            arts_ns = DiscoveredArtifacts([], [env_ns], [], [], [], [env_ns], [])
            tgts_ns = [ResolvedTarget(ns_mod, "lean/InfoGeometry/Test/NsMod.lean", "InfoGeometry.Test.NsMod", True)]

            ns_aud.write_text("#print axioms Foo.Ns.ok\n", encoding="utf-8")
            res_f8a = check_t3_cons_02_contracts_to_lean_declarations(
                root, arts_ns, tgts_ns, require_all_envelope_targets=True
            )
            self.assertEqual(res_f8a.status, "FAIL", msg=res_f8a.summary)

            ns_aud.write_text("namespace Ns\n#print axioms ok\nend Ns\n", encoding="utf-8")
            res_f8b = check_t3_cons_02_contracts_to_lean_declarations(
                root, arts_ns, tgts_ns, require_all_envelope_targets=True
            )
            self.assertEqual(res_f8b.status, "PASS", msg=res_f8b.summary)
            self.assertEqual(res_f8b.details, {"checked_theorems": 1, "checked_audits": 1})

            ns_aud.write_text("namespace Other\n#print axioms ok\nend Other\n", encoding="utf-8")
            res_f8_wrong_ns = check_t3_cons_02_contracts_to_lean_declarations(
                root, arts_ns, tgts_ns, require_all_envelope_targets=True
            )
            self.assertEqual(res_f8_wrong_ns.status, "FAIL", msg=res_f8_wrong_ns.summary)

            # 5. C4: T3-CONS-05 external URL 64-hex masking, #fragment, CommonMark (title), empty QA guard
            (root / "docs").mkdir(parents=True)
            samp = root / "docs" / "sample.md"
            samp.write_bytes(b"sample content\n")
            s_sha = hashlib.sha256(b"sample content\n").hexdigest()
            qa_rep = root / "qa_report.md"
            url_hex = "a" * 64
            bad_hex = "b" * 64
            for qa_line in (
                f"| [Drive](https://example.com/{url_hex}/view) | docs/sample.md | `{s_sha}` |\n",
                f"| [Doc](docs/sample.md#sec1) | `{s_sha}` |\n",
                f"| [Doc](docs/sample.md (verified)) | `{s_sha}` |\n",
                f'| [Doc (part 1)](docs/sample.md "v1 (draft)") | `{s_sha}` |\n',
            ):
                qa_rep.write_text(qa_line, encoding="utf-8")
                r_ok = check_t3_cons_05_audit_report_hashes(
                    root,
                    DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]),
                    targets=tgts_ns,
                )
                self.assertEqual(r_ok.status, "PASS", msg=f"{qa_line.strip()} -> {r_ok.summary}")
                self.assertIn("(1/1 files)", r_ok.summary)

            qa_rep.write_text(
                f"| [Drive](https://example.com/{url_hex}/view) | docs/sample.md | `{bad_hex}` |\n",
                encoding="utf-8",
            )
            r_stale = check_t3_cons_05_audit_report_hashes(
                root,
                DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]),
                targets=tgts_ns,
            )
            self.assertEqual(r_stale.status, "FAIL", msg=r_stale.summary)
            self.assertEqual(r_stale.details.get("checked"), 1)

            qa_rep.write_text("# QA Report\nAll checks passed.\n", encoding="utf-8")
            r_empty = check_t3_cons_05_audit_report_hashes(
                root,
                DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]),
                targets=tgts_ns,
            )
            self.assertEqual(r_empty.status, "FAIL", msg=r_empty.summary)

            # 6. C1-C3: Intake checks (`~~E~~`, `[**A**'s](url)`, shared possessives, sub-header seps, `: see below:`, headings)
            (root / "cached" / "drive_docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )
            m1b = root / "docs" / "M1B.md"
            c_ok_bytes = b"Source C valid markdown\n"
            c_sha = hashlib.sha256(c_ok_bytes).hexdigest()
            e_ok_bytes = b"Source E valid markdown\n"
            e_sha = hashlib.sha256(e_ok_bytes).hexdigest()
            c_err_json = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.json"
            c_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            e_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.md"
            e_html = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"
            c_html = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.html"

            r11_ce_cases = (
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): ~~C~~ saved locally, ~~E~~ blocked by HTTP 403",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C: ok — E: HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C: ok. E: HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C: ok / E: HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): see below:\n  - C: saved locally\n  - E: HTTP 403 Access Denied",
                f"### Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`)\n- C: saved locally\n- E: HTTP 403 Access Denied",
            )
            # Negative: C=403 JSON, E=valid -> FAIL (no bleed into C)
            c_err_json.write_text(json.dumps({"error": {"code": 403, "message": "Access denied"}}), encoding="utf-8")
            e_ok_path.write_bytes(e_ok_bytes)
            for block in r11_ce_cases:
                m1b.write_text(
                    block + "\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"C bleed on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Unexpected PASS when C=403 JSON on:\n{block}",
                )

            # Positive: C=valid, E=HTML -> PASS
            c_err_json.unlink()
            e_ok_path.unlink()
            c_ok_path.write_bytes(c_ok_bytes)
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            for block in r11_ce_cases:
                m1b.write_text(
                    block + "\n"
                    f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"Lost E blocker on:\n{block}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"False C blocker on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "PASS",
                    msg=f"Unexpected FAIL on:\n{block}",
                )

            # C2: Shared possessives (both C & E blocked)
            c_ok_path.unlink()
            c_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            for poss_line in (
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): Source E's & Source C's links, HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C's & E's, HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): E’s & C’s, HTTP 403 Access Denied",
            ):
                m1b.write_text(
                    poss_line + "\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=poss_line)
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=poss_line)
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_A_ID), msg=poss_line)
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "PASS",
                    msg=poss_line,
                )

            # C1 `[**A**'s](url)` + C3 `E.g.` / `N/A` safety controls
            for line, exp_a, exp_c in (
                (
                    f"- Sources A (`{SOURCE_A_ID}`) & C (`{SOURCE_C_ID}`): [**A**'s](https://x.com) link returned HTTP 403, [**C**'s](https://y.com) link saved locally",
                    True,
                    False,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`) & C (`{SOURCE_C_ID}`): [**C**'s](https://y.com) link saved locally, [**A**'s](https://x.com) link returned HTTP 403",
                    True,
                    False,
                ),
                (
                    f"- Source C (`{SOURCE_C_ID}`): E.g. HTTP 403 N/A for local cache",
                    False,
                    True,
                ),
            ):
                m1b.write_text(line + "\n", encoding="utf-8")
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), exp_a, msg=line)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_C_ID), exp_c, msg=line)

    def test_regression_r12_iter11_findings(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        bundle_hdr = "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
        with tempfile.TemporaryDirectory(prefix="ec_reg_r12_") as td:
            root = Path(td)

            # 1. Lean vacuous `: True` fail cases (if-let, same-indent let, inline multiline let, forall/exists guillemets)
            r12_vac_fail_cases = (
                (
                    "R12IfLetRetTrue.lean",
                    "theorem vac (o : Option Nat) : if let some _ := o then True else True := by cases o <;> trivial\n",
                ),
                (
                    "R12ParenLetSameIndentTrue.lean",
                    "theorem vac : (let _ :=\n  0\n  True) := trivial\n",
                ),
                (
                    "R12LetBySameIndentTrue.lean",
                    "theorem vac :\n    let _ : 0 = 0 :=\n    by rfl\n    True := trivial\n",
                ),
                (
                    "R12InlineLetMultilineTrue.lean",
                    "theorem vac : let _ :=\n  0\n  True := trivial\n",
                ),
                (
                    "R12ExistsGuilTrue.lean",
                    "theorem vac : ∀ h : exists«x» : Nat, «x» = 0, True := fun _ => trivial\n",
                ),
                (
                    "R12ForallGuilTrue.lean",
                    "theorem vac : forall«x» : Nat, True := fun _ => trivial\n",
                ),
            )
            for fname, body in r12_vac_fail_cases:
                self.assertTrue(scan_native_decide_and_vacuous_true(body), msg=f"{fname} missed by vacuous scanner")
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 2. Lean bundler fail cases (if-let, same-indent let, wrapped combinator suffices, .mk/refine/by rfl, extends, typed tuple, exists«x»)
            r12_bundler_fail_cases = (
                (
                    "R12IfLetRetBundler.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : if let some _ := (none : Option Nat) then Bundle n else Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "R12ParenLetSameIndentBundler.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : (let _ :=\n  0\n  Bundle n) := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "R12LetBySameIndentBundler.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) :\n    let _ : 0 = 0 :=\n    by rfl\n    Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "R12ParenTrySuffices.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  (try suffices _ : n = n by exact ⟨rfl, Nat.add_zero n⟩)\n  cases n <;> rfl\n",
                ),
                (
                    "R12FocusParenSuffices.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  focus (suffices _ : n = n by exact ⟨rfl, Nat.add_zero n⟩)\n  cases n <;> rfl\n",
                ),
                (
                    "R12TryParenSuffices.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  try (suffices _ : n = n by exact ⟨rfl, Nat.add_zero n⟩)\n  cases n <;> rfl\n",
                ),
                (
                    "R12AllGoalsParenSuffices.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  all_goals (suffices _ : n = n by exact ⟨rfl, Nat.add_zero n⟩)\n  cases n <;> rfl\n",
                ),
                (
                    "R12FirstParenSuffices.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  first | (suffices _ : n = n by exact ⟨rfl, Nat.add_zero n⟩) | exact ⟨rfl, Nat.add_zero n⟩\n  cases n <;> rfl\n",
                ),
                (
                    "R12SimpRefineAngle.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle 0 := by\n  suffices _ : 0 = 0 by simp only [Nat.add_zero] at *; refine ⟨rfl, rfl⟩\n  rfl\n",
                ),
                (
                    "R12SimpBundleMk.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle 0 := by\n  suffices _ : 0 = 0 by simp only [Nat.add_zero] at *; exact Bundle.mk rfl rfl\n  rfl\n",
                ),
                (
                    "R12SimpDotMk.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle 0 := by\n  suffices _ : 0 = 0 by simp only [Nat.add_zero] at *; exact .mk rfl rfl\n  rfl\n",
                ),
                (
                    "R12SimpExactByRfl.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle 0 := by\n  suffices _ : 0 = 0 by simp only [Nat.add_zero] at *; exact ⟨by rfl, rfl⟩\n  rfl\n",
                ),
                (
                    "R12SimpCtorExactRfl.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle 0 := by\n  suffices _ : 0 = 0 by simp only [Nat.add_zero] at *; constructor <;> exact rfl\n  rfl\n",
                ),
                (
                    "R12DirectSimpAtHDotMk.lean",
                    bundle_hdr
                    + "theorem bypass (h : 0 + 0 = 0) : Bundle 0 := by\n  simp only [Nat.add_zero] at h\n  exact .mk rfl rfl\n",
                ),
                (
                    "R12ExtendsNoProp.lean",
                    "structure Base (n : Nat) : Prop where\n  p1 : n = n\n"
                    "structure SubExt (n : Nat) extends Base n where\n  p2 : n + 0 = n\n  p3 : n = n\n"
                    "theorem ok (n : Nat) : SubExt n := ⟨⟨rfl⟩, Nat.add_zero n, rfl⟩\n",
                ),
                (
                    "R12ExtendsUnparamNoProp.lean",
                    "structure Base : Prop where\n  p1 : 0 = 0\n"
                    "structure SubExt extends Base where\n  p2 : 0 + 0 = 0\n  p3 : 0 = 0\n"
                    "theorem ok : SubExt := ⟨⟨rfl⟩, Nat.add_zero 0, rfl⟩\n",
                ),
                (
                    "R12ExtendsInherited1New.lean",
                    "structure Base (n : Nat) : Prop where\n  p1 : n = n\n"
                    "structure SubExt (n : Nat) : Prop extends Base n where\n  p2 : n + 0 = n\n"
                    "theorem ok (n : Nat) : SubExt n := ⟨⟨rfl⟩, Nat.add_zero n⟩\n",
                ),
                (
                    "R12LetTypedTupleShadow.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    let (h, k) : Nat × Nat := (0, 0)\n"
                    "    exact (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
                (
                    "R12HaveTypedTupleShadow.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    have (h, k) : Nat × Nat := (0, 0)\n"
                    "    exact (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
                (
                    "R12ExistsGuilBundler.lean",
                    bundle_hdr
                    + "theorem wrapper (n : Nat) : ∀ h : exists«x» : Nat, «x» = n, Bundle n := fun _ => ⟨rfl, Nat.add_zero n⟩\n",
                ),
            )
            for fname, body in r12_bundler_fail_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertTrue(scan_parameterized_prop_bundlers(body), msg=f"{fname} missed by bundler scanner")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 3. Lean positive controls
            dot_mk_h_src = (
                bundle_hdr
                + "theorem ok (h : 0 + 0 = 0) : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact .mk rfl h\n"
            )
            self.assertEqual(scan_native_decide_and_vacuous_true(dot_mk_h_src), [])
            self.assertEqual(scan_parameterized_prop_bundlers(dot_mk_h_src), [])
            r12_lean_pass_cases = (
                (
                    "R12PosFirstFailSkip.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  first | suffices _ : 0 = 1 by exact rfl | skip\n"
                    "  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R12PosTryFail.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  try suffices _ : 0 = 1 by exact rfl\n"
                    "  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R12PosIfLetNotTrue.lean",
                    "theorem ok (o : Option Nat) : if let some _ := o then True else (1 = 1) := by cases o <;> trivial\n",
                ),
                (
                    "R12PosLetSameIndentEq.lean",
                    "theorem ok : (let x :=\n  0\n  x = 0) := rfl\n",
                ),
                (
                    "R12PosForallGuilConsumed.lean",
                    bundle_hdr
                    + "theorem wrapper (n : Nat) : ∀ h : exists«x» : Nat, «x» = n, Bundle n := fun _ => ⟨rfl, Nat.add_zero n⟩\n"
                    + "theorem witness (n : Nat) : Bundle n := by\n  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    + "theorem use_bundle (n : Nat) (h : Bundle n) : n = n := h.p1\n",
                ),
            )
            for fname, body in r12_lean_pass_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertEqual(scan_native_decide_and_vacuous_true(body), [], msg=f"{fname} false vacuous hit")
                self.assertEqual(scan_parameterized_prop_bundlers(body), [], msg=f"{fname} false bundler hit")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "PASS", msg=f"{fname} false-failed T1-LEAN-04: {res.summary}")

            # 4. T3-CONS-02: partial end, root spoofing/ns, _root_., nested ns shadowing vs non-shadowing G15
            lean_dir = root / "lean" / "InfoGeometry" / "Test"
            lean_dir.mkdir(parents=True)
            t_mod = lean_dir / "TMod.lean"
            t_aud = lean_dir / "TModAudit.lean"
            t_env = root / "env_t.json"
            t_arts = DiscoveredArtifacts([], [t_env], [], [], [], [t_env], [])

            def _set_ns_case(mod_src: str, acc_thm: str, aud_src: str) -> str:
                t_mod.write_text(mod_src, encoding="utf-8")
                t_aud.write_text(aud_src, encoding="utf-8")
                t_env.write_text(
                    json.dumps(
                        {
                            "owner_search": {
                                "target_artifacts": [
                                    "lean/InfoGeometry/Test/TMod.lean",
                                    "lean/InfoGeometry/Test/TModAudit.lean",
                                ]
                            },
                            "formal_objects": {"lane_t": ["TMod.obj"]},
                            "acceptance_theorems": {"lane_t": [acc_thm]},
                        }
                    ),
                    encoding="utf-8",
                )
                tgts = [ResolvedTarget(t_mod, "lean/InfoGeometry/Test/TMod.lean", "InfoGeometry.Test.TMod", True)]
                return check_t3_cons_02_contracts_to_lean_declarations(
                    root, t_arts, tgts, require_all_envelope_targets=True
                ).status

            self.assertEqual(_set_ns_case("namespace A\ntheorem ok : 1 = 1 := rfl\nend A\n", "A.ok", "namespace A.B\nend B\n#print axioms ok\nend A\n"), "PASS")
            self.assertEqual(_set_ns_case("namespace Ns\ntheorem ok : 1 = 1 := rfl\nend Ns\n", "Ns.ok", "namespace Ns\nnamespace Inner\ntheorem ok : 1 = 1 := rfl\n#print axioms ok\nend Inner\nend Ns\n"), "FAIL")
            self.assertEqual(_set_ns_case("namespace Outer\ntheorem ok : 1 = 1 := rfl\nend Outer\n", "Outer.ok", "namespace Outer\nsection S\nnamespace Inner\n#print axioms ok\nend Inner\nend S\nend Outer\n"), "PASS")
            self.assertEqual(_set_ns_case("namespace Ns\ntheorem ok : 1 = 1 := rfl\nend Ns\n", "Ns.ok", "open Ns\n#print axioms ok\n"), "PASS")
            self.assertEqual(_set_ns_case("namespace Ns\ntheorem ok : 1 = 1 := rfl\nend Ns\n", "Ns.ok", "open WrongNs\n#print axioms ok\n"), "FAIL")
            self.assertEqual(_set_ns_case("theorem ok : 1 = 1 := rfl\n", "ok", "#print axioms Foo.ok\n"), "FAIL")
            self.assertEqual(_set_ns_case("theorem ok : 1 = 1 := rfl\n", "ok", "namespace Foo\n#print axioms ok\nend Foo\n"), "FAIL")
            self.assertEqual(_set_ns_case("theorem ok : 1 = 1 := rfl\n", "ok", "namespace Foo\n#print axioms _root_.ok\nend Foo\n"), "PASS")
            self.assertEqual(_set_ns_case("theorem ok : 1 = 1 := rfl\n", "ok", "#print axioms ok\n"), "PASS")

            # 5. T3-CONS-05: apostrophe filenames, nested-paren titles, bare URLs with balanced parens
            (root / "docs").mkdir(parents=True)
            apos = root / "bob's_note.md"
            apos.write_bytes(b"bob note\n")
            apos_sha = hashlib.sha256(b"bob note\n").hexdigest()
            samp = root / "docs" / "sample.md"
            samp.write_bytes(b"sample v2\n")
            samp_sha = hashlib.sha256(b"sample v2\n").hexdigest()
            qa_rep = root / "qa_report.md"
            url_hex = "a" * 64
            bad_hex = "b" * 64
            for qa_line in (
                f"| [Bob](bob's_note.md) | `{apos_sha}` |\n",
                f"| [Doc](docs/sample.md (v1 (draft))) | `{samp_sha}` |\n",
                f"| https://en.wikipedia.org/wiki/Foo_(bar)/{url_hex} | docs/sample.md | `{samp_sha}` |\n",
            ):
                qa_rep.write_text(qa_line, encoding="utf-8")
                r_ok = check_t3_cons_05_audit_report_hashes(
                    root, DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]), targets=[]
                )
                self.assertEqual(r_ok.status, "PASS", msg=f"{qa_line.strip()} -> {r_ok.summary}")
                self.assertIn("(1/1 files)", r_ok.summary)

            qa_rep.write_text(f"| https://en.wikipedia.org/wiki/Foo_(bar)/{url_hex} | docs/sample.md | `{bad_hex}` |\n", encoding="utf-8")
            r_bad = check_t3_cons_05_audit_report_hashes(
                root, DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]), targets=[]
            )
            self.assertEqual(r_bad.status, "FAIL", msg=r_bad.summary)
            self.assertEqual(r_bad.details.get("checked"), 1)

            # 6. Intake Challenges 1-3: delimiters before A, multi-headers/headings, linked shared-subject lists & separators
            (root / "cached" / "drive_docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )
            m1b = root / "docs" / "M1B_R12.md"
            c_ok_bytes = b"Source C valid markdown\n"
            c_sha = hashlib.sha256(c_ok_bytes).hexdigest()
            e_ok_bytes = b"Source E valid markdown\n"
            e_sha = hashlib.sha256(e_ok_bytes).hexdigest()
            c_err_json = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.json"
            c_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            e_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.md"
            e_html = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"
            c_html = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.html"

            r12_ce_blocks = (
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): one saved, one HTTP 403:\n  - C: saved locally\n  - E: HTTP 403 Access Denied",
                f"### Intake Summary: Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`)\n- C: saved locally\n- E: HTTP 403 Access Denied",
                f"- Additional intake: Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`)\n  - C: saved locally\n  - E: HTTP 403 Access Denied",
                f"### Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`)\nSource C was saved locally.\nSource E returned HTTP 403 Access Denied.",
                f"### Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`)\n\n- C: saved locally\n- E: HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C: ok—E: HTTP 403",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C: ok - E: HTTP 403",
            )
            c_err_json.write_text(json.dumps({"error": {"code": 403, "message": "Access denied"}}), encoding="utf-8")
            e_ok_path.write_bytes(e_ok_bytes)
            for block in r12_ce_blocks:
                m1b.write_text(
                    block + "\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"C bleed on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Unexpected PASS when C=403 JSON on:\n{block}",
                )

            c_err_json.unlink()
            e_ok_path.unlink()
            c_ok_path.write_bytes(c_ok_bytes)
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            for block in r12_ce_blocks:
                m1b.write_text(
                    block + "\n"
                    f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"Lost E blocker on:\n{block}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"False C blocker on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "PASS",
                    msg=f"Unexpected FAIL on:\n{block}",
                )

            c_ok_path.unlink()
            c_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            m1b.write_text(
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): [**C**'s](https://y.com) & [**E**'s](https://z.com) links returned HTTP 403\n"
                f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_C_ID))
            self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID))
            self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_A_ID))
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "PASS",
            )

            for line, exp_a, exp_c, exp_e in (
                (
                    f"- Sources A (`{SOURCE_A_ID}`) & C (`{SOURCE_C_ID}`): C saved locally. A blocked by HTTP 403",
                    True, False, False,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`) & C (`{SOURCE_C_ID}`): C saved locally — A returned HTTP 403",
                    True, False, False,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`) & C (`{SOURCE_C_ID}`): C saved locally / A failed with HTTP 403",
                    True, False, False,
                ),
                (
                    f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally. A sign-in page (HTTP 403) was returned for E.",
                    False, False, True,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): [A](https://x.com), [C](https://y.com) & [E](https://z.com) returned HTTP 403 Access Denied",
                    True, True, True,
                ),
            ):
                m1b.write_text(line + "\n", encoding="utf-8")
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), exp_a, msg=line)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_C_ID), exp_c, msg=line)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_E_ID), exp_e, msg=line)

    def test_regression_r13_iter12_findings(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        bundle_hdr = "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
        with tempfile.TemporaryDirectory(prefix="ec_reg_r13_") as td:
            root = Path(td)

            # 1. Lean vacuous `: True` fail cases (indented `by`, same-line `by`, multiline op continuation)
            r13_vac_fail_cases = (
                (
                    "R13LetIndentedByTrue.lean",
                    "theorem vac :\n  let _ : 0 = 0 :=\n    by\n      rfl\n    True := trivial\n",
                ),
                (
                    "R13LetSameLineByIndentTrue.lean",
                    "theorem vac :\n  let _ : 0 = 0 := by\n      rfl\n    True := trivial\n",
                ),
                (
                    "R13LetMultilineOpTrue.lean",
                    "theorem vac :\n    let _ := 0\n      + 1\n    True := trivial\n",
                ),
            )
            for fname, body in r13_vac_fail_cases:
                self.assertTrue(scan_native_decide_and_vacuous_true(body), msg=f"{fname} missed by vacuous scanner")
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 2. Lean bundler fail cases (Items 1-5)
            base_1 = "structure Base (n : Nat) : Prop where\n  p1 : n = n\n"
            base_2 = (
                "structure Base1 (n : Nat) : Prop where\n  p1 : n = n\n"
                "structure Base2 (n : Nat) : Prop where\n  p2 : n + 0 = n\n"
            )
            r13_bundler_fail_cases = (
                (
                    "R13TryNewlineSuffices.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  try\n    suffices _ : n = n by exact ⟨rfl, Nat.add_zero n⟩\n  cases n <;> rfl\n",
                ),
                (
                    "R13FocusNewlineSuffices.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  focus\n    suffices _ : n = n by exact ⟨rfl, Nat.add_zero n⟩\n  cases n <;> rfl\n",
                ),
                (
                    "R13AllGoalsNewlineSuffices.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  all_goals\n    suffices _ : n = n by exact ⟨rfl, Nat.add_zero n⟩\n  cases n <;> rfl\n",
                ),
                (
                    "R13FirstNewlinePipeSuffices.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  first\n  | suffices _ : n = n by exact ⟨rfl, Nat.add_zero n⟩\n  | skip\n  cases n <;> rfl\n",
                ),
                (
                    "R13SimpGoalBraceLiteral.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact { p1 := rfl, p2 := rfl }\n",
                ),
                (
                    "R13SimpGoalRefineBrace.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  refine { p1 := rfl, p2 := rfl }\n",
                ),
                (
                    "R13SimpAtHBraceLiteral.lean",
                    bundle_hdr + "theorem bypass (h : 0 + 0 = 0) : Bundle 0 := by\n  simp only [Nat.add_zero] at h\n  exact { p1 := rfl, p2 := rfl }\n",
                ),
                (
                    "R13SimpGoalParenAngle.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (⟨rfl, rfl⟩)\n",
                ),
                (
                    "R13SimpGoalParenBundleMk.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (Bundle.mk rfl rfl)\n",
                ),
                (
                    "R13SimpGoalParenDotMk.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (.mk rfl rfl)\n",
                ),
                (
                    "R13SimpGoalCtorBullets.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  constructor\n  · rfl\n  · rfl\n",
                ),
                (
                    "R13SimpGoalCtorBraces.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  constructor\n  { rfl }\n  { rfl }\n",
                ),
                (
                    "R13SimpGoalExactByExactRfl.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact ⟨by exact rfl, rfl⟩\n",
                ),
                (
                    "R13SimpGoalExactEqRefl.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact ⟨Eq.refl _, Eq.refl _⟩\n",
                ),
                (
                    "R13SimpGoalNested3Extends.lean",
                    "structure AExt (n : Nat) : Prop where\n  p1 : n = n\n"
                    "structure BExt (n : Nat) : Prop extends AExt n where\n  p2 : n = n\n"
                    "structure CExt (n : Nat) : Prop extends BExt n where\n  p3 : n = n\n"
                    "theorem bypass : CExt (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact ⟨⟨⟨rfl⟩, rfl⟩, rfl⟩\n",
                ),
                (
                    "R13LetIndentedByBundler.lean",
                    bundle_hdr + "theorem bypass (n : Nat) :\n  let _ : 0 = 0 :=\n    by\n      rfl\n    Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "R13LetMultilineOpBundler.lean",
                    bundle_hdr + "theorem bypass (n : Nat) :\n    let _ := 0\n      + 1\n    Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "R13ExtendsNoWhere2Parents.lean",
                    base_2 + "structure SubExt (n : Nat) extends Base1 n, Base2 n\ntheorem bypass (n : Nat) : SubExt n := ⟨⟨rfl⟩, ⟨Nat.add_zero n⟩⟩\n",
                ),
                (
                    "R13ExtendsCustomProjNoProp.lean",
                    base_1 + "structure SubExt (n : Nat) extends toB : Base n where\n  p2 : n + 0 = n\ntheorem bypass (n : Nat) : SubExt n := ⟨⟨rfl⟩, Nat.add_zero n⟩\n",
                ),
                (
                    "R13ExtendsCustomProjPropBrace.lean",
                    base_1 + "structure SubExt (n : Nat) : Prop extends toB : Base n where\n  p2 : n + 0 = n\ntheorem bypass (n : Nat) : SubExt n := { toB := ⟨rfl⟩, p2 := Nat.add_zero n }\n",
                ),
                (
                    "R13HaveSingleParenTypedShadow.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    have (h) : Nat := 0\n"
                    "    exact (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
            )
            for fname, body in r13_bundler_fail_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertTrue(scan_parameterized_prop_bundlers(body), msg=f"{fname} missed by bundler scanner")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 3. Lean positive controls (Items 1-5)
            r13_lean_pass_cases = (
                (
                    "R13PosFirstParenFailSkip.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  first | (suffices _ : 0 = 1 by exact rfl) | skip\n"
                    "  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R13PosFirstNewlineFailSkip.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  first\n  | suffices _ : 0 = 1 by exact rfl\n  | skip\n"
                    "  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R13PosTryNewlineFail.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  try\n    suffices _ : 0 = 1 by exact rfl\n"
                    "  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R13PosSimpDotMkH.lean",
                    bundle_hdr
                    + "theorem witness (n : Nat) : Bundle n := by\n  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    + "theorem ok (h : 0 + 0 = 0) : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact .mk rfl h\n",
                ),
                (
                    "R13PosSimpBundleMkH.lean",
                    bundle_hdr
                    + "theorem witness (n : Nat) : Bundle n := by\n  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    + "theorem ok (h : 0 + 0 = 0) : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact Bundle.mk rfl h\n",
                ),
                (
                    "R13PosSimpBraceH.lean",
                    bundle_hdr
                    + "theorem witness (n : Nat) : Bundle n := by\n  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    + "theorem ok (h : 0 + 0 = 0) : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact { p1 := rfl, p2 := h }\n",
                ),
                (
                    "R13PosSimpCtorBulletsH.lean",
                    bundle_hdr
                    + "theorem witness (n : Nat) : Bundle n := by\n  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    + "theorem ok (h : 0 + 0 = 0) : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  constructor\n  · rfl\n  · exact h\n",
                ),
                (
                    "R13PosLetIndentedByEq.lean",
                    "theorem ok :\n  let _ : 0 = 0 :=\n    by\n      rfl\n    0 = 0 := rfl\n",
                ),
                (
                    "R13PosLetMultilineOpEq.lean",
                    "theorem ok :\n    let x := 0\n      + 1\n    x = 1 := rfl\n",
                ),
                (
                    "R13PosExtendsNoWhereType.lean",
                    "structure Base1T (n : Nat) : Type where\n  p1 : Nat\n"
                    "theorem b1_wit (n : Nat) : Nonempty (Base1T n) := ⟨⟨n⟩⟩\n"
                    "structure Base2T (n : Nat) : Type where\n  p2 : Nat\n"
                    "theorem b2_wit (n : Nat) : Nonempty (Base2T n) := ⟨⟨n⟩⟩\n"
                    "structure SubExtT (n : Nat) extends Base1T n, Base2T n\n"
                    "theorem sub_wit (n : Nat) : Nonempty (SubExtT n) := ⟨⟨⟨n⟩, ⟨n⟩⟩⟩\n"
                    "def mkSub (n : Nat) : SubExtT n := ⟨⟨n⟩, ⟨n⟩⟩\n",
                ),
                (
                    "R13PosHaveSingleParenOther.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    have (k) : Nat := 0\n"
                    "    exact (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
            )
            for fname, body in r13_lean_pass_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertEqual(scan_native_decide_and_vacuous_true(body), [], msg=f"{fname} false vacuous hit")
                self.assertEqual(scan_parameterized_prop_bundlers(body), [], msg=f"{fname} false bundler hit")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "PASS", msg=f"{fname} false-failed T1-LEAN-04: {res.summary}")

            # 4. T3-CONS-02: open hiding/(only)/renaming, axiom shadow, export, single-line & multiline open ... in
            lean_dir = root / "lean" / "InfoGeometry" / "Test"
            lean_dir.mkdir(parents=True)
            t_mod = lean_dir / "TMod.lean"
            t_aud = lean_dir / "TModAudit.lean"
            t_env = root / "env_t13.json"
            t_arts = DiscoveredArtifacts([], [t_env], [], [], [], [t_env], [])

            def _set_ns13_case(mod_src: str, acc_thm: str, aud_src: str) -> str:
                t_mod.write_text(mod_src, encoding="utf-8")
                t_aud.write_text(aud_src, encoding="utf-8")
                t_env.write_text(
                    json.dumps(
                        {
                            "owner_search": {
                                "target_artifacts": [
                                    "lean/InfoGeometry/Test/TMod.lean",
                                    "lean/InfoGeometry/Test/TModAudit.lean",
                                ]
                            },
                            "formal_objects": {"lane_t": ["TMod.obj"]},
                            "acceptance_theorems": {"lane_t": [acc_thm]},
                        }
                    ),
                    encoding="utf-8",
                )
                tgts = [ResolvedTarget(t_mod, "lean/InfoGeometry/Test/TMod.lean", "InfoGeometry.Test.TMod", True)]
                return check_t3_cons_02_contracts_to_lean_declarations(
                    root, t_arts, tgts, require_all_envelope_targets=True
                ).status

            ns_ok_src = "namespace Ns\ntheorem ok : 1 = 1 := rfl\ntheorem other : 2 = 2 := rfl\nend Ns\n"
            self.assertEqual(_set_ns13_case(ns_ok_src, "Ns.ok", "theorem ok : 1 = 1 := rfl\nopen Ns hiding ok\n#print axioms ok\n"), "FAIL")
            self.assertEqual(_set_ns13_case(ns_ok_src, "Ns.ok", "open Ns hiding other\n#print axioms ok\n"), "PASS")
            self.assertEqual(_set_ns13_case(ns_ok_src, "Ns.ok", "theorem ok : 1 = 1 := rfl\nopen Ns (other)\n#print axioms ok\n"), "FAIL")
            self.assertEqual(_set_ns13_case(ns_ok_src, "Ns.ok", "open Ns (ok)\n#print axioms ok\n"), "PASS")
            self.assertEqual(_set_ns13_case(ns_ok_src, "Ns.ok", "theorem ok : 1 = 1 := rfl\nopen Ns renaming ok → ok'\n#print axioms ok\n"), "FAIL")
            self.assertEqual(_set_ns13_case(ns_ok_src, "Ns.ok", "open Ns renaming ok → ok'\n#print axioms ok'\n"), "PASS")
            self.assertEqual(_set_ns13_case(ns_ok_src, "Ns.ok", "namespace Ns\nnamespace Inner\naxiom ok : 1 = 1\n#print axioms ok\nend Inner\nend Ns\n"), "FAIL")
            self.assertEqual(_set_ns13_case(ns_ok_src, "Ns.ok", "export Ns (ok)\n#print axioms ok\n"), "PASS")
            self.assertEqual(_set_ns13_case(ns_ok_src, "Ns.ok", "open Ns in #print axioms ok\n"), "PASS")
            self.assertEqual(_set_ns13_case(ns_ok_src, "Ns.ok", "open Ns in\n#print axioms ok\n"), "PASS")
            self.assertEqual(_set_ns13_case(ns_ok_src, "Ns.ok", "open Ns in\n#print axioms other\n#print axioms ok\n"), "FAIL")

            # 5. T3-CONS-05: 3+ nested parens in bare URLs
            (root / "docs").mkdir(parents=True)
            samp = root / "docs" / "sample.md"
            samp.write_bytes(b"sample v3\n")
            samp_sha = hashlib.sha256(b"sample v3\n").hexdigest()
            qa_rep = root / "qa_report.md"
            url_hex = "a" * 64
            bad_hex = "b" * 64
            for qa_line in (
                f"| https://en.wikipedia.org/wiki/Foo_(a_(b_(c)))/{url_hex} | docs/sample.md | `{samp_sha}` |\n",
                f"| (see https://en.wikipedia.org/wiki/Foo_(a_(b_(c)))/{url_hex}) | docs/sample.md | `{samp_sha}` |\n",
            ):
                qa_rep.write_text(qa_line, encoding="utf-8")
                r_ok = check_t3_cons_05_audit_report_hashes(
                    root, DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]), targets=[]
                )
                self.assertEqual(r_ok.status, "PASS", msg=f"{qa_line.strip()} -> {r_ok.summary}")
                self.assertIn("(1/1 files)", r_ok.summary)
            qa_rep.write_text(
                f"| https://en.wikipedia.org/wiki/Foo_(a_(b_(c)))/{url_hex} | docs/sample.md | `{bad_hex}` |\n",
                encoding="utf-8",
            )
            r_bad = check_t3_cons_05_audit_report_hashes(
                root, DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]), targets=[]
            )
            self.assertEqual(r_bad.status, "FAIL", msg=r_bad.summary)
            self.assertEqual(r_bad.details.get("checked"), 1)

            # 6. Intake Items 8-10: English A NP vs verb, multi-header summaries/R9/intro/loose/5-src/subheadings, shared-subject sentence cutoff, link quotes/angles, no-space slash
            (root / "cached" / "drive_docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )
            m1b = root / "docs" / "M1B_R13.md"
            c_ok_bytes = b"Source C valid markdown\n"
            c_sha = hashlib.sha256(c_ok_bytes).hexdigest()
            e_ok_bytes = b"Source E valid markdown\n"
            e_sha = hashlib.sha256(e_ok_bytes).hexdigest()
            c_err_json = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.json"
            c_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            e_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.md"
            e_html = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"

            filler_lines = "\n".join(f"  - Note {idx_f}: metadata line" for idx_f in range(1, 13))
            r13_ce_blocks = (
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): one saved, one HTTP 403\n  - C: saved locally\n  - E: HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): one saved, one HTTP 403.\n  - C: saved locally\n  - E: HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): one saved, one HTTP 403 (details below)\n  - C: saved locally\n  - E: HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`) — one saved, one HTTP 403\n  - C: saved locally\n  - E: HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally, E:\n  HTTP 403 Access Denied",
                f"### Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`)\nOne source hit HTTP 403:\n- C: saved locally\n- E: HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`):\n\n  - C: saved locally\n  - E: HTTP 403 Access Denied",
                f"### Sources A (`{SOURCE_A_ID}`), B (`{SOURCE_B_ID}`), C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`) & E (`{SOURCE_E_ID}`)\n- A: saved locally\n- B: saved locally\n- C: saved locally\n{filler_lines}\n- D: saved locally\n- E: HTTP 403 Access Denied",
                f"### Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`)\n#### Source C\nsaved locally\n#### Source E\nHTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally. A blocked HTTP 403 response was returned for E.",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally. A failed HTTP 403 download occurred for E.",
            )

            c_err_json.write_text(json.dumps({"error": {"code": 403, "message": "Access denied"}}), encoding="utf-8")
            e_ok_path.write_bytes(e_ok_bytes)
            for block in r13_ce_blocks:
                m1b.write_text(
                    block + "\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"C bleed on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Unexpected PASS when C=403 JSON on:\n{block}",
                )

            c_err_json.unlink()
            e_ok_path.unlink()
            c_ok_path.write_bytes(c_ok_bytes)
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            for block in r13_ce_blocks:
                m1b.write_text(
                    block + "\n"
                    f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"Lost E blocker on:\n{block}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"False C blocker on:\n{block}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_A_ID), msg=f"False A bleed on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "PASS",
                    msg=f"Unexpected FAIL on:\n{block}",
                )

            for line, exp_a, exp_c, exp_e in (
                (
                    f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): A saved locally; C saved locally. A blocked HTTP 403 response was returned for E.",
                    False, False, True,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): A saved locally; E failed (HTTP 403). A blocked HTTP 403 response was returned.",
                    False, False, True,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`) & C (`{SOURCE_C_ID}`): C saved locally. A blocked by HTTP 403",
                    True, False, False,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C & E returned HTTP 403. A was saved locally.",
                    False, True, True,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C, E returned HTTP 403. A was saved locally.",
                    False, True, True,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C & A were blocked by HTTP 403. E saved locally.",
                    True, True, False,
                ),
                (
                    f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): [C](https://y.com \"a ) b\") & [E](https://z.com) returned HTTP 403",
                    False, True, True,
                ),
                (
                    f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): [C](<https://y.com/a)b>) & [E](https://z.com) returned HTTP 403",
                    False, True, True,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`) & C (`{SOURCE_C_ID}`): C saved locally/A failed with HTTP 403",
                    True, False, False,
                ),
                (
                    f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): [C](https://example.com/A) saved locally, E returned HTTP 403 (N/A elsewhere)",
                    False, False, True,
                ),
            ):
                m1b.write_text(line + "\n", encoding="utf-8")
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), exp_a, msg=line)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_C_ID), exp_c, msg=line)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_E_ID), exp_e, msg=line)

    def test_regression_r14_iter13_findings(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        bundle_hdr = "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
        with tempfile.TemporaryDirectory(prefix="ec_reg_r14_") as td:
            root = Path(td)

            # 1. Lean vacuous `: True` fail cases (Item 3: app continuation, && continuation, by skip; rfl, indented by rfl)
            r14_vac_fail_cases = (
                (
                    "R14LetAppContTrue.lean",
                    "theorem vac :\n    let _ := Nat.succ\n      0\n    True := trivial\n",
                ),
                (
                    "R14LetAndContTrue.lean",
                    "theorem vac :\n    let _ := true\n      && false\n    True := trivial\n",
                ),
                (
                    "R14LetBySemiTrue.lean",
                    "theorem vac :\n    let _ : 0 = 0 := by skip; rfl\n    True := trivial\n",
                ),
                (
                    "R14LetIndentedByRflTrue.lean",
                    "theorem vac :\n  let _ : 0 = 0 :=\n    by rfl\n    True := trivial\n",
                ),
            )
            for fname, body in r14_vac_fail_cases:
                self.assertTrue(scan_native_decide_and_vacuous_true(body), msg=f"{fname} missed by vacuous scanner")
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 2. Lean bundler fail cases (Items 1-5)
            r14_bundler_fail_cases = (
                (
                    "R14FirstMlSuccDeadCases.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  first\n"
                    "  | suffices _ : n = n by exact ⟨rfl, Nat.add_zero n⟩\n    exact rfl\n  | cases n <;> rfl\n",
                ),
                (
                    "R14FirstSlSuccDeadCases.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n"
                    "  first | (suffices _ : n = n by exact ⟨rfl, Nat.add_zero n⟩) | cases n <;> rfl\n  exact rfl\n",
                ),
                (
                    "R14FirstSlUnparenSuccDeadCases.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n"
                    "  first | suffices _ : n = n by exact ⟨rfl, Nat.add_zero n⟩ | cases n <;> rfl\n  exact rfl\n",
                ),
                (
                    "R14SimpCtorAllGoalsRfl.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  constructor\n  all_goals rfl\n",
                ),
                (
                    "R14SimpCtorSemiAllGoalsRfl.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  constructor <;> all_goals rfl\n",
                ),
                (
                    "R14SimpCtorSemiRepeatRfl.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  constructor <;> repeat rfl\n",
                ),
                (
                    "R14SimpCtorDoneRfl.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  constructor <;> (rfl; done)\n",
                ),
                (
                    "R14SimpExactAngleBySimp.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact ⟨by simp, rfl⟩\n",
                ),
                (
                    "R14SimpExactBraceMlVal.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact {\n    p1 :=\n      rfl\n    p2 := rfl\n  }\n",
                ),
                (
                    "R14SimpExactBraceByNl.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact {\n    p1 := by\n      rfl\n    p2 := rfl\n  }\n",
                ),
                (
                    "R14SimpExactAtMk.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact @Bundle.mk _ rfl rfl\n",
                ),
                (
                    "R14SimpRefinePrime.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  refine' ⟨rfl, rfl⟩\n",
                ),
                (
                    "R14SimpExactAscriptionAngle.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (⟨rfl, rfl⟩ : Bundle 0)\n",
                ),
                (
                    "R14SimpExactAscriptionBrace.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact ({ p1 := rfl, p2 := rfl } : Bundle 0)\n",
                ),
                (
                    "R14SimpExactAscriptionDotMk.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (.mk rfl rfl : Bundle 0)\n",
                ),
                (
                    "R14SimpExactIdAngle.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact id ⟨rfl, rfl⟩\n",
                ),
                (
                    "R14SimpApplyMk.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  apply Bundle.mk\n  · rfl\n  · rfl\n",
                ),
                (
                    "R14LetAppContBundler.lean",
                    bundle_hdr + "theorem bypass (n : Nat) :\n    let _ := Nat.succ\n      0\n    Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "R14LetBySemiBundler.lean",
                    bundle_hdr + "theorem bypass (n : Nat) :\n    let _ : 0 = 0 := by skip; rfl\n    Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "R14LetIndentedByRflBundler.lean",
                    bundle_hdr + "theorem bypass (n : Nat) :\n  let _ : 0 = 0 :=\n    by rfl\n    Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "R14Extends3LevelGrandparentProj.lean",
                    "structure Base (n : Nat) : Prop where\n  p1 : n = n\n"
                    "structure Mid (n : Nat) : Prop extends Base n where\n  p2 : n + 0 = n\n"
                    "structure SubExt (n : Nat) : Prop extends Mid n where\n  p3 : n = n\n"
                    "theorem bypass (n : Nat) : SubExt n := { toBase := ⟨rfl⟩, p2 := Nat.add_zero n, p3 := rfl }\n",
                ),
                (
                    "R14Extends3LevelCustomGrandparentProj.lean",
                    "structure Base (n : Nat) : Prop where\n  p1 : n = n\n"
                    "structure Mid (n : Nat) : Prop extends toB : Base n where\n  p2 : n + 0 = n\n"
                    "structure SubExt (n : Nat) : Prop extends Mid n where\n  p3 : n = n\n"
                    "theorem bypass (n : Nat) : SubExt n := { toB := ⟨rfl⟩, p2 := Nat.add_zero n, p3 := rfl }\n",
                ),
                (
                    "R14LetParenUntypedShadow.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    let (h) := 0\n    exact (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
                (
                    "R14LetAngleNestedTypedShadow.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    let ⟨(h : Nat), k⟩ := (0, 0)\n    exact (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
                (
                    "R14LetTupleNestedTypedShadow.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    let ((h : Nat), k) := (0, 0)\n    exact (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
                (
                    "R14HaveAngleSingleThenTwo.lean",
                    "structure S1 : Prop where\n  q : 0 = 0\n"
                    + bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n"
                    "  have ⟨x⟩ : S1 := ⟨rfl⟩\n  exact (fun _ => ⟨rfl, Nat.add_zero n⟩) ()\n",
                ),
            )
            for fname, body in r14_bundler_fail_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertTrue(scan_parameterized_prop_bundlers(body), msg=f"{fname} missed by bundler scanner")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 3. Lean positive controls (Items 1-5)
            r14_lean_pass_cases = (
                (
                    "R14PosWithReducibleTry.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  with_reducible\n    try\n      suffices _ : 0 = 1 by exact rfl\n"
                    "  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R14PosAllGoalsTry.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  all_goals\n    try\n      suffices _ : 0 = 1 by exact rfl\n"
                    "  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R14PosFirstSlFailCases.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n"
                    "  first | (suffices _ : 0 = 1 by exact rfl) | cases n with | zero => exact ⟨rfl, rfl⟩ | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R14PosSimpCtorAllGoalsH.lean",
                    bundle_hdr
                    + "theorem witness (n : Nat) : Bundle n := by\n  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    + "theorem myRefl (k : Nat) : k = k := rfl\n"
                    + "theorem ok : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  constructor\n  all_goals exact myRefl _\n",
                ),
                (
                    "R14PosSimpAngleMyLem.lean",
                    bundle_hdr
                    + "theorem witness (n : Nat) : Bundle n := by\n  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    + "theorem myLem (k : Nat) : k = k := rfl\n"
                    + "theorem ok : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact ⟨myLem 0, rfl⟩\n",
                ),
                (
                    "R14PosSimpAtMkH.lean",
                    bundle_hdr
                    + "theorem witness (n : Nat) : Bundle n := by\n  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    + "theorem ok (h : 0 + 0 = 0) : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact @Bundle.mk _ rfl h\n",
                ),
                (
                    "R14PosSimpAscriptionH.lean",
                    bundle_hdr
                    + "theorem witness (n : Nat) : Bundle n := by\n  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    + "theorem ok (h : 0 + 0 = 0) : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (⟨rfl, h⟩ : Bundle (0 + 0))\n",
                ),
                (
                    "R14PosSimpBraceMlH.lean",
                    bundle_hdr
                    + "theorem witness (n : Nat) : Bundle n := by\n  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    + "theorem ok (h : 0 + 0 = 0) : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact {\n    p1 :=\n      rfl\n    p2 := h\n  }\n",
                ),
                (
                    "R14PosLetAppContEq.lean",
                    "theorem ok :\n    let x := Nat.succ\n      0\n    x = 1 := rfl\n",
                ),
                (
                    "R14PosLetBySemiEq.lean",
                    "theorem ok :\n    let _ : 0 = 0 := by skip; rfl\n    0 = 0 := rfl\n",
                ),
                (
                    "R14PosLetIndentedByRflEq.lean",
                    "theorem ok :\n  let _ : 0 = 0 :=\n    by rfl\n    0 = 0 := rfl\n",
                ),
                (
                    "R14PosExtends3LevelType.lean",
                    "structure BaseT (n : Nat) : Type where\n  p1 : Nat\n"
                    "theorem b_wit (n : Nat) : Nonempty (BaseT n) := ⟨⟨n⟩⟩\n"
                    "structure MidT (n : Nat) extends BaseT n where\n  p2 : Nat\n"
                    "theorem m_wit (n : Nat) : Nonempty (MidT n) := ⟨⟨⟨n⟩, n⟩⟩\n"
                    "structure SubExtT (n : Nat) extends MidT n where\n  p3 : Nat\n"
                    "def mkSub (n : Nat) : SubExtT n := { toBaseT := ⟨n⟩, p2 := n, p3 := n }\n",
                ),
                (
                    "R14PosLetParenTypedBindsThis.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    let (h : Nat) := 0\n"
                    "    exact (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => rfl\n",
                ),
                (
                    "R14PosHaveAngleOtherUsed.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    have ⟨(k : Nat), m⟩ := (0, 0)\n"
                    "    exact (fun _ : k + m = k + m => (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl) rfl\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => rfl\n",
                ),
            )
            for fname, body in r14_lean_pass_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertEqual(scan_native_decide_and_vacuous_true(body), [], msg=f"{fname} false vacuous hit")
                self.assertEqual(scan_parameterized_prop_bundlers(body), [], msg=f"{fname} false bundler hit")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "PASS", msg=f"{fname} false-failed T1-LEAN-04: {res.summary}")

            # 4. T3-CONS-02 (Item 6): root-level axiom shadowing, _root_.Ns, nested export, multiline open/export
            lean_dir = root / "lean" / "InfoGeometry" / "Test"
            lean_dir.mkdir(parents=True)
            t_mod = lean_dir / "TMod.lean"
            t_aud = lean_dir / "TModAudit.lean"
            t_env = root / "env_t14.json"
            t_arts = DiscoveredArtifacts([], [t_env], [], [], [], [t_env], [])

            def _set_ns14_case(mod_src: str, acc_thm: str, aud_src: str) -> str:
                t_mod.write_text(mod_src, encoding="utf-8")
                t_aud.write_text(aud_src, encoding="utf-8")
                t_env.write_text(
                    json.dumps(
                        {
                            "owner_search": {
                                "target_artifacts": [
                                    "lean/InfoGeometry/Test/TMod.lean",
                                    "lean/InfoGeometry/Test/TModAudit.lean",
                                ]
                            },
                            "formal_objects": {"lane_t": ["TMod.obj"]},
                            "acceptance_theorems": {"lane_t": [acc_thm]},
                        }
                    ),
                    encoding="utf-8",
                )
                tgts = [ResolvedTarget(t_mod, "lean/InfoGeometry/Test/TMod.lean", "InfoGeometry.Test.TMod", True)]
                return check_t3_cons_02_contracts_to_lean_declarations(
                    root, t_arts, tgts, require_all_envelope_targets=True
                ).status

            ns14_src = (
                "namespace Ns\ntheorem ok : 1 = 1 := rfl\ntheorem other : 2 = 2 := rfl\n"
                "namespace Inner\ntheorem ok : 3 = 3 := rfl\nend Inner\nend Ns\n"
            )
            self.assertEqual(_set_ns14_case(ns14_src, "Ns.ok", "open Ns\naxiom ok : 1 = 1\n#print axioms ok\n"), "FAIL")
            self.assertEqual(_set_ns14_case(ns14_src, "Ns.ok", "axiom ok : 1 = 1\nopen Ns\n#print axioms ok\n"), "FAIL")
            self.assertEqual(_set_ns14_case(ns14_src, "Ns.ok", "axiom ok' : 1 = 1\nopen Ns renaming ok → ok'\n#print axioms ok'\n"), "FAIL")
            self.assertEqual(_set_ns14_case(ns14_src, "Ns.Inner.ok", "namespace Inner\naxiom ok : 1 = 1\nend Inner\nopen Ns\n#print axioms Inner.ok\n"), "FAIL")
            self.assertEqual(_set_ns14_case(ns14_src, "Ns.ok", "open _root_.Ns\n#print axioms ok\n"), "PASS")
            self.assertEqual(_set_ns14_case(ns14_src, "Ns.ok", "namespace A\nopen _root_.Ns in #print axioms ok\nend A\n"), "PASS")
            self.assertEqual(_set_ns14_case(ns14_src, "Ns.ok", "namespace Outer\nexport Ns (ok)\nend Outer\n#print axioms Outer.ok\n"), "PASS")
            self.assertEqual(_set_ns14_case(ns14_src, "Ns.ok", "namespace Outer\nexport Ns (ok)\nend Outer\nopen Outer\n#print axioms ok\n"), "PASS")
            self.assertEqual(_set_ns14_case(ns14_src, "Ns.ok", "open Ns (\n  ok\n)\n#print axioms ok\n"), "PASS")
            self.assertEqual(_set_ns14_case(ns14_src, "Ns.ok", "theorem ok : 1 = 1 := rfl\nopen Ns (\n  other\n)\n#print axioms ok\n"), "FAIL")
            self.assertEqual(_set_ns14_case(ns14_src, "Ns.ok", "namespace Outer\nexport Ns (\n  ok\n)\nend Outer\nopen Outer\n#print axioms ok\n"), "PASS")

            # 5. T3-CONS-05 (Item 7): URL path hijack prevention & IPv6/bracketed bare URL masking
            (root / "docs").mkdir(parents=True)
            samp = root / "docs" / "sample.md"
            other = root / "docs" / "other.md"
            samp.write_bytes(b"sample v14\n")
            other.write_bytes(b"other v14\n")
            samp_sha = hashlib.sha256(b"sample v14\n").hexdigest()
            qa_rep = root / "qa_report_r14.md"
            url_hex = "a" * 64
            bad_hex = "b" * 64
            for qa_line in (
                f"| [Upstream](https://example.com/docs/other.md) | docs/sample.md | `{samp_sha}` |\n",
                f"| https://example.com/docs/other.md/{url_hex} | docs/sample.md | `{samp_sha}` |\n",
                f"| https://example.com/a[1]/{url_hex} | docs/sample.md | `{samp_sha}` |\n",
                f"| http://[::1]:8080/{url_hex} | docs/sample.md | `{samp_sha}` |\n",
            ):
                qa_rep.write_text(qa_line, encoding="utf-8")
                r_ok = check_t3_cons_05_audit_report_hashes(
                    root, DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]), targets=[]
                )
                self.assertEqual(r_ok.status, "PASS", msg=f"{qa_line.strip()} -> {r_ok.summary}")
                self.assertIn("(1/1 files)", r_ok.summary)
            qa_rep.write_text(
                f"| [Ref](https://example.com/docs/other.md) | docs/sample.md | `{bad_hex}` |\n",
                encoding="utf-8",
            )
            r_hijack_fail = check_t3_cons_05_audit_report_hashes(
                root, DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]), targets=[]
            )
            self.assertEqual(r_hijack_fail.status, "FAIL", msg=r_hijack_fail.summary)
            self.assertEqual(r_hijack_fail.details.get("checked"), 1)

            # 6. Intake Items 8-9: end-to-end T1-INTAKE-07 on P14 + heading summaries, #### blanks/notes, R9 ;/—, verb-object vs English NP, P6/P7b/P18/P19
            (root / "cached" / "drive_docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )
            m1b = root / "docs" / "M1B_R14.md"
            c_ok_bytes = b"Source C valid markdown R14\n"
            c_sha = hashlib.sha256(c_ok_bytes).hexdigest()
            e_ok_bytes = b"Source E valid markdown R14\n"
            e_sha = hashlib.sha256(e_ok_bytes).hexdigest()
            c_err_json = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.json"
            c_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            e_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.md"
            e_html = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"

            r14_ce_blocks = (
                f"### Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): one saved, one HTTP 403\n- C: saved locally\n- E: HTTP 403 Access Denied",
                f"### Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`) — one saved, one HTTP 403\n- C: saved locally\n- E: HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): one saved, one HTTP 403.\n  Source C: saved locally\n  Source E: HTTP 403 Access Denied",
                f"### Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`)\n\n#### Source C\n\nsaved locally\n\n#### Source E\n\nHTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally; E:\n  HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`) — C saved locally, E:\n  HTTP 403 Access Denied",
                f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): A saved locally; C saved locally. A returned error (HTTP 403) prevented E.",
                f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): A saved locally; C saved locally. A required login (HTTP 403) blocked E.",
                f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): A saved locally; C saved locally. A returned HTTP 403 response was observed for E.",
            )

            c_err_json.write_text(json.dumps({"error": {"code": 403, "message": "Access denied"}}), encoding="utf-8")
            e_ok_path.write_bytes(e_ok_bytes)
            for block in r14_ce_blocks:
                m1b.write_text(
                    block + "\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"C bleed on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Unexpected PASS when C=403 JSON on:\n{block}",
                )

            c_err_json.unlink()
            e_ok_path.unlink()
            c_ok_path.write_bytes(c_ok_bytes)
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            for block in r14_ce_blocks:
                m1b.write_text(
                    block + "\n"
                    f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"Lost E blocker on:\n{block}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"False C blocker on:\n{block}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_A_ID), msg=f"False A bleed on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "PASS",
                    msg=f"Unexpected FAIL on:\n{block}",
                )

            for line, exp_a, exp_c, exp_e in (
                (
                    f"- Sources A (`{SOURCE_A_ID}`) & C (`{SOURCE_C_ID}`): C saved locally. A returned a sign-in page (HTTP 403)",
                    True, False, False,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`) & C (`{SOURCE_C_ID}`): C saved locally. A required a Google sign-in page",
                    True, False, False,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`) & C (`{SOURCE_C_ID}`): C saved locally. A returned an HTTP 403 response",
                    True, False, False,
                ),
                (
                    f"### Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`)\n- C: saved locally\n#### General Notes\nOne source returned HTTP 403.",
                    False, False, False,
                ),
                (
                    f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C & E were saved locally. A blocked HTTP 403 response was returned.",
                    False, False, False,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C (Drive 2) & E (Drive 3) returned HTTP 403. A was saved locally.",
                    False, True, True,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): [C](https://y.com \"Grade A (draft)\") & [E](https://z.com) returned HTTP 403",
                    False, True, True,
                ),
                (
                    f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C https://y.com/?other=E returned HTTP 403, E saved locally",
                    False, True, False,
                ),
            ):
                m1b.write_text(line + "\n", encoding="utf-8")
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), exp_a, msg=line)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_C_ID), exp_c, msg=line)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_E_ID), exp_e, msg=line)

    def test_regression_r15_iter14_findings(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        bundle_hdr = "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
        with tempfile.TemporaryDirectory(prefix="ec_reg_r15_") as td:
            root = Path(td)

            # 1. Lean vacuous `: True` fail cases (Item 3: 2-arg multiline app, smaller-indented app arg, ^/%/<<< infix ops)
            r15_vac_fail_cases = (
                (
                    "R15LetNatAdd2ArgsTrue.lean",
                    "theorem vac :\n    let _ := Nat.add\n      0\n      1\n    True := trivial\n",
                ),
                (
                    "R15LetSmallerIndAppTrue.lean",
                    "theorem vac :\n  let _ :=\n      Nat.succ\n    0\n  True := trivial\n",
                ),
                (
                    "R15LetPowContTrue.lean",
                    "theorem vac :\n    let _ := 1 +\n      2\n      ^ 3\n    True := trivial\n",
                ),
                (
                    "R15LetModContTrue.lean",
                    "theorem vac :\n    let _ := 5\n      % 3\n    True := trivial\n",
                ),
                (
                    "R15LetOpContInValTrue.lean",
                    "theorem vac :\n    let _ :=\n      1 + 2\n      ^ 3\n    True := trivial\n",
                ),
                (
                    "R15LetShiftContTrue.lean",
                    "theorem vac :\n    let _ := 1\n      <<< 2\n    True := trivial\n",
                ),
            )
            for fname, body in r15_vac_fail_cases:
                self.assertTrue(scan_native_decide_and_vacuous_true(body), msg=f"{fname} missed by vacuous scanner")
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 2. Lean bundler fail cases (Items 1-4)
            r15_bundler_fail_cases = (
                (
                    "R15CtorFirstMlRflDeadCases.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  constructor\n  · first\n"
                    "    | suffices _ : n = n by\n        exact rfl\n      exact rfl\n"
                    "    | cases n with\n      | zero => rfl\n      | succ _ => rfl\n  · exact Nat.add_zero n\n",
                ),
                (
                    "R15FirstMlStructRflDeadCases.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  first\n"
                    "  | suffices _ : n = n by\n      exact ⟨rfl, Nat.add_zero n⟩\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R15TryStructRflDeadCases.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  try\n"
                    "    suffices _ : n = n by\n      exact ⟨rfl, Nat.add_zero n⟩\n    exact rfl\n"
                    "  all_goals (cases n <;> rfl)\n",
                ),
                (
                    "R15SimpCtorColonBullets.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  constructor;\n  · rfl\n  · rfl\n",
                ),
                (
                    "R15SimpCtorFirstRfl.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  constructor <;> first | rfl | trivial\n",
                ),
                (
                    "R15SimpRefineAngleHoles.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  refine ⟨?_, ?_⟩\n  · rfl\n  · rfl\n",
                ),
                (
                    "R15SimpRefineBraceHoles.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  refine { p1 := ?_, p2 := ?_ }\n  · rfl\n  · rfl\n",
                ),
                (
                    "R15SimpRefineMkHoles.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  refine Bundle.mk ?_ ?_\n  · rfl\n  · rfl\n",
                ),
                (
                    "R15SimpCtorAllGoalsNl.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  constructor\n  all_goals\n    rfl\n",
                ),
                (
                    "R15SimpApplyMkAllGoalsNl.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  apply Bundle.mk\n  all_goals\n    rfl\n",
                ),
                (
                    "R15SimpExactByCtorAllGoals.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (by constructor; all_goals rfl)\n",
                ),
                (
                    "R15SimpExactByCtorSemiAllGoals.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (by constructor <;> all_goals rfl)\n",
                ),
                (
                    "R15SimpExactByApplyMkSemi.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (by apply Bundle.mk <;> rfl)\n",
                ),
                (
                    "R15SimpExactByApplyMkBullets.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (by\n    apply Bundle.mk\n    · rfl\n    · rfl)\n",
                ),
                (
                    "R15SimpShowFromAngle.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact show Bundle 0 from ⟨rfl, rfl⟩\n",
                ),
                (
                    "R15SimpNamedMk.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact Bundle.mk (p1 := rfl) (p2 := rfl)\n",
                ),
                (
                    "R15SimpIdNamedArg.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact id (α := Bundle 0) ⟨rfl, rfl⟩\n",
                ),
                (
                    "R15LetNatAdd2ArgsBundler.lean",
                    bundle_hdr + "theorem bypass (n : Nat) :\n    let _ := Nat.add\n      0\n      1\n    Bundle n := ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "R15LetParenAngleShadow.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    let (⟨h, k⟩) := (0, 0)\n    exact (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
                (
                    "R15LetParenProdMkShadow.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    let (Prod.mk h k) := (0, 0)\n    exact (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
                (
                    "R15LetDoubleParenTypedShadow.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    let ((h : Nat)) := 0\n    exact (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
                (
                    "R15LetParenAtShadow.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    let (h@k) := 0\n    exact (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
                (
                    "R15LetParenProdMkTypedShadow.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    let (Prod.mk (h : Nat) k) := (0, 0)\n    exact (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
            )
            for fname, body in r15_bundler_fail_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertTrue(scan_parameterized_prop_bundlers(body), msg=f"{fname} missed by bundler scanner")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 3. Lean positive controls (Items 1-4)
            r15_lean_pass_cases = (
                (
                    "R15PosFirstSlSimpFailCases.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n"
                    "  first | (suffices _ : 0 = 1 by simp) | cases n with | zero => exact ⟨rfl, rfl⟩ | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R15PosFirstMlTypedUnsatEq.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  first\n"
                    "  | suffices _ : (0 : Nat) = 1 by exact Eq.refl 0\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R15PosFirstMlTrueFalseEq.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  first\n"
                    "  | suffices _ : true = false by exact Eq.refl true\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R15PosTryEqReflFail.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  try\n"
                    "    suffices _ : 0 = 1 by exact Eq.refl 0\n"
                    "  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R15PosSimpCtorColonMyLem.lean",
                    bundle_hdr
                    + "theorem witness (n : Nat) : Bundle n := by\n  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    + "theorem myLem (k : Nat) : k = k := rfl\n"
                    + "theorem ok : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  constructor;\n  · exact myLem 0\n  · rfl\n",
                ),
                (
                    "R15PosSimpRefineMyLem.lean",
                    bundle_hdr
                    + "theorem witness (n : Nat) : Bundle n := by\n  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    + "theorem myLem (k : Nat) : k = k := rfl\n"
                    + "theorem ok : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  refine ⟨?_, ?_⟩\n  · exact myLem 0\n  · rfl\n",
                ),
                (
                    "R15PosSimpShowFromMyLem.lean",
                    bundle_hdr
                    + "theorem witness (n : Nat) : Bundle n := by\n  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    + "theorem myLem (k : Nat) : k = k := rfl\n"
                    + "theorem ok : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact show Bundle 0 from ⟨myLem 0, rfl⟩\n",
                ),
                (
                    "R15PosSimpNamedMkH.lean",
                    bundle_hdr
                    + "theorem witness (n : Nat) : Bundle n := by\n  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    + "theorem ok (h : 0 + 0 = 0) : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact Bundle.mk (p1 := h) (p2 := rfl)\n",
                ),
                (
                    "R15PosLetNatAdd2ArgsEq.lean",
                    "theorem ok :\n    let x := Nat.add\n      0\n      1\n    x = 1 := rfl\n",
                ),
                (
                    "R15PosLetSmallerIndEq.lean",
                    "theorem ok :\n  let x :=\n      Nat.succ\n    0\n  x = 1 := rfl\n",
                ),
                (
                    "R15PosLetPowContEq.lean",
                    "theorem ok :\n    let x := 1 +\n      2\n      ^ 3\n    x = 9 := rfl\n",
                ),
                (
                    "R15PosLetParenTypedNotShadow.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    let (h : Nat) := 0\n    exact (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => rfl\n",
                ),
            )
            for fname, body in r15_lean_pass_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertEqual(scan_native_decide_and_vacuous_true(body), [], msg=f"{fname} false vacuous hit")
                self.assertEqual(scan_parameterized_prop_bundlers(body), [], msg=f"{fname} false bundler hit")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "PASS", msg=f"{fname} false-failed T1-LEAN-04: {res.summary}")

            # 4. T3-CONS-02 (Item 5): d == 0 shadow after export, section export, open ... in section, multiline open renaming/hiding
            lean_dir = root / "lean" / "InfoGeometry" / "Test"
            lean_dir.mkdir(parents=True)
            t_mod = lean_dir / "TMod.lean"
            t_aud = lean_dir / "TModAudit.lean"
            t_env = root / "env_t15.json"
            t_arts = DiscoveredArtifacts([], [t_env], [], [], [], [t_env], [])

            def _set_ns15_case(mod_src: str, acc_thm: str, aud_src: str) -> str:
                t_mod.write_text(mod_src, encoding="utf-8")
                t_aud.write_text(aud_src, encoding="utf-8")
                t_env.write_text(
                    json.dumps(
                        {
                            "owner_search": {
                                "target_artifacts": [
                                    "lean/InfoGeometry/Test/TMod.lean",
                                    "lean/InfoGeometry/Test/TModAudit.lean",
                                ]
                            },
                            "formal_objects": {"lane_t": ["TMod.obj"]},
                            "acceptance_theorems": {"lane_t": [acc_thm]},
                        }
                    ),
                    encoding="utf-8",
                )
                tgts = [ResolvedTarget(t_mod, "lean/InfoGeometry/Test/TMod.lean", "InfoGeometry.Test.TMod", True)]
                return check_t3_cons_02_contracts_to_lean_declarations(
                    root, t_arts, tgts, require_all_envelope_targets=True
                ).status

            ns15_src = "namespace Ns\ntheorem ok : 1 = 1 := rfl\nend Ns\n"
            self.assertEqual(
                _set_ns15_case(
                    ns15_src,
                    "Ns.ok",
                    "namespace Outer\nexport Ns (ok)\nend Outer\nnamespace Outer\naxiom ok : 1 = 1\nend Outer\n#print axioms Outer.ok\n",
                ),
                "FAIL",
            )
            self.assertEqual(_set_ns15_case(ns15_src, "Ns.ok", "section S\nexport Ns (ok)\nend S\n#print axioms ok\n"), "PASS")
            self.assertEqual(_set_ns15_case(ns15_src, "Ns.ok", "open Ns in\nsection\n#print axioms ok\nend\n"), "PASS")
            self.assertEqual(
                _set_ns15_case(ns15_src, "Ns.ok", "theorem ok : 1 = 1 := rfl\nopen Ns in\nsection\nend\n#print axioms ok\n"),
                "FAIL",
            )
            self.assertEqual(
                _set_ns15_case(ns15_src, "Ns.ok", "open Ns renaming\n  ok → ok_ren\n#print axioms ok_ren\n"),
                "PASS",
            )
            self.assertEqual(
                _set_ns15_case(ns15_src, "Ns.ok", "theorem ok : 1 = 1 := rfl\nopen Ns hiding\n  ok\n#print axioms ok\n"),
                "FAIL",
            )

            # 5. T3-CONS-05 (Item 6): external Markdown link label `[docs/other.md](https://...)` must not hijack m_plain
            (root / "docs").mkdir(parents=True)
            samp = root / "docs" / "sample.md"
            other = root / "docs" / "other.md"
            samp.write_bytes(b"sample v15\n")
            other.write_bytes(b"other v15\n")
            samp_sha = hashlib.sha256(b"sample v15\n").hexdigest()
            other_sha = hashlib.sha256(b"other v15\n").hexdigest()
            qa_rep = root / "qa_report_r15.md"
            qa_rep.write_text(f"| [docs/other.md](https://example.com/other) | docs/sample.md | `{samp_sha}` |\n", encoding="utf-8")
            r_ext_ok = check_t3_cons_05_audit_report_hashes(
                root, DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]), targets=[]
            )
            self.assertEqual(r_ext_ok.status, "PASS", msg=r_ext_ok.summary)
            self.assertIn("(1/1 files)", r_ext_ok.summary)
            qa_rep.write_text(f"| [docs/other.md](https://example.com/other) | docs/sample.md | `{other_sha}` |\n", encoding="utf-8")
            r_ext_fail = check_t3_cons_05_audit_report_hashes(
                root, DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]), targets=[]
            )
            self.assertEqual(r_ext_fail.status, "FAIL", msg=r_ext_fail.summary)
            self.assertEqual(r_ext_fail.details.get("checked"), 1)

            # 6. Intake Items 7-8: end-to-end T1-INTAKE-07 on NEW_H5 (bold sub-labels) & NEW_H1..H4, NEW_A1..A6
            (root / "cached" / "drive_docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )
            m1b = root / "docs" / "M1B_R15.md"
            c_ok_bytes = b"Source C valid markdown R15\n"
            c_sha = hashlib.sha256(c_ok_bytes).hexdigest()
            e_ok_bytes = b"Source E valid markdown R15\n"
            e_sha = hashlib.sha256(e_ok_bytes).hexdigest()
            c_err_json = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.json"
            c_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            e_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.md"
            e_html = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"

            r15_ce_blocks = (
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): one saved, one HTTP 403.\n  **Source C**: saved locally\n  **Source E**:\n    HTTP 403 Access Denied",
                f"### Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`)\n#### Source C\nsaved locally\n#### Source E\n##### Access Blocker\nHTTP 403 Access Denied",
                f"### Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`)\n#### General Notes\nOne source returned HTTP 403.\n- C: saved locally\n- E: HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally; E:\n  HTTP 403 Access Denied\n  Note: C was 47 KB.",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`). C saved locally, E:\n  HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`)—C saved locally, E:\n  HTTP 403 Access Denied",
                f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): A saved locally; C saved locally. A returned HTTP 403 errors prevented E.",
                f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): A saved locally; C saved locally. A returned HTTP 403 error can block E.",
                f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): A saved locally; C saved locally. A required login token blocks E.",
                f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): A saved locally; C saved locally. A required Google sign-in prevented E.",
                f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): A saved locally; C saved locally. A returned HTTP 403 responses caused E to fail.",
                f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): A saved locally; C saved locally. A required Google sign-in was triggered for E (HTTP 403).",
            )

            c_err_json.write_text(json.dumps({"error": {"code": 403, "message": "Access denied"}}), encoding="utf-8")
            e_ok_path.write_bytes(e_ok_bytes)
            for block in r15_ce_blocks:
                m1b.write_text(
                    block + "\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"C bleed on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Unexpected PASS when C=403 JSON on:\n{block}",
                )

            c_err_json.unlink()
            e_ok_path.unlink()
            c_ok_path.write_bytes(c_ok_bytes)
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            for block in r15_ce_blocks:
                m1b.write_text(
                    block + "\n"
                    f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"Lost E blocker on:\n{block}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"False C blocker on:\n{block}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_A_ID), msg=f"False A bleed on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "PASS",
                    msg=f"Unexpected FAIL on:\n{block}",
                )

            for line, exp_a, exp_c, exp_e in (
                (
                    f"- Sources A (`{SOURCE_A_ID}`) & C (`{SOURCE_C_ID}`): C saved locally. A returned HTTP 403 error can block fetch.",
                    False, False, False,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`) & C (`{SOURCE_C_ID}`): C saved locally. A returned a sign-in page (HTTP 403).",
                    True, False, False,
                ),
            ):
                m1b.write_text(line + "\n", encoding="utf-8")
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), exp_a, msg=line)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_C_ID), exp_c, msg=line)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_E_ID), exp_e, msg=line)

    def test_regression_r16_iter15_findings(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        bundle_hdr = "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
        with tempfile.TemporaryDirectory(prefix="ec_reg_r16_") as td:
            root = Path(td)

            # 1. Lean vacuous `: True` fail cases (F3 + Rev2 C.1: 2-arg app + smaller-indented body, bare `by` same-indent tactics)
            r16_vac_fail_cases = (
                (
                    "R16Let2ArgForallSmallerBodyTrue.lean",
                    "theorem vac :\n  let _ := Nat.add\n    0\n    1\n  ∀ _ : Nat,\n True := fun _ => trivial\n",
                ),
                (
                    "R16LetBareBySameIndentTacticsTrue.lean",
                    "theorem vac :\n  let _ : 0 = 0 :=\n    by\n    skip\n    rfl\n  True := trivial\n",
                ),
            )
            for fname, body in r16_vac_fail_cases:
                self.assertTrue(scan_native_decide_and_vacuous_true(body), msg=f"{fname} missed by vacuous scanner")
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 2. Lean bundler fail cases (F1-F4 + Rev2 C.1-C.2)
            r16_bundler_fail_cases = (
                (
                    "R16SuffBypDefeq0Add0.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle (0 + 0) := by\n  constructor\n  · first\n"
                    "    | suffices _ : 0 + 0 = 0 by\n        exact rfl\n      exact rfl\n"
                    "    | cases n with\n      | zero => rfl\n      | succ _ => rfl\n  · rfl\n",
                ),
                (
                    "R16SuffBypConjAndTrue.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle (0 + 0) := by\n  constructor\n  · first\n"
                    "    | suffices _ : (0 = 0 ∧ True) by\n        exact rfl\n      exact ⟨rfl, trivial⟩\n"
                    "    | cases n with\n      | zero => rfl\n      | succ _ => rfl\n  · rfl\n",
                ),
                (
                    "R16SimpCtorCaseArms.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  constructor\n  case p1 => rfl\n  case p2 => rfl\n",
                ),
                (
                    "R16SimpCtorNextArms.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  constructor\n  next => rfl\n  next => rfl\n",
                ),
                (
                    "R16SimpRefineCaseArms.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  refine ⟨?_, ?_⟩\n  case refine_1 => rfl\n  case refine_2 => rfl\n",
                ),
                (
                    "R16SimpRefineNextArms.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  refine ⟨?_, ?_⟩\n  next => rfl\n  next => rfl\n",
                ),
                (
                    "R16SimpTryParenSemi.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  try (constructor; all_goals rfl)\n",
                ),
                (
                    "R16SimpTryBraceSemi.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  try { constructor; all_goals rfl }\n",
                ),
                (
                    "R16SimpFocusParenSemi.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  focus (constructor; all_goals rfl)\n",
                ),
                (
                    "R16SimpAllGoalsTryParen.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  all_goals (try (constructor; all_goals rfl))\n",
                ),
                (
                    "R16SimpExactByRefineAllGoals.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (by refine ⟨?_, ?_⟩; all_goals rfl)\n",
                ),
                (
                    "R16SimpExactByRefineSemi.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (by refine ⟨?_, ?_⟩ <;> rfl)\n",
                ),
                (
                    "R16SimpExactByRefineMkAllGoals.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (by refine Bundle.mk ?_ ?_; all_goals rfl)\n",
                ),
                (
                    "R16SimpExactByRefineRflRfl.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (by refine ⟨?_, ?_⟩; rfl; rfl)\n",
                ),
                (
                    "R16SimpExactByRefineBullets.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (by\n    refine ⟨?_, ?_⟩\n    · rfl\n    · rfl)\n",
                ),
                (
                    "R16SimpExactByRefineBraceBullets.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (by\n    refine { p1 := ?_, p2 := ?_ }\n    · rfl\n    · rfl)\n",
                ),
                (
                    "R16SimpAtIdNamedArg.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact @id (α := Bundle 0) ⟨rfl, rfl⟩\n",
                ),
                (
                    "R16Let2ArgForallSmallerBodyBundler.lean",
                    bundle_hdr + "theorem bypass (n : Nat) :\n  let _ := Nat.add\n    0\n    1\n  ∀ _ : Nat,\n Bundle n := fun _ => ⟨rfl, Nat.add_zero n⟩\n",
                ),
                (
                    "R16LetStructPatShadow.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    let { fst := h, snd := k } := (0, 0)\n    exact (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
                (
                    "R16LetParenStructPatShadow.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    let ({ fst := h, snd := k }) := (0, 0)\n    exact (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
                (
                    "R16LetNestedStructPatShadow.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    let { fst := (h : Nat), snd := ⟨a, b⟩ } := (0, (0, 0))\n    exact (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
            )
            for fname, body in r16_bundler_fail_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertTrue(scan_parameterized_prop_bundlers(body), msg=f"{fname} missed by bundler scanner")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 3. Lean positive controls (F1-F4 + Rev2 C.1-C.2)
            r16_lean_pass_cases = (
                (
                    "R16PosSuffExactRflOnBundle.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  first\n"
                    "  | suffices _ : n = n by\n      exact rfl\n    exact ⟨rfl, Nat.add_zero n⟩\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R16PosTrySuffExactRflOnBundle.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  try\n"
                    "    suffices _ : n = n by\n      exact rfl\n    exact ⟨rfl, Nat.add_zero n⟩\n"
                    "  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R16PosSuffNotTrueContradiction.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  first\n"
                    "  | suffices _ : ¬ True by contradiction\n    trivial\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R16PosSuff1Plus1Eq0Done.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  first\n"
                    "  | (suffices _ : 1 + 1 = 0 by exact Eq.refl 2; done)\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R16PosSuffConjPlainRflFail.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle (0 + 0) := by\n  constructor\n  · first\n"
                    "    | suffices _ : (0 = 0 ∧ True) by\n        exact rfl\n      exact rfl\n"
                    "    | cases n with\n      | zero => exact rfl\n      | succ _ => exact rfl\n  · exact rfl\n",
                ),
                (
                    "R16PosSimpCtorCaseMyLem.lean",
                    bundle_hdr
                    + "theorem witness (n : Nat) : Bundle n := by\n  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    + "theorem myLem (k : Nat) : k = k := rfl\n"
                    + "theorem ok : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  constructor\n  case p1 => rfl\n  case p2 => exact myLem 0\n",
                ),
                (
                    "R16PosSimpRefineNextMyLem.lean",
                    bundle_hdr
                    + "theorem witness (n : Nat) : Bundle n := by\n  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    + "theorem myLem (k : Nat) : k = k := rfl\n"
                    + "theorem ok : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  refine ⟨?_, ?_⟩\n  next => rfl\n  next => exact myLem 0\n",
                ),
                (
                    "R16PosSimpExactByRefineMyLem.lean",
                    bundle_hdr
                    + "theorem witness (n : Nat) : Bundle n := by\n  cases n with\n  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
                    + "theorem myLem (k : Nat) : k = k := rfl\n"
                    + "theorem ok : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (by\n    refine ⟨?_, ?_⟩\n    · rfl\n    · exact myLem 0)\n",
                ),
                (
                    "R16PosLet2ArgForallSmallerBodyEq.lean",
                    "theorem ok :\n  let x := Nat.add\n    0\n    1\n  ∀ _ : Nat,\n x = 1 := fun _ => rfl\n",
                ),
                (
                    "R16PosLetBareBySameIndentEq.lean",
                    "theorem ok :\n  let _ : 0 = 0 :=\n    by\n    skip\n    rfl\n  0 = 0 := rfl\n",
                ),
                (
                    "R16PosLetStructPatOtherUsed.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    let { fst := k, snd := m } := (0, 0)\n"
                    "    exact (fun _ : k + m = k + m => (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl) rfl\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => rfl\n",
                ),
            )
            for fname, body in r16_lean_pass_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertEqual(scan_native_decide_and_vacuous_true(body), [], msg=f"{fname} false vacuous hit")
                self.assertEqual(scan_parameterized_prop_bundlers(body), [], msg=f"{fname} false bundler hit")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "PASS", msg=f"{fname} false-failed T1-LEAN-04: {res.summary}")

            # 4. T3-CONS-02 (F5 + Rev2 C.4 + Rev1 §D `?`/`!` idents)
            lean_dir = root / "lean" / "InfoGeometry" / "Test"
            lean_dir.mkdir(parents=True)
            t_mod = lean_dir / "TMod.lean"
            t_aud = lean_dir / "TModAudit.lean"
            t_env = root / "env_t16.json"
            t_arts = DiscoveredArtifacts([], [t_env], [], [], [], [t_env], [])

            def _set_ns16_case(mod_src: str, acc_thm: str, aud_src: str) -> str:
                t_mod.write_text(mod_src, encoding="utf-8")
                t_aud.write_text(aud_src, encoding="utf-8")
                t_env.write_text(
                    json.dumps(
                        {
                            "owner_search": {
                                "target_artifacts": [
                                    "lean/InfoGeometry/Test/TMod.lean",
                                    "lean/InfoGeometry/Test/TModAudit.lean",
                                ]
                            },
                            "formal_objects": {"lane_t": ["TMod.obj"]},
                            "acceptance_theorems": {"lane_t": [acc_thm]},
                        }
                    ),
                    encoding="utf-8",
                )
                tgts = [ResolvedTarget(t_mod, "lean/InfoGeometry/Test/TMod.lean", "InfoGeometry.Test.TMod", True)]
                return check_t3_cons_02_contracts_to_lean_declarations(
                    root, t_arts, tgts, require_all_envelope_targets=True
                ).status

            ns16_src = (
                "namespace Ns\n"
                "theorem a : 1 = 1 := rfl\n"
                "theorem b : 2 = 2 := rfl\n"
                "theorem ok : 3 = 3 := rfl\n"
                "theorem getElem?_ok : 4 = 4 := rfl\n"
                "theorem bang!_ok : 5 = 5 := rfl\n"
                "end Ns\n"
            )
            self.assertEqual(
                _set_ns16_case(
                    ns16_src,
                    "Ns.b",
                    "namespace Ms\naxiom b : 1 = 1\nend Ms\nopen Ms\nopen Ns hiding a\n  b\n#print axioms b\n",
                ),
                "FAIL",
            )
            self.assertEqual(
                _set_ns16_case(ns16_src, "Ns.ok", "theorem ok : 1 = 1 := rfl\nopen Ns hiding\n  a\n  ok\n#print axioms ok\n"),
                "FAIL",
            )
            self.assertEqual(
                _set_ns16_case(ns16_src, "Ns.ok", "export Ns\n  (ok)\n#print axioms ok\n"),
                "PASS",
            )
            self.assertEqual(
                _set_ns16_case(ns16_src, "Ns.b", "open Ns renaming a → a1\n  , b → b1\n#print axioms b1\n"),
                "PASS",
            )
            self.assertEqual(
                _set_ns16_case(ns16_src, "Ns.getElem?_ok", "open Ns\n#print axioms getElem?_ok\n"),
                "PASS",
            )
            self.assertEqual(
                _set_ns16_case(ns16_src, "Ns.bang!_ok", "open Ns\n#print axioms bang!_ok\n"),
                "PASS",
            )

            # 5. T3-CONS-05 (C3): non-local links (`#anchor`, `()`, `<>`, `ftp://`, `file:///`) must not hijack m_plain
            (root / "docs").mkdir(parents=True)
            samp = root / "docs" / "sample.md"
            other = root / "docs" / "other.md"
            samp.write_bytes(b"sample v16\n")
            other.write_bytes(b"other v16\n")
            samp_sha = hashlib.sha256(b"sample v16\n").hexdigest()
            other_sha = hashlib.sha256(b"other v16\n").hexdigest()
            qa_rep = root / "qa_report_r16.md"
            for md_line in (
                f"| [docs/other.md](#section-1) | docs/sample.md | `{samp_sha}` |\n",
                f"| [docs/other.md]() | docs/sample.md | `{samp_sha}` |\n",
                f"| [docs/other.md](<>) | docs/sample.md | `{samp_sha}` |\n",
                f"| [docs/other.md](ftp://example.com/x) | docs/sample.md | `{samp_sha}` |\n",
                f"| [docs/other.md](file:///tmp/x) | docs/sample.md | `{samp_sha}` |\n",
            ):
                qa_rep.write_text(md_line, encoding="utf-8")
                r_nonloc_ok = check_t3_cons_05_audit_report_hashes(
                    root, DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]), targets=[]
                )
                self.assertEqual(r_nonloc_ok.status, "PASS", msg=f"{md_line}: {r_nonloc_ok.summary}")
                self.assertIn("(1/1 files)", r_nonloc_ok.summary)

            qa_rep.write_text(f"| [docs/other.md](#section-1) | docs/sample.md | `{other_sha}` |\n", encoding="utf-8")
            r_nonloc_fail = check_t3_cons_05_audit_report_hashes(
                root, DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]), targets=[]
            )
            self.assertEqual(r_nonloc_fail.status, "FAIL", msg=r_nonloc_fail.summary)
            self.assertEqual(r_nonloc_fail.details.get("checked"), 1)

            # 6. Intake C1 & C2: unit & end-to-end T1-INTAKE-07 on Source-A coord/relativizer, R9 sibling-note bleed, & `, ` / ` - ` seps
            (root / "cached" / "drive_docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )
            m1b = root / "docs" / "M1B_R16.md"
            c_ok_bytes = b"Source C valid markdown R16\n"
            c_sha = hashlib.sha256(c_ok_bytes).hexdigest()
            e_ok_bytes = b"Source E valid markdown R16\n"
            e_sha = hashlib.sha256(e_ok_bytes).hexdigest()
            c_err_json = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.json"
            c_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            e_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.md"
            e_html = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"

            r16_e2e_c_unreported_blocks = (
                f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally; E saved locally. A returned HTTP 403 error and was blocked.",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally; E:\n  (C was 47 KB)\n  HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally; E:\n  HTTP 403 Access Denied\n  Note: C was 47 KB.\n  Retry returned HTTP 403.",
            )
            c_err_json.write_text(json.dumps({"error": {"code": 403, "message": "Access denied"}}), encoding="utf-8")
            e_ok_path.write_bytes(e_ok_bytes)
            for block in r16_e2e_c_unreported_blocks:
                m1b.write_text(
                    block + "\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"C bleed on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Silent false-PASS when C=403 JSON on:\n{block}",
                )

            c_err_json.unlink()
            e_ok_path.unlink()
            c_ok_path.write_bytes(c_ok_bytes)
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            r16_e_blocked_blocks = (
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally; E:\n  (C was 47 KB)\n  HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally; E:\n  HTTP 403 Access Denied\n  Note: C was 47 KB.\n  Retry returned HTTP 403.",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`), C saved locally, E:\n  HTTP 403 Access Denied\n  Note: C was 47 KB.",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`) - C saved locally, E:\n  HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`) (note: see below), C saved locally, E:\n  HTTP 403 Access Denied",
                f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally. A returned 403 wall blocked E.",
                f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally. A required Google verification blocked E.",
                f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): E returned login redirect.",
                f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): E requires a Google login.",
            )
            for block in r16_e_blocked_blocks:
                m1b.write_text(
                    block + "\n"
                    f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"Lost E blocker on:\n{block}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"False C blocker on:\n{block}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_A_ID), msg=f"False A bleed on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "PASS",
                    msg=f"Unexpected FAIL on:\n{block}",
                )

            for line, exp_a, exp_c, exp_e in (
                (
                    f"- Sources A (`{SOURCE_A_ID}`) & C (`{SOURCE_C_ID}`): C saved locally. A returned HTTP 403 error and was blocked.",
                    True, False, False,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`) & C (`{SOURCE_C_ID}`): C saved locally. A returned HTTP 403 page which blocks fetch.",
                    True, False, False,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`) & C (`{SOURCE_C_ID}`): C saved locally. A required credentials and was blocked.",
                    True, False, False,
                ),
                (
                    f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): C saved locally. A returned HTTP 403 error denied access.",
                    False, False, False,
                ),
            ):
                m1b.write_text(line + "\n", encoding="utf-8")
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), exp_a, msg=line)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_C_ID), exp_c, msg=line)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_E_ID), exp_e, msg=line)

    def test_regression_r17_iter16_findings(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        bundle_hdr = "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
        bundle2_hdr = "structure Bundle2 (n : Nat) : Prop where\n  p1 : 0 = 0\n  p2 : 0 + n = n\n"
        nest_hdr = bundle_hdr + "structure NestBundle (n : Nat) : Prop where\n  a : 0 = 0\n  b : Bundle n\n"
        wit_bundle = (
            "theorem witness_b (n : Nat) : Bundle n := by\n  cases n with\n"
            "  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
        )
        wit_bundle2 = (
            "theorem witness_b2 (n : Nat) : Bundle2 n := by\n  cases n with\n"
            "  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.zero_add _⟩\n"
        )
        wit_nest = (
            wit_bundle
            + "theorem witness_nb (n : Nat) : NestBundle n := by\n  cases n with\n"
            "  | zero => exact ⟨rfl, rfl, rfl⟩\n  | succ _ => exact ⟨rfl, rfl, Nat.add_zero _⟩\n"
        )
        with tempfile.TemporaryDirectory(prefix="ec_reg_r17_") as td:
            root = Path(td)

            # 1. Lean bundler FAIL cases (F1 ADV7-ADV9 + Rev2 C.3, F2 ADV11-ADV22, F3 ADV23-ADV25)
            r17_bundler_fail_cases = (
                (
                    "R17SuffBypIffRfl.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle (0 + 0) := by\n  first\n"
                    "  | suffices _ : (0 = 0 ↔ 0 = 0) by\n      exact ⟨rfl, rfl⟩\n    exact Iff.rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R17SuffBypNAdd0.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle (0 + 0) := by\n  first\n"
                    "  | suffices _ : n + 0 = n by\n      exact ⟨rfl, rfl⟩\n    rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R17SuffBypAuxCases.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle (0 + 0) := by\n  first\n"
                    "  | suffices h : 0 + n = n by\n      exact ⟨rfl, rfl⟩\n    cases n <;> simp [Nat.zero_add]\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R17RefineAtMkSuffices.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle (0 + 0) := by\n  refine @Bundle.mk _ ?_ ?_\n  · first\n"
                    "    | suffices _ : 0 + 0 = 0 by\n        exact rfl\n      exact rfl\n"
                    "    | cases n with\n      | zero => rfl\n      | succ _ => rfl\n  · rfl\n",
                ),
                (
                    "R17RefineParenAngleSuffices.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle (0 + 0) := by\n  refine (⟨?_, ?_⟩)\n  · first\n"
                    "    | suffices _ : 0 + 0 = 0 by\n        exact rfl\n      exact rfl\n"
                    "    | cases n with\n      | zero => rfl\n      | succ _ => rfl\n  · rfl\n",
                ),
                (
                    "R17SimpCtorCasePrimeArms.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n"
                    "  constructor\n  case' p1 => rfl\n  case' p2 => rfl\n",
                ),
                (
                    "R17SimpExactByCasePrimeArms.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n"
                    "  exact (by\n    constructor\n    case' p1 => rfl\n    case' p2 => rfl)\n",
                ),
                (
                    "R17SimpRefineNamedHoles.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n"
                    "  refine ⟨?a, ?b⟩\n  · rfl\n  · rfl\n",
                ),
                (
                    "R17SimpRefineNamedHolesCase.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n"
                    "  refine ⟨?a, ?b⟩\n  case a => rfl\n  case b => rfl\n",
                ),
                (
                    "R17SimpRefineStructNamedHoles.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n"
                    "  refine { p1 := ?a, p2 := ?b }\n  · rfl\n  · rfl\n",
                ),
                (
                    "R17SimpExactByRefineNamed.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n"
                    "  exact (by refine ⟨?a, ?b⟩ <;> rfl)\n",
                ),
                (
                    "R17SimpTryParenNl.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n"
                    "  try (\n    constructor\n    · rfl\n    · rfl)\n",
                ),
                (
                    "R17SimpAtBundleMk0.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact @Bundle.mk 0 rfl rfl\n",
                ),
                (
                    "R17SimpBundleMkMlNamed.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n"
                    "  exact Bundle.mk\n    (p1 := rfl)\n    (p2 := rfl)\n",
                ),
                (
                    "R17SimpBundleMkMlEqRefl.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n"
                    "  exact Bundle.mk\n    (Eq.refl 0)\n    (Eq.refl 0)\n",
                ),
                (
                    "R17LetStructPatWildcardShadow.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    let { fst := h, .. } := (0, 0)\n"
                    "    exact (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
                (
                    "R17LetStructPatPunningShadow.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  suffices fst : 0 = 0 by\n"
                    "    let { fst, snd } := (0, 0)\n"
                    "    exact (fun _ : fst + snd = fst + snd => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
                (
                    "R17LetAtStructPatShadow.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    let x@{ fst := h, snd := k } := (0, 0)\n"
                    "    exact (fun _ : x.1 + h + k = x.1 + h + k => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
            )
            for fname, body in r17_bundler_fail_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertTrue(scan_parameterized_prop_bundlers(body), msg=f"{fname} missed by bundler scanner")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 2. Lean positive controls (F1 ADV1-ADV6 + Rev2 C.2 + ADV8 0+n!=n + F2 @T.mk real-lemma control + F3 non-shadow control)
            r17_lean_pass_cases = (
                (
                    "R17PosCtorNonRflField.lean",
                    bundle2_hdr
                    + wit_bundle2
                    + "theorem ok (n : Nat) : Bundle2 n := by\n  constructor\n  · rfl\n  · first\n"
                    "    | suffices _ : n = n by\n        exact rfl\n      exact Nat.zero_add n\n"
                    "    | cases n with\n      | zero => rfl\n      | succ _ => simp [Nat.zero_add]\n",
                ),
                (
                    "R17PosCtorNestedStructField.lean",
                    nest_hdr
                    + wit_nest
                    + "theorem ok (n : Nat) : NestBundle n := by\n  constructor\n  · rfl\n  · first\n"
                    "    | suffices _ : n = n by\n        exact rfl\n      exact ⟨rfl, Nat.add_zero n⟩\n"
                    "    | cases n with\n      | zero => exact ⟨rfl, rfl⟩\n      | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R17PosCtorExactTrivialOnEq.lean",
                    bundle_hdr
                    + wit_bundle
                    + "theorem ok (n : Nat) : Bundle n := by\n  constructor\n  · first\n"
                    "    | suffices _ : n = n by\n        exact trivial\n      exact rfl\n"
                    "    | cases n with\n      | zero => rfl\n      | succ _ => rfl\n  · exact Nat.add_zero n\n",
                ),
                (
                    "R17PosSuffAuxRflOnTrue.lean",
                    bundle_hdr
                    + wit_bundle
                    + "theorem ok (n : Nat) : Bundle n := by\n  first\n"
                    "  | suffices _ : True by\n      exact ⟨rfl, Nat.add_zero n⟩\n    rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R17PosSuffAuxTrivialOnConj.lean",
                    bundle_hdr
                    + wit_bundle
                    + "theorem ok (n : Nat) : Bundle n := by\n  first\n"
                    "  | suffices _ : (0 = 0 ∧ 0 = 0) by\n      exact ⟨rfl, Nat.add_zero n⟩\n    trivial\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R17PosSuffIntSub0Minus1.lean",
                    bundle_hdr
                    + wit_bundle
                    + "theorem ok (n : Nat) : Bundle n := by\n  first\n"
                    "  | suffices _ : (0 - 1 : Int) = 0 by\n      exact ⟨rfl, Nat.add_zero n⟩\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R17PosSuffIntSub1Minus2.lean",
                    bundle_hdr
                    + wit_bundle
                    + "theorem ok (n : Nat) : Bundle n := by\n  first\n"
                    "  | suffices _ : (1 - 2 : Int) = 0 by\n      exact ⟨rfl, Nat.add_zero n⟩\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R17PosSuff0AddNNotDefeq.lean",
                    bundle_hdr
                    + wit_bundle
                    + "theorem ok (n : Nat) : Bundle n := by\n  first\n"
                    "  | suffices _ : 0 + n = n by\n      exact ⟨rfl, Nat.add_zero n⟩\n    rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R17PosAtMkRealLemma.lean",
                    bundle_hdr
                    + wit_bundle
                    + "theorem myLem (k : Nat) : k = k := rfl\n"
                    + "theorem ok : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact @Bundle.mk 0 (myLem 0) rfl\n",
                ),
                (
                    "R17PosLetStructPunningOtherUsed.lean",
                    bundle_hdr
                    + wit_bundle
                    + "theorem ok (n : Nat) : Bundle n := by\n  suffices h : 0 = 0 by\n"
                    "    let { fst, .. } := (0, 0)\n"
                    "    exact (fun _ : fst = fst => (fun _ : h = h => ⟨rfl, Nat.add_zero n⟩) rfl) rfl\n"
                    "  cases n with\n  | zero => rfl\n  | succ _ => rfl\n",
                ),
            )
            for fname, body in r17_lean_pass_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertEqual(scan_native_decide_and_vacuous_true(body), [], msg=f"{fname} false vacuous hit")
                self.assertEqual(scan_parameterized_prop_bundlers(body), [], msg=f"{fname} false bundler hit")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "PASS", msg=f"{fname} false-failed T1-LEAN-04: {res.summary}")

            # 3. T3-CONS-02 (F4: multiline open namespaces, guillemet `.` in hiding, `in` at open_indent & statement-order hiding)
            lean_dir = root / "lean" / "InfoGeometry" / "Test"
            lean_dir.mkdir(parents=True)
            t_mod = lean_dir / "TMod.lean"
            t_aud = lean_dir / "TModAudit.lean"
            t_env = root / "env_t17.json"
            t_arts = DiscoveredArtifacts([], [t_env], [], [], [], [t_env], [])

            def _set_ns17_case(mod_src: str, acc_thm: str, aud_src: str) -> str:
                t_mod.write_text(mod_src, encoding="utf-8")
                t_aud.write_text(aud_src, encoding="utf-8")
                t_env.write_text(
                    json.dumps(
                        {
                            "owner_search": {
                                "target_artifacts": [
                                    "lean/InfoGeometry/Test/TMod.lean",
                                    "lean/InfoGeometry/Test/TModAudit.lean",
                                ]
                            },
                            "formal_objects": {"lane_t": ["TMod.obj"]},
                            "acceptance_theorems": {"lane_t": [acc_thm]},
                        }
                    ),
                    encoding="utf-8",
                )
                tgts = [ResolvedTarget(t_mod, "lean/InfoGeometry/Test/TMod.lean", "InfoGeometry.Test.TMod", True)]
                return check_t3_cons_02_contracts_to_lean_declarations(
                    root, t_arts, tgts, require_all_envelope_targets=True
                ).status

            self.assertEqual(
                _set_ns17_case(
                    "namespace Ns\ntheorem a : 1 = 1 := rfl\nend Ns\nnamespace Ms\ntheorem ok : 1 = 1 := rfl\nend Ms\n",
                    "Ms.ok",
                    "open Ns\n  Ms\n#print axioms ok\n",
                ),
                "PASS",
            )
            self.assertEqual(
                _set_ns17_case(
                    "namespace Ns\ntheorem «a.b» : 1 = 1 := rfl\ntheorem ok : 1 = 1 := rfl\nend Ns\n",
                    "Ns.«a.b»",
                    "namespace Ms\naxiom «a.b» : 1 = 1\nend Ms\nopen Ms\nopen Ns hiding ok\n  «a.b»\n#print axioms «a.b»\n",
                ),
                "FAIL",
            )
            self.assertEqual(
                _set_ns17_case(
                    "namespace Ns\ntheorem ok : 1 = 1 := rfl\nend Ns\n",
                    "Ns.ok",
                    "namespace Ms\naxiom ok : 1 = 1\nend Ms\nopen Ms\nopen Ns\nopen Ns hiding\n  ok\nin\n#print axioms ok\n",
                ),
                "FAIL",
            )
            self.assertEqual(
                _set_ns17_case(
                    "namespace Ns\ntheorem ok : 1 = 1 := rfl\nend Ns\n",
                    "Ns.ok",
                    "namespace Ms\naxiom ok : 1 = 1\nend Ms\nopen Ms\nopen Ns hiding\n  ok\nin\n#print axioms ok\n",
                ),
                "FAIL",
            )

            # 4. T3-CONS-05 (C3: protocol-relative `//example.com/x` must be treated as non-local)
            (root / "docs").mkdir(parents=True)
            samp = root / "docs" / "sample.md"
            other = root / "docs" / "other.md"
            samp.write_bytes(b"sample v17\n")
            other.write_bytes(b"other v17\n")
            samp_sha = hashlib.sha256(b"sample v17\n").hexdigest()
            other_sha = hashlib.sha256(b"other v17\n").hexdigest()
            qa_rep = root / "qa_report_r17.md"
            qa_rep.write_text(f"| [docs/other.md](//example.com/x) | docs/sample.md | `{samp_sha}` |\n", encoding="utf-8")
            r_proto_ok = check_t3_cons_05_audit_report_hashes(
                root, DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]), targets=[]
            )
            self.assertEqual(r_proto_ok.status, "PASS", msg=r_proto_ok.summary)
            self.assertIn("(1/1 files)", r_proto_ok.summary)
            qa_rep.write_text(f"| [docs/other.md](//example.com/x) | docs/sample.md | `{other_sha}` |\n", encoding="utf-8")
            r_proto_fail = check_t3_cons_05_audit_report_hashes(
                root, DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]), targets=[]
            )
            self.assertEqual(r_proto_fail.status, "FAIL", msg=r_proto_fail.summary)
            self.assertEqual(r_proto_fail.details.get("checked"), 1)

            # 5. Intake C1, C2, & Rev2 C.1: unit + end-to-end T1-INTAKE-07 on subordinators/comma/dash/pipe/rel-clause, prefix-colon, Oxford `&`, bare 3+-src comma, and `mentions_self` non-bullet
            (root / "cached" / "drive_docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )
            m1b = root / "docs" / "M1B_R17.md"
            c_ok_bytes = b"Source C valid markdown R17\n"
            c_sha = hashlib.sha256(c_ok_bytes).hexdigest()
            e_ok_bytes = b"Source E valid markdown R17\n"
            e_sha = hashlib.sha256(e_ok_bytes).hexdigest()
            c_err_json = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.json"
            c_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            e_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.md"
            e_html = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"

            r17_e2e_e_unreported_blocks = (
                f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): A returned HTTP 403 error because login was required.",
                f"- Note: Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied",
            )
            c_ok_path.write_bytes(c_ok_bytes)
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            for block in r17_e2e_e_unreported_blocks:
                m1b.write_text(
                    block
                    + "\n"
                    + f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"E bleed on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Silent false-PASS when E=403 HTML on:\n{block}",
                )

            c_ok_path.unlink()
            e_html.unlink()
            c_err_json.write_text(json.dumps({"error": {"code": 403, "message": "Access denied"}}), encoding="utf-8")
            e_ok_path.write_bytes(e_ok_bytes)
            r17_e2e_c_blocked_blocks = (
                f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`), & E (`{SOURCE_E_ID}`):\n  C returned HTTP 403 Access Denied.\n  E saved locally.",
                f"- Status: Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`):\n  C returned HTTP 403 Access Denied.\n  E saved locally.",
                f"- Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  C returned HTTP 403.\n  D saved locally.\n  E saved locally.",
                f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`, note):\n  C returned HTTP 403.\n  Note: C was 47 KB.\n  E saved locally.",
            )
            for block in r17_e2e_c_blocked_blocks:
                m1b.write_text(
                    block
                    + "\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"Lost C blocker on:\n{block}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"False E blocker on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "PASS",
                    msg=f"Unexpected FAIL on:\n{block}",
                )

            c_err_json.unlink()
            e_ok_path.unlink()
            c_err_json.write_text(json.dumps({"error": {"code": 403, "message": "Access denied"}}), encoding="utf-8")
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            b7_block = (
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): see notes; E:\n"
                "  C returned HTTP 403 Access Denied.\n"
                "  E: HTTP 403 Access Denied"
            )
            m1b.write_text(
                b7_block + "\n" + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n" + claims_tail,
                encoding="utf-8",
            )
            self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg="B7 lost C")
            self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg="B7 lost E")
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "PASS",
                msg="B7 unexpected FAIL",
            )

            for text, exp_a, exp_c, exp_e in (
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): A returned HTTP 403 error, blocked by Drive.", True, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): A returned HTTP 403 error because login was required.", True, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): A returned HTTP 403 error when fetch was attempted.", True, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): A returned HTTP 403 error — access was denied.", True, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): E saved locally | A returned HTTP 403.", True, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): A returned HTTP 403 error that occurred yesterday was logged.", False, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`), C (`{SOURCE_C_ID}`), & E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", True, True, True),
                (f"- Status: Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False, True, True),
                (f"- Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), & E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False, True, True),
            ):
                m1b.write_text(text + "\n", encoding="utf-8")
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), exp_a, msg=text)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_C_ID), exp_c, msg=text)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_E_ID), exp_e, msg=text)

    def test_regression_r18_iter17_findings(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        bundle_hdr = "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
        bundle2_hdr = "structure Bundle2 (n : Nat) : Prop where\n  p1 : 0 = 0\n  p2 : 0 + n = n\n"
        int_hdr = "structure IntBundle (m : Int) : Prop where\n  p1 : m = m\n  p2 : m + 0 = m\n"
        wit_bundle = (
            "theorem witness_b (n : Nat) : Bundle n := by\n  cases n with\n"
            "  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
        )
        wit_bundle2 = (
            "theorem witness_b2 (n : Nat) : Bundle2 n := by\n  cases n with\n"
            "  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.zero_add _⟩\n"
        )
        wit_int0 = "theorem wit_i0 : IntBundle 0 := by cases (0 : Int) <;> exact ⟨rfl, Int.add_zero _⟩\n"

        with tempfile.TemporaryDirectory(prefix="ec_reg_r18_") as td:
            root = Path(td)

            # 1. Lean bundler FAIL cases (F1 S10/S11, F2 C1-C3d, F3 P3/P3b, Rev2 C.1/C.3)
            r18_bundler_fail_cases = (
                (
                    "R18SuffNatAdd0Plus0.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle (0 + 0) := by\n  first\n"
                    "  | suffices _ : n + (0 + 0) = n by\n      exact ⟨rfl, rfl⟩\n    rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R18SuffNatSub0.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle (0 + 0) := by\n  first\n"
                    "  | suffices _ : n - 0 = n by\n      exact ⟨rfl, rfl⟩\n    rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R18SuffAscribedNatAdd0.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle (0 + 0) := by\n  first\n"
                    "  | suffices _ : (n : Nat) + 0 = n by\n      exact ⟨rfl, rfl⟩\n    rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R18SuffIffTrivial.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle (0 + 0) := by\n  first\n"
                    "  | suffices _ : (0 = 0 ↔ 0 = 0) by\n      exact ⟨rfl, rfl⟩\n    trivial\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R18RefineMkMl.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n"
                    "  refine Bundle.mk\n    ?_\n    ?_\n  · rfl\n  · rfl\n",
                ),
                (
                    "R18RefineMkMlNamed.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n"
                    "  refine Bundle.mk\n    (p1 := ?_)\n    (p2 := ?_)\n  · rfl\n  · rfl\n",
                ),
                (
                    "R18ExactAngleNoSpace.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact⟨rfl, rfl⟩\n",
                ),
                (
                    "R18RefineAngleNoSpace.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  refine⟨?_, ?_⟩\n  · rfl\n  · rfl\n",
                ),
                (
                    "R18ExactBraceNoSpace.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact{ p1 := rfl, p2 := rfl }\n",
                ),
                (
                    "R18RefineBraceNoSpace.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  refine{ p1 := ?_, p2 := ?_ }\n  · rfl\n  · rfl\n",
                ),
                (
                    "R18LetStructMl.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  suffices snd : 0 = 0 by\n"
                    "    let {\n      fst := h,\n      snd\n    } := (0, 0)\n"
                    "    exact (fun _ : h + snd = h + snd => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
                (
                    "R18LetStructMlAssign.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle n := by\n  suffices k : 0 = 0 by\n"
                    "    let {\n      fst := h,\n      snd := k\n    } := (0, 0)\n"
                    "    exact (fun _ : h + k = h + k => ⟨rfl, Nat.add_zero n⟩) rfl\n  cases n <;> rfl\n",
                ),
                (
                    "R18AtMkNamedParam.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact @Bundle.mk (n := 0) rfl rfl\n",
                ),
                (
                    "R18MkNamedParam.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact Bundle.mk (n := 0) rfl rfl\n",
                ),
                (
                    "R18RefineAtMkNamedParam.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  refine @Bundle.mk (n := 0) ?_ rfl\n  · rfl\n",
                ),
            )
            for fname, body in r18_bundler_fail_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertTrue(scan_parameterized_prop_bundlers(body), msg=f"{fname} missed by bundler scanner")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 2. Lean positive controls (F1 S1-S9 + S13 + Rev2 C.1/C.2)
            r18_lean_pass_cases = (
                (
                    "R18PosExactByRfl.lean",
                    bundle_hdr
                    + wit_bundle
                    + "theorem ok (n : Nat) : Bundle n := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact (by rfl)\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R18PosExactIdRfl.lean",
                    bundle_hdr
                    + wit_bundle
                    + "theorem ok (n : Nat) : Bundle n := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact (id rfl)\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R18PosExactAtEqRefl.lean",
                    bundle_hdr
                    + wit_bundle
                    + "theorem ok (n : Nat) : Bundle n := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact @Eq.refl _ _\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R18PosArm1StructMismatch.lean",
                    bundle2_hdr
                    + wit_bundle2
                    + "theorem ok (n : Nat) : Bundle2 n := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨rfl, rfl⟩\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.zero_add _⟩\n",
                ),
                (
                    "R18PosCtorNoBulletPipe.lean",
                    bundle2_hdr
                    + wit_bundle2
                    + "theorem ok (n : Nat) : Bundle2 n := by\n  constructor\n  rfl\n  first\n"
                    "    | suffices _ : n = n by\n        exact rfl\n      exact Nat.zero_add n\n"
                    "    | cases n with\n      | zero => rfl\n      | succ _ => simp [Nat.zero_add]\n",
                ),
                (
                    "R18PosCtorNoBulletInlinePipe.lean",
                    bundle2_hdr
                    + wit_bundle2
                    + "theorem ok (n : Nat) : Bundle2 n := by\n  constructor\n  rfl\n"
                    "  first | suffices _ : n = n by exact rfl; exact Nat.zero_add n | cases n with | zero => rfl | succ _ => simp [Nat.zero_add]\n",
                ),
                (
                    "R18PosRefineReordStruct.lean",
                    bundle2_hdr
                    + wit_bundle2
                    + "theorem ok (n : Nat) : Bundle2 n := by\n  refine { p2 := ?_, p1 := ?_ }\n  · rfl\n  · first\n"
                    "    | suffices _ : n = n by\n        exact rfl\n      exact Nat.zero_add n\n"
                    "    | cases n with\n      | zero => rfl\n      | succ _ => simp [Nat.zero_add]\n",
                ),
                (
                    "R18PosAuxRefineRflTrue.lean",
                    bundle_hdr
                    + wit_bundle
                    + "theorem ok (n : Nat) : Bundle n := by\n  first\n"
                    "  | suffices _ : True by\n      exact ⟨rfl, Nat.add_zero n⟩\n    refine rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R18PosAuxConjMismatch.lean",
                    bundle_hdr
                    + wit_bundle
                    + "theorem ok (n : Nat) : Bundle n := by\n  first\n"
                    "  | suffices _ : (0 = 0 ∧ 0 = 0) by\n      exact ⟨rfl, Nat.add_zero n⟩\n    exact ⟨rfl, True.intro⟩\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R18PosSectionVariableScope.lean",
                    int_hdr
                    + wit_int0
                    + "section\nvariable (n : Nat)\nend\ntheorem ok (n : Int) : IntBundle n := by\n  first\n"
                    "  | suffices _ : n + 0 = n by\n      exact ⟨rfl, Int.add_zero n⟩\n    rfl\n"
                    "  | cases n with\n    | ofNat k => exact ⟨rfl, Int.add_zero _⟩\n    | negSucc k => exact ⟨rfl, Int.add_zero _⟩\n",
                ),
                (
                    "R18PosForallShadowInt.lean",
                    int_hdr
                    + wit_int0
                    + "theorem ok (n : Nat) : ∀ n : Int, IntBundle n := by\n  intro n\n  first\n"
                    "  | suffices _ : n + 0 = n by\n      exact ⟨rfl, Int.add_zero n⟩\n    exact rfl\n"
                    "  | cases n with\n    | ofNat k => exact ⟨rfl, Int.add_zero _⟩\n    | negSucc k => exact ⟨rfl, Int.add_zero _⟩\n",
                ),
                (
                    "R18PosAtMkNamedParamRealLemma.lean",
                    bundle_hdr
                    + wit_bundle
                    + "theorem myLem (k : Nat) : k = k := rfl\n"
                    + "theorem ok : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact @Bundle.mk (n := 0) (myLem 0) rfl\n",
                ),
            )
            for fname, body in r18_lean_pass_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertEqual(scan_native_decide_and_vacuous_true(body), [], msg=f"{fname} false vacuous hit")
                self.assertEqual(scan_parameterized_prop_bundlers(body), [], msg=f"{fname} false bundler hit")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "PASS", msg=f"{fname} false-failed T1-LEAN-04: {res.summary}")

            # 3. T3-CONS-02 (F4: indented prime-containing namespaces/identifiers in open / open hiding)
            lean_dir = root / "lean" / "InfoGeometry" / "Test"
            lean_dir.mkdir(parents=True)
            t_mod = lean_dir / "TMod.lean"
            t_aud = lean_dir / "TModAudit.lean"
            t_env = root / "env_t18.json"
            t_arts = DiscoveredArtifacts([], [t_env], [], [], [], [t_env], [])

            def _set_ns18_case(mod_src: str, acc_thm: str, aud_src: str) -> str:
                t_mod.write_text(mod_src, encoding="utf-8")
                t_aud.write_text(aud_src, encoding="utf-8")
                t_env.write_text(
                    json.dumps(
                        {
                            "owner_search": {
                                "target_artifacts": [
                                    "lean/InfoGeometry/Test/TMod.lean",
                                    "lean/InfoGeometry/Test/TModAudit.lean",
                                ]
                            },
                            "formal_objects": {"lane_t": ["TMod.obj"]},
                            "acceptance_theorems": {"lane_t": [acc_thm]},
                        }
                    ),
                    encoding="utf-8",
                )
                tgts = [ResolvedTarget(t_mod, "lean/InfoGeometry/Test/TMod.lean", "InfoGeometry.Test.TMod", True)]
                return check_t3_cons_02_contracts_to_lean_declarations(
                    root, t_arts, tgts, require_all_envelope_targets=True
                ).status

            self.assertEqual(
                _set_ns18_case(
                    "namespace Ns\ntheorem a : 1 = 1 := rfl\nend Ns\nnamespace Ms'\ntheorem ok : 1 = 1 := rfl\nend Ms'\n",
                    "Ms'.ok",
                    "open Ns\n  Ms'\n#print axioms ok\n",
                ),
                "PASS",
            )
            self.assertEqual(
                _set_ns18_case(
                    "namespace Ns\ntheorem ok : 1 = 1 := rfl\ntheorem ok' : 1 = 1 := rfl\nend Ns\n",
                    "Ns.ok'",
                    "namespace Ms\naxiom ok' : 1 = 1\nend Ms\nopen Ms\nopen Ns hiding ok\n  ok'\n#print axioms ok'\n",
                ),
                "FAIL",
            )

            # 4. T3-CONS-05 (C4: bare protocol-relative `//example.com/<64hex>` masked cleanly)
            (root / "docs").mkdir(parents=True)
            samp = root / "docs" / "sample.md"
            samp.write_bytes(b"sample v18\n")
            samp_sha = hashlib.sha256(b"sample v18\n").hexdigest()
            other_sha = hashlib.sha256(b"other v18\n").hexdigest()
            qa_rep = root / "qa_report_r18.md"
            qa_rep.write_text(f"| //example.com/{other_sha} | docs/sample.md | `{samp_sha}` |\n", encoding="utf-8")
            r_bare_ok = check_t3_cons_05_audit_report_hashes(
                root, DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]), targets=[]
            )
            self.assertEqual(r_bare_ok.status, "PASS", msg=r_bare_ok.summary)
            self.assertIn("(1/1 files)", r_bare_ok.summary)
            qa_rep.write_text(f"| //example.com/{samp_sha} | docs/sample.md | `{other_sha}` |\n", encoding="utf-8")
            r_bare_fail = check_t3_cons_05_audit_report_hashes(
                root, DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]), targets=[]
            )
            self.assertEqual(r_bare_fail.status, "FAIL", msg=r_bare_fail.summary)
            self.assertEqual(r_bare_fail.details.get("checked"), 1)

            # 5. Intake C1, C2, C3 & Auditor §3: unit + end-to-end T1-INTAKE-07
            (root / "cached" / "drive_docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )
            m1b = root / "docs" / "M1B_R18.md"
            c_ok_bytes = b"Source C valid markdown R18\n"
            c_sha = hashlib.sha256(c_ok_bytes).hexdigest()
            e_ok_bytes = b"Source E valid markdown R18\n"
            e_sha = hashlib.sha256(e_ok_bytes).hexdigest()
            c_err_json = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.json"
            c_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            e_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.md"
            e_html = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"

            # 5a. 6 E=403_html unreported cases MUST FAIL T1-INTAKE-07 (no bleed from A or C)
            c_ok_path.write_bytes(c_ok_bytes)
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            for block in (
                f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`):\n  A returned HTTP 403 error that was silently blocked.",
                f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Per log, A returned HTTP 403 error that was silently blocked.",
                f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`):\n  A returned HTTP 403 error (access was denied).",
                f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`):\n  A returned HTTP 403 error, so login failed.",
                f"- Audit of A (`{SOURCE_A_ID}`): Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied",
                f"- Note (see Source A): Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied",
            ):
                m1b.write_text(
                    block
                    + "\n"
                    + f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"E bleed on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Silent false-PASS when E=403 HTML on:\n{block}",
                )

            # 5b. C=403_html unreported with `- Sources C & E, E:` MUST FAIL T1-INTAKE-07 (E=ok)
            c_ok_path.unlink()
            e_html.unlink()
            c_err_json.write_text(json.dumps({"error": {"code": 403, "message": "Access denied"}}), encoding="utf-8")
            e_ok_path.write_bytes(e_ok_bytes)
            # Invert: C is unreported 403_html, E is ok
            c_err_json.unlink()
            c_html = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.html"
            c_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            comma_bare_e = f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`), E:\n  HTTP 403 Access Denied"
            m1b.write_text(
                comma_bare_e
                + "\n"
                + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                + f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg="C bleed on comma bare E")
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "FAIL",
                msg="Silent false-PASS when C=403 HTML on comma bare E",
            )

            # 5c. C3 positive controls: `; E:`, `: fetch status:`, non-bullet indented `C download attempt:`, and `Note: Sources C & E: ...; E:`
            c_html.unlink()
            e_ok_path.unlink()
            c_ok_path.write_bytes(c_ok_bytes)
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            for block in (
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`); E:\n  HTTP 403 Access Denied",
                f"- Note: Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): see notes; E:\n  HTTP 403 Access Denied",
            ):
                m1b.write_text(
                    block
                    + "\n"
                    + f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"Lost E on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "PASS",
                    msg=f"False FAIL on:\n{block}",
                )

            c_ok_path.unlink()
            c_err_json.write_text(json.dumps({"error": {"code": 403, "message": "Access denied"}}), encoding="utf-8")
            for block in (
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): fetch status:\n  HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): see notes; E:\n  C download attempt:\n    HTTP 403 Access Denied\n  E: HTTP 403 Access Denied",
            ):
                m1b.write_text(
                    block
                    + "\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"Lost C on:\n{block}")
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"Lost E on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "PASS",
                    msg=f"False FAIL on:\n{block}",
                )

            # 5d. Unit controls for nested subordinate clauses inside relative clauses & `arrived`
            for text, exp_a, exp_c, exp_e in (
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): A returned HTTP 403 error that happened because login failed was logged.", False, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): A returned HTTP 403 error that happened because login failed.", True, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): A returned 403 modal that arrived earlier was logged.", False, False, False),
            ):
                m1b.write_text(text + "\n", encoding="utf-8")
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), exp_a, msg=text)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_C_ID), exp_c, msg=text)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_E_ID), exp_e, msg=text)

    def test_regression_r19_iter18_findings(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        bundle_hdr = "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
        bundle2_hdr = "structure Bundle2 (n : Nat) : Prop where\n  p1 : 0 = 0\n  p2 : 0 + n = n\n"
        bundle1_hdr = "structure Bundle1 (n : Nat) : Prop where\n  p1 : 1 = 1\n  p2 : 0 + n = n\n"
        bundle_iff_hdr = "structure BundleIff2 (n : Nat) : Prop where\n  p1 : 0 = 0 ↔ 0 = 0\n  p2 : 0 + n = n\n"
        iff_wrap_hdr = "structure IffWrap (n : Nat) : Prop where\n  h1 : 0 = 0 ↔ 0 + n = n\n  h2 : 0 = 0\n"
        outer_hdr = bundle_hdr + "structure Outer (n : Nat) : Prop where\n  w : Bundle n\n  p3 : n + 0 = n\n"
        int_hdr = "structure IntBundle (m : Int) : Prop where\n  p1 : m = m\n  p2 : m + 0 = m\n"
        wit_bundle = (
            "theorem witness_b (n : Nat) : Bundle n := by\n  cases n with\n"
            "  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
        )
        wit_bundle2 = (
            "theorem witness_b2 (n : Nat) : Bundle2 n := by\n  cases n with\n"
            "  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.zero_add _⟩\n"
        )
        wit_bundle1 = (
            "theorem witness_b1 (n : Nat) : Bundle1 n := by\n  cases n with\n"
            "  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.zero_add _⟩\n"
        )
        wit_iff2 = (
            "theorem witness_bi (n : Nat) : BundleIff2 n := by\n  cases n with\n"
            "  | zero => exact ⟨Iff.rfl, rfl⟩\n  | succ _ => exact ⟨Iff.rfl, Nat.zero_add _⟩\n"
        )
        wit_iff_wrap = (
            "theorem witness_iw (n : Nat) : IffWrap n := by\n  cases n with\n"
            "  | zero => exact ⟨Iff.rfl, rfl⟩\n  | succ _ => exact ⟨⟨fun _ => Nat.zero_add _, fun _ => rfl⟩, rfl⟩\n"
        )
        wit_outer = (
            "theorem witness_o (n : Nat) : Outer n := by\n  cases n with\n"
            "  | zero => exact ⟨⟨rfl, rfl⟩, rfl⟩\n  | succ _ => exact ⟨⟨rfl, Nat.add_zero _⟩, Nat.add_zero _⟩\n"
        )
        wit_int0 = "theorem wit_i0 : IntBundle 0 := by cases (0 : Int) <;> exact ⟨rfl, Int.add_zero _⟩\n"

        with tempfile.TemporaryDirectory(prefix="ec_reg_r19_") as td:
            root = Path(td)

            # 1. Lean bundler FAIL cases (Ch1 #1 paren heads, #2 Outer.mk { ... } ?_, Rev2 #4 inner ascription, #4 var in / intro Nat)
            r19_bundler_fail_cases = (
                (
                    "R19ParenHeadMk.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (Bundle.mk) rfl rfl\n",
                ),
                (
                    "R19ParenHeadAtMkParam.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (@Bundle.mk (n := 0)) rfl rfl\n",
                ),
                (
                    "R19ParenHeadMkParam.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (Bundle.mk (n := 0)) rfl rfl\n",
                ),
                (
                    "R19ParenRefineHeadMk.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n"
                    "  refine (Bundle.mk) ?_ ?_\n  · rfl\n  · rfl\n",
                ),
                (
                    "R19ParenRefineAtMkParam.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n"
                    "  refine (@Bundle.mk (n := 0)) ?_ ?_\n  · rfl\n  · rfl\n",
                ),
                (
                    "R19OuterMkBraceMlWit.lean",
                    outer_hdr
                    + wit_bundle
                    + wit_outer
                    + "theorem bypass : Outer (0 + 0) := by\n  simp only [Nat.add_zero]\n"
                    "  refine Outer.mk { p1 := rfl, p2 := rfl }\n    ?_\n  · rfl\n",
                ),
                (
                    "R19OuterMkBraceMl2Holes.lean",
                    outer_hdr
                    + wit_bundle
                    + wit_outer
                    + "theorem bypass : Outer (0 + 0) := by\n  simp only [Nat.add_zero]\n"
                    "  refine Outer.mk { p1 := ?_, p2 := rfl }\n    ?_\n  · rfl\n  · rfl\n",
                ),
                (
                    "R19SuffInnerAscribedNatAdd0.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle (0 + 0) := by\n  first\n"
                    "  | suffices _ : ((n : Nat) + 0) + 0 = n by\n      exact ⟨rfl, rfl⟩\n    rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R19VarInTargetBypass.lean",
                    bundle_hdr
                    + "variable (n : Int)\nvariable (n : Nat) in\n"
                    "theorem bypass (_h : n = n) : Bundle (0 + 0) := by\n  first\n"
                    "  | suffices _ : n + 0 = n by\n      exact ⟨rfl, rfl⟩\n    rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R19IntroNatBypass.lean",
                    bundle_hdr
                    + "theorem bypass (n : Int) : ∀ n : Nat, Bundle (0 + 0) := by\n  intro n\n  first\n"
                    "  | suffices _ : n + 0 = n by\n      exact ⟨rfl, rfl⟩\n    rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
            )
            for fname, body in r19_bundler_fail_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertTrue(scan_parameterized_prop_bundlers(body), msg=f"{fname} missed by bundler scanner")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 2. Lean positive controls (Ch1 #3-#4, Rev2 #2-#3, Rev1 #1)
            r19_lean_pass_cases = (
                (
                    "R19PosCtorSemiRfl.lean",
                    bundle2_hdr
                    + wit_bundle2
                    + "theorem ok (n : Nat) : Bundle2 n := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor; rfl; rfl\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.zero_add _⟩\n",
                ),
                (
                    "R19PosCtorSemiExactRfl.lean",
                    bundle2_hdr
                    + wit_bundle2
                    + "theorem ok (n : Nat) : Bundle2 n := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor; exact rfl; exact rfl\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.zero_add _⟩\n",
                ),
                (
                    "R19PosExactAngleByRfl.lean",
                    bundle2_hdr
                    + wit_bundle2
                    + "theorem ok (n : Nat) : Bundle2 n := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨rfl, by rfl⟩\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.zero_add _⟩\n",
                ),
                (
                    "R19PosMkByRflArg.lean",
                    bundle2_hdr
                    + wit_bundle2
                    + "theorem ok (n : Nat) : Bundle2 n := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact Bundle2.mk rfl (by rfl)\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.zero_add _⟩\n",
                ),
                (
                    "R19PosBraceByRflInFirst.lean",
                    bundle2_hdr
                    + wit_bundle2
                    + "theorem ok (n : Nat) : Bundle2 n := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact { p1 := rfl, p2 := by rfl }\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.zero_add _⟩\n",
                ),
                (
                    "R19PosIffCtorMismatchFirst.lean",
                    bundle_iff_hdr
                    + wit_iff2
                    + "theorem ok (n : Nat) : BundleIff2 n := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨⟨rfl, rfl⟩, Nat.zero_add n⟩\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨Iff.rfl, rfl⟩\n    | succ _ => exact ⟨Iff.rfl, Nat.zero_add _⟩\n",
                ),
                (
                    "R19PosIffCtorMismatchAux.lean",
                    bundle_hdr
                    + wit_bundle
                    + "theorem ok (n : Nat) : Bundle n := by\n  first\n"
                    "  | suffices _ : (0 = 0 ↔ 0 = 0) by\n      exact ⟨rfl, Nat.add_zero n⟩\n    exact ⟨rfl, rfl⟩\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R19PosIffGoalAngleRflArm1.lean",
                    iff_wrap_hdr
                    + wit_iff_wrap
                    + "theorem ok (n : Nat) : IffWrap n := by\n  constructor\n  · first\n"
                    "    | suffices _ : 0 = 0 by\n        exact ⟨rfl, rfl⟩\n      exact rfl\n"
                    "    | cases n with\n      | zero => exact Iff.rfl\n      | succ _ => exact ⟨fun _ => Nat.zero_add _, fun _ => rfl⟩\n"
                    "  · exact rfl\n",
                ),
                (
                    "R19PosEqRefl0On1First.lean",
                    bundle1_hdr
                    + wit_bundle1
                    + "theorem ok (n : Nat) : Bundle1 n := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨Eq.refl 0, Nat.zero_add n⟩\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.zero_add _⟩\n",
                ),
                (
                    "R19PosEqRefl0On1Aux.lean",
                    bundle_hdr
                    + wit_bundle
                    + "theorem ok (n : Nat) : Bundle n := by\n  first\n"
                    "  | suffices _ : 1 = 1 by\n      exact ⟨rfl, Nat.add_zero n⟩\n    exact Eq.refl 0\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R19PosIntroRenameNatToInt.lean",
                    int_hdr
                    + wit_int0
                    + "theorem ok (n : Nat) : ∀ m : Int, IntBundle (m + n * 0) := by\n  intro n\n  first\n"
                    "  | suffices _ : n + 0 = n by\n      exact ⟨rfl, Int.add_zero _⟩\n    exact rfl\n"
                    "  | cases n with\n    | ofNat k => exact ⟨rfl, Int.add_zero _⟩\n    | negSucc k => exact ⟨rfl, Int.add_zero _⟩\n",
                ),
                (
                    "R19PosVarInScopeLeak.lean",
                    int_hdr
                    + wit_int0
                    + "variable (n : Int)\nvariable (n : Nat) in\ntheorem dummy : n = n := rfl\n"
                    "theorem ok : IntBundle n := by\n  first\n"
                    "  | suffices _ : n + 0 = n by\n      exact ⟨rfl, Int.add_zero n⟩\n    exact rfl\n"
                    "  | cases n with\n    | ofNat k => exact ⟨rfl, Int.add_zero _⟩\n    | negSucc k => exact ⟨rfl, Int.add_zero _⟩\n",
                ),
                (
                    "R19PosLetShadowInt.lean",
                    int_hdr
                    + wit_int0
                    + "theorem ok (n : Nat) : ∀ m : Int, IntBundle m := by\n  intro m\n  let n : Int := m\n  first\n"
                    "  | suffices _ : n + 0 = n by\n      exact ⟨rfl, Int.add_zero _⟩\n    exact rfl\n"
                    "  | cases m with\n    | ofNat k => exact ⟨rfl, Int.add_zero _⟩\n    | negSucc k => exact ⟨rfl, Int.add_zero _⟩\n",
                ),
            )
            for fname, body in r19_lean_pass_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertEqual(scan_native_decide_and_vacuous_true(body), [], msg=f"{fname} false vacuous hit")
                self.assertEqual(scan_parameterized_prop_bundlers(body), [], msg=f"{fname} false bundler hit")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "PASS", msg=f"{fname} false-failed T1-LEAN-04: {res.summary}")

            # 3. T3-CONS-02 (Ch1 #5, Rev1 #2: guillemet normalization & relative nested sub-namespace resolution)
            lean_dir = root / "lean" / "InfoGeometry" / "Test"
            lean_dir.mkdir(parents=True)
            t_mod = lean_dir / "TMod.lean"
            t_aud = lean_dir / "TModAudit.lean"
            t_env = root / "env_t19.json"
            t_arts = DiscoveredArtifacts([], [t_env], [], [], [], [t_env], [])

            def _set_ns19_case(mod_src: str, acc_thm: str, aud_src: str) -> str:
                t_mod.write_text(mod_src, encoding="utf-8")
                t_aud.write_text(aud_src, encoding="utf-8")
                t_env.write_text(
                    json.dumps(
                        {
                            "owner_search": {
                                "target_artifacts": [
                                    "lean/InfoGeometry/Test/TMod.lean",
                                    "lean/InfoGeometry/Test/TModAudit.lean",
                                ]
                            },
                            "formal_objects": {"lane_t": ["TMod.obj"]},
                            "acceptance_theorems": {"lane_t": [acc_thm]},
                        }
                    ),
                    encoding="utf-8",
                )
                tgts = [ResolvedTarget(t_mod, "lean/InfoGeometry/Test/TMod.lean", "InfoGeometry.Test.TMod", True)]
                return check_t3_cons_02_contracts_to_lean_declarations(
                    root, t_arts, tgts, require_all_envelope_targets=True
                ).status

            self.assertEqual(
                _set_ns19_case(
                    "namespace Ns\ntheorem ok : 1 = 1 := rfl\ntheorem ok' : 1 = 1 := rfl\nend Ns\n",
                    "Ns.ok'",
                    "namespace Ms\naxiom ok' : 1 = 1\nend Ms\nopen Ms\nopen Ns hiding ok\n  «ok'»\n#print axioms ok'\n",
                ),
                "FAIL",
            )
            self.assertEqual(
                _set_ns19_case(
                    "namespace Ns\ntheorem a : 1 = 1 := rfl\nend Ns\nnamespace Ms'\ntheorem ok : 1 = 1 := rfl\nend Ms'\n",
                    "Ms'.ok",
                    "open Ns\n  «Ms'»\n#print axioms ok\n",
                ),
                "PASS",
            )
            self.assertEqual(
                _set_ns19_case(
                    "namespace «Ns'»\ntheorem «ok'» : 1 = 1 := rfl\nend «Ns'»\n",
                    "Ns'.ok'",
                    "open Ns'\n#print axioms ok'\n",
                ),
                "PASS",
            )
            self.assertEqual(
                _set_ns19_case(
                    "namespace Ns\nnamespace Ms'\ntheorem ok : 1 = 1 := rfl\nend Ms'\nend Ns\n",
                    "Ns.Ms'.ok",
                    "open Ns\nopen Ms'\n#print axioms ok\n",
                ),
                "PASS",
            )
            self.assertEqual(
                _set_ns19_case(
                    "namespace Ns\nnamespace Ms'\ntheorem ok' : 1 = 1 := rfl\nend Ms'\nend Ns\n",
                    "Ns.Ms'.ok'",
                    "open Ns\n  Ms'\nopen Ms' hiding ok'\nopen Ms' (ok')\n#print axioms ok'\n",
                ),
                "PASS",
            )

            # 4. T3-CONS-05 (Ch2 #4: generalized bare `<scheme>://` URI masking e.g. `ftp://`)
            (root / "docs").mkdir(parents=True)
            samp = root / "docs" / "sample.md"
            samp.write_bytes(b"sample v19\n")
            samp_sha = hashlib.sha256(b"sample v19\n").hexdigest()
            other_sha = hashlib.sha256(b"other v19\n").hexdigest()
            qa_rep = root / "qa_report_r19.md"
            qa_rep.write_text(f"| ftp://files.test/{other_sha} | docs/sample.md | `{samp_sha}` |\n", encoding="utf-8")
            r_ftp_ok = check_t3_cons_05_audit_report_hashes(
                root, DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]), targets=[]
            )
            self.assertEqual(r_ftp_ok.status, "PASS", msg=r_ftp_ok.summary)
            self.assertIn("(1/1 files)", r_ftp_ok.summary)
            qa_rep.write_text(f"| ftp://files.test/{samp_sha} | docs/sample.md | `{other_sha}` |\n", encoding="utf-8")
            r_ftp_fail = check_t3_cons_05_audit_report_hashes(
                root, DiscoveredArtifacts([], [], [], [], qa_reports=[qa_rep], manifest_paths=[], explicit_targets=[]), targets=[]
            )
            self.assertEqual(r_ftp_fail.status, "FAIL", msg=r_ftp_fail.summary)
            self.assertEqual(r_ftp_fail.details.get("checked"), 1)

            # 5. Intake Ch2 #1-#3 & Rev2 #1: unit + end-to-end T1-INTAKE-07
            (root / "cached" / "drive_docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )
            m1b = root / "docs" / "M1B_R19.md"
            c_ok_bytes = b"Source C valid markdown R19\n"
            c_sha = hashlib.sha256(c_ok_bytes).hexdigest()
            e_ok_bytes = b"Source E valid markdown R19\n"
            e_sha = hashlib.sha256(e_ok_bytes).hexdigest()
            c_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            e_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.md"
            e_html = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"
            c_html = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.html"

            # 5a. E=403_html unreported MUST FAIL T1-INTAKE-07 (no bleed from A or C or multi-source headers)
            c_ok_path.write_bytes(c_ok_bytes)
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            for block, exp_a in (
                (f"- Audit of A (`{SOURCE_A_ID}`): C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`) notes:\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Audit of A (`{SOURCE_A_ID}`): C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`) status:\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Status & Notes: Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Fetch and audit: Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`) — fetch log:\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Per log, A returned HTTP 403 error, and then silently failed.", True),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): A returned HTTP 403 error, and then silently failed.", True),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Per log, A returned HTTP 403 error, which is why login failed.", True),
            ):
                m1b.write_text(
                    block
                    + "\n"
                    + f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), exp_a, msg=f"A mismatch on:\n{block}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"C mismatch on:\n{block}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"E bleed on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Silent false-PASS when E=403 HTML on:\n{block}",
                )

            # 5b. Unit consistency controls: neutral shared multi-source headers (symmetric, no solo E hijack) & embedded wh-clause with matrix verb
            for text, exp_a, exp_c, exp_e in (
                (f"- Audit of A (`{SOURCE_A_ID}`): C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`) status:\n  HTTP 403 Access Denied", False, True, True),
                (f"- Status & Notes: Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False, True, True),
                (f"- Fetch and audit: Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False, True, True),
                (f"- Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`) — fetch log:\n  HTTP 403 Access Denied", False, True, True),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): A returned HTTP 403 error, which is why login failed, was logged.", False, False, False),
            ):
                m1b.write_text(text + "\n", encoding="utf-8")
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), exp_a, msg=text)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_C_ID), exp_c, msg=text)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_E_ID), exp_e, msg=text)

            # 5c. Challenge 3 positive & negative controls: heading + non-bullet sub-header vs sibling non-colon prose
            c_ok_path.unlink()
            e_html.unlink()
            c_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            e_ok_path.write_bytes(e_ok_bytes)
            ch3_pass = (
                f"## Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`)\n"
                "C download attempt:\n  HTTP 403 Access Denied\nE: preserved"
            )
            m1b.write_text(
                ch3_pass
                + "\n"
                + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                + f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg="Lost C on heading non-bullet colon")
            self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg="False E on heading non-bullet colon")
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "PASS",
                msg="False FAIL on heading non-bullet colon",
            )
            ch3_neg = (
                f"## Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`)\n"
                "C saved locally.\nHTTP 403 Access Denied"
            )
            m1b.write_text(
                ch3_neg
                + "\n"
                + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                + f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg="False C bleed on unindented non-colon prose")
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "FAIL",
                msg="Silent false-PASS when C=403 HTML on unindented non-colon prose",
            )

    def test_regression_r20_iter19_findings(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        bundle_hdr = "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
        bundle1_hdr = "structure Bundle1 (n : Nat) : Prop where\n  p1 : 1 = 1\n  p2 : 0 + n = n\n"
        bundle2_hdr = "structure Bundle2 (n : Nat) : Prop where\n  p1 : 0 = 0\n  p2 : 0 + n = n\n"
        outer_hdr = bundle_hdr + "structure Outer (n : Nat) : Prop where\n  w : Bundle n\n  p3 : n + 0 = n\n"
        iff_wrap_hdr = "structure IffWrap (n : Nat) : Prop where\n  h1 : 0 = 0 ↔ 0 + n = n\n  h2 : 0 = 0\n"
        iff_const_hdr = "structure IffConst (n : Nat) : Prop where\n  h1 : 0 = 0 ↔ 0 = 0\n  h2 : n = n\n"
        wit_bundle = (
            "theorem witness_b (n : Nat) : Bundle n := by\n  cases n with\n"
            "  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n"
        )
        wit_bundle1 = (
            "theorem witness_b1 (n : Nat) : Bundle1 n := by\n  cases n with\n"
            "  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.zero_add _⟩\n"
        )
        wit_bundle2 = (
            "theorem witness_b2 (n : Nat) : Bundle2 n := by\n  cases n with\n"
            "  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.zero_add _⟩\n"
        )
        wit_outer = (
            "theorem witness_o (n : Nat) : Outer n := by\n  cases n with\n"
            "  | zero => exact ⟨⟨rfl, rfl⟩, rfl⟩\n  | succ _ => exact ⟨⟨rfl, Nat.add_zero _⟩, Nat.add_zero _⟩\n"
        )
        wit_iff_wrap = (
            "theorem witness_iw (n : Nat) : IffWrap n := by\n  cases n with\n"
            "  | zero => exact ⟨Iff.rfl, rfl⟩\n  | succ _ => exact ⟨⟨fun _ => Nat.zero_add _, fun _ => rfl⟩, rfl⟩\n"
        )
        wit_iff_const = (
            "theorem witness_ic (n : Nat) : IffConst n := by\n  cases n with\n"
            "  | zero => exact ⟨Iff.rfl, rfl⟩\n  | succ _ => exact ⟨Iff.rfl, rfl⟩\n"
        )

        with tempfile.TemporaryDirectory(prefix="ec_reg_r20_") as td:
            root = Path(td)

            # 1. Lean bundler FAIL cases (Ch1 #1-#3, Rev2 #2, Rev1 Minor #1)
            r20_bundler_fail_cases = (
                (
                    "R20NestedMkHoleRefine.lean",
                    outer_hdr
                    + wit_bundle
                    + wit_outer
                    + "theorem bypass : Outer (0 + 0) := by\n  simp only [Nat.add_zero]\n"
                    "  refine Outer.mk (Bundle.mk ?_ rfl) rfl\n  · rfl\n",
                ),
                (
                    "R20AscribedHeadMk.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (Bundle.mk : _) rfl rfl\n",
                ),
                (
                    "R20IdHeadMk.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (id Bundle.mk) rfl rfl\n",
                ),
                (
                    "R20ShowHeadMk.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (show _ from Bundle.mk) rfl rfl\n",
                ),
                (
                    "R20EqReflNamedAlpha.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact ⟨Eq.refl (α := Nat) 0, Eq.refl (α := Nat) 0⟩\n",
                ),
                (
                    "R20EqReflNamedAFirst.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨Eq.refl (a := 0), Eq.refl (a := 0)⟩\n    rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R20ApplyParenAtMkParam.lean",
                    bundle_hdr
                    + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n"
                    "  apply (@Bundle.mk (n := 0))\n  · rfl\n  · rfl\n",
                ),
                (
                    "R20ForallShadowIntroM.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : ∀ n : Int, Bundle (0 + 0) := by\n  intro m\n  first\n"
                    "  | suffices _ : n + 0 = n by\n      exact ⟨rfl, rfl⟩\n    rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R20IntroParenIntBypass.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : ∀ n : Int, Bundle (0 + 0) := by\n  intro (m : Int)\n  first\n"
                    "  | suffices _ : n + 0 = n by\n      exact ⟨rfl, rfl⟩\n    rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R20CtorDsimpSemi.lean",
                    bundle2_hdr
                    + "theorem bypass (n : Nat) : Bundle2 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor; dsimp only; exact rfl; exact rfl\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R20CtorNestedCtor.lean",
                    outer_hdr
                    + wit_bundle
                    + wit_outer
                    + "theorem bypass (n : Nat) : Outer (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      · constructor\n        · rfl\n        · rfl\n      · rfl\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨⟨rfl, rfl⟩, rfl⟩\n    | succ _ => exact ⟨⟨rfl, rfl⟩, rfl⟩\n",
                ),
                (
                    "R20CtorNestedSemi.lean",
                    outer_hdr
                    + wit_bundle
                    + wit_outer
                    + "theorem bypass (n : Nat) : Outer (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor; constructor; rfl; rfl; rfl\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨⟨rfl, rfl⟩, rfl⟩\n    | succ _ => exact ⟨⟨rfl, rfl⟩, rfl⟩\n",
                ),
                (
                    "R20IffFunRflConst.lean",
                    iff_const_hdr
                    + wit_iff_const
                    + "theorem bypass (n : Nat) : IffConst (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨⟨fun _ => rfl, fun _ => rfl⟩, rfl⟩\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨Iff.rfl, rfl⟩\n    | succ _ => exact ⟨Iff.rfl, rfl⟩\n",
                ),
            )
            for fname, body in r20_bundler_fail_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertTrue(scan_parameterized_prop_bundlers(body), msg=f"{fname} missed by bundler scanner")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 2. Lean positive controls (Ch1 #3, Rev1 Minor #2, Eq.refl named mismatch, dsimp+rfl)
            r20_lean_pass_cases = (
                (
                    "R20PosCtorSemiDsimp.lean",
                    bundle2_hdr
                    + wit_bundle2
                    + "theorem ok (n : Nat) : Bundle2 n := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor; dsimp; exact Nat.zero_add n\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.zero_add _⟩\n",
                ),
                (
                    "R20PosIffFunRflArm1.lean",
                    iff_wrap_hdr
                    + wit_iff_wrap
                    + "theorem ok (n : Nat) : IffWrap n := by\n  constructor\n  · first\n"
                    "    | suffices _ : 0 = 0 by\n        exact ⟨fun _ => rfl, fun _ => rfl⟩\n      exact rfl\n"
                    "    | cases n with\n      | zero => exact Iff.rfl\n      | succ _ => exact ⟨fun _ => Nat.zero_add _, fun _ => rfl⟩\n"
                    "  · exact rfl\n",
                ),
                (
                    "R20PosDsimpRflOnNonDefeq.lean",
                    bundle2_hdr
                    + wit_bundle2
                    + "theorem ok (n : Nat) : Bundle2 n := by\n  constructor\n  · rfl\n  · first\n"
                    "    | suffices _ : 0 = 0 by\n        dsimp only; rfl\n      exact rfl\n"
                    "    | cases n with\n      | zero => rfl\n      | succ _ => exact Nat.zero_add _\n",
                ),
                (
                    "R20PosEqReflNamedAMismatch.lean",
                    bundle1_hdr
                    + wit_bundle1
                    + "theorem ok (n : Nat) : Bundle1 n := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨Eq.refl (a := 0), Nat.zero_add n⟩\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.zero_add _⟩\n",
                ),
            )
            for fname, body in r20_lean_pass_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertEqual(scan_native_decide_and_vacuous_true(body), [], msg=f"{fname} false vacuous hit")
                self.assertEqual(scan_parameterized_prop_bundlers(body), [], msg=f"{fname} false bundler hit")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "PASS", msg=f"{fname} false-failed T1-LEAN-04: {res.summary}")

            # 3. T3-CONS-02 (Ch1 #4: local namespace open shadowing & additive open ... hiding)
            lean_dir = root / "lean" / "InfoGeometry" / "Test"
            lean_dir.mkdir(parents=True)
            t_mod = lean_dir / "TMod.lean"
            t_aud = lean_dir / "TModAudit.lean"
            t_env = root / "env_t20.json"
            t_arts = DiscoveredArtifacts([], [t_env], [], [], [], [t_env], [])

            def _set_ns20_case(mod_src: str, acc_thm: str, aud_src: str) -> str:
                t_mod.write_text(mod_src, encoding="utf-8")
                t_aud.write_text(aud_src, encoding="utf-8")
                t_env.write_text(
                    json.dumps(
                        {
                            "owner_search": {
                                "target_artifacts": [
                                    "lean/InfoGeometry/Test/TMod.lean",
                                    "lean/InfoGeometry/Test/TModAudit.lean",
                                ]
                            },
                            "formal_objects": {"lane_t": ["TMod.obj"]},
                            "acceptance_theorems": {"lane_t": [acc_thm]},
                        }
                    ),
                    encoding="utf-8",
                )
                tgts = [ResolvedTarget(t_mod, "lean/InfoGeometry/Test/TMod.lean", "InfoGeometry.Test.TMod", True)]
                return check_t3_cons_02_contracts_to_lean_declarations(
                    root, t_arts, tgts, require_all_envelope_targets=True
                ).status

            self.assertEqual(
                _set_ns20_case(
                    "namespace Ns\ntheorem ok : 1 = 1 := rfl\nend Ns\n",
                    "Ns.ok",
                    "namespace Audit\nnamespace Ns\naxiom ok : 1 = 1\nend Ns\nopen Ns\n#print axioms ok\nend Audit\n",
                ),
                "FAIL",
            )
            self.assertEqual(
                _set_ns20_case(
                    "namespace Ns\nnamespace Ms'\ntheorem ok : 1 = 1 := rfl\nend Ms'\nend Ns\n",
                    "Ns.Ms'.ok",
                    "namespace Audit\nnamespace Ns\nnamespace Ms'\naxiom ok : 1 = 1\nend Ms'\nend Ns\nopen Ns\nopen Ms'\n#print axioms ok\nend Audit\n",
                ),
                "FAIL",
            )
            self.assertEqual(
                _set_ns20_case(
                    "namespace Ns\ntheorem ok : 1 = 1 := rfl\nend Ns\n",
                    "Ns.ok",
                    "namespace Audit\nnamespace Ns\naxiom ok : 1 = 1\nend Ns\nopen _root_.Ns\n#print axioms ok\nend Audit\n",
                ),
                "PASS",
            )
            self.assertEqual(
                _set_ns20_case(
                    "namespace Ns\ntheorem ok : 1 = 1 := rfl\nend Ns\n",
                    "Ns.ok",
                    "open Ns\nopen Ns hiding ok\n#print axioms ok\n",
                ),
                "PASS",
            )
            self.assertEqual(
                _set_ns20_case(
                    "namespace Ns\ntheorem a : 1 = 1 := rfl\ntheorem b : 1 = 1 := rfl\nend Ns\n",
                    "Ns.b",
                    "open Ns hiding a\nopen Ns hiding b\n#print axioms b\n",
                ),
                "PASS",
            )

            # 4. Intake (Ch2 #1-#2 & Rev2 #1): unit + end-to-end T1-INTAKE-07
            (root / "cached" / "drive_docs").mkdir(parents=True)
            (root / "docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )
            m1b = root / "docs" / "M1B_R20.md"
            c_ok_bytes = b"Source C valid markdown R20\n"
            c_sha = hashlib.sha256(c_ok_bytes).hexdigest()
            c_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            e_html = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"
            c_ok_path.write_bytes(c_ok_bytes)
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")

            for block, exp_a in (
                (f"- Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`) notes:\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Audit of A (`{SOURCE_A_ID}`): Fetch log for C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`) notes:\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Audit of A (`{SOURCE_A_ID}`): Regarding C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`) status:\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Audit of A (`{SOURCE_A_ID}`): Note on C (`{SOURCE_C_ID}`), E (`{SOURCE_E_ID}`) notes:\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Audit of A (`{SOURCE_A_ID}`): For C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Summary - C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Summary; C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Per log, A returned HTTP 403 error, which indicates login failed.", True),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Per log, A returned HTTP 403 error, which indicates that login failed.", True),
            ):
                m1b.write_text(
                    block
                    + "\n"
                    + f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), exp_a, msg=f"A mismatch on:\n{block}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"C mismatch on:\n{block}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"E bleed on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Silent false-PASS when E=403 HTML on:\n{block}",
                )

            # Positive PASS control with explicit trailing `; E:`
            m1b.write_text(
                f"- Summary — C (`{SOURCE_C_ID}`) ok; E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied\n"
                + f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                + claims_tail,
                encoding="utf-8",
            )
            self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID))
            self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID))
            self.assertEqual(
                check_t1_intake_07_additional_sources_f10(
                    root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                ).status,
                "PASS",
                msg="False FAIL on explicit trailing `; E:`",
            )

            # Unit controls: bare shared symmetry, single-line Source-A complement clauses, & matrix finite verb rejection
            for text, exp_a, exp_c, exp_d, exp_e in (
                (f"- Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`) notes:\n  HTTP 403 Access Denied", False, True, True, True),
                (f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False, True, True, True),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): A returned HTTP 403 error, which indicates login failed.", True, False, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): A returned HTTP 403 error, which indicates that login failed.", True, False, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): A returned HTTP 403 error, which indicates login failed, was logged.", False, False, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): A returned HTTP 403 error, which indicates that login failed, was logged.", False, False, False, False),
            ):
                m1b.write_text(text + "\n", encoding="utf-8")
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), exp_a, msg=text)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_C_ID), exp_c, msg=text)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_D_ID), exp_d, msg=text)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_E_ID), exp_e, msg=text)

    def test_regression_r21_iter20_findings(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        bundle_hdr = "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
        swapped_bundle_hdr = "structure SwappedBundle (n : Nat) : Prop where\n  p1 : n + 0 = n\n  p2 : n = n\n"
        bundle1_hdr = "structure Bundle1 (n : Nat) : Prop where\n  p1 : 0 = 0\n  p2 : 1 = 1\n"
        bundle2_hdr = "structure Bundle2 (n : Nat) : Prop where\n  p1 : 0 = 0\n  p2 : 0 + n = n\n"
        bundle3_hdr = "structure Bundle3 (n : Nat) : Prop where\n  p1 : 0 + n = n\n  p2 : n + 0 = n\n"
        outer_hdr = bundle_hdr + "structure Outer (n : Nat) : Prop where\n  w : Bundle n\n  p3 : n + 0 = n\n"
        eqb_hdr = "structure EqB (n : Nat) : Prop where\n  p1 : 0 = 0\n  p2 : n = n\n"
        arr2_hdr = "structure Arr2 (n : Nat) : Prop where\n  h1 : (0 = 0) → (0 = 0)\n  h2 : (0 = 0) → (n = n)\n"
        arr3_hdr = "structure Arr3 (n : Nat) : Prop where\n  h : (0 = 0) → (0 = 0) → (0 = 0)\n  h2 : n = n\n"
        natarr_hdr = "structure NatArr (k : Nat) : Prop where\n  h : ∀ n : Nat, n + 0 = n\n  h2 : k = k\n"
        iff_const_hdr = "structure IffConst (n : Nat) : Prop where\n  h1 : 0 = 0 ↔ 0 = 0\n  h2 : n = n\n"
        iff_wrap_hdr = "structure IffWrap (n : Nat) : Prop where\n  h1 : 0 = 0 ↔ 0 + n = n\n  h2 : 0 = 0\n"
        wit_bundle2 = (
            "theorem witness_b2 (n : Nat) : Bundle2 n := by\n  cases n with\n"
            "  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, Nat.zero_add _⟩\n"
        )
        wit_bundle3 = (
            "theorem witness_b3 (n : Nat) : Bundle3 n := by\n  cases n with\n"
            "  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨Nat.zero_add _, Nat.add_zero _⟩\n"
        )
        wit_iff_wrap = (
            "theorem witness_iw (n : Nat) : IffWrap n := by\n  cases n with\n"
            "  | zero => exact ⟨Iff.rfl, rfl⟩\n  | succ _ => exact ⟨⟨fun _ => Nat.zero_add _, fun _ => rfl⟩, rfl⟩\n"
        )

        with tempfile.TemporaryDirectory(prefix="ec_reg_r21_") as td:
            root = Path(td)

            # 1. Lean bundler FAIL cases (Ch1 #1-#3, Rev2 #2 & Minor)
            r21_bundler_fail_cases = (
                (
                    "R21IdUnparenMk.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact id Bundle.mk rfl rfl\n",
                ),
                (
                    "R21IdParenMkUnparen.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact id (Bundle.mk) rfl rfl\n",
                ),
                (
                    "R21AtIdUnparenMk.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact @id _ Bundle.mk rfl rfl\n",
                ),
                (
                    "R21IdUnparenRefine.lean",
                    outer_hdr
                    + "theorem bypass : Outer (0 + 0) := by\n  simp only [Nat.add_zero]\n"
                    "  refine id Outer.mk (Bundle.mk ?_ rfl) rfl\n  · rfl\n",
                ),
                (
                    "R21IdUnparenEqRefl.lean",
                    eqb_hdr + "theorem bypass : EqB (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact id EqB.mk (id Eq.refl 0) rfl\n",
                ),
                (
                    "R21CtorRwEndBypass.lean",
                    bundle_hdr
                    + "theorem bypass (n : Nat) : Bundle (n + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor; exact rfl; rw [Nat.add_zero]\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R21CtorRwMidBypass.lean",
                    swapped_bundle_hdr
                    + "theorem bypass (n : Nat) : SwappedBundle n := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor; rw [Nat.add_zero]; exact rfl\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨Nat.add_zero _, rfl⟩\n",
                ),
                (
                    "R21CtorRwSemiBypass.lean",
                    swapped_bundle_hdr
                    + "theorem bypass (n : Nat) : SwappedBundle (n + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor; rw [Nat.add_zero]; rfl\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨Nat.add_zero _, rfl⟩\n",
                ),
                (
                    "R21CtorIntroSemiArr.lean",
                    arr2_hdr
                    + "theorem bypass (n : Nat) : Arr2 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor; intro _; rfl; intro _; rfl\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩\n    | succ _ => exact ⟨fun _ => rfl, fun _ => rfl⟩\n",
                ),
                (
                    "R21CtorIntroSemiIffNested.lean",
                    iff_const_hdr
                    + "theorem bypass (n : Nat) : IffConst (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      · constructor; intro _; rfl; intro _; rfl\n      · rfl\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨Iff.rfl, rfl⟩\n    | succ _ => exact ⟨Iff.rfl, rfl⟩\n",
                ),
                (
                    "R21CtorCaseReorder.lean",
                    bundle1_hdr
                    + "theorem bypass (n : Nat) : Bundle1 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      case p2 => exact Eq.refl 1\n      case p1 => exact Eq.refl 0\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R21FunMultiBinderArrow.lean",
                    arr3_hdr
                    + "theorem bypass (n : Nat) : Arr3 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨fun (_ _ : 0 = 0) => rfl, rfl⟩\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨fun _ _ => rfl, rfl⟩\n    | succ _ => exact ⟨fun _ _ => rfl, rfl⟩\n",
                ),
                (
                    "R21FunNatDiscardBypass.lean",
                    natarr_hdr
                    + "theorem bypass (k : Nat) : NatArr (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨fun n => rfl, rfl⟩\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => Nat.add_zero _, rfl⟩\n    | succ _ => exact ⟨fun _ => Nat.add_zero _, rfl⟩\n",
                ),
                (
                    "R21FunNatAnnotDiscardBypass.lean",
                    natarr_hdr
                    + "theorem bypass (k : Nat) : NatArr (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨fun (n : Nat) => rfl, rfl⟩\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => Nat.add_zero _, rfl⟩\n    | succ _ => exact ⟨fun _ => Nat.add_zero _, rfl⟩\n",
                ),
                (
                    "R21CtorChangeSemiBypass.lean",
                    bundle2_hdr
                    + "theorem bypass (n : Nat) : Bundle2 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      · change 0 = 0; rfl\n      · change 0 + (0 + 0) = 0 + 0; rfl\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, Nat.zero_add _⟩\n",
                ),
                (
                    "R21ApplyAtMkTrivialNamedP2.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  apply (@Bundle.mk (n := 0) (p2 := rfl))\n  · rfl\n",
                ),
            )
            for fname, body in r21_bundler_fail_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertTrue(scan_parameterized_prop_bundlers(body), msg=f"{fname} missed by bundler scanner")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 2. Lean positive PASS controls (Rev1 Minor #1, Ch1 #2/#3, Rev2 Minor)
            r21_lean_pass_cases = (
                (
                    "R21PosApplyAtMkNamedP2.lean",
                    bundle3_hdr
                    + wit_bundle3
                    + "theorem ok (n : Nat) : Bundle3 n := by\n  apply (@Bundle3.mk (n := n) (p2 := Nat.add_zero n))\n"
                    "  · first\n    | suffices _ : 0 = 0 by rfl\n      exact rfl\n"
                    "    | cases n with\n      | zero => rfl\n      | succ _ => exact Nat.zero_add _\n",
                ),
                (
                    "R21PosCtorIntroNonDefeq.lean",
                    iff_wrap_hdr
                    + wit_iff_wrap
                    + "theorem ok (n : Nat) : IffWrap n := by\n  constructor\n  · first\n"
                    "    | suffices _ : 0 = 0 by\n        constructor; intro _; rfl; intro _; rfl\n      exact rfl\n"
                    "    | cases n with\n      | zero => exact Iff.rfl\n      | succ _ => exact ⟨fun _ => Nat.zero_add _, fun _ => rfl⟩\n"
                    "  · exact rfl\n",
                ),
                (
                    "R21PosCtorCaseReorderNonDefeq.lean",
                    bundle2_hdr
                    + wit_bundle2
                    + "theorem ok (n : Nat) : Bundle2 n := by\n  constructor\n"
                    "  case p2 =>\n    cases n with\n    | zero => rfl\n    | succ _ => exact Nat.zero_add _\n"
                    "  case p1 => exact rfl\n",
                ),
                (
                    "R21PosUnfoldNonDefeq.lean",
                    bundle2_hdr
                    + wit_bundle2
                    + "theorem ok (n : Nat) : Bundle2 n := by\n  constructor\n  · rfl\n  · first\n"
                    "    | suffices _ : 0 = 0 by\n        unfold HAdd.hAdd; rfl\n      exact rfl\n"
                    "    | cases n with\n      | zero => exact rfl\n      | succ _ => exact Nat.zero_add _\n",
                ),
            )
            for fname, body in r21_lean_pass_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertEqual(scan_native_decide_and_vacuous_true(body), [], msg=f"{fname} false vacuous hit")
                self.assertEqual(scan_parameterized_prop_bundlers(body), [], msg=f"{fname} false bundler hit")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "PASS", msg=f"{fname} false-failed T1-LEAN-04: {res.summary}")

            # 3. T3-CONS-02 (Ch1 #4: export local-namespace shadowing & open ... renaming false shadow)
            lean_dir = root / "lean" / "InfoGeometry" / "Test"
            lean_dir.mkdir(parents=True)
            t_mod = lean_dir / "TMod.lean"
            t_aud = lean_dir / "TModAudit.lean"
            t_env = root / "env_t21.json"
            t_arts = DiscoveredArtifacts([], [t_env], [], [], [], [t_env], [])

            def _set_ns21_case(mod_src: str, acc_thm: str, aud_src: str) -> str:
                t_mod.write_text(mod_src, encoding="utf-8")
                t_aud.write_text(aud_src, encoding="utf-8")
                t_env.write_text(
                    json.dumps(
                        {
                            "owner_search": {
                                "target_artifacts": [
                                    "lean/InfoGeometry/Test/TMod.lean",
                                    "lean/InfoGeometry/Test/TModAudit.lean",
                                ]
                            },
                            "formal_objects": {"lane_t": ["TMod.obj"]},
                            "acceptance_theorems": {"lane_t": [acc_thm]},
                        }
                    ),
                    encoding="utf-8",
                )
                tgts = [ResolvedTarget(t_mod, "lean/InfoGeometry/Test/TMod.lean", "InfoGeometry.Test.TMod", True)]
                return check_t3_cons_02_contracts_to_lean_declarations(
                    root, t_arts, tgts, require_all_envelope_targets=True
                ).status

            self.assertEqual(
                _set_ns21_case(
                    "namespace Ns\ntheorem ok : 1 = 1 := rfl\nend Ns\n",
                    "Ns.ok",
                    "namespace Audit\nnamespace Ns\naxiom ok : 1 = 1\nend Ns\nexport Ns (ok)\nend Audit\nopen Audit\n#print axioms ok\n",
                ),
                "FAIL",
            )
            self.assertEqual(
                _set_ns21_case(
                    "namespace Ns\ntheorem ok : 1 = 1 := rfl\nend Ns\n",
                    "Ns.ok",
                    "namespace Audit\nnamespace Ns\naxiom ok : 1 = 1\nend Ns\nexport Ns (ok)\nend Audit\n#print axioms Audit.ok\n",
                ),
                "FAIL",
            )
            self.assertEqual(
                _set_ns21_case(
                    "namespace Ns\ntheorem ok : 1 = 1 := rfl\nend Ns\n",
                    "Ns.ok",
                    "namespace Ns\naxiom my_ok : 1 = 1\nend Ns\nopen Ns renaming ok → my_ok\n#print axioms my_ok\n",
                ),
                "PASS",
            )
            self.assertEqual(
                _set_ns21_case(
                    "namespace Ns\ntheorem ok : 1 = 1 := rfl\nend Ns\n",
                    "Ns.ok",
                    "namespace Audit\nnamespace Ns\naxiom ok : 1 = 1\nend Ns\nexport _root_.Ns (ok)\nend Audit\nopen Audit\n#print axioms ok\n",
                ),
                "PASS",
            )

            # 4. Intake (Ch2 #1-#2, Rev2 #1, Auditor §3 caveats): unit + end-to-end T1-INTAKE-07
            (root / "cached" / "drive_docs").mkdir(parents=True)
            (root / "docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )
            m1b = root / "docs" / "M1B_R21.md"
            c_ok_bytes = b"Source C valid markdown R21\n"
            c_sha = hashlib.sha256(c_ok_bytes).hexdigest()
            c_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            e_html = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"
            c_ok_path.write_bytes(c_ok_bytes)
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")

            for block, exp_a in (
                (f"- Audit of A (`{SOURCE_A_ID}`): Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Intake log — Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Summary — C (`{SOURCE_C_ID}`) / E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Summary — C (`{SOURCE_C_ID}`) / D (`{SOURCE_D_ID}`) / E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Summary — C (`{SOURCE_C_ID}`) — D (`{SOURCE_D_ID}`) — E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Summary - C (`{SOURCE_C_ID}`) - D (`{SOURCE_D_ID}`) - E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Sources C (`{SOURCE_C_ID}`) & D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`) availability:\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) errors:\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`) errors:\n  C saved locally.\n  HTTP 403 Access Denied", False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Per log, A returned HTTP 403 error, which indicates that when auth was required, access failed.", True),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Per log, A returned HTTP 403 error, which shows that when auth was required, access failed.", True),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Per log, A also returned HTTP 403 error.", True),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Per audit, A triggered HTTP 403 error.", True),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Per audit A returned HTTP 403 error.", True),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Per audit, A blocked HTTP 403 response was logged.", False),
            ):
                m1b.write_text(
                    block
                    + "\n"
                    + f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), exp_a, msg=f"A mismatch on:\n{block}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"C mismatch on:\n{block}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"E bleed on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Silent false-PASS when E=403 HTML on:\n{block}",
                )

            # Positive PASS controls: shared multi-source headers & explicit trailing owners
            for pass_block, exp_c, exp_d, exp_e in (
                (f"- Summary — C (`{SOURCE_C_ID}`) / D (`{SOURCE_D_ID}`) / E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", True, True, True),
                (f"- Sources C (`{SOURCE_C_ID}`) & D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", True, True, True),
                (f"- Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`) availability:\n  HTTP 403 Access Denied", True, True, True),
                (f"- Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`) errors:\n  HTTP 403 Access Denied", True, True, True),
                (f"- Audit of A (`{SOURCE_A_ID}`): Summary — E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False, False, True),
                (f"- Summary — C (`{SOURCE_C_ID}`) ok — E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False, False, True),
                (f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`), E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False, False, True),
            ):
                m1b.write_text(
                    pass_block
                    + "\n"
                    + f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_C_ID), exp_c, msg=pass_block)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_D_ID), exp_d, msg=pass_block)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_E_ID), exp_e, msg=pass_block)
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "PASS",
                    msg=f"False FAIL on:\n{pass_block}",
                )

            # Unit controls: single-line Source-A adverb/complement & matrix finite verb rejection
            for text, exp_a, exp_c, exp_d, exp_e in (
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): A returned HTTP 403 error, which indicates that when auth was required, access failed, was logged.", False, False, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Per log, A returned HTTP 403 error, which indicates that when auth was required, access failed.", True, False, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Per log, A also returned HTTP 403 error.", True, False, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Per audit, A triggered HTTP 403 error.", True, False, False, False),
            ):
                m1b.write_text(text + "\n", encoding="utf-8")
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), exp_a, msg=text)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_C_ID), exp_c, msg=text)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_D_ID), exp_d, msg=text)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_E_ID), exp_e, msg=text)

    def test_regression_r22_iter21_findings(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        b_hdr = "structure B (n : Nat) : Prop where\n  p1 : 0 = 0\n  p2 : n = n\n"
        bundle_hdr = "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
        bundle2_hdr = "structure Bundle2 (n : Nat) : Prop where\n  p1 : 0 = 0\n  p2 : 0 + n = n\n"
        eqb_hdr = "structure EqB (n : Nat) : Prop where\n  p1 : 0 = 0\n  p2 : n = n\n"
        pand_hdr = "structure PAnd (n : Nat) : Prop where\n  a : (1 = 1) ∧ (0 = 0)\n  b : n = n\n"
        pand_nondefeq_hdr = "structure PAndNonDefeq (n : Nat) : Prop where\n  a : (1 = 1) ∧ (0 = 0)\n  b : 0 + n = n\n"
        natarr_hdr = "structure NatArr (k : Nat) : Prop where\n  h : ∀ n : Nat, n + 0 = n\n  h2 : k = k\n"
        natarr2m_hdr = "structure NatArr2M (k : Nat) : Prop where\n  h : ∀ a b : Nat, a + 0 = a ∧ b + 0 = b\n  h2 : k = k\n"
        natarr2_hdr = "structure NatArr2 (n : Nat) : Prop where\n  h : ∀ n : Prop, n = n\n  h2 : n = n\n"
        arr2_hdr = "structure Arr2 (n : Nat) : Prop where\n  h1 : (0 = 0) → (1 = 1)\n  h2 : (0 = 0) → (0 = 0)\n"

        with tempfile.TemporaryDirectory(prefix="ec_reg_r22_") as td:
            root = Path(td)

            # 1. Lean bundler FAIL cases (Rev1 #2, Rev2 #2-#5, Ch1 #1-#3, Auditor §3 #1-#2)
            r22_bundler_fail_cases = (
                (
                    "R22IdNamedAThenAlpha.lean",
                    b_hdr + "theorem bypass : B (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact id (a := B.mk) (α := 0 = 0 → 0 = 0 → B 0) rfl rfl\n",
                ),
                (
                    "R22AtIdNamedAThenAlpha.lean",
                    b_hdr + "theorem bypass : B (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact @id (a := B.mk) (α := 0 = 0 → 0 = 0 → B 0) rfl rfl\n",
                ),
                (
                    "R22ParenIdNamedAMk.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (id (a := Bundle.mk)) rfl rfl\n",
                ),
                (
                    "R22IdNamedAEqRefl.lean",
                    eqb_hdr + "theorem bypass : EqB (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact ⟨id (a := Eq.refl 0), rfl⟩\n",
                ),
                (
                    "R22ParenAtIdNamedAMk.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact (@id _ (a := Bundle.mk)) rfl rfl\n",
                ),
                (
                    "R22IdUnivAnon.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact id.{0} ⟨rfl, rfl⟩\n",
                ),
                (
                    "R22IdUnivField.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact id Bundle.mk (id.{0} rfl) rfl\n",
                ),
                (
                    "R22AtIdUnivField.lean",
                    eqb_hdr + "theorem bypass : EqB (0 + 0) := by\n  simp only [Nat.add_zero]\n  exact ⟨@id.{0} _ rfl, rfl⟩\n",
                ),
                (
                    "R22AndCaseRightLeft.lean",
                    pand_hdr
                    + "theorem bypass (n : Nat) : PAnd (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      · constructor\n        case right => exact Eq.refl 0\n        case left => exact Eq.refl 1\n      · exact rfl\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨⟨rfl, rfl⟩, rfl⟩\n    | succ _ => exact ⟨⟨rfl, rfl⟩, rfl⟩\n",
                ),
                (
                    "R22CtorIntroRenameNat.lean",
                    natarr_hdr
                    + "theorem bypass (k : Nat) : NatArr (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor; intro m; rfl; rfl\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => Nat.add_zero _, rfl⟩\n    | succ _ => exact ⟨fun _ => Nat.add_zero _, rfl⟩\n",
                ),
                (
                    "R22CtorIntroAnonNat.lean",
                    natarr_hdr
                    + "theorem bypass (k : Nat) : NatArr (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor; intro _; rfl; rfl\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => Nat.add_zero _, rfl⟩\n    | succ _ => exact ⟨fun _ => Nat.add_zero _, rfl⟩\n",
                ),
                (
                    "R22FunNatRename.lean",
                    natarr_hdr
                    + "theorem bypass (k : Nat) : NatArr (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨fun m => rfl, rfl⟩\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => Nat.add_zero _, rfl⟩\n    | succ _ => exact ⟨fun _ => Nat.add_zero _, rfl⟩\n",
                ),
                (
                    "R22FunNatAnon.lean",
                    natarr_hdr
                    + "theorem bypass (k : Nat) : NatArr (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨fun _ => rfl, rfl⟩\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => Nat.add_zero _, rfl⟩\n    | succ _ => exact ⟨fun _ => Nat.add_zero _, rfl⟩\n",
                ),
                (
                    "R22FunNatParenAnnotRename.lean",
                    natarr_hdr
                    + "theorem bypass (k : Nat) : NatArr (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨fun (m : Nat) => rfl, rfl⟩\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => Nat.add_zero _, rfl⟩\n    | succ _ => exact ⟨fun _ => Nat.add_zero _, rfl⟩\n",
                ),
                (
                    "R22FunNatMultiRename.lean",
                    natarr2m_hdr
                    + "theorem bypass (k : Nat) : NatArr2M (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨fun x y => ⟨rfl, rfl⟩, rfl⟩\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ _ => ⟨rfl, rfl⟩, rfl⟩\n    | succ _ => exact ⟨fun _ _ => ⟨Nat.add_zero _, Nat.add_zero _⟩, rfl⟩\n",
                ),
                (
                    "R22ApplyAtMkBothNamed.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  apply (@Bundle.mk (p1 := rfl) (p2 := rfl))\n",
                ),
                (
                    "R22ApplyAtMkAllNamedWithN.lean",
                    bundle_hdr + "theorem bypass : Bundle (0 + 0) := by\n  simp only [Nat.add_zero]\n  apply (@Bundle.mk (n := 0) (p1 := rfl) (p2 := rfl))\n",
                ),
                (
                    "R22RwConcreteFirstFailFallback.lean",
                    bundle2_hdr + "theorem bypass : Bundle2 (0 + 0) := by\n  first\n  | rw [Nat.succ_eq_add_one]\n  | exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R22DsimpClosesDefeq.lean",
                    arr2_hdr
                    + "theorem bypass (k : Nat) : Arr2 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      case h2 => intro _; dsimp\n      case h1 => intro _; exact Eq.refl 1\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩\n    | succ _ => exact ⟨fun _ => rfl, fun _ => rfl⟩\n",
                ),
                (
                    "R22CaptureShadowNatArr2.lean",
                    natarr2_hdr
                    + "theorem bypass (k : Nat) : NatArr2 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨fun _ => rfl, rfl⟩\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => rfl, rfl⟩\n    | succ _ => exact ⟨fun _ => rfl, rfl⟩\n",
                ),
            )
            for fname, body in r22_bundler_fail_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertTrue(scan_parameterized_prop_bundlers(body), msg=f"{fname} missed by bundler scanner")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 2. Lean positive PASS controls
            r22_lean_pass_cases = (
                (
                    "R22PosAndCaseNonDefeq.lean",
                    pand_nondefeq_hdr
                    + "theorem ok (n : Nat) : PAndNonDefeq n := by\n  constructor\n  · constructor\n    case right => exact Eq.refl 0\n    case left => exact Eq.refl 1\n"
                    "  · cases n with\n    | zero => rfl\n    | succ _ => exact Nat.zero_add _\n",
                ),
                (
                    "R22PosDsimpOnlyNonDefeq.lean",
                    bundle2_hdr
                    + "theorem ok (n : Nat) : Bundle2 n := by\n  constructor\n  · rfl\n  · first\n"
                    "    | suffices _ : 0 = 0 by dsimp only\n      exact rfl\n"
                    "    | cases n with\n      | zero => exact rfl\n      | succ _ => exact Nat.zero_add _\n",
                ),
                (
                    "R22PosRwConcreteFirstBothRw.lean",
                    bundle2_hdr
                    + "theorem ok : Bundle2 (0 + 0) := by\n  first\n  | rw [Nat.succ_eq_add_one]\n  | rw [Nat.zero_add]; exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R22PosApplyAtMkPartial.lean",
                    bundle_hdr
                    + "theorem ok (n : Nat) : Bundle n := by\n  apply (@Bundle.mk (n := n) (p1 := rfl))\n"
                    "  · cases n with\n    | zero => rfl\n    | succ _ => exact Nat.add_zero _\n",
                ),
                (
                    "R22PosCaptureShadowNatArr2.lean",
                    natarr2_hdr
                    + "theorem ok (n : Nat) : NatArr2 n := by\n  cases n with\n"
                    "  | zero => exact ⟨fun _ => rfl, rfl⟩\n  | succ _ => exact ⟨fun _ => rfl, rfl⟩\n",
                ),
            )
            for fname, body in r22_lean_pass_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertEqual(scan_native_decide_and_vacuous_true(body), [], msg=f"{fname} false vacuous hit")
                self.assertEqual(scan_parameterized_prop_bundlers(body), [], msg=f"{fname} false bundler hit")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "PASS", msg=f"{fname} false-failed T1-LEAN-04: {res.summary}")

            # 3. Intake (Rev1 #1, Rev2 #1, Ch2 Challenges 1-2): unit + end-to-end T1-INTAKE-07
            (root / "cached" / "drive_docs").mkdir(parents=True)
            (root / "docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )
            m1b = root / "docs" / "M1B_R22.md"
            c_ok_bytes = b"Source C valid markdown R22\n"
            c_sha = hashlib.sha256(c_ok_bytes).hexdigest()
            c_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            e_html = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"
            c_ok_path.write_bytes(c_ok_bytes)
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")

            # 3a. Excluded earlier sources when trailing group is D, E (Rev1 #1): C=403_html unreported -> MUST FAIL
            c_html_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.html"
            e_ok_bytes = b"Source E valid markdown R22\n"
            e_sha = hashlib.sha256(e_ok_bytes).hexdigest()
            e_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.md"
            c_ok_path.unlink()
            e_html.unlink()
            c_html_path.write_text("<!DOCTYPE html><html><title>Access Denied</title></html>", encoding="utf-8")
            e_ok_path.write_bytes(e_ok_bytes)
            for block, exp_a in (
                (f"- Summary — C (`{SOURCE_C_ID}`) ok — D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False),
                (f"- Audit of C (`{SOURCE_C_ID}`): Summary — D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False),
                (f"- Summary — C (`{SOURCE_C_ID}`) done; D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False),
                (f"- Summary — C (`{SOURCE_C_ID}`) checked; D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False),
                (f"- Audit of A (`{SOURCE_A_ID}`): Summary — C (`{SOURCE_C_ID}`) ok — D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False),
            ):
                m1b.write_text(
                    block
                    + "\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), exp_a, msg=block)
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"C leak on:\n{block}")
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_D_ID), msg=f"D lost on:\n{block}")
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"E lost on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Silent false-PASS when C=403 HTML on:\n{block}",
                )

            # 3b. Shared topic nouns on C/D/E (C=403_html shared-reported, E=ok) -> MUST PASS (Ch2 false-FAIL fix)
            for shared_block in (
                f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) access blocker:\n  HTTP 403 Access Denied",
                f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) sign-in:\n  HTTP 403 Access Denied",
                f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) failure:\n  HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`) blocked:\n  HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`) access blocker:\n  HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`) — intake summary — E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied",
            ):
                m1b.write_text(
                    shared_block
                    + "\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=shared_block)
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_D_ID), msg=shared_block)
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=shared_block)
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "PASS",
                    msg=f"False FAIL on shared topic header:\n{shared_block}",
                )

            # 3c. E=403_html unreported with topic-noun + C saved / comma-status / dash-topic / sentence-indef A/An -> MUST FAIL
            c_html_path.unlink()
            e_ok_path.unlink()
            c_ok_path.write_bytes(c_ok_bytes)
            e_html.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            for block, exp_c, exp_d in (
                (f"- Summary — C (`{SOURCE_C_ID}`) ok, D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied", False, False),
                (f"- Audit of A (`{SOURCE_A_ID}`): C (`{SOURCE_C_ID}`) saved locally, D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied", False, False),
                (f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) access blocker:\n  C saved locally.\n  HTTP 403 Access Denied", False, False),
                (f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) sign-in:\n  C saved locally.\n  HTTP 403 Access Denied", False, False),
                (f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) failure:\n  C saved locally.\n  HTTP 403 Access Denied", False, False),
                (f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) blocked:\n  C saved locally.\n  HTTP 403 Access Denied", False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Verification ran. A blocked HTTP 403 response was logged.", False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Note that A blocked HTTP 403 response was logged.", False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Verification ran. An HTTP 403 error was logged.", False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): During the comprehensive automated repository verification audit run today, A blocked HTTP 403 response was logged.", False, False),
            ):
                m1b.write_text(
                    block
                    + "\n"
                    + f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_A_ID), msg=f"A leak on:\n{block}")
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_C_ID), exp_c, msg=block)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_D_ID), exp_d, msg=block)
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"E leak on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Silent false-PASS when E=403 HTML on:\n{block}",
                )

            # 3d. Unit & PASS controls for comma/dash partial status (`D, E` shared vs `E` solo after `C ok, E`)
            for unit_txt, exp_a, exp_c, exp_d, exp_e, exp_st in (
                (f"- Summary — C (`{SOURCE_C_ID}`) ok, D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False, False, True, True, "PASS"),
                (f"- Summary — C (`{SOURCE_C_ID}`) saved locally, D (`{SOURCE_D_ID}`) — E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False, False, True, True, "PASS"),
                (f"- Summary — C (`{SOURCE_C_ID}`) ok, E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False, False, False, True, "PASS"),
            ):
                m1b.write_text(
                    unit_txt
                    + "\n"
                    + f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), exp_a, msg=unit_txt)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_C_ID), exp_c, msg=unit_txt)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_D_ID), exp_d, msg=unit_txt)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_E_ID), exp_e, msg=unit_txt)
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    exp_st,
                    msg=unit_txt,
                )

    def test_regression_r23_iter22_findings(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        bundle_hdr = "structure Bundle (n : Nat) : Prop where\n  p1 : n = n\n  p2 : n + 0 = n\n"
        bundle2_hdr = "structure Bundle2 (n : Nat) : Prop where\n  p1 : 0 = 0\n  p2 : 0 + n = n\n"
        arr2_hdr = "structure Arr2 (n : Nat) : Prop where\n  h1 : (0 = 0) → (1 = 1)\n  h2 : (0 = 0) → (0 = 0)\n"
        arr2first_hdr = "structure Arr2First (n : Nat) : Prop where\n  h1 : (0 = 0) → (0 = 0)\n  h2 : (0 = 0) → (1 = 1)\n"
        pand_hdr = "structure PAnd (n : Nat) : Prop where\n  a : (1 = 1) ∧ (0 = 0)\n  b : n = n\n"
        twoeq_hdr = "structure TwoEq (n : Nat) : Prop where\n  a : 0 = 0\n  b : 1 = 1\n"
        natarrlet_hdr = "structure NatArrLet (n : Nat) : Prop where\n  h : let n : Prop := True; n = n\n  h2 : n = n\n"
        natarrlet_f_hdr = "structure NatArrLetF (n : Nat) : Prop where\n  h : ∀ {x : Nat}, x = x → (let n : Prop := True; n = n)\n  h2 : n = n\n"
        natarrlet_u_hdr = "structure NatArrLetU (n : Nat) : Prop where\n  h : let n := True; n = n\n  h2 : n = n\n"
        arrnd_hdr = "structure ArrND (n : Nat) : Prop where\n  h : (0 = 0) → (0 + n + 0 = n)\n  h2 : n = n\n"

        # 1. Capture-avoiding substitution: alpha-renaming & let shadowing
        self.assertEqual(
            _subst_lean_expr_capture_avoiding("∀ m : Nat, (m = n) ↔ (n = m)", {"n": "m"}),
            "∀ m_1 : Nat, (m_1 = m) ↔ (m = m_1)",
        )
        self.assertEqual(
            _subst_lean_expr_capture_avoiding("∀ m : Nat, m = n", {"n": "(m + 0)"}),
            "∀ m_1 : Nat, m_1 = (m + 0)",
        )
        self.assertEqual(
            _subst_lean_expr_capture_avoiding("(m : Nat) → m = n", {"n": "m"}),
            "(m_1 : Nat) → m_1 = m",
        )
        self.assertEqual(
            _subst_lean_expr_capture_avoiding("fun m : Nat => m = n", {"n": "m"}),
            "fun m_1 : Nat => m_1 = m",
        )
        self.assertEqual(
            _subst_lean_expr_capture_avoiding("let n : Prop := True; n = n", {"n": "(0 + 0)"}),
            "let n : Prop := True; n = n",
        )
        self.assertEqual(
            _subst_lean_expr_capture_avoiding("let m : Nat := n; m = n", {"n": "m"}),
            "let m_1 : Nat := m; m_1 = m",
        )

        with tempfile.TemporaryDirectory(prefix="ec_reg_r23_") as td:
            root = Path(td)

            # 2. Lean bundler FAIL cases (named param, dsimp variants, { ... } blocks, first/try rw variants, let shadowing)
            r23_bundler_fail_cases = (
                (
                    "R23NamedParamBundle.lean",
                    bundle_hdr
                    + "theorem bypass (k : Nat) : Bundle (n := 0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨rfl, rfl⟩\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨rfl, Nat.add_zero _⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R23DsimpNoBoundary.lean",
                    arr2_hdr
                    + "theorem bypass (k : Nat) : Arr2 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      intro _\n      dsimp\n      intro _\n      exact Eq.refl 0\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩\n    | succ _ => exact ⟨fun _ => rfl, fun _ => rfl⟩\n",
                ),
                (
                    "R23DsimpOnlyBracket.lean",
                    arr2_hdr
                    + "theorem bypass (k : Nat) : Arr2 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      case h2 => intro _; dsimp only []\n      case h1 => intro _; exact Eq.refl 1\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩\n    | succ _ => exact ⟨fun _ => rfl, fun _ => rfl⟩\n",
                ),
                (
                    "R23DsimpNatAddZero.lean",
                    arr2_hdr
                    + "theorem bypass (k : Nat) : Arr2 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      case h2 => intro _; dsimp [Nat.add_zero]\n      case h1 => intro _; exact Eq.refl 1\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩\n    | succ _ => exact ⟨fun _ => rfl, fun _ => rfl⟩\n",
                ),
                (
                    "R23DsimpDoneInCase.lean",
                    arr2_hdr
                    + "theorem bypass (k : Nat) : Arr2 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      case h2 => intro _; dsimp; done\n      case h1 => intro _; exact Eq.refl 1\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩\n    | succ _ => exact ⟨fun _ => rfl, fun _ => rfl⟩\n",
                ),
                (
                    "R23AndDsimpDone.lean",
                    pand_hdr
                    + "theorem bypass (k : Nat) : PAnd (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      · constructor\n        case right => dsimp; done\n        case left => exact Eq.refl 1\n      · exact rfl\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨⟨rfl, rfl⟩, rfl⟩\n    | succ _ => exact ⟨⟨rfl, rfl⟩, rfl⟩\n",
                ),
                (
                    "R23DsimpUnbulletedNextEq.lean",
                    twoeq_hdr
                    + "theorem bypass (k : Nat) : TwoEq (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      dsimp\n      exact Eq.refl 1\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R23CtorBracesIntroDsimp.lean",
                    arr2first_hdr
                    + "theorem bypass (k : Nat) : Arr2First (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      { intro _; dsimp }\n      { intro _; exact Eq.refl 1 }\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩\n    | succ _ => exact ⟨fun _ => rfl, fun _ => rfl⟩\n",
                ),
                (
                    "R23CtorCaseBracesDsimp.lean",
                    arr2_hdr
                    + "theorem bypass (k : Nat) : Arr2 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      case h2 => { intro _; dsimp }\n      case h1 => { intro _; exact Eq.refl 1 }\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩\n    | succ _ => exact ⟨fun _ => rfl, fun _ => rfl⟩\n",
                ),
                (
                    "R23DsimpFollowedByBraces.lean",
                    arr2_hdr
                    + "theorem bypass (k : Nat) : Arr2 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      case h2 => intro _; dsimp\n      { intro _; exact Eq.refl 1 }\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩\n    | succ _ => exact ⟨fun _ => rfl, fun _ => rfl⟩\n",
                ),
                (
                    "R23FirstInlineThenMultiline.lean",
                    bundle2_hdr + "theorem bypass : Bundle2 (0 + 0) := by\n  first | rw [Nat.succ_eq_add_one]\n        | exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R23SemiFirstFallback.lean",
                    bundle2_hdr + "theorem bypass : Bundle2 (0 + 0) := by\n  constructor; exact rfl; first | rw [Nat.succ_eq_add_one] | exact rfl\n",
                ),
                (
                    "R23ParenFirstFallback.lean",
                    bundle2_hdr + "theorem bypass : Bundle2 (0 + 0) := by\n  (first | rw [Nat.succ_eq_add_one] | exact ⟨rfl, rfl⟩)\n",
                ),
                (
                    "R23CtorAllFirstFallback.lean",
                    bundle2_hdr + "theorem bypass : Bundle2 (0 + 0) := by\n  constructor <;> first | rw [Nat.succ_eq_add_one] | rfl\n",
                ),
                (
                    "R23TryBracesRw.lean",
                    bundle2_hdr + "theorem bypass : Bundle2 (0 + 0) := by\n  try { rw [Nat.succ_eq_add_one] }\n  exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R23ParenTryRw.lean",
                    bundle2_hdr + "theorem bypass : Bundle2 (0 + 0) := by\n  (try rw [Nat.succ_eq_add_one])\n  exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R23TryNewlineRw.lean",
                    bundle2_hdr + "theorem bypass : Bundle2 (0 + 0) := by\n  try\n    rw [Nat.succ_eq_add_one]\n  exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R23CtorSemiParenTryRw.lean",
                    bundle2_hdr + "theorem bypass : Bundle2 (0 + 0) := by\n  constructor; exact rfl; (try rw [Nat.succ_eq_add_one]); exact rfl\n",
                ),
                (
                    "R23BulletParenTryRw.lean",
                    bundle2_hdr + "theorem bypass : Bundle2 (0 + 0) := by\n  constructor\n  · (try rw [Nat.succ_eq_add_one]); rfl\n  · rfl\n",
                ),
                (
                    "R23LetShadowInField.lean",
                    natarrlet_hdr
                    + "theorem bypass (k : Nat) : NatArrLet (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨rfl, rfl⟩\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R23LetShadowUnderForall.lean",
                    natarrlet_f_hdr
                    + "theorem bypass (k : Nat) : NatArrLetF (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨fun _ => rfl, rfl⟩\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => rfl, rfl⟩\n    | succ _ => exact ⟨fun _ => rfl, rfl⟩\n",
                ),
                (
                    "R23LetShadowUnannot.lean",
                    natarrlet_u_hdr
                    + "theorem bypass (k : Nat) : NatArrLetU (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨rfl, rfl⟩\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
            )
            for fname, body in r23_bundler_fail_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertTrue(scan_parameterized_prop_bundlers(body), msg=f"{fname} missed by bundler scanner")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 3. Lean positive PASS controls
            r23_lean_pass_cases = (
                (
                    "R23PosConcreteTryRwThenRealRw.lean",
                    bundle2_hdr + "theorem ok : Bundle2 (0 + 0) := by\n  try rw [Nat.succ_eq_add_one]\n  rw [Nat.zero_add]\n  exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R23PosFirstBothRwInline.lean",
                    bundle2_hdr + "theorem ok : Bundle2 (0 + 0) := by\n  first | rw [Nat.succ_eq_add_one] | rw [Nat.zero_add]; exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R23PosFirstBothRwMultiline.lean",
                    bundle2_hdr + "theorem ok : Bundle2 (0 + 0) := by\n  first | rw [Nat.succ_eq_add_one]\n        | rw [Nat.zero_add]; exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R23PosDsimpNonDefeqThenLemma.lean",
                    arrnd_hdr
                    + "theorem ok (n : Nat) : ArrND n := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      · intro _; dsimp; exact Nat.zero_add n\n      · rfl\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨fun _ => rfl, rfl⟩\n    | succ _ => exact ⟨fun _ => Nat.zero_add _, rfl⟩\n",
                ),
                (
                    "R23PosLetShadowGenuine.lean",
                    natarrlet_hdr
                    + "theorem ok (n : Nat) : NatArrLet n := by\n  cases n with\n"
                    "  | zero => exact ⟨rfl, rfl⟩\n  | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
            )
            for fname, body in r23_lean_pass_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertEqual(scan_native_decide_and_vacuous_true(body), [], msg=f"{fname} false vacuous hit")
                self.assertEqual(scan_parameterized_prop_bundlers(body), [], msg=f"{fname} false bundler hit")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "PASS", msg=f"{fname} false-failed T1-LEAN-04: {res.summary}")

            # 4. Intake (Rev1 #1-#2, Rev2 #4-#5, Ch2 Challenges 1-3): unit + end-to-end T1-INTAKE-07
            (root / "cached" / "drive_docs").mkdir(parents=True)
            (root / "docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )
            m1b = root / "docs" / "M1B_R23.md"
            c_ok_bytes = b"Source C valid markdown R23\n"
            c_sha = hashlib.sha256(c_ok_bytes).hexdigest()
            e_ok_bytes = b"Source E valid markdown R23\n"
            e_sha = hashlib.sha256(e_ok_bytes).hexdigest()
            c_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            c_html_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.html"
            e_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.md"
            e_html_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"

            # 4a. Colon-prefixed & bare partial-status headers (`C=403_html` unreported -> MUST FAIL)
            c_html_path.write_text("<!DOCTYPE html><html><title>Access Denied</title></html>", encoding="utf-8")
            e_ok_path.write_bytes(e_ok_bytes)
            for block in (
                f"- Summary: C (`{SOURCE_C_ID}`) done, D (`{SOURCE_D_ID}`) & E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied",
                f"- C (`{SOURCE_C_ID}`) checked, D (`{SOURCE_D_ID}`) and E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied",
            ):
                m1b.write_text(
                    block
                    + "\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"C leak on:\n{block}")
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_D_ID), msg=f"D lost on:\n{block}")
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"E lost on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Silent false-PASS when C=403 HTML on:\n{block}",
                )

            # 4b. Shared topic tails & middle-dash topic segments (`C=403_html` shared-reported, `E=ok` -> MUST PASS)
            for shared_block in (
                f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) Google Sign-In:\n  HTTP 403 Access Denied",
                f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) 403 errors:\n  HTTP 403 Access Denied",
                f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) HTTP 403:\n  HTTP 403 Access Denied",
                f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) inaccessible:\n  HTTP 403 Access Denied",
                f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) sign-in/auth:\n  HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`) — access blocker — E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`) — error log — E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied",
                f"- Summary: C (`{SOURCE_C_ID}`) ok, D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied",
            ):
                m1b.write_text(
                    shared_block
                    + "\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                is_c_ok_d_e = "C (`" + SOURCE_C_ID + "`) ok" in shared_block
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_C_ID), not is_c_ok_d_e, msg=shared_block)
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_D_ID), msg=shared_block)
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=shared_block)
                expected_st = "FAIL" if is_c_ok_d_e else "PASS"
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    expected_st,
                    msg=f"Unexpected status on:\n{shared_block}",
                )

            # 4c. `E=403_html` unreported with generalized topic tails, middle-dash, & indefinite A/An/quantifiers -> MUST FAIL
            c_html_path.unlink()
            e_ok_path.unlink()
            c_ok_path.write_bytes(c_ok_bytes)
            e_html_path.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            for block in (
                f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) Google Sign-In:\n  C saved locally.\n  HTTP 403 Access Denied",
                f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) 403 errors:\n  C saved locally.\n  HTTP 403 Access Denied",
                f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) HTTP 403:\n  C saved locally.\n  HTTP 403 Access Denied",
                f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) inaccessible:\n  C saved locally.\n  HTTP 403 Access Denied",
                f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) sign-in/auth:\n  C saved locally.\n  HTTP 403 Access Denied",
                f"- Summary — C (`{SOURCE_C_ID}`) ok, D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) Google Sign-In:\n  C saved locally.\n  HTTP 403 Access Denied",
                f"- Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`) — access blocker — E (`{SOURCE_E_ID}`):\n  C saved locally.\n  HTTP 403 Access Denied",
                f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Result: A blocked HTTP 403 response was logged.",
                f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Logs show A blocked HTTP 403 response was logged.",
                f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): We noticed that A blocked HTTP 403 response was logged.",
                f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Note A blocked HTTP 403 response was logged.",
                f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Failed because A blocked HTTP 403 response was logged.",
                f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Failed when An HTTP 403 error was returned.",
                f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): There was A blocked HTTP 403 response.",
                f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Today A blocked HTTP 403 response was logged.",
                f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Despite retries A blocked HTTP 403 response was logged.",
                f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): (1) A blocked HTTP 403 response was logged.",
                f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Verification logged An HTTP 403 error.",
                f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Verification ran — A blocked HTTP 403 response was logged.",
                f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Log entry: An HTTP 403 error was logged.",
                f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): One of the sources returned HTTP 403.",
                f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): One of the sources returned HTTP 403.",
            ):
                m1b.write_text(
                    block
                    + "\n"
                    + f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_A_ID), msg=f"A leak on:\n{block}")
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"E leak on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Silent false-PASS when E=403 HTML on:\n{block}",
                )

            # 4d. Positive PASS controls (`C ok, D, E` with E=403_html; `N/A — HTTP 403`; genuine `A returned HTTP 403`)
            for pos_block, exp_a, exp_c, exp_d, exp_e in (
                (f"- Summary: C (`{SOURCE_C_ID}`) ok, D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False, False, True, True),
                (f"- C (`{SOURCE_C_ID}`) ok, D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False, False, True, True),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Fallback N/A — HTTP 403 Access Denied", True, False, False, True),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Verification ran. A returned HTTP 403. E returned HTTP 403.", True, False, False, True),
            ):
                m1b.write_text(
                    pos_block
                    + "\n"
                    + f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), exp_a, msg=pos_block)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_C_ID), exp_c, msg=pos_block)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_D_ID), exp_d, msg=pos_block)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_E_ID), exp_e, msg=pos_block)
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "PASS",
                    msg=f"False FAIL on valid intake block:\n{pos_block}",
                )

            # 5. T3-CONS-05 uppercase `SHA256:` prefix in `audit_report.json` (`PASS` matching, `FAIL` stale)
            (root / "lean" / "InfoGeometry").mkdir(parents=True)
            foo_lean = root / "lean" / "InfoGeometry" / "FooR23.lean"
            foo_lean.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n-- r23\n", encoding="utf-8")
            foo_sha = hashlib.sha256(foo_lean.read_bytes()).hexdigest().upper()
            aud_json = root / "audit_report.json"
            aud_json.write_text(
                json.dumps({"artifact_hashes": {"lean/InfoGeometry/FooR23.lean": f"SHA256:{foo_sha}"}}),
                encoding="utf-8",
            )
            foo_target = [ResolvedTarget(foo_lean, "InfoGeometry.FooR23", None, True)]
            aud_arts = DiscoveredArtifacts([], [], [], [aud_json], [], [], [])
            self.assertEqual(
                check_t3_cons_05_audit_report_hashes(root, aud_arts, foo_target).status,
                "PASS",
            )
            aud_json.write_text(
                json.dumps({"artifact_hashes": {"lean/InfoGeometry/FooR23.lean": "SHA256:" + ("0" * 64)}}),
                encoding="utf-8",
            )
            self.assertEqual(
                check_t3_cons_05_audit_report_hashes(root, aud_arts, foo_target).status,
                "FAIL",
            )

    def test_regression_r24_iter23_findings(self) -> None:
        extract_script = REPO_ROOT / "tools" / "infra" / "extract_aistudio_math.py"
        bundle2_hdr = "structure Bundle2 (n : Nat) : Prop where\n  p1 : 0 = 0\n  p2 : 0 + n = n\n"
        bundle_ab_hdr = "structure BundleAB (a b : Nat) : Prop where\n  p1 : a = a\n  p2 : b + 0 = b\n"
        arr2_hdr = "structure Arr2 (n : Nat) : Prop where\n  h1 : (0 = 0) → (1 = 1)\n  h2 : (0 = 0) → (0 = 0)\n"
        arrnd_hdr = "structure ArrND (n : Nat) : Prop where\n  h : (0 = 0) → (0 + n + 0 = n)\n  h2 : n = n\n"
        arrnd2_hdr = "structure ArrND2 (n : Nat) : Prop where\n  h1 : (0 = 0) → (0 + n + 0 = n)\n  h2 : (0 + 0 = 0) → (0 = 0)\n"
        have_prop_hdr = "structure NatArrHave2 (n : Nat) : Prop where\n  h : have n : Prop := True; n\n  h2 : n = n\n"
        have_nat_hdr = "structure HaveShadow (n : Nat) : Prop where\n  h : have n : Nat := 1; n = 1\n  h2 : n = n\n"
        let_noannot_hdr = "structure LetNatNoAnnot (k : Nat) : Prop where\n  h : let n := 0; n + 0 = n\n  h2 : k = k\n"
        let_nl_noannot_hdr = "structure LetNL3 (k : Nat) : Prop where\n  h : let n := 1\n      n + 0 = n\n  h2 : k = k\n"
        let_tuple_hdr = "structure LetTuple (n : Nat) : Prop where\n  h : let (n, k) := (0, 0); n + 0 = n ∧ k = k\n  h2 : n = n\n"

        # 1. Capture-avoiding `have` shadowing & `let`/`have` parameter binder alpha-renaming
        self.assertEqual(
            _subst_lean_expr_capture_avoiding("have n : Prop := True; n", {"n": "(0 + 0)"}),
            "have n : Prop := True; n",
        )
        self.assertEqual(
            _subst_lean_expr_capture_avoiding("have n : Nat := 1; n = 1", {"n": "(0 + 0)"}),
            "have n : Nat := 1; n = 1",
        )
        self.assertEqual(
            _subst_lean_expr_capture_avoiding("let f (m : Nat) : Nat := m + n; f 0 = n", {"n": "m"}),
            "let f (m_1 : Nat) : Nat := m_1 + m; f 0 = m",
        )
        self.assertEqual(
            _subst_lean_expr_capture_avoiding("have f (m : Nat) : Nat := m + n; f 0 = n", {"n": "m"}),
            "have f (m_1 : Nat) : Nat := m_1 + m; f 0 = m",
        )
        self.assertEqual(
            _classify_suffices_prop_detail("let n := 0; n + 0 = n", nat_vars=set())[1],
            "eq_refl",
        )
        self.assertEqual(
            _classify_suffices_prop_detail("let (n, k) := (0, 0); n + 0 = n ∧ k = k", nat_vars=set())[1],
            "conj_refl",
        )
        self.assertEqual(
            _classify_suffices_prop_detail("let (n, k) := ((-1 : Int), (0 : Int)); n + 0 = n", nat_vars={"n"})[1],
            "other",
        )

        with tempfile.TemporaryDirectory(prefix="ec_reg_r24_") as td:
            root = Path(td)

            # 2. Lean bundler FAIL cases (have shadowing, unannotated/tuple let, named+pos params, dsimp modifiers, multiline try, first ctor bullets)
            r24_bundler_fail_cases = (
                (
                    "R24HaveShadowProp.lean",
                    have_prop_hdr
                    + "theorem bypass (k : Nat) : NatArrHave2 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨True.intro, rfl⟩\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨True.intro, rfl⟩\n    | succ _ => exact ⟨True.intro, rfl⟩\n",
                ),
                (
                    "R24HaveShadowNat.lean",
                    have_nat_hdr
                    + "theorem bypass (k : Nat) : HaveShadow (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨rfl, rfl⟩\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R24NamedThenPosParam.lean",
                    bundle_ab_hdr
                    + "theorem bypass (k : Nat) : BundleAB (a := 0) (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨rfl, rfl⟩\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨rfl, Nat.add_zero _⟩\n    | succ _ => exact ⟨rfl, Nat.add_zero _⟩\n",
                ),
                (
                    "R24LetNoAnnotNat.lean",
                    let_noannot_hdr
                    + "theorem bypass (m : Nat) : LetNatNoAnnot (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨rfl, rfl⟩\n    exact rfl\n"
                    "  | cases m with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R24LetNewlineNoAnnot.lean",
                    let_nl_noannot_hdr
                    + "theorem bypass (m : Nat) : LetNL3 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨rfl, rfl⟩\n    exact rfl\n"
                    "  | cases m with\n    | zero => exact ⟨rfl, rfl⟩\n    | succ _ => exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R24LetTupleShadow.lean",
                    let_tuple_hdr
                    + "theorem bypass (m : Nat) : LetTuple (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      exact ⟨⟨rfl, rfl⟩, rfl⟩\n    exact rfl\n"
                    "  | cases m with\n    | zero => exact ⟨⟨rfl, rfl⟩, rfl⟩\n    | succ _ => exact ⟨⟨rfl, rfl⟩, rfl⟩\n",
                ),
                (
                    "R24DsimpAtStar.lean",
                    arr2_hdr
                    + "theorem bypass (k : Nat) : Arr2 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      case h2 => intro _; dsimp at *\n      case h1 => intro _; exact Eq.refl 1\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩\n    | succ _ => exact ⟨fun _ => rfl, fun _ => rfl⟩\n",
                ),
                (
                    "R24DsimpOnlyAddZeroAtStar.lean",
                    arr2_hdr
                    + "theorem bypass (k : Nat) : Arr2 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      case h2 => intro _; dsimp only [Nat.add_zero] at *\n      case h1 => intro _; exact Eq.refl 1\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩\n    | succ _ => exact ⟨fun _ => rfl, fun _ => rfl⟩\n",
                ),
                (
                    "R24DsimpOnlyAtHTurnstile.lean",
                    arr2_hdr
                    + "theorem bypass (k : Nat) : Arr2 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      intro h\n      dsimp only at h ⊢\n      intro _\n      exact Eq.refl 0\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩\n    | succ _ => exact ⟨fun _ => rfl, fun _ => rfl⟩\n",
                ),
                (
                    "R24DsimpPlusZeta.lean",
                    arr2_hdr
                    + "theorem bypass (k : Nat) : Arr2 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      case h2 => intro _; dsimp +zeta\n      case h1 => intro _; exact Eq.refl 1\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩\n    | succ _ => exact ⟨fun _ => rfl, fun _ => rfl⟩\n",
                ),
                (
                    "R24DsimpPlusZetaDelta.lean",
                    arr2_hdr
                    + "theorem bypass (k : Nat) : Arr2 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      case h2 => intro _; dsimp +zetaDelta\n      case h1 => intro _; exact Eq.refl 1\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩\n    | succ _ => exact ⟨fun _ => rfl, fun _ => rfl⟩\n",
                ),
                (
                    "R24DsimpConfigEmpty.lean",
                    arr2_hdr
                    + "theorem bypass (k : Nat) : Arr2 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      intro _\n      dsimp (config := {})\n      intro _\n      exact Eq.refl 0\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩\n    | succ _ => exact ⟨fun _ => rfl, fun _ => rfl⟩\n",
                ),
                (
                    "R24DsimpConfigZeta.lean",
                    arr2_hdr
                    + "theorem bypass (k : Nat) : Arr2 (0 + 0) := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      intro _\n      dsimp (config := { zeta := true })\n      intro _\n      exact Eq.refl 0\n    exact rfl\n"
                    "  | cases k with\n    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩\n    | succ _ => exact ⟨fun _ => rfl, fun _ => rfl⟩\n",
                ),
                (
                    "R24ParenTryNewlineRw.lean",
                    bundle2_hdr
                    + "theorem bypass : Bundle2 (0 + 0) := by\n  (try\n    rw [Nat.succ_eq_add_one])\n  exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R24SemiTryNewlineRw.lean",
                    bundle2_hdr
                    + "theorem bypass : Bundle2 (0 + 0) := by\n  constructor; exact rfl; try\n    rw [Nat.succ_eq_add_one]\n  exact rfl\n",
                ),
                (
                    "R24CtorAllTryNewlineRw.lean",
                    bundle2_hdr
                    + "theorem bypass : Bundle2 (0 + 0) := by\n  constructor <;> try\n    rw [Nat.succ_eq_add_one]\n  exact rfl\n  exact rfl\n",
                ),
                (
                    "R24PipeTryNewlineRw.lean",
                    bundle2_hdr
                    + "theorem bypass : Bundle2 (0 + 0) := by\n  first\n  | rw [Nat.succ_eq_add_one]\n  | try\n      rw [Nat.succ_eq_add_one]\n    exact ⟨rfl, rfl⟩\n",
                ),
                (
                    "R24FirstCtorBullets.lean",
                    bundle2_hdr
                    + "theorem bypass : Bundle2 (0 + 0) := by\n  first\n  | rw [Nat.succ_eq_add_one]\n  | constructor\n    · exact rfl\n    · exact rfl\n",
                ),
                (
                    "R24FirstCtorDsimpAtStarBullets.lean",
                    bundle2_hdr
                    + "theorem bypass : Bundle2 (0 + 0) := by\n  first\n  | rw [Nat.succ_eq_add_one]\n  | constructor\n    · dsimp at *\n    · rfl\n",
                ),
            )
            for fname, body in r24_bundler_fail_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertTrue(scan_parameterized_prop_bundlers(body), msg=f"{fname} missed by bundler scanner")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "FAIL", msg=f"{fname} bypassed T1-LEAN-04")

            # 3. Lean positive PASS controls (bullet { ... } block, dsimp at h only, first ctor bullets with real rw, first semi real rw)
            r24_lean_pass_cases = (
                (
                    "R24PosBulletBracesNonTriv.lean",
                    arrnd_hdr
                    + "theorem ok (n : Nat) : ArrND n := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      · { intro _; dsimp; exact Nat.zero_add n }\n      · rfl\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨fun _ => rfl, rfl⟩\n    | succ _ => exact ⟨fun _ => Nat.zero_add _, rfl⟩\n",
                ),
                (
                    "R24PosDsimpAtHypOnly.lean",
                    arrnd2_hdr
                    + "theorem ok (n : Nat) : ArrND2 n := by\n  first\n"
                    "  | suffices _ : 0 = 0 by\n      constructor\n      case h2 => intro h; dsimp at h; exact Eq.refl 0\n      case h1 => intro _; exact Nat.zero_add n\n    exact rfl\n"
                    "  | cases n with\n    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩\n    | succ _ => exact ⟨fun _ => Nat.zero_add _, fun _ => rfl⟩\n",
                ),
                (
                    "R24PosFirstCtorBulletsRealRw.lean",
                    bundle2_hdr
                    + "theorem ok : Bundle2 (0 + 0) := by\n  first\n"
                    "  | rw [Nat.succ_eq_add_one]\n  | constructor\n    · exact rfl\n    · rw [Nat.zero_add]\n",
                ),
                (
                    "R24PosFirstSemiRealRw.lean",
                    bundle2_hdr
                    + "theorem ok : Bundle2 (0 + 0) := by\n"
                    "  constructor; first | rw [Nat.succ_eq_add_one] | rfl; rw [Nat.zero_add]\n",
                ),
            )
            for fname, body in r24_lean_pass_cases:
                fp = root / fname
                fp.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n" + body, encoding="utf-8")
                self.assertEqual(scan_native_decide_and_vacuous_true(body), [], msg=f"{fname} false vacuous hit")
                self.assertEqual(scan_parameterized_prop_bundlers(body), [], msg=f"{fname} false bundler hit")
                res = check_t1_lean_04_placeholder_and_vacuity(
                    REPO_ROOT, [ResolvedTarget(fp, fname, None, True)], strict_live=True
                )
                self.assertEqual(res.status, "PASS", msg=f"{fname} false-failed T1-LEAN-04: {res.summary}")

            # 4. Intake (Ch2 Challenges 1-3, Rev2 #3-#4)
            (root / "cached" / "drive_docs").mkdir(parents=True)
            (root / "docs").mkdir(parents=True)
            d_bytes = json.dumps(
                {
                    "runSettings": {},
                    "systemInstruction": {},
                    "chunkedPrompt": {"chunks": [{"role": "user", "text": "x", "createTime": "2026-11-22T10:00:00Z"}]},
                }
            ).encode("utf-8")
            d_path = root / "cached" / f"aistudio_prompt_{SOURCE_D_ID}.json"
            d_path.write_bytes(d_bytes)
            d_sha = hashlib.sha256(d_bytes).hexdigest()
            subprocess.run(
                [sys.executable, str(extract_script), str(d_path), "--output-dir", str(root / "cached" / "aistudio_extracts")],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                check=True,
            )
            claims_tail = (
                "\n| Claim ID | Source Provenance | Statement | Carrier | Classification & Bucket | Notes |\n"
                "|---|---|---|---|---|---|\n"
                "| `CDE-1` | D | ok | `R` | `[kernel_verified]` (`BUCKET 1`) | ok |\n"
                "| `CDE-2` | D | debt | `Inf` | `[bucket_3_open_debt]` (`BUCKET 3`) | open |\n"
            )
            m1b = root / "docs" / "M1B_R24.md"
            c_ok_bytes = b"Source C valid markdown R24\n"
            c_sha = hashlib.sha256(c_ok_bytes).hexdigest()
            e_ok_bytes = b"Source E valid markdown R24\n"
            e_sha = hashlib.sha256(e_ok_bytes).hexdigest()
            c_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.md"
            c_html_path = root / "cached" / "drive_docs" / f"{SOURCE_C_ID}.html"
            e_ok_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.md"
            e_html_path = root / "cached" / "drive_docs" / f"{SOURCE_E_ID}.html"

            # 4a. `&` / `and` / `/` status-bearing headers (`C=403_html` unreported -> MUST FAIL)
            c_html_path.write_text("<!DOCTYPE html><html><title>Access Denied</title></html>", encoding="utf-8")
            e_ok_path.write_bytes(e_ok_bytes)
            for block, exp_d in (
                (f"- Summary: C (`{SOURCE_C_ID}`) ok & E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False),
                (f"- Summary: C (`{SOURCE_C_ID}`) ok and E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False),
                (f"- C (`{SOURCE_C_ID}`) ok & E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False),
                (f"- C (`{SOURCE_C_ID}`) ok and E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False),
                (f"- Summary: C (`{SOURCE_C_ID}`) done and D (`{SOURCE_D_ID}`) & E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", True),
                (f"- Summary: C (`{SOURCE_C_ID}`) checked / D (`{SOURCE_D_ID}`) and E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", True),
                (f"- Summary: C (`{SOURCE_C_ID}`) ok / D (`{SOURCE_D_ID}`) / E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", True),
                (f"- Summary: C (`{SOURCE_C_ID}`) available & E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False),
                (f"- Summary: C (`{SOURCE_C_ID}`) present and E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False),
                (f"- Summary: C (`{SOURCE_C_ID}`) skipped & E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False),
                (f"- Summary: C (`{SOURCE_C_ID}`) done and D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", True),
            ):
                m1b.write_text(
                    block
                    + "\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertFalse(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=f"C leak on:\n{block}")
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_D_ID), exp_d, msg=f"D mismatch on:\n{block}")
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=f"E lost on:\n{block}")
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Silent false-PASS when C=403 HTML on:\n{block}",
                )

            # 4b. Shared middle-dash comma & shared `(HTTP 403)` parenthetical headers (`C=403_html` shared -> MUST PASS)
            for shared_block in (
                f"- Sources C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`) — HTTP 403, access blocker — E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied",
                f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) — access blocker (HTTP 403):\n  HTTP 403 Access Denied",
                f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) (HTTP 403):\n  HTTP 403 Access Denied",
            ):
                m1b.write_text(
                    shared_block
                    + "\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + f"- Source E (`{SOURCE_E_ID}`): {len(e_ok_bytes)} bytes, 1 lines, sha256 `{e_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_C_ID), msg=shared_block)
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_D_ID), msg=shared_block)
                self.assertTrue(_has_explicit_blocker_report([m1b], SOURCE_E_ID), msg=shared_block)
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "PASS",
                    msg=f"False FAIL on valid shared intake header:\n{shared_block}",
                )

            # 4c. `E=403_html` unreported with `(HTTP 403)` + `C saved locally.`, `(ok)`/`(403)` per-source, multi-line `pre_breakdown_lines` A/An, & demonstrative/partitive quantifiers -> MUST FAIL
            c_html_path.unlink()
            e_ok_path.unlink()
            c_ok_path.write_bytes(c_ok_bytes)
            e_html_path.write_text("<!DOCTYPE html><html><title>Sign-in</title></html>", encoding="utf-8")
            for block, exp_a, exp_c, exp_d, exp_e in (
                (f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) — access blocker (HTTP 403):\n  C saved locally.\n  HTTP 403 Access Denied", False, False, False, False),
                (f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) (HTTP 403):\n  C saved locally.\n  HTTP 403 Access Denied", False, False, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) ok, C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) — access blocker (HTTP 403):\n  C saved locally.\n  HTTP 403 Access Denied", False, False, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`):\n  An HTTP 403 error was returned.", False, False, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`):\n  A blocked HTTP 403 response was logged.", False, False, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): One of these sources returned HTTP 403.", False, False, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): One of those sources returned HTTP 403.", False, False, False, False),
                (f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`): One of the two sources returned HTTP 403.", False, False, False, False),
                (f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`):\n  One of these sources returned HTTP 403.", False, False, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Several sources returned HTTP 403.", False, False, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Multiple sources returned HTTP 403.", False, False, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): Certain sources returned HTTP 403.", False, False, False, False),
                (f"- Sources A (`{SOURCE_A_ID}`) & E (`{SOURCE_E_ID}`): At least one source returned HTTP 403.", False, False, False, False),
            ):
                m1b.write_text(
                    block
                    + "\n"
                    + f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), exp_a, msg=block)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_C_ID), exp_c, msg=block)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_D_ID), exp_d, msg=block)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_E_ID), exp_e, msg=block)
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "FAIL",
                    msg=f"Silent false-PASS when E=403 HTML on:\n{block}",
                )

            # 4d. Positive PASS controls (`C done and D, E` with E=403_html & D=ok; `C ok, D ok, E (403)` with E=403_html; `Both sources` multi-line)
            for pos_block, exp_a, exp_c, exp_d, exp_e in (
                (f"- Summary: C (`{SOURCE_C_ID}`) done and D (`{SOURCE_D_ID}`), E (`{SOURCE_E_ID}`):\n  HTTP 403 Access Denied", False, False, True, True),
                (f"- Summary: C (`{SOURCE_C_ID}`) ok, D (`{SOURCE_D_ID}`) ok, E (`{SOURCE_E_ID}`) (403):\n  HTTP 403 Access Denied", False, False, False, True),
                (f"- Summary — C (`{SOURCE_C_ID}`), D (`{SOURCE_D_ID}`), and E (`{SOURCE_E_ID}`) (ok):\n  C saved locally.\n  HTTP 403 Access Denied", False, False, False, True),
                (f"- Sources C (`{SOURCE_C_ID}`) & E (`{SOURCE_E_ID}`):\n  An HTTP 403 error was logged on one attempt.\n  Both returned HTTP 403 Access Denied.", False, True, False, True),
            ):
                m1b.write_text(
                    pos_block
                    + "\n"
                    + f"- Source C (`{SOURCE_C_ID}`): {len(c_ok_bytes)} bytes, 1 lines, sha256 `{c_sha}`\n"
                    + f"- Source D `{SOURCE_D_ID}`: {len(d_bytes)} bytes, 1 chunks, sha256 `{d_sha}`\n"
                    + claims_tail,
                    encoding="utf-8",
                )
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_A_ID), exp_a, msg=pos_block)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_C_ID), exp_c, msg=pos_block)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_D_ID), exp_d, msg=pos_block)
                self.assertEqual(_has_explicit_blocker_report([m1b], SOURCE_E_ID), exp_e, msg=pos_block)
                self.assertEqual(
                    check_t1_intake_07_additional_sources_f10(
                        root, [m1b], [], "live84", require_all_sources=True, extract_script_override=extract_script
                    ).status,
                    "PASS",
                    msg=f"False FAIL on valid intake block:\n{pos_block}",
                )

            # 5. T3-CONS-05 `SHA256: <hex>` with space after colon (`PASS` matching, `FAIL` stale)
            (root / "lean" / "InfoGeometry").mkdir(parents=True)
            foo_lean = root / "lean" / "InfoGeometry" / "FooR24.lean"
            foo_lean.write_text(REQUIRED_LEAN_COPYRIGHT_HEADER + "\n-- r24\n", encoding="utf-8")
            foo_sha = hashlib.sha256(foo_lean.read_bytes()).hexdigest().upper()
            aud_json = root / "audit_report.json"
            aud_json.write_text(
                json.dumps({"artifact_hashes": {"lean/InfoGeometry/FooR24.lean": f"SHA256: {foo_sha}"}}),
                encoding="utf-8",
            )
            foo_target = [ResolvedTarget(foo_lean, "InfoGeometry.FooR24", None, True)]
            aud_arts = DiscoveredArtifacts([], [], [], [aud_json], [], [], [])
            self.assertEqual(
                check_t3_cons_05_audit_report_hashes(root, aud_arts, foo_target).status,
                "PASS",
            )
            aud_json.write_text(
                json.dumps({"artifact_hashes": {"lean/InfoGeometry/FooR24.lean": "SHA256: " + ("0" * 64)}}),
                encoding="utf-8",
            )
            self.assertEqual(
                check_t3_cons_05_audit_report_hashes(root, aud_arts, foo_target).status,
                "FAIL",
            )

    @unittest.skipUnless(os.environ.get("EPISTEMIC_E2E_MODE") == "full", "Full Tier 1-4 live run requires EPISTEMIC_E2E_MODE=full")
    def test_tier4_full_acceptance_when_enabled(self) -> None:
        report = run_acceptance_pipeline(repo_root=REPO_ROOT, tier="all", source_b_mode="live84", all_sources=True)
        self.assertEqual(report["exit_code"], 0, msg=json.dumps(report, indent=2))


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "4-tier opaque-box E2E acceptance suite for Drive 13ED/12bA/1wzq & AI Studio 1v8J/1VUS epistemic compilation.\n"
            "Exit codes: 0=pass, 1=check failure, 2=CLI usage error or missing required live targets."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--self-test", action="store_true", help="Run fast non-destructive baseline + synthetic negative unittest suite (<5s, zero lake build).")
    parser.add_argument("--dry-run", action="store_true", help="Run Tiers 1-3 read-only checks + print serialized Tier 4 commands without running lake/lean.")
    parser.add_argument("--tier", choices=("1", "2", "3", "4", "all"), default="all", help="Select verification tier(s) (default: all).")
    parser.add_argument(
        "--source-b-mode",
        choices=("baseline45", "live84", "auto"),
        default=None,
        help="Source B mode (default: auto in --self-test/--dry-run, live84 in full Tier 1-4 acceptance).",
    )
    parser.add_argument("--all-sources", action="store_true", help="Enforce F10 5-source intake/blocker checks (A, B, C, D, E) regardless of Source B mode.")
    parser.add_argument("--targets", nargs="+", action="extend", default=None, help="Explicit .lean file paths and/or dotted InfoGeometry.* module names.")
    parser.add_argument("--manifest", nargs="+", action="extend", default=None, help="One or more M1/M1b contract/ledger JSON or Markdown paths.")
    parser.add_argument("--json-out", type=Path, default=None, help="Path to write JSON report (default under scratch/epistemic_compilation_e2e/reports/).")
    parser.add_argument("--md-out", type=Path, default=None, help="Path to write Markdown report (default under scratch/epistemic_compilation_e2e/reports/).")
    parser.add_argument("--no-reports", action="store_true", help="Disable writing JSON/Markdown report files.")
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_arg_parser()
    args = parser.parse_args(argv)

    if args.self_test and args.dry_run:
        print("[epistemic_e2e] ERROR: --self-test and --dry-run are mutually exclusive", file=sys.stderr)
        return 2

    if args.self_test:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(TestEpistemicCompilationE2E)
        runner = unittest.TextTestRunner(verbosity=2)
        res = runner.run(suite)
        return 0 if res.wasSuccessful() else 1

    mode = args.source_b_mode or ("auto" if args.dry_run else "live84")
    report = run_acceptance_pipeline(
        repo_root=REPO_ROOT,
        tier=args.tier,
        source_b_mode=mode,
        raw_targets=args.targets,
        manifest_args=args.manifest,
        dry_run=args.dry_run,
        all_sources=args.all_sources,
    )
    if report.get("error"):
        print(f"[epistemic_e2e] ERROR: {report['error']}", file=sys.stderr)
        return int(report["exit_code"])

    if not args.no_reports:
        suffix = f"tier_{args.tier}_{report['effective_source_b_mode']}" + ("_dry_run" if args.dry_run else "")
        if args.json_out is None or args.md_out is None:
            DEFAULT_REPORTS_DIR.mkdir(parents=True, exist_ok=True)
        json_out = args.json_out or (DEFAULT_REPORTS_DIR / f"report_{suffix}.json")
        md_out = args.md_out or (DEFAULT_REPORTS_DIR / f"report_{suffix}.md")
        json_out.parent.mkdir(parents=True, exist_ok=True)
        md_out.parent.mkdir(parents=True, exist_ok=True)
        json_out.write_text(json.dumps(report, indent=2), encoding="utf-8")
        md_out.write_text(render_markdown_report(report), encoding="utf-8")

    for o in report["outcomes"]:
        print(f"[{o['status']}] {o['check_id']} (Tier {o['tier']}/{o['feature']}): {o['summary']}")
        if o["check_id"] == "T4-E2E-DRY-RUN" and o.get("details", {}).get("planned_commands"):
            cmds = o["details"]["planned_commands"]
            print("  Planned Tier 4 serialized commands:")
            for group, cmd_list in cmds.items():
                for c in cmd_list:
                    print(f"    [{group}] {' '.join(c)}")

    s = report["summary"]
    print(
        f"[epistemic_e2e] tier={args.tier} source_b={report['effective_source_b_mode']} dry_run={args.dry_run} "
        f"passed={s['passed']} failed={s['failed']} skipped={s['skipped']} exit={report['exit_code']}"
    )
    return int(report["exit_code"])


if __name__ == "__main__":
    raise SystemExit(main())
