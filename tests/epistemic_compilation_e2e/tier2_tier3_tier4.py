"""Tier 2 (Boundary/Corner), Tier 3 (Cross-Artifact Consistency), and Tier 4 (Serialized Acceptance)."""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from tests.epistemic_compilation_e2e import (
    BUCKET_ALLOWED_LABELS,
    CheckOutcome,
    DEFAULT_BUILD_LOCK_PATH,
    FORBIDDEN_CONCURRENT_DRAFTS,
    FORBIDDEN_RIEMANN_MASULLO_IMPORTS,
    KNOWN_COUNTERMODEL_IDS,
    PERMITTED_FOUNDATIONAL_AXIOMS,
    SOURCE_A_ID,
    SOURCE_A_REL,
    SOURCE_B_EXTRACT_DIR_REL,
    SOURCE_B_ID,
    SOURCE_B_REL,
)
from tests.epistemic_compilation_e2e.epistemic_checks import (
    DiscoveredArtifacts,
    MERMAID_BLOCK_RE,
    ParsedClaimRow,
    parse_mermaid_dag,
)
from tests.epistemic_compilation_e2e.intake_checks import run_subprocess_safe, sha256_file
from tests.epistemic_compilation_e2e.lean_checks import (
    _LEAN_IDENT_SEG,
    _LEAN_IDENT_SEG_RE,
    _LEAN_QUAL_IDENT,
    _LEAN_TERM_KEYWORDS,
    ResolvedTarget,
    check_lean_copyright_header,
    extract_lean_declarations,
    extract_lean_imports,
    extract_non_opaque_lean_declarations,
    lean_short_name,
    run_static_placeholder_vacuity_suite,
    split_lean_qual_ident,
    strip_lean_comments_and_strings,
)

FORBIDDEN_RM_IMPORT_RE = re.compile(
    r"(?:^|\.)RiemannMasullo\.(?:Ch0[5-9]|Ch1[0-2]|Challenge|Main)(?:[_.\s]|$)|_Printed|external_refs"
)


def _norm_claim_id(cid: str) -> str:
    return cid.replace("-", "_")


def _extract_obj_module_stems(objs: list[Any], known_stems: set[str] | None = None) -> list[str]:
    """Extract module stems from `Mod.obj` or `InfoGeometry.Ns.Mod.obj` strings."""
    stems: list[str] = []
    for o in objs:
        parts = split_lean_qual_ident(str(o))
        if len(parts) < 2:
            continue
        stem = None
        if known_stems:
            for cand in (parts[-2], parts[-1], parts[0]):
                if cand in known_stems:
                    stem = cand
                    break
        if stem is None:
            stem = parts[-2]
        if stem not in stems:
            stems.append(stem)
    return stems


# ---------------------------------------------------------------------------
# Tier 2: Boundary & Corner Cases (T2-BND-01 .. T2-BND-07)
# ---------------------------------------------------------------------------


def check_t2_bnd_01_turn10_drive_attachment(
    repo_root: Path,
    compilation_docs: list[Path],
) -> CheckOutcome:
    """T2-BND-01: Turn 10 driveDocument attachment (no text key, blank in transcript.md, linked to Source A)."""
    src_b = repo_root / SOURCE_B_REL
    transcript = repo_root / SOURCE_B_EXTRACT_DIR_REL / "transcript.md"
    if not src_b.is_file() or not transcript.is_file():
        return CheckOutcome("T2-BND-01", 2, "F2", "FAIL", "Missing Source B JSON or transcript.md")
    data = json.loads(src_b.read_text(encoding="utf-8"))
    cp = data.get("chunkedPrompt") if isinstance(data, dict) else None
    chunks = cp.get("chunks", []) if isinstance(cp, dict) else []
    if not isinstance(chunks, list) or len(chunks) < 10:
        return CheckOutcome("T2-BND-01", 2, "F2", "FAIL", f"Source B has only {len(chunks)} chunks (<10)")
    chunk10 = chunks[9]
    if not isinstance(chunk10, dict):
        return CheckOutcome("T2-BND-01", 2, "F2", "FAIL", "chunks[9] is not a JSON object")
    drive_doc = chunk10.get("driveDocument", {})
    if not isinstance(drive_doc, dict) or drive_doc.get("id") != SOURCE_A_ID:
        return CheckOutcome(
            "T2-BND-01",
            2,
            "F2",
            "FAIL",
            f"chunks[9] driveDocument.id={drive_doc.get('id')!r} (expected {SOURCE_A_ID!r})",
        )
    if "text" in chunk10 and chunk10["text"]:
        return CheckOutcome("T2-BND-01", 2, "F2", "FAIL", "chunks[9] unexpectedly has non-empty text key")

    t_text = transcript.read_text(encoding="utf-8")
    m = re.search(r"^## Turn 0010\b[^\n]*\n\n(.*?)(?=\n## Turn 0011\b|\Z)", t_text, re.M | re.S)
    if not m or m.group(1).strip() != "":
        return CheckOutcome("T2-BND-01", 2, "F2", "FAIL", "transcript.md Turn 0010 body is not blank")

    combined_docs = "\n".join(p.read_text(encoding="utf-8") for p in compilation_docs)
    if ("Turn 10" not in combined_docs and "chunks[9]" not in combined_docs) or SOURCE_A_ID not in combined_docs:
        return CheckOutcome(
            "T2-BND-01",
            2,
            "F2",
            "FAIL",
            "Compilation doc(s) do not explicitly link Turn 10 driveDocument to Source A",
        )
    return CheckOutcome(
        "T2-BND-01",
        2,
        "F2",
        "PASS",
        "Turn 10 driveDocument attachment boundary verified (no text key, blank transcript Turn 10, linked to 13ED)",
    )


def check_t2_bnd_02_turn24_indented_fence(
    repo_root: Path,
    compilation_docs: list[Path],
) -> CheckOutcome:
    """T2-BND-02: Turn 24 2-space indented ```lean fence & extract_aistudio_math.py column-0 behavior."""
    src_b = repo_root / SOURCE_B_REL
    manifest_path = repo_root / SOURCE_B_EXTRACT_DIR_REL / "manifest.json"
    if not src_b.is_file() or not manifest_path.is_file():
        return CheckOutcome("T2-BND-02", 2, "F2", "FAIL", "Missing Source B JSON or extract manifest.json")
    data = json.loads(src_b.read_text(encoding="utf-8"))
    cp = data.get("chunkedPrompt") if isinstance(data, dict) else None
    chunks = cp.get("chunks", []) if isinstance(cp, dict) else []
    if not isinstance(chunks, list) or len(chunks) < 24:
        return CheckOutcome("T2-BND-02", 2, "F2", "FAIL", f"Source B has only {len(chunks)} chunks (<24)")
    chunk24 = chunks[23]
    if not isinstance(chunk24, dict):
        return CheckOutcome("T2-BND-02", 2, "F2", "FAIL", "chunks[23] is not a JSON object")
    chunk24_text = str(chunk24.get("text", ""))
    if "  ```lean" not in chunk24_text:
        return CheckOutcome("T2-BND-02", 2, "F2", "FAIL", "Expected 2-space indented `  ```lean` fence in chunks[23]")

    # Verify extract_aistudio_math.extract_fences skips 2-space indented fences
    from tools.infra.extract_aistudio_math import extract_fences

    fences24 = extract_fences(chunk24_text)
    if any(lang in ("lean", "lean4") for lang, _, _ in fences24):
        return CheckOutcome(
            "T2-BND-02",
            2,
            "F2",
            "FAIL",
            "extract_aistudio_math.extract_fences unexpectedly captured 2-space indented Lean fence",
        )
    combined_docs = "\n".join(p.read_text(encoding="utf-8") for p in compilation_docs)
    if "Turn 24" not in combined_docs or ("indented" not in combined_docs.lower() and "column 0" not in combined_docs.lower()):
        return CheckOutcome(
            "T2-BND-02",
            2,
            "F2",
            "FAIL",
            "Compilation doc(s) do not document Turn 24 indented Lean fence behavior",
        )
    return CheckOutcome(
        "T2-BND-02",
        2,
        "F2",
        "PASS",
        "Turn 24 2-space indented ```lean fence boundary & extract_aistudio_math column-0 behavior verified",
    )


def check_t2_bnd_03_turn_delta_separation(
    repo_root: Path,
    compilation_docs: list[Path],
    rows: list[ParsedClaimRow],
    effective_mode: str,
) -> CheckOutcome:
    """T2-BND-03: Turns 1-45 vs 46-84 delta separation without conflating provenance."""
    src_b = repo_root / SOURCE_B_REL
    if not src_b.is_file():
        return CheckOutcome("T2-BND-03", 2, "F2", "FAIL", "Missing Source B JSON")
    raw_b = json.loads(src_b.read_text(encoding="utf-8"))
    cp = raw_b.get("chunkedPrompt") if isinstance(raw_b, dict) else None
    chunks = cp.get("chunks", []) if isinstance(cp, dict) else []
    if not isinstance(chunks, list):
        chunks = []

    turn_46_84_re = re.compile(r"\b(?:Turn|Turns|Chunk|Chunks|T|C)\s*(?:4[6-9]|[5-8]\d)\b")

    if effective_mode == "baseline45":
        if len(chunks) < 45:
            return CheckOutcome("T2-BND-03", 2, "F2", "FAIL", f"Expected >=45 chunks for baseline45 prefix, found {len(chunks)}")
        c44 = chunks[44]
        if not isinstance(c44, dict):
            return CheckOutcome("T2-BND-03", 2, "F2", "FAIL", "baseline45 prefix chunks[44] is not a JSON object")
        if c44.get("createTime") != "2026-11-18T22:47:27.873Z":
            return CheckOutcome("T2-BND-03", 2, "F2", "FAIL", f"baseline45 prefix Turn 45 timestamp mismatch: {c44.get('createTime')!r}")
        # Ensure no Turn 46-84 chunk citations exist in baseline45 verified claims
        bad_turn = [
            r.claim_id for r in rows
            if "[kernel_verified]" in r.labels and turn_46_84_re.search(r.provenance)
        ]
        if bad_turn:
            return CheckOutcome("T2-BND-03", 2, "F2", "FAIL", f"baseline45 claims cite Turn 46-84: {bad_turn}")
        return CheckOutcome(
            "T2-BND-03",
            2,
            "F2",
            "PASS",
            f"Turns 1-45 baseline prefix verified ({len(chunks)} chunks on disk, Turn 1-45 ledger clean)",
        )

    # live84 mode
    if len(chunks) < 84:
        return CheckOutcome("T2-BND-03", 2, "F2", "FAIL", f"Expected >=84 chunks in live84, found {len(chunks)}")
    # Check Turn 10 and Turn 24 anchors in first 45 chunks remain intact
    c9 = chunks[9]
    c9_drive = c9.get("driveDocument") if isinstance(c9, dict) else None
    if not isinstance(c9_drive, dict) or c9_drive.get("id") != SOURCE_A_ID:
        return CheckOutcome("T2-BND-03", 2, "F2", "FAIL", "live84 prefix lost Turn 10 driveDocument anchor")
    turn46_84_claims = [
        r for r in rows
        if turn_46_84_re.search(r.provenance + " " + r.doc_path)
    ]
    if not turn46_84_claims:
        return CheckOutcome(
            "T2-BND-03",
            2,
            "F2",
            "FAIL",
            "live84 mode has >=84 chunks on disk, but compilation ledger contains no Turn/Chunk 46-84 provenance claims",
        )
    return CheckOutcome(
        "T2-BND-03",
        2,
        "F2",
        "PASS",
        f"Turns 1-45 vs 46-84 delta separation verified ({len(chunks)} chunks; {len(turn46_84_claims)} Turn 46-84 claims)",
        {"chunks": len(chunks), "delta_claims": len(turn46_84_claims)},
    )


def check_t2_bnd_04_riemann_masullo_quarantine(
    repo_root: Path,
    targets: list[ResolvedTarget],
    compilation_docs: list[Path],
    effective_mode: str,
) -> CheckOutcome:
    """T2-BND-04: Non-import of riemann-masullo Ch05-Ch12 / *_Printed sorry files + errata quarantine."""
    bad_imports: list[str] = []
    for t in targets:
        if not t.exists:
            continue
        imports = extract_lean_imports(t.path.read_text(encoding="utf-8"))
        for imp in imports:
            norm_imp = imp.replace("«", "").replace("»", "")
            if (
                any(norm_imp.startswith(pref) for pref in FORBIDDEN_RIEMANN_MASULLO_IMPORTS)
                or FORBIDDEN_RM_IMPORT_RE.search(norm_imp)
            ):
                bad_imports.append(f"{t.rel_path} imports {imp}")
    if bad_imports:
        return CheckOutcome(
            "T2-BND-04",
            2,
            "F6",
            "FAIL",
            f"Forbidden riemann-masullo Ch05-Ch12 / *_Printed import(s): {bad_imports}",
        )
    if effective_mode == "live84":
        combined = "\n".join(p.read_text(encoding="utf-8") for p in compilation_docs)
        missing_errata = [
            tok for tok in ("F8", "F9", "F13", "1.4.3", "Ch05", "Ch12")
            if tok not in combined
        ]
        if missing_errata:
            return CheckOutcome(
                "T2-BND-04",
                2,
                "F6",
                "FAIL",
                f"live84 compilation docs missing riemann-masullo errata quarantine markers: {missing_errata}",
            )
    return CheckOutcome(
        "T2-BND-04",
        2,
        "F6",
        "PASS",
        f"riemann-masullo Ch05-Ch12 / *_Printed non-import boundary verified across {sum(1 for t in targets if t.exists)} target(s)",
    )


def check_t2_bnd_05_colimit_rh_bucket3_enforcement(
    rows: list[ParsedClaimRow],
    artifacts: DiscoveredArtifacts,
    effective_mode: str = "baseline45",
) -> CheckOutcome:
    """T2-BND-05: Ungrounded RH / Weil / Li equivalence / Bost-Connes C*-simplex / N->inf / simplicity must be BUCKET 3."""
    forbidden_bucket1_patterns = (
        re.compile(r"(?:\\mathcal\{W\}\s*\([^)]*\)|Weil\s+(?:positivity|explicit[- ]formula)[^.\n]*?)\s*(?:>=|\\geq?|≥)\s*0", re.I),
        re.compile(r"(?:\\mathcal\{W\}|\bW)\s*(?:\([^)]*\))?\s*(?:>=|\\geq?|≥)\s*0.*?(?:<->|\\iff|↔|implies)", re.I),
        re.compile(r"(?:\\mathrm\{RH\}|\\text\{RH\}|\bRH\b)\s*(?:<->|\\iff|↔)\s*(?:\\mathcal\{W\}|\bW|.*(?:\\lambda_n|λ_n))", re.I),
        re.compile(r"\bWeil\s+(?:positivity|explicit[- ]formula).*?(?:\bRH\b|Riemann\s+Hypothesis|implies|iff)", re.I),
        re.compile(r"(?:\\lambda_n|λ_n)\s*.*(?:>=|\\geq?|≥)\s*0", re.I),
        re.compile(r"\ball\s+Li\s+coefficients\b|\bLi\s+criterion\b", re.I),
        re.compile(r"\\zeta'\s*\(\s*\\rho\s*\)\s*(?:!=|\\neq?|≠)\s*0|\bzero\s+simplicity\b|\ball\s+(?:nontrivial\s+)?zeros\s+are\s+simple\b", re.I),
        re.compile(r"\bnontrivial\s+zeros\s+of\s+\$?(?:\\zeta|ζ|zeta)\b[^.\n]*(?:\\operatorname\s*\{Re\}|\\Re|\bRe)\s*\([^)]*\)\s*=\s*(?:1/2|\\frac\{1\}\{2\}|0\.5)", re.I),
        re.compile(r"\ball\s+nontrivial\s+zeros\b[^.\n]*\bcritical\s+line\b", re.I),
        re.compile(r"(?:\\lim_\{?N|\bN)\s*(?:->|\\rightarrow|\\to|→)\s*(?:\\infty|∞|infinity)", re.I),
        re.compile(r"\binductive\s+colimit\b|\bglobal\s+(?:Riemann\s+Hypothesis|RH|colimit|completion)\b", re.I),
        re.compile(r"\bRiemann\s+Hypothesis\s+(?:holds|is\s+(?:true|proved|proven|established))\b", re.I),
        re.compile(
            r"\bBost[-– ]Connes\b.*?(?:\b|\\mathrm\{|\\text\{)?KMS\}?(?:_\{?\s*\\?beta\s*\}?|\s+state|\s+simplex)"
            r"|(?:\b|\\mathrm\{|\\text\{)?KMS\}?(?:_\{?\s*\\?beta\s*\}?)?\s+(?:state[- ]?simplex|classification)\b"
            r"|\bC\*-?algebra(?:ic)?\s+state[- ]simplex\b",
            re.I,
        ),
        re.compile(r"\bcurv(?:ed)?[- ]spacetime\s+(?:Einstein|Kerr)\s+PDE", re.I),
    )
    violations: list[str] = []
    for r in rows:
        if r.implied_bucket == "BUCKET 3" or "[bucket_3_open_debt]" in r.labels or "[countermodel_found]" in r.labels:
            continue
        text = f"{r.statement} {r.carrier}"
        for pat in forbidden_bucket1_patterns:
            if pat.search(text):
                violations.append(f"{r.claim_id} ({r.labels}): matched open-debt pattern {pat.pattern!r}")
    if violations:
        return CheckOutcome(
            "T2-BND-05",
            2,
            "F7",
            "FAIL",
            "Ungrounded RH/Weil/Li/Bost-Connes/infinite-horizon claim promoted out of BUCKET 3: " + "; ".join(violations),
        )
    if effective_mode == "live84":
        bucket3_texts = " ".join(
            f"{r.statement} {r.carrier} {r.notes_col}"
            for r in rows
            if r.implied_bucket == "BUCKET 3" or "[bucket_3_open_debt]" in r.labels
        )
        required_debt = (
            ("RH", re.compile(r"\bRH\b|\\mathrm\{RH\}|Riemann\s+Hypothesis", re.I)),
            ("Weil", re.compile(r"\bWeil\b|\\mathcal\{W\}", re.I)),
            ("Li", re.compile(r"\bLi\b|\\lambda_n|λ_n", re.I)),
            ("zero simplicity", re.compile(r"simplicity|\\zeta'\s*\(\s*\\rho\s*\)|Jordan", re.I)),
        )
        missing_debt = [name for name, pat in required_debt if not pat.search(bucket3_texts)]
        if missing_debt:
            return CheckOutcome(
                "T2-BND-05",
                2,
                "F7",
                "FAIL",
                f"live84 BUCKET 3 open-debt coverage missing explicit items: {missing_debt}",
            )
    # Also ensure intent envelopes record open debt in non_theorem_claims
    has_non_thm = any(
        bool(json.loads(p.read_text(encoding="utf-8")).get("non_theorem_claims"))
        for p in artifacts.intent_envelopes
    )
    if artifacts.intent_envelopes and not has_non_thm:
        return CheckOutcome(
            "T2-BND-05",
            2,
            "F7",
            "FAIL",
            "Intent envelope(s) have empty non_theorem_claims",
        )
    return CheckOutcome(
        "T2-BND-05",
        2,
        "F7",
        "PASS",
        "Colimit/RH/Weil/Li/Bost-Connes BUCKET 3 open-debt boundary enforced",
    )


def _extract_proved_mermaid_nodes_and_edges(compilation_docs: list[Path]) -> tuple[set[str], list[tuple[str, str]], list[str]]:
    all_nodes: set[str] = set()
    all_edges: list[tuple[str, str]] = []
    mermaid_raws: list[str] = []
    for doc in compilation_docs:
        text = doc.read_text(encoding="utf-8")
        for block in MERMAID_BLOCK_RE.findall(text):
            mermaid_raws.append(block)
            n, e = parse_mermaid_dag(block)
            all_nodes.update(n)
            all_edges.extend(e)
    return all_nodes, all_edges, mermaid_raws


def check_t2_bnd_06_countermodel_quarantine(
    compilation_docs: list[Path],
    rows: list[ParsedClaimRow],
) -> CheckOutcome:
    """T2-BND-06: Countermodels (SA-18, SB-17, SB-35, etc.) carry [countermodel_found] (BUCKET 3) and stay outside proved DAG."""
    by_id = {r.claim_id: r for r in rows}
    issues: list[str] = []
    has_baseline_scope = any(
        r.doc_path.endswith("DRIVE_13ED_AISTUDIO_1v8J_EPISTEMIC_COMPILATION.md")
        or r.claim_id.startswith("SA-")
        or bool(re.match(r"^SB-(?:0\d|[1-3]\d|40)\b", r.claim_id))
        for r in rows
    )
    if has_baseline_scope:
        for cid in KNOWN_COUNTERMODEL_IDS:
            row = by_id.get(cid)
            if row is None:
                issues.append(f"Missing countermodel claim {cid}")
                continue
            if "[countermodel_found]" not in row.labels or row.implied_bucket != "BUCKET 3":
                issues.append(f"{cid}: expected [countermodel_found] (BUCKET 3), got {row.labels}/{row.implied_bucket}")

    countermodel_rows = [r for r in rows if "[countermodel_found]" in r.labels]
    nodes, _edges, raw_blocks = _extract_proved_mermaid_nodes_and_edges(compilation_docs)
    norm_nodes = {_norm_claim_id(n) for n in nodes}
    raw_mermaid_norm = _norm_claim_id("\n".join(raw_blocks))
    for r in countermodel_rows:
        norm_cid = _norm_claim_id(r.claim_id)
        if norm_cid in norm_nodes or re.search(rf"\b{re.escape(norm_cid)}\b", raw_mermaid_norm):
            issues.append(f"Countermodel {r.claim_id} appears inside proved Mermaid DAG")

    if issues:
        return CheckOutcome(
            "T2-BND-06",
            2,
            "F3",
            "FAIL",
            "Countermodel quarantine failed: " + "; ".join(issues),
        )
    return CheckOutcome(
        "T2-BND-06",
        2,
        "F3",
        "PASS",
        f"Countermodel quarantine verified ({len(countermodel_rows)} [countermodel_found] claims excluded from proved DAG)",
        {"countermodel_ids": [r.claim_id for r in countermodel_rows]},
    )


def check_t2_bnd_07_bucket_label_disjointness(rows: list[ParsedClaimRow]) -> CheckOutcome:
    """T2-BND-07: Bucket <-> Label disjointness & no non-HEAD concurrent draft marked [kernel_verified]."""
    issues: list[str] = []
    for r in rows:
        if len(r.labels) != 1 or r.implied_bucket not in BUCKET_ALLOWED_LABELS:
            issues.append(f"{r.claim_id}: invalid label/bucket ({r.labels}, {r.implied_bucket})")
            continue
        label = r.labels[0]
        if label not in BUCKET_ALLOWED_LABELS[r.implied_bucket]:
            issues.append(f"{r.claim_id}: bucket/label mismatch ({r.implied_bucket} with {label})")
        if label == "[kernel_verified]" and (
            "not in `head`" in r.notes_col.lower()
            or "concurrent non-`head`" in r.notes_col.lower()
            or "unimplemented" in r.notes_col.lower()
        ):
            issues.append(f"{r.claim_id}: marked [kernel_verified] while notes say unimplemented/non-HEAD")
    if issues:
        return CheckOutcome(
            "T2-BND-07",
            2,
            "F3",
            "FAIL",
            "Bucket/label disjointness violated: " + "; ".join(issues[:5]),
        )
    return CheckOutcome(
        "T2-BND-07",
        2,
        "F3",
        "PASS",
        f"Bucket <-> label disjointness verified across {len(rows)} claim rows",
    )


def run_tier2_checks(
    repo_root: Path,
    artifacts: DiscoveredArtifacts,
    rows: list[ParsedClaimRow],
    targets: list[ResolvedTarget],
    effective_mode: str,
) -> list[CheckOutcome]:
    return [
        check_t2_bnd_01_turn10_drive_attachment(repo_root, artifacts.compilation_docs),
        check_t2_bnd_02_turn24_indented_fence(repo_root, artifacts.compilation_docs),
        check_t2_bnd_03_turn_delta_separation(repo_root, artifacts.compilation_docs, rows, effective_mode),
        check_t2_bnd_04_riemann_masullo_quarantine(repo_root, targets, artifacts.compilation_docs, effective_mode),
        check_t2_bnd_05_colimit_rh_bucket3_enforcement(rows, artifacts, effective_mode),
        check_t2_bnd_06_countermodel_quarantine(artifacts.compilation_docs, rows),
        check_t2_bnd_07_bucket_label_disjointness(rows),
    ]


# ---------------------------------------------------------------------------
# Tier 3: Cross-Feature Pairwise Consistency (T3-CONS-01 .. T3-CONS-05)
# ---------------------------------------------------------------------------


def check_t3_cons_01_claims_dag_quarantine_partition(
    compilation_docs: list[Path],
    rows: list[ParsedClaimRow],
) -> CheckOutcome:
    """T3-CONS-01: Claim IDs partition cleanly across proved DAG/contracts vs quarantine/open-debt tables."""
    if not rows:
        return CheckOutcome("T3-CONS-01", 3, "F3", "FAIL", "No claim rows to cross-check against DAG/quarantine")
    nodes, _edges, raw_blocks = _extract_proved_mermaid_nodes_and_edges(compilation_docs)
    norm_nodes = {_norm_claim_id(n) for n in nodes}
    raw_mermaid_norm = _norm_claim_id("\n".join(raw_blocks))
    combined_docs = "\n".join(p.read_text(encoding="utf-8") for p in compilation_docs)

    quarantined_labels = {"[countermodel_found]", "[bucket_3_open_debt]", "[documentation_only]"}
    issues: list[str] = []
    quarantined_count = 0
    for r in rows:
        if r.labels and r.labels[0] in quarantined_labels:
            quarantined_count += 1
            norm_cid = _norm_claim_id(r.claim_id)
            if norm_cid in norm_nodes or re.search(rf"\b{re.escape(norm_cid)}\b", raw_mermaid_norm):
                issues.append(f"Quarantined claim {r.claim_id} ({r.labels[0]}) leaked into proved Mermaid DAG")
            # Ensure quarantined claim is mentioned in quarantine/open-debt section if §5.1 exists
            if "## 5.1" in combined_docs or "Quarantined Non-DAG" in combined_docs:
                sec51 = combined_docs.split("Quarantined Non-DAG", 1)[-1]
                if r.claim_id not in sec51 and r.doc_path.endswith("DRIVE_13ED_AISTUDIO_1v8J_EPISTEMIC_COMPILATION.md"):
                    # In baseline doc, SB-01a/SB-04b/etc. are BUCKET 1/2; all BUCKET 3 SB/SA claims are in 5.1
                    issues.append(f"Quarantined claim {r.claim_id} missing from §5.1 Quarantined Non-DAG table")
    if issues:
        return CheckOutcome(
            "T3-CONS-01",
            3,
            "F3",
            "FAIL",
            "Claim ID <-> DAG/quarantine partition failed: " + "; ".join(issues[:5]),
        )
    return CheckOutcome(
        "T3-CONS-01",
        3,
        "F3",
        "PASS",
        f"Claim ID <-> DAG/quarantine partition consistent ({len(rows)} claims, {quarantined_count} quarantined outside DAG)",
    )


@dataclass(frozen=True)
class _OpenSpec:
    ns: list[str]
    mode: str = "all"  # "all" | "only" | "hiding" | "renaming"
    names: frozenset[str] = frozenset()
    renames: tuple[tuple[str, str], ...] = ()
    is_root: bool = False
    alias_prefix: tuple[str, ...] = ()


_RESERVED_LEAN_IDENT_WORDS = _LEAN_TERM_KEYWORDS | frozenset({
    "theorem", "lemma", "def", "abbrev", "example", "instance", "structure", "class", "inductive",
    "axiom", "opaque", "namespace", "section", "end", "open", "export", "import", "variable",
    "universe", "private", "protected", "noncomputable", "unsafe", "partial", "scoped", "local",
    "in", "where", "then", "else", "with", "from", "at", "as", "hiding", "renaming", "forall",
    "exists", "Prop", "Type", "Sort", "true", "false", "sorry", "admit", "set_option", "deriving",
    "attribute", "mutual", "do", "return", "unless", "for", "while", "macro", "syntax", "elab", "_",
})


def _normalize_lean_ident_seg(seg: str) -> str:
    """Unescape simple Lean guillemet segments `«ok'»` -> `ok'` while preserving non-simple/keyword tokens."""
    s = seg.strip()
    if len(s) >= 2 and s.startswith("«") and s.endswith("»"):
        inner = s[1:-1]
        if (
            inner
            and not inner.startswith("«")
            and "»" not in inner
            and _LEAN_IDENT_SEG_RE.fullmatch(inner)
            and inner not in _RESERVED_LEAN_IDENT_WORDS
        ):
            return inner
    return s


def _normalize_lean_qual_ident(ident: str) -> str:
    """Normalize simple guillemet segments across a dotted Lean identifier."""
    parts = split_lean_qual_ident(ident)
    return ".".join(_normalize_lean_ident_seg(p) for p in parts) if parts else ident.strip()


def _normalize_simple_guil_in_line(line: str) -> str:
    """Replace simple `«seg»` tokens in a Lean source line with unescaped `seg`."""
    return re.sub(r"«[^»\n]+»", lambda m: _normalize_lean_ident_seg(m.group(0)), line)


def _split_ns_with_root(tok: str) -> tuple[list[str], bool]:
    s = tok.strip()
    is_root = s.startswith("_root_.")
    if is_root:
        s = s.removeprefix("_root_.")
    return [_normalize_lean_ident_seg(p) for p in split_lean_qual_ident(s)], is_root


def _paren_balance_outside_guillemets(line: str) -> int:
    bal = 0
    in_guil = False
    for ch in line:
        if ch == "«":
            in_guil = True
        elif ch == "»":
            in_guil = False
        elif not in_guil:
            if ch == "(":
                bal += 1
            elif ch == ")":
                bal -= 1
    return bal


def _split_ws_outside_guillemets(text: str) -> list[str]:
    """Split `text` on whitespace outside `«...»` guillemets."""
    toks: list[str] = []
    cur: list[str] = []
    in_guil = False
    for ch in text:
        if ch == "«":
            in_guil = True
            cur.append(ch)
        elif ch == "»":
            in_guil = False
            cur.append(ch)
        elif not in_guil and ch.isspace():
            if cur:
                toks.append("".join(cur))
                cur.clear()
        else:
            cur.append(ch)
    if cur:
        toks.append("".join(cur))
    return toks


def _parse_open_specs(clause: str) -> list[_OpenSpec]:
    """Parse an `open <ns> [hiding ... | (...) | renaming ...]` clause (without trailing `in ...`)."""
    rest = clause.strip()
    if not rest or re.match(r"^scoped(?:\s|$)", rest):
        return []
    m_mod = re.search(r"(?:^|\s)(hiding|renaming)(?=\s|$)|\(", rest)
    if m_mod:
        ns_part = rest[: m_mod.start()].strip()
        mod_tail = rest[m_mod.start() :].strip()
    else:
        ns_part = rest
        mod_tail = ""
    ns_list: list[tuple[list[str], bool]] = []
    for tok in _split_ws_outside_guillemets(ns_part):
        parts, is_root = _split_ns_with_root(tok)
        if parts:
            ns_list.append((parts, is_root))
    if not ns_list:
        return []
    if not mod_tail:
        return [_OpenSpec(parts, "all", is_root=is_root) for parts, is_root in ns_list]
    specs = [_OpenSpec(parts, "all", is_root=is_root) for parts, is_root in ns_list[:-1]]
    last_ns, last_is_root = ns_list[-1]
    if mod_tail.startswith("("):
        end_p = mod_tail.find(")")
        inner = mod_tail[1:end_p] if end_p != -1 else mod_tail[1:]
        only_names = frozenset(_normalize_lean_qual_ident(tok) for tok in _split_ws_outside_guillemets(inner) if tok)
        specs.append(_OpenSpec(last_ns, "only", names=only_names, is_root=last_is_root))
    elif mod_tail.startswith("hiding"):
        after_h = mod_tail[len("hiding") :].strip()
        hid_names = frozenset(_normalize_lean_qual_ident(tok) for tok in _split_ws_outside_guillemets(after_h) if tok)
        specs.append(_OpenSpec(last_ns, "hiding", names=hid_names, is_root=last_is_root))
    elif mod_tail.startswith("renaming"):
        after_r = mod_tail[len("renaming") :].strip()
        ren_pairs: list[tuple[str, str]] = []
        for seg in after_r.split(","):
            m_ren = re.match(r"^\s*([^\s]+)\s*(?:→|->)\s*([^\s]+)\s*$", seg)
            if m_ren:
                ren_pairs.append(
                    (_normalize_lean_qual_ident(m_ren.group(1)), _normalize_lean_qual_ident(m_ren.group(2)))
                )
        specs.append(_OpenSpec(last_ns, "renaming", renames=tuple(ren_pairs), is_root=last_is_root))
    return specs


def _parse_open_or_export_line(line: str) -> tuple[list[_OpenSpec], str | None, bool, bool]:
    """Parse `open ... [in ...]` or `export Ns (...)`, returning `(specs, inline_cmd, is_scoped_in, is_export)`."""
    m_exp = re.match(r"^\s*export\s+([^\s(]+)\s*\(([^)]*)\)\s*$", line)
    if m_exp:
        ns_parts, is_root = _split_ns_with_root(m_exp.group(1))
        names = frozenset(_normalize_lean_qual_ident(tok) for tok in _split_ws_outside_guillemets(m_exp.group(2)) if tok)
        if ns_parts and names:
            return [_OpenSpec(ns_parts, "only", names=names, is_root=is_root)], None, False, True
        return [], None, False, False
    m = re.match(r"^\s*(export\s+)?open\s+(.*)$", line)
    if not m:
        return [], None, False, False
    is_export = bool(m.group(1))
    rest = m.group(2).strip()
    if not rest:
        return [], None, False, False
    m_in = re.search(r"(?:^|\s)in(?=\s|$)", rest)
    if m_in:
        before_in = rest[: m_in.start()].strip()
        after_in = rest[m_in.end() :].strip()
        return _parse_open_specs(before_in), after_in, True, False
    return _parse_open_specs(rest), None, False, is_export


def _parse_open_namespaces(line: str) -> list[list[str]]:
    """Extract opened namespace paths from a non-`in` Lean `open ...` line (compat helper)."""
    specs, _after, is_in, _is_exp = _parse_open_or_export_line(line)
    if is_in:
        return []
    return [sp.ns for sp in specs if sp.mode == "all"]


def _extract_audit_print_axioms_with_opens(audit_clean: str) -> list[tuple[list[str], list[_OpenSpec], str]]:
    """Return `[(active_ns_parts, opened_specs, line), ...]` for `#print axioms` lines."""
    scope_stack: list[tuple[str, list[str], list[_OpenSpec]]] = []
    module_opens: list[_OpenSpec] = []
    module_export_aliases: list[_OpenSpec] = []
    pending_in_opens: list[_OpenSpec] = []
    entries: list[tuple[list[str], list[_OpenSpec], str]] = []
    raw_lines = audit_clean.splitlines()
    idx_line = 0
    n_lines = len(raw_lines)
    while idx_line < n_lines:
        raw_line = raw_lines[idx_line]
        idx_line += 1
        if not raw_line.strip():
            continue
        line = raw_line
        if re.match(r"^\s*(?:export\s+)?open\b|^\s*export\s+[^\s(]+", line):
            is_open_cmd = bool(re.match(r"^\s*(?:export\s+)?open\b", line))
            open_indent = len(line) - len(line.lstrip())
            bal = _paren_balance_outside_guillemets(line)
            while idx_line < n_lines:
                has_in = bool(re.search(r"(?:^|\s)in(?=\s|$)", line))
                needs_cont = bal > 0 or (
                    is_open_cmd
                    and not has_in
                    and bool(re.search(r"(?:\b(?:renaming|hiding)|,|→|->)\s*$", line))
                )
                if not needs_cont and not has_in:
                    # Peek ahead for indented `(`, `,`, `→`/`->`, `hiding`, `renaming`, `in`, or `hiding` ident continuation
                    k_peek = idx_line
                    while k_peek < n_lines and not raw_lines[k_peek].strip():
                        k_peek += 1
                    if k_peek < n_lines:
                        pk_raw = raw_lines[k_peek]
                        pk_s = pk_raw.strip()
                        pk_ind = len(pk_raw) - len(pk_raw.lstrip())
                        _non_open_cmd_re = re.compile(
                            r"^(?:#|@\[|(?:namespace|section|end|open|export|theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom|variable|universe|import|attribute|private|protected|noncomputable|unsafe|partial|scoped|local|set_option|example|deriving|macro|syntax|elab|infix|prefix|postfix|notation|in)\b)"
                        )
                        _ident_seg_tok_re = re.compile(rf"^(?:{_LEAN_IDENT_SEG})$")
                        _qual_ns_tok_re = re.compile(rf"^(?:{_LEAN_QUAL_IDENT})$")
                        if is_open_cmd and pk_ind >= open_indent and re.match(r"^in(?=\s|$)", pk_s):
                            needs_cont = True
                        elif pk_ind > open_indent:
                            if pk_s.startswith("("):
                                needs_cont = True
                            elif is_open_cmd:
                                if re.match(r"^(?:,|→|->|(?:hiding|renaming|in)\b)", pk_s):
                                    needs_cont = True
                                elif re.search(r"(?:^|\s)hiding(?=\s|$)", line) and not re.search(r"(?:^|\s)renaming(?=\s|$)", line):
                                    if not _non_open_cmd_re.match(pk_s) and all(
                                        _ident_seg_tok_re.fullmatch(tok)
                                        for tok in _split_ws_outside_guillemets(pk_s)
                                    ):
                                        needs_cont = True
                                elif not re.search(r"(?:^|\s)(?:hiding|renaming)(?=\s|$)|\(", line):
                                    if not _non_open_cmd_re.match(pk_s) and all(
                                        _qual_ns_tok_re.fullmatch(tok)
                                        for tok in _split_ws_outside_guillemets(pk_s)
                                    ):
                                        needs_cont = True
                if not needs_cont:
                    break
                nxt_raw = raw_lines[idx_line]
                idx_line += 1
                if not nxt_raw.strip():
                    continue
                line = line + " " + nxt_raw.strip()
                bal += _paren_balance_outside_guillemets(nxt_raw)
        cur_in_opens = pending_in_opens
        pending_in_opens = []
        while True:
            specs_here, after_in, is_in, is_export = _parse_open_or_export_line(line)
            if is_in:
                cur_in_opens = [*cur_in_opens, *specs_here]
                if after_in:
                    line = after_in
                    continue
                pending_in_opens = cur_in_opens
                cur_in_opens = []
                break
            if specs_here:
                if scope_stack:
                    cur_active_ns = tuple(p for kind, parts, _ in scope_stack if kind == "ns" for p in parts)
                    if is_export and not cur_active_ns:
                        # `export` inside a non-namespace root `section` persists in the root namespace
                        module_opens.extend(specs_here)
                    else:
                        scope_stack[-1][2].extend(specs_here)
                        if is_export and cur_active_ns:
                            for sp in specs_here:
                                module_export_aliases.append(
                                    _OpenSpec(
                                        sp.ns,
                                        sp.mode,
                                        sp.names,
                                        sp.renames,
                                        is_root=sp.is_root,
                                        alias_prefix=cur_active_ns,
                                    )
                                )
                else:
                    module_opens.extend(specs_here)
                line = ""
            break
        if not line.strip():
            continue
        m_ns = re.match(r"^\s*namespace\s+([^\s]+)", line)
        if m_ns:
            parts, _ = _split_ns_with_root(m_ns.group(1))
            for idx_p, part in enumerate(parts):
                scope_stack.append(("ns", [part], list(cur_in_opens) if idx_p == 0 else []))
            continue
        m_sec = re.match(r"^\s*section(?:\s+([^\s]+))?", line)
        if m_sec:
            sec_name = m_sec.group(1)
            sec_parts = [_normalize_lean_ident_seg(p) for p in split_lean_qual_ident(sec_name)] if sec_name else []
            scope_stack.append(("sec", sec_parts, list(cur_in_opens)))
            continue
        m_end = re.match(r"^\s*end(?:\s+([^\s]+))?\s*$", line)
        if m_end:
            end_name = m_end.group(1)
            if not end_name:
                if scope_stack:
                    scope_stack.pop()
            else:
                end_parts, _ = _split_ns_with_root(end_name)
                if scope_stack:
                    if scope_stack[-1][1] == end_parts:
                        scope_stack.pop()
                    else:
                        rem = list(end_parts)
                        while rem and scope_stack:
                            _, top_parts, _ = scope_stack[-1]
                            if not top_parts:
                                scope_stack.pop()
                                continue
                            if len(rem) >= len(top_parts) and rem[-len(top_parts) :] == top_parts:
                                scope_stack.pop()
                                rem = rem[: -len(top_parts)]
                            else:
                                scope_stack.pop()
                                break
            continue
        if re.search(r"(?:^|\s)#print\s+axioms\b", line):
            active_ns = [p for kind, parts, _ in scope_stack if kind == "ns" for p in parts]
            opened_specs = (
                list(module_opens)
                + list(module_export_aliases)
                + [op for _, _, ops in scope_stack for op in ops]
                + list(cur_in_opens)
            )
            entries.append((active_ns, opened_specs, line))
    return entries


def _extract_audit_print_axioms_entries(audit_clean: str) -> list[tuple[list[str], str]]:
    """Return `[(active_ns_parts, line), ...]` for `#print axioms` lines with Lean namespace stack tracking."""
    return [(ns, line) for ns, _ops, line in _extract_audit_print_axioms_with_opens(audit_clean)]


def _extract_local_lean_fqns(clean_src: str) -> set[str]:
    """Extract fully-qualified declaration names declared in `clean_src` respecting `namespace`/`section`/`end`."""
    from tests.epistemic_compilation_e2e.lean_checks import DECL_NAME_RE

    scope_stack: list[tuple[str, list[str]]] = []
    fqns: set[str] = set()
    for line in clean_src.splitlines():
        m_ns = re.match(r"^\s*namespace\s+([^\s]+)", line)
        if m_ns:
            parts, _ = _split_ns_with_root(m_ns.group(1))
            for part in parts:
                scope_stack.append(("ns", [part]))
            continue
        m_sec = re.match(r"^\s*section(?:\s+([^\s]+))?", line)
        if m_sec:
            sec_name = m_sec.group(1)
            sec_parts = [_normalize_lean_ident_seg(p) for p in split_lean_qual_ident(sec_name)] if sec_name else []
            scope_stack.append(("sec", sec_parts))
            continue
        m_end = re.match(r"^\s*end(?:\s+([^\s]+))?\s*$", line)
        if m_end:
            end_name = m_end.group(1)
            if not end_name:
                if scope_stack:
                    scope_stack.pop()
            else:
                end_parts, _ = _split_ns_with_root(end_name)
                if scope_stack:
                    if scope_stack[-1][1] == end_parts:
                        scope_stack.pop()
                    else:
                        rem = list(end_parts)
                        while rem and scope_stack:
                            _, top_parts = scope_stack[-1]
                            if not top_parts:
                                scope_stack.pop()
                                continue
                            if len(rem) >= len(top_parts) and rem[-len(top_parts) :] == top_parts:
                                scope_stack.pop()
                                rem = rem[: -len(top_parts)]
                            else:
                                scope_stack.pop()
                                break
            continue
        m_decl = DECL_NAME_RE.match(line)
        if m_decl:
            active_ns = [p for kind, parts in scope_stack if kind == "ns" for p in parts]
            decl_name = _normalize_lean_qual_ident(m_decl.group(1))
            if decl_name.startswith("_root_."):
                fqns.add(decl_name.removeprefix("_root_."))
            else:
                fqns.add(".".join([*active_ns, decl_name]) if active_ns else decl_name)
    return fqns


def _open_spec_exposed_name(op: _OpenSpec, thm_parts: list[str]) -> str | None:
    """Return the unqualified/relative name exposed by `op` for `thm_parts`, or `None` if hidden/excluded."""
    op_ns = [_normalize_lean_ident_seg(p) for p in op.ns]
    norm_parts = [_normalize_lean_ident_seg(p) for p in thm_parts]
    if not op_ns or len(norm_parts) <= len(op_ns) or norm_parts[: len(op_ns)] != op_ns:
        return None
    rel_parts = norm_parts[len(op_ns) :]
    rel_thm = ".".join(rel_parts)
    lead_seg = rel_parts[0]
    op_names = {_normalize_lean_qual_ident(nm) for nm in op.names}
    if op.mode == "all":
        return rel_thm
    if op.mode == "hiding":
        if rel_thm in op_names or lead_seg in op_names:
            return None
        return rel_thm
    if op.mode == "only":
        if rel_thm in op_names or lead_seg in op_names:
            return rel_thm
        return None
    if op.mode == "renaming":
        for orig_raw, new_raw in op.renames:
            orig = _normalize_lean_qual_ident(orig_raw)
            new_name = _normalize_lean_qual_ident(new_raw)
            if orig == rel_thm:
                return new_name
            if orig == lead_seg and len(rel_parts) > 1:
                return ".".join([new_name, *rel_parts[1:]])
        return None
    return None


def _audit_entries_cover_theorem(
    audit_entries: (
        list[tuple[list[str], str]]
        | list[tuple[list[str], list[list[str]], str]]
        | list[tuple[list[str], list[_OpenSpec], str]]
    ),
    thm: str,
    thm_parts: list[str],
    short_thm: str,
    *,
    shadow_fqns: set[str] | None = None,
) -> bool:
    """Check whether any `#print axioms` entry covers `thm` cleanly (rejecting prefix spoofs & shadowed names)."""
    shadows = {_normalize_lean_qual_ident(s) for s in (shadow_fqns or set())}
    thm_parts = [_normalize_lean_ident_seg(p) for p in thm_parts]
    thm = _normalize_lean_qual_ident(thm)
    short_thm = _normalize_lean_ident_seg(short_thm)
    norm_entries: list[tuple[list[str], list[_OpenSpec], str]] = []
    for ent in audit_entries:
        if len(ent) == 2:
            norm_entries.append(
                ([_normalize_lean_ident_seg(p) for p in ent[0]], [], _normalize_simple_guil_in_line(ent[1]))
            )
        else:
            ops_raw = ent[1]
            ops_norm = [
                _OpenSpec(
                    [_normalize_lean_ident_seg(p) for p in op.ns],
                    op.mode,
                    frozenset(_normalize_lean_qual_ident(nm) for nm in op.names),
                    tuple(
                        (_normalize_lean_qual_ident(o), _normalize_lean_qual_ident(n))
                        for o, n in op.renames
                    ),
                    is_root=op.is_root,
                    alias_prefix=tuple(_normalize_lean_ident_seg(p) for p in op.alias_prefix),
                )
                if isinstance(op, _OpenSpec)
                else _OpenSpec([_normalize_lean_ident_seg(p) for p in op], "all")
                for op in ops_raw
            ]
            norm_entries.append(
                ([_normalize_lean_ident_seg(p) for p in ent[0]], ops_norm, _normalize_simple_guil_in_line(ent[2]))
            )
    if len(thm_parts) <= 1:
        root_pat = re.compile(
            rf"(?:^|\s)#print\s+axioms\b[^\n]*(?<=_root_\.)@?{re.escape(short_thm)}(?:\.\{{[^\n}}]*\}})?(?![^\s),:])"
        )
        unqual_pat = re.compile(
            rf"(?:^|\s)#print\s+axioms\b[^\n]*(?<![^\s(,])@?{re.escape(short_thm)}(?:\.\{{[^\n}}]*\}})?(?![^\s),:])"
        )
        for active_ns, _opened_specs, line in norm_entries:
            if root_pat.search(line):
                return True
            if not active_ns and unqual_pat.search(line):
                return True
        return False

    root_direct_pat = re.compile(
        rf"(?:^|\s)#print\s+axioms\b[^\n]*(?<=_root_\.)@?{re.escape(thm)}(?:\.\{{[^\n}}]*\}})?(?![^\s),:])"
    )
    direct_pat = re.compile(
        rf"(?:^|\s)#print\s+axioms\b[^\n]*(?<![^\s(,])@?{re.escape(thm)}(?:\.\{{[^\n}}]*\}})?(?![^\s),:])"
    )
    for active_ns, opened_specs, line in norm_entries:
        real_opens = [op for op in opened_specs if not op.alias_prefix]
        export_aliases = [op for op in opened_specs if op.alias_prefix]
        cand_thms: list[tuple[str, list[str]]] = [(thm, thm_parts)]
        seen_cands: set[str] = {thm}
        if export_aliases:
            for _round in range(10):
                added = False
                eff_export_aliases: list[_OpenSpec] = []
                for exp_op in export_aliases:
                    eff_exp_op = exp_op
                    if not exp_op.is_root and exp_op.alias_prefix and exp_op.ns:
                        for d in range(len(exp_op.alias_prefix), 0, -1):
                            local_ns = [*exp_op.alias_prefix[:d], *exp_op.ns]
                            local_pref = ".".join(local_ns) + "."
                            if any(s.startswith(local_pref) for s in shadows) or any(
                                ".".join(c_p).startswith(local_pref) for _, c_p in cand_thms
                            ):
                                eff_exp_op = _OpenSpec(
                                    local_ns,
                                    exp_op.mode,
                                    exp_op.names,
                                    exp_op.renames,
                                    is_root=True,
                                    alias_prefix=exp_op.alias_prefix,
                                )
                                break
                    eff_export_aliases.append(eff_exp_op)
                for _c_name, c_parts in list(cand_thms):
                    for exp_op in eff_export_aliases:
                        exposed_exp = _open_spec_exposed_name(exp_op, c_parts)
                        if not exposed_exp:
                            continue
                        alias_parts = [*exp_op.alias_prefix, *split_lean_qual_ident(exposed_exp)]
                        alias_name = ".".join(alias_parts)
                        if alias_name not in seen_cands:
                            seen_cands.add(alias_name)
                            cand_thms.append((alias_name, alias_parts))
                            added = True
                if not added:
                    break
        for c_thm, c_parts in cand_thms:
            c_root_direct_pat = (
                root_direct_pat
                if c_thm == thm
                else re.compile(
                    rf"(?:^|\s)#print\s+axioms\b[^\n]*(?<=_root_\.)@?{re.escape(c_thm)}(?:\.\{{[^\n}}]*\}})?(?![^\s),:])"
                )
            )
            c_direct_pat = (
                direct_pat
                if c_thm == thm
                else re.compile(
                    rf"(?:^|\s)#print\s+axioms\b[^\n]*(?<![^\s(,])@?{re.escape(c_thm)}(?:\.\{{[^\n}}]*\}})?(?![^\s),:])"
                )
            )
            if c_root_direct_pat.search(line):
                return True
            if c_direct_pat.search(line):
                is_shadowed = any(
                    ((".".join(active_ns[:d]) + "." + c_thm) if d > 0 else c_thm) in shadows
                    for d in range(len(active_ns), -1, -1)
                )
                if not is_shadowed:
                    return True
            if active_ns:
                for k in range(len(active_ns), 0, -1):
                    ns_pref = c_parts[:k]
                    if len(active_ns) >= k and active_ns[:k] == ns_pref:
                        rel_thm = ".".join(c_parts[k:])
                        rel_pat = re.compile(
                            rf"(?:^|\s)#print\s+axioms\b[^\n]*(?<![^\s(,])@?{re.escape(rel_thm)}(?:\.\{{[^\n}}]*\}})?(?![^\s),:])"
                        )
                        if rel_pat.search(line):
                            is_shadowed = any(
                                (".".join(active_ns[:d]) + "." + rel_thm) in shadows
                                for d in range(len(active_ns), k, -1)
                            )
                            if not is_shadowed:
                                return True
            exposed_by_ns_rel: dict[tuple[tuple[str, ...], str], set[str]] = {}
            opened_ns_prefixes: list[tuple[tuple[str, ...], _OpenSpec]] = []
            all_eff_ops: list[_OpenSpec] = []
            for op in real_opens:
                cand_ops = [op]
                if not op.is_root:
                    local_shadow_op: _OpenSpec | None = None
                    if active_ns and op.ns:
                        for d in range(len(active_ns), 0, -1):
                            local_ns = [*active_ns[:d], *op.ns]
                            local_pref = ".".join(local_ns) + "."
                            if any(s.startswith(local_pref) for s in shadows) or any(
                                ".".join(c_p).startswith(local_pref) for _, c_p in cand_thms
                            ):
                                local_shadow_op = _OpenSpec(local_ns, op.mode, op.names, op.renames, is_root=True)
                                break
                    if local_shadow_op is not None:
                        cand_ops = [local_shadow_op]
                    elif op.ns:
                        lead_op_seg = op.ns[0]
                        for prev_ns, prev_op in opened_ns_prefixes:
                            prev_allows = (
                                prev_op.mode == "all"
                                or (prev_op.mode == "hiding" and lead_op_seg not in prev_op.names)
                                or (prev_op.mode == "only" and lead_op_seg in prev_op.names)
                            )
                            if prev_allows:
                                cand_ops.append(
                                    _OpenSpec([*prev_ns, *op.ns], op.mode, op.names, op.renames, is_root=True)
                                )
                for eff_op in cand_ops:
                    all_eff_ops.append(eff_op)
                    ns_key = tuple(eff_op.ns)
                    if eff_op.ns and eff_op.mode != "only":
                        opened_ns_prefixes.append((ns_key, eff_op))
                    if not eff_op.ns or len(c_parts) <= len(eff_op.ns) or c_parts[: len(eff_op.ns)] != eff_op.ns:
                        continue
                    rel_thm = ".".join(c_parts[len(eff_op.ns) :])
                    exposed = _open_spec_exposed_name(eff_op, c_parts)
                    if exposed:
                        exposed_by_ns_rel.setdefault((ns_key, rel_thm), set()).add(exposed)
            for (ns_key, _rel_thm), exposed_set in exposed_by_ns_rel.items():
                for exposed in exposed_set:
                    rel_pat = re.compile(
                        rf"(?:^|\s)#print\s+axioms\b[^\n]*(?<![^\s(,])@?{re.escape(exposed)}(?:\.\{{[^\n}}]*\}})?(?![^\s),:])"
                    )
                    if rel_pat.search(line):
                        is_shadowed = (
                            any(
                                ((".".join(active_ns[:d]) + "." + exposed) if d > 0 else exposed) in shadows
                                for d in range(len(active_ns), -1, -1)
                            )
                            or any(
                                _open_spec_exposed_name(other_op, split_lean_qual_ident(sh_fqn)) == exposed
                                for other_op in all_eff_ops
                                for sh_fqn in shadows
                            )
                        )
                        if not is_shadowed:
                            return True
    return False


def check_t3_cons_02_contracts_to_lean_declarations(
    repo_root: Path,
    artifacts: DiscoveredArtifacts,
    targets: list[ResolvedTarget],
    *,
    require_all_envelope_targets: bool,
) -> CheckOutcome:
    """T3-CONS-02: Intent envelope/contract acceptance_theorems <-> Lean declarations on disk <-> *Audit.lean."""
    checked_theorems = 0
    checked_audits = 0
    issues: list[str] = []

    for env_path in artifacts.intent_envelopes:
        data = json.loads(env_path.read_text(encoding="utf-8"))
        formal_objs = data.get("formal_objects", {})
        acc_thms = data.get("acceptance_theorems", {})
        # Build module stem -> target file map from owner_search.target_artifacts
        mod_to_file: dict[str, Path] = {}
        declared_audit_paths: set[Path] = set()
        declared_audit_primary_stems: set[str] = set()
        for art in data.get("owner_search", {}).get("target_artifacts", []):
            if isinstance(art, str) and art.endswith(".lean"):
                p = (repo_root / art).resolve()
                mod_to_file[p.stem] = p
                if p.stem.endswith("Audit"):
                    declared_audit_paths.add(p)
                    declared_audit_primary_stems.add(p.stem.removesuffix("Audit"))
        for lane_objs in formal_objs.values() if isinstance(formal_objs, dict) else ():
            if isinstance(lane_objs, list):
                for obj in lane_objs:
                    parts = split_lean_qual_ident(str(obj))
                    for pt in parts:
                        if pt.endswith("Audit"):
                            declared_audit_primary_stems.add(pt.removesuffix("Audit"))

        known_stems = set(mod_to_file.keys())
        reported_missing_audits: set[Path] = set()
        for lane, thms in acc_thms.items():
            objs = formal_objs.get(lane, [])
            stems = _extract_obj_module_stems(objs if isinstance(objs, list) else [], known_stems)
            lean_files: list[Path] = []
            for stem in stems:
                lf = mod_to_file.get(stem)
                if lf is not None:
                    lean_files.append(lf)
            if not lean_files:
                continue
            existing_lane_files: list[Path] = []
            for lf in lean_files:
                if not lf.is_file():
                    if require_all_envelope_targets:
                        issues.append(f"Missing target Lean file for lane {lane}: {lf.name}")
                else:
                    existing_lane_files.append(lf)
            if not existing_lane_files:
                continue
            lane_decls: set[str] = set()
            lane_fqns: set[str] = set()
            lane_audit_groups: list[tuple[list[tuple[list[str], list[_OpenSpec], str]], set[str]]] = []
            for lf in existing_lane_files:
                lf_text = lf.read_text(encoding="utf-8")
                for raw_d in extract_non_opaque_lean_declarations(lf_text):
                    lane_decls.add(raw_d)
                    lane_decls.add(_normalize_lean_qual_ident(raw_d))
                lane_fqns.update(_extract_local_lean_fqns(strip_lean_comments_and_strings(lf_text)))
                audit_file = lf.with_name(f"{lf.stem}Audit.lean")
                audit_declared = (
                    (lf.stem in declared_audit_primary_stems)
                    or (audit_file.resolve() in declared_audit_paths)
                )
                if audit_file.is_file():
                    checked_audits += 1
                    audit_clean = strip_lean_comments_and_strings(audit_file.read_text(encoding="utf-8"))
                    lane_audit_groups.append(
                        (_extract_audit_print_axioms_with_opens(audit_clean), _extract_local_lean_fqns(audit_clean))
                    )
                elif audit_declared:
                    reported_missing_audits.add(audit_file.resolve())
                    issues.append(f"Lane {lane} missing declared Audit Lean file: {audit_file.name}")
            for thm in thms:
                checked_theorems += 1
                thm_parts = [_normalize_lean_ident_seg(p) for p in split_lean_qual_ident(thm)]
                short_thm = thm_parts[-1] if thm_parts else _normalize_lean_ident_seg(thm)
                thm_norm = _normalize_lean_qual_ident(thm)
                if thm not in lane_decls and thm_norm not in lane_decls and short_thm not in lane_decls:
                    issues.append(
                        f"Lane {lane} ({', '.join(f.name for f in existing_lane_files)}) missing implemented acceptance theorem `{thm}`"
                    )
                if lane_audit_groups:
                    target_candidates: list[tuple[str, list[str], str]] = [(thm_norm, thm_parts, short_thm)]
                    if len(thm_parts) <= 1 and thm_norm not in lane_fqns:
                        matched_fqns = sorted(fqn for fqn in lane_fqns if lean_short_name(fqn) == short_thm)
                        if matched_fqns:
                            target_candidates = [
                                (cand, [_normalize_lean_ident_seg(p) for p in split_lean_qual_ident(cand)], lean_short_name(cand))
                                for cand in matched_fqns
                            ]
                    if not any(
                        _audit_entries_cover_theorem(
                            entries,
                            c_thm,
                            c_parts,
                            c_short,
                            shadow_fqns=(aud_fqns | (lane_fqns - {c_thm.removeprefix("_root_.")})),
                        )
                        for c_thm, c_parts, c_short in target_candidates
                        for entries, aud_fqns in lane_audit_groups
                    ):
                        issues.append(f"Lane {lane} *Audit.lean missing uncommented `#print axioms` reference to `{thm}`")
        if require_all_envelope_targets:
            for aud_p in sorted(declared_audit_paths):
                if aud_p not in reported_missing_audits and not aud_p.is_file():
                    issues.append(f"Missing declared target Audit Lean file: {aud_p.name}")

    # Also check v1 contract JSON owner_declarations
    for c_path in artifacts.contract_jsons:
        data = json.loads(c_path.read_text(encoding="utf-8"))
        for od in data.get("owner_declarations", []):
            sp = od.get("source_path")
            qn = od.get("qualified_name", "")
            short = lean_short_name(qn) if qn else ""
            if isinstance(sp, str) and short:
                target_file = repo_root / sp
                if target_file.is_file():
                    checked_theorems += 1
                    decls_raw = extract_non_opaque_lean_declarations(target_file.read_text(encoding="utf-8"))
                    decls = {d for rd in decls_raw for d in (rd, _normalize_lean_qual_ident(rd))}
                    qn_norm = _normalize_lean_qual_ident(qn)
                    short_norm = _normalize_lean_ident_seg(short)
                    if qn not in decls and qn_norm not in decls and short not in decls and short_norm not in decls:
                        issues.append(f"{c_path.name}: {sp} missing owner_declaration `{short}`")
                elif require_all_envelope_targets:
                    issues.append(f"{c_path.name}: missing contract owner_declaration source_path `{sp}`")

    if issues:
        return CheckOutcome(
            "T3-CONS-02",
            3,
            "F4",
            "FAIL",
            "Contract <-> Lean declaration <-> Audit consistency failed: " + "; ".join(issues[:5]),
        )
    return CheckOutcome(
        "T3-CONS-02",
        3,
        "F4",
        "PASS",
        f"Contract <-> Lean declaration <-> Audit consistency verified ({checked_theorems} decls, {checked_audits} Audit files)",
        {"checked_theorems": checked_theorems, "checked_audits": checked_audits},
    )


def check_t3_cons_03_imports_isolation(
    repo_root: Path,
    artifacts: DiscoveredArtifacts,
    targets: list[ResolvedTarget],
) -> CheckOutcome:
    """T3-CONS-03: Target Lean imports match allowed_imports (where specified) and never import forbidden concurrent drafts."""
    # Map target file stem -> allowed_imports set from intent envelopes
    allowed_by_stem: dict[str, set[str]] = {}
    excluded_paths: set[str] = set()
    for env_path in artifacts.intent_envelopes:
        data = json.loads(env_path.read_text(encoding="utf-8"))
        known_stems = {
            Path(art).stem
            for art in data.get("owner_search", {}).get("target_artifacts", [])
            if isinstance(art, str) and art.endswith(".lean")
        }
        for exc in data.get("owner_search", {}).get("excluded_dirty_or_concurrent_owners", []):
            excluded_paths.add(str(exc))
        allowed_map = data.get("allowed_imports", {})
        formal_objs = data.get("formal_objects", {})
        if isinstance(allowed_map, dict):
            for lane, mods in allowed_map.items():
                if not isinstance(mods, list):
                    continue
                objs = formal_objs.get(lane, [])
                stems = _extract_obj_module_stems(objs if isinstance(objs, list) else [], known_stems)
                if stems:
                    for stem in stems:
                        allowed_by_stem.setdefault(stem, set()).update(mods)
                elif "_" in lane:
                    stem = lane.split("_", 1)[1]
                    allowed_by_stem.setdefault(stem, set()).update(mods)

    issues: list[str] = []
    checked = 0
    for t in targets:
        if not t.exists:
            continue
        checked += 1
        imports = extract_lean_imports(t.path.read_text(encoding="utf-8"))
        for imp in imports:
            if imp in FORBIDDEN_CONCURRENT_DRAFTS:
                issues.append(f"{t.rel_path} imports forbidden concurrent draft `{imp}`")
            # Check excluded paths converted to module suffix
            for exc in excluded_paths:
                exc_mod = exc.removeprefix("lean/").removesuffix(".lean").replace("/", ".")
                if imp == exc_mod:
                    issues.append(f"{t.rel_path} imports excluded concurrent owner `{imp}`")
        stem = t.path.stem.removesuffix("Audit")
        if stem in allowed_by_stem:
            self_mods = {t.module} if t.module else {f"InfoGeometry.{t.path.parent.name}.{stem}"}
            allowed = allowed_by_stem[stem] | self_mods
            for imp in imports:
                if imp.startswith("InfoGeometry.") and imp not in allowed and not (t.path.stem.endswith("Audit") and imp.endswith(f".{stem}")):
                    issues.append(f"{t.rel_path} imports `{imp}` outside allowed_imports for {stem}")
    if issues:
        return CheckOutcome(
            "T3-CONS-03",
            3,
            "F5",
            "FAIL",
            "Import isolation check failed: " + "; ".join(issues[:5]),
        )
    return CheckOutcome(
        "T3-CONS-03",
        3,
        "F5",
        "PASS",
        f"Import isolation verified across {checked} target file(s) (0 forbidden concurrent draft imports)",
    )


def check_t3_cons_04_source_checksums_across_artifacts(
    repo_root: Path,
    artifacts: DiscoveredArtifacts,
    effective_mode: str = "live84",
) -> CheckOutcome:
    """T3-CONS-04: Source A/B SHA256 on disk <-> extract manifest.json <-> intent_envelope <-> compilation provenance."""
    from tests.epistemic_compilation_e2e import SOURCE_B_BASELINE45_SHA256

    src_a = repo_root / SOURCE_A_REL
    src_b = repo_root / SOURCE_B_REL
    extract_manifest = repo_root / SOURCE_B_EXTRACT_DIR_REL / "manifest.json"
    if not (src_a.is_file() and src_b.is_file() and extract_manifest.is_file()):
        return CheckOutcome("T3-CONS-04", 3, "F1", "FAIL", "Missing Source A, Source B, or extract manifest.json")
    sha_a = sha256_file(src_a)
    sha_b = sha256_file(src_b)
    m_data = json.loads(extract_manifest.read_text(encoding="utf-8"))
    if m_data.get("source_sha256") != sha_b:
        return CheckOutcome(
            "T3-CONS-04",
            3,
            "F2",
            "FAIL",
            f"Extract manifest source_sha256 ({m_data.get('source_sha256')}) != live Source B ({sha_b})",
        )
    expected_b_sha_for_docs = SOURCE_B_BASELINE45_SHA256 if effective_mode == "baseline45" else sha_b
    # Check at least one intent envelope matches expected Source A & B sha256
    env_matches = 0
    for env_path in artifacts.intent_envelopes:
        e_data = json.loads(env_path.read_text(encoding="utf-8"))
        s_map = e_data.get("source_sha256", {})
        vals = set(s_map.values()) if isinstance(s_map, dict) else set()
        if sha_a in vals and expected_b_sha_for_docs in vals:
            env_matches += 1
    if artifacts.intent_envelopes and env_matches == 0:
        return CheckOutcome(
            "T3-CONS-04",
            3,
            "F2",
            "FAIL",
            f"No intent envelope matches Source A ({sha_a[:12]}...) + Source B ({expected_b_sha_for_docs[:12]}...) SHA256",
        )
    docs_text = "\n".join(p.read_text(encoding="utf-8") for p in artifacts.compilation_docs)
    if sha_a[:12] not in docs_text or expected_b_sha_for_docs[:12] not in docs_text:
        return CheckOutcome(
            "T3-CONS-04",
            3,
            "F1",
            "FAIL",
            "Compilation doc provenance does not match Source A & B SHA256 prefixes",
        )
    return CheckOutcome(
        "T3-CONS-04",
        3,
        "F1",
        "PASS",
        f"Source A & B SHA256s consistent across disk, extract manifest, intent envelope ({env_matches}), and docs",
    )


_BARE_URL_SCHEME_RE = re.compile(
    r"(?<![:/\w])(?:[a-z][a-z0-9+.-]*://|mailto:|//(?=[^\s)>|`\"]))",
    flags=re.I,
)


def _mask_bare_urls(line: str) -> str:
    """Replace bare `<scheme>://...`, `mailto:...`, and protocol-relative `//host/...` URLs with spaces."""
    out: list[str] = []
    n = len(line)
    pos = 0
    for m in _BARE_URL_SCHEME_RE.finditer(line):
        if m.start() < pos:
            continue
        out.append(line[pos : m.start()])
        end = m.end()
        paren_depth = 0
        bracket_depth = 0
        while end < n:
            ch = line[end]
            if ch.isspace() or ch in "<>|`\"":
                break
            if ch == "(":
                paren_depth += 1
            elif ch == ")":
                if paren_depth == 0:
                    break
                paren_depth -= 1
            elif ch == "[":
                bracket_depth += 1
            elif ch == "]":
                if bracket_depth == 0:
                    break
                bracket_depth -= 1
            end += 1
        out.append(" ")
        pos = end
    out.append(line[pos:])
    return "".join(out)


def _iter_markdown_link_spans(line: str) -> list[tuple[int, int, int, str]]:
    """Extract `[(link_start, dest_start, dest_end, dest_and_title), ...]` for Markdown `[...](...)` links."""
    results: list[tuple[int, int, int, str]] = []
    n = len(line)
    i = 0
    while i < n:
        if line[i] == "\\" and i + 1 < n:
            i += 2
            continue
        if line[i] == "[":
            j = i + 1
            b_depth = 1
            while j < n and b_depth > 0:
                if line[j] == "\\" and j + 1 < n:
                    j += 2
                    continue
                if line[j] == "[":
                    b_depth += 1
                elif line[j] == "]":
                    b_depth -= 1
                j += 1
            if b_depth == 0 and j < n and line[j] == "(":
                dest_start = j + 1
                k = dest_start
                p_depth = 1
                in_quote: str | None = None
                in_angle = False
                while k < n and p_depth > 0:
                    ch = line[k]
                    if ch == "\\" and k + 1 < n:
                        k += 2
                        continue
                    if in_quote is not None:
                        if ch == in_quote:
                            in_quote = None
                        k += 1
                        continue
                    if in_angle:
                        if ch == ">":
                            in_angle = False
                        k += 1
                        continue
                    if ch == "<" and (k == dest_start or line[k - 1].isspace()):
                        in_angle = True
                    elif ch in ('"', "'") and k > dest_start and line[k - 1].isspace():
                        in_quote = ch
                    elif ch == "(":
                        p_depth += 1
                    elif ch == ")":
                        p_depth -= 1
                        if p_depth == 0:
                            break
                    k += 1
                if p_depth == 0:
                    results.append((i, dest_start, k, line[dest_start:k]))
                    i = k + 1
                    continue
        i += 1
    return results


def _iter_markdown_links(line: str) -> list[tuple[int, int, str]]:
    """Extract `[(dest_start, dest_end, dest_and_title), ...]` for Markdown `[...](...)` links with balanced parens."""
    return [(ds, de, rd) for _, ds, de, rd in _iter_markdown_link_spans(line)]


def _clean_markdown_link_target(raw_dest: str) -> str:
    """Strip optional CommonMark title (`"..."`, `'...'`, balanced `(...)`) and `<...>` wrapper from a link destination."""
    cand = raw_dest.strip()
    cand_q = re.sub(r"""\s+(?:"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*')\s*$""", "", cand).strip()
    if cand_q != cand:
        cand = cand_q
    elif cand.endswith(")"):
        depth = 0
        match_open: int | None = None
        idx = len(cand) - 1
        while idx >= 0:
            if idx > 0 and cand[idx - 1] == "\\":
                idx -= 2
                continue
            ch = cand[idx]
            if ch == ")":
                depth += 1
            elif ch == "(":
                depth -= 1
                if depth == 0:
                    match_open = idx
                    break
            idx -= 1
        if match_open is not None and match_open > 0 and cand[match_open - 1].isspace():
            prefix = cand[:match_open].strip()
            if prefix:
                cand = prefix
    if cand.startswith("<") and cand.endswith(">"):
        cand = cand[1:-1].strip()
    return cand


_URI_SCHEME_RE = re.compile(r"^[a-z][a-z0-9+.-]*:", flags=re.I)


def _is_nonlocal_markdown_dest(cand_ref: str) -> bool:
    """Return True iff `cand_ref` is empty, a `#anchor`, a protocol-relative `//...` URL, or a `<scheme>:` URI."""
    return (not cand_ref) or cand_ref.startswith("#") or cand_ref.startswith("//") or bool(_URI_SCHEME_RE.match(cand_ref))


def check_t3_cons_05_audit_report_hashes(
    repo_root: Path,
    artifacts: DiscoveredArtifacts,
    targets: list[ResolvedTarget] | None = None,
) -> CheckOutcome:
    """T3-CONS-05: QA/Audit report artifact_hashes and QA report SHA256 tables match live SHA256s on disk."""
    if not artifacts.audit_reports and not artifacts.qa_reports:
        return CheckOutcome("T3-CONS-05", 3, "F9", "PASS", "No audit_report.json or qa_report.md present for run (skipped)")
    has_targets = bool(
        targets
        or artifacts.compilation_docs
        or artifacts.intent_envelopes
        or artifacts.contract_jsons
    )
    checked = 0
    mismatches: list[str] = []
    for rep in artifacts.audit_reports:
        try:
            data = json.loads(rep.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            mismatches.append(f"{rep.name}: invalid JSON ({exc})")
            continue
        hashes = data.get("artifact_hashes") if isinstance(data, dict) else None
        if not isinstance(hashes, dict) or not hashes:
            if has_targets:
                mismatches.append(f"{rep.name}: missing or empty `artifact_hashes`")
            continue
        for rel, expected in hashes.items():
            expected_hex = str(expected).strip().lower().removeprefix("sha256:").strip()
            p = repo_root / rel
            if not p.is_file():
                mismatches.append(f"{rep.name}: missing hashed artifact {rel}")
                continue
            checked += 1
            actual = sha256_file(p)
            if actual != expected_hex:
                mismatches.append(f"{rep.name}: stale hash for {rel} (disk={actual[:12]} vs report={expected_hex[:12]})")

    for qa_rep in artifacts.qa_reports:
        try:
            qa_text = qa_rep.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError) as exc:
            mismatches.append(f"{qa_rep.name}: cannot read QA report ({exc})")
            continue
        qa_checked = 0
        for line in qa_text.splitlines():
            link_spans = _iter_markdown_link_spans(line)
            # Mask external Markdown links `[label](https://...)` in full and local link targets before digest/path scans
            masked_parts: list[str] = []
            prev_pos = 0
            for ls, ds, de, raw_dest in link_spans:
                cand_mask_ref = _clean_markdown_link_target(raw_dest)
                is_external_link = _is_nonlocal_markdown_dest(cand_mask_ref)
                mask_s = ls if is_external_link else ds
                mask_e = (de + 1) if is_external_link else de
                if mask_s >= prev_pos:
                    masked_parts.append(line[prev_pos:mask_s])
                    masked_parts.append(" ")
                    prev_pos = mask_e
            masked_parts.append(line[prev_pos:])
            line_for_hash = _mask_bare_urls("".join(masked_parts))
            m_hash = re.search(r"\b(?:sha256:)?([0-9a-fA-F]{64})\b", line_for_hash)
            if not m_hash:
                continue
            local_link_ref: str | None = None
            for _, _, _, raw_dest in link_spans:
                cand_ref = _clean_markdown_link_target(raw_dest)
                if _is_nonlocal_markdown_dest(cand_ref):
                    continue
                cand_ref = cand_ref.split("#", 1)[0].strip()
                if not cand_ref:
                    continue
                local_link_ref = cand_ref
                break
            m_plain = re.search(r"\b((?:lean|docs|artifacts|cached)/[^\s|`#)]+\.(?:lean|json|md|txt|pdf|jsonl))\b", line_for_hash)
            raw_ref: str | None = None
            resolved_path: Path | None = None
            if local_link_ref is not None:
                raw_ref = local_link_ref
                cand = (qa_rep.parent / raw_ref).resolve()
                resolved_path = cand if cand.is_file() else (repo_root / raw_ref).resolve()
            elif m_plain:
                raw_ref = m_plain.group(1)
                resolved_path = (repo_root / raw_ref).resolve()
            if raw_ref is None or resolved_path is None:
                continue
            if not resolved_path.is_file():
                qa_checked += 1
                mismatches.append(f"{qa_rep.name}: missing hashed artifact {raw_ref}")
                continue
            qa_checked += 1
            checked += 1
            actual = sha256_file(resolved_path)
            expected_hex = m_hash.group(1).lower()
            if actual != expected_hex:
                mismatches.append(
                    f"{qa_rep.name}: stale hash for {raw_ref} (disk={actual[:12]} vs report={expected_hex[:12]})"
                )
        if qa_checked == 0 and has_targets:
            mismatches.append(f"{qa_rep.name}: missing or empty artifact hash entries")

    if mismatches:
        return CheckOutcome(
            "T3-CONS-05",
            3,
            "F9",
            "FAIL",
            "Audit/QA report hash consistency failed: " + "; ".join(mismatches[:4]),
            {"checked": checked, "mismatches": mismatches},
        )
    return CheckOutcome(
        "T3-CONS-05",
        3,
        "F9",
        "PASS",
        f"Audit/QA report hashes match live disk SHA256s ({checked}/{checked} files)",
    )


def run_tier3_checks(
    repo_root: Path,
    artifacts: DiscoveredArtifacts,
    rows: list[ParsedClaimRow],
    targets: list[ResolvedTarget],
    effective_mode: str,
) -> list[CheckOutcome]:
    return [
        check_t3_cons_01_claims_dag_quarantine_partition(artifacts.compilation_docs, rows),
        check_t3_cons_02_contracts_to_lean_declarations(
            repo_root,
            artifacts,
            targets,
            require_all_envelope_targets=(effective_mode == "live84"),
        ),
        check_t3_cons_03_imports_isolation(repo_root, artifacts, targets),
        check_t3_cons_04_source_checksums_across_artifacts(repo_root, artifacts, effective_mode),
        check_t3_cons_05_audit_report_hashes(repo_root, artifacts, targets),
    ]


# ---------------------------------------------------------------------------
# Tier 4: Real-World Serialized Acceptance (T4-E2E-01 .. T4-E2E-05)
# ---------------------------------------------------------------------------


def parse_axiom_check_json_output(stdout: str) -> list[dict[str, Any]]:
    """Extract JSON array from `tools/infra/axiom_check.py --json` stdout."""
    decoder = json.JSONDecoder()
    # Prefer line-anchored `[` (from last to first) whose elements are module result dicts
    candidates = [m.start() for m in re.finditer(r"(?m)^\s*\[", stdout)]
    dict_list_fallback: list[dict[str, Any]] | None = None
    any_list_fallback: list[Any] | None = None
    for pos in reversed(candidates):
        stripped_pos = pos + len(stdout[pos:]) - len(stdout[pos:].lstrip())
        try:
            parsed, _end = decoder.raw_decode(stdout, stripped_pos)
        except json.JSONDecodeError:
            continue
        if isinstance(parsed, list):
            if parsed and all(isinstance(e, dict) and "module" in e for e in parsed):
                return parsed
            if dict_list_fallback is None and parsed and any(isinstance(e, dict) for e in parsed):
                dict_list_fallback = parsed
            if any_list_fallback is None:
                any_list_fallback = parsed
    if dict_list_fallback is not None:
        return dict_list_fallback
    if any_list_fallback is not None:
        return any_list_fallback
    start = stdout.find("[")
    end = stdout.rfind("]")
    if start == -1 or end == -1 or end < start:
        raise ValueError("axiom_check.py stdout did not contain a JSON array")
    parsed = json.loads(stdout[start : end + 1])
    if not isinstance(parsed, list):
        raise ValueError("axiom_check.py JSON payload is not a list")
    return parsed


def validate_axiom_check_entries(
    entries: list[dict[str, Any]],
    expected_modules: list[str],
) -> tuple[bool, list[str]]:
    """Validate axiom_check.py JSON entries (and optional axiom_usage fields)."""
    by_mod = {str(e.get("module")): e for e in entries if isinstance(e, dict)}
    issues: list[str] = []
    for mod in expected_modules:
        entry = by_mod.get(mod)
        if entry is None:
            issues.append(f"Missing axiom_check result for module `{mod}`")
            continue
        if entry.get("passed") is not True:
            issues.append(f"{mod}: passed={entry.get('passed')!r} error={entry.get('error')!r}")
        if entry.get("isPartial") is True or entry.get("partial") is True:
            issues.append(f"{mod}: contains partial declaration")
        if entry.get("isUnsafe") is True or entry.get("unsafe") is True:
            issues.append(f"{mod}: contains unsafe declaration")
        if "returncode" in entry and entry.get("returncode") != 0:
            issues.append(f"{mod}: non-zero returncode ({entry.get('returncode')!r})")
        if "axioms" in entry:
            axioms = entry.get("axioms")
            if not isinstance(axioms, list):
                issues.append(f"{mod}: `axioms` must be a non-null list (got {type(axioms).__name__})")
            else:
                disallowed = sorted(set(axioms) - PERMITTED_FOUNDATIONAL_AXIOMS)
                if disallowed:
                    issues.append(f"{mod}: disallowed axioms {disallowed}")
        elif entry.get("returncode") != 0:
            issues.append(f"{mod}: missing `axioms` list and non-zero/missing `returncode` ({entry.get('returncode')!r})")
        if "axiom_usage" in entry:
            usage = entry.get("axiom_usage")
            if not isinstance(usage, dict):
                issues.append(f"{mod}: `axiom_usage` must be a dict")
            else:
                for decl_name, used in usage.items():
                    if not isinstance(used, list):
                        issues.append(f"{mod}.{decl_name}: `axiom_usage` value must be a list")
                        continue
                    bad_used = sorted(set(used) - PERMITTED_FOUNDATIONAL_AXIOMS)
                    if bad_used:
                        issues.append(f"{mod}.{decl_name}: disallowed axioms in axiom_usage {bad_used}")
    return len(issues) == 0, issues


def build_tier4_commands(repo_root: Path, targets: list[ResolvedTarget]) -> dict[str, list[list[str]]]:
    """Build exact serialized Tier 4 commands without executing lake/lean."""
    file_args = [t.rel_path for t in targets]
    lib_modules = [t.module for t in targets if t.module]
    non_lib_files = [t.rel_path for t in targets if not t.module]

    lint_cmds: list[list[str]] = []
    if file_args:
        lint_cmds.extend([
            [sys.executable, "scripts/lint/required/style_lint.py", *file_args],
            [sys.executable, "scripts/lint/required/module_doc_lint.py", *file_args],
            [sys.executable, "scripts/lint/required/theorem_lint.py", *file_args],
            [sys.executable, "tools/infra/axiom_audit.py", "--fail-on-gaps", *file_args],
            [sys.executable, "tools/quality/placeholder_audit.py", "--strict", "--format", "json", *file_args],
            [sys.executable, "tools/quality/semantic_vacuity_gate.py", "--fail-on", "error", *file_args],
            [sys.executable, "tools/quality/detect_hollow_theorems.py", "--strict", *file_args],
            [sys.executable, "tools/infra/opengauss_screener.py", "--strict", "--json", *file_args],
        ])

    build_cmds: list[list[str]] = []
    if lib_modules:
        build_cmds.append([
            sys.executable,
            "tools/infra/run_locked_lake_build.py",
            "--wait-for-build-lock",
            "--wfail",
            *lib_modules,
        ])
    if non_lib_files:
        build_cmds.append([
            sys.executable,
            "tools/infra/run_locked_lean.py",
            "--wait-for-build-lock",
            "--check-files",
            *non_lib_files,
            "--",
            "-DwarningAsError=true",
        ])

    axiom_cmds: list[list[str]] = []
    if lib_modules:
        axiom_cmds.append([
            sys.executable,
            "tools/infra/axiom_check.py",
            "--json",
            *lib_modules,
        ])
    return {"lint_and_vacuity": lint_cmds, "locked_build": build_cmds, "axiom_audit": axiom_cmds}


def _porcelain_path(line: str) -> str:
    raw = line[3:] if len(line) > 3 and line[2] == " " else line.lstrip()
    if " -> " in raw:
        raw = raw.split(" -> ", 1)[1]
    return raw.strip().strip('"')


def _git_status_snapshot(repo_root: Path) -> set[str]:
    proc = run_subprocess_safe(["git", "status", "--porcelain"], cwd=repo_root, timeout=30)
    if proc.returncode != 0:
        return set()
    return set(proc.stdout.splitlines())


def run_tier4_checks(
    repo_root: Path,
    targets: list[ResolvedTarget],
    *,
    dry_run: bool = False,
) -> list[CheckOutcome]:
    """Run Tier 4 serialized acceptance checks (or dry-run plan)."""
    cmds = build_tier4_commands(repo_root, targets)
    if dry_run:
        return [
            CheckOutcome(
                "T4-E2E-DRY-RUN",
                4,
                "F9",
                "PASS",
                f"Dry-run planned {len(cmds['lint_and_vacuity'])} lint/vacuity, "
                f"{len(cmds['locked_build'])} locked build, and {len(cmds['axiom_audit'])} axiom_check commands",
                {"planned_commands": cmds},
            )
        ]

    before_git = _git_status_snapshot(repo_root)
    outcomes: list[CheckOutcome] = []

    # T4-E2E-01: Workspace integrity & non-blocking lock inspection
    from tools.build_lock import read_lock_metadata
    from tools.infra.build import _validate_lake_workspace_integrity

    ws_err = _validate_lake_workspace_integrity(repo_root)
    lock_meta = read_lock_metadata(DEFAULT_BUILD_LOCK_PATH)
    if ws_err is not None:
        outcomes.append(CheckOutcome("T4-E2E-01", 4, "F9", "FAIL", f"Workspace integrity failed: {ws_err}"))
    else:
        outcomes.append(
            CheckOutcome(
                "T4-E2E-01",
                4,
                "F9",
                "PASS",
                f"Workspace integrity clean (lock_owner={lock_meta.get('owner') if lock_meta else 'none'})",
                {"lock_metadata": lock_meta},
            )
        )

    # T4-E2E-02: Full static header + lint + placeholder + vacuity + opengauss + staged gate (if staged)
    existing_paths = [t.path for t in targets if t.exists]
    missing_targets = [t.rel_path for t in targets if not t.exists]
    t4_02_failures: list[str] = []
    if missing_targets:
        t4_02_failures.append(f"missing target files: {missing_targets}")
    for p in existing_paths:
        if not check_lean_copyright_header(p):
            t4_02_failures.append(f"{p.name}: missing exact 5-line Apache copyright header")
    for lint_rel in (
        "scripts/lint/required/style_lint.py",
        "scripts/lint/required/module_doc_lint.py",
        "scripts/lint/required/theorem_lint.py",
    ):
        if existing_paths:
            pr = run_subprocess_safe(
                [sys.executable, str(repo_root / lint_rel), *[str(p) for p in existing_paths]],
                cwd=repo_root,
                timeout=60,
            )
            if pr.returncode != 0:
                t4_02_failures.append(f"{Path(lint_rel).name} rc={pr.returncode}: {(pr.stdout + pr.stderr).strip()[:200]}")
    if existing_paths:
        ok_static, static_fails, _ = run_static_placeholder_vacuity_suite(
            repo_root, existing_paths, strict_opengauss=True
        )
        if not ok_static:
            t4_02_failures.extend(static_fails)
        # Check git staged status for target files; if staged, run proof_proxy_staged_gate.py --strict
        staged_q = run_subprocess_safe(
            ["git", "diff", "--cached", "--name-only", "--", *[t.rel_path for t in targets]],
            cwd=repo_root,
            timeout=30,
        )
        staged_files = [s.strip() for s in staged_q.stdout.splitlines() if s.strip()]
        if staged_files:
            pg = run_subprocess_safe(
                [sys.executable, str(repo_root / "tools/quality/proof_proxy_staged_gate.py"), "--strict", *staged_files],
                cwd=repo_root,
                timeout=120,
            )
            if pg.returncode != 0:
                t4_02_failures.append(f"proof_proxy_staged_gate --strict rc={pg.returncode}: {(pg.stdout + pg.stderr).strip()[:240]}")
    if t4_02_failures:
        outcomes.append(
            CheckOutcome(
                "T4-E2E-02",
                4,
                "F9",
                "FAIL",
                "Tier 4 static header/lint/vacuity/opengauss gate failed: " + "; ".join(t4_02_failures[:4]),
                {"failures": t4_02_failures},
            )
        )
    else:
        outcomes.append(
            CheckOutcome(
                "T4-E2E-02",
                4,
                "F9",
                "PASS",
                f"Full static header, style/doc/theorem lint, placeholder/vacuity & strict opengauss passed ({len(existing_paths)} target(s))",
            )
        )

    # T4-E2E-03: Serialized locked Lake build (with run_locked_lean fallback for non-library files)
    build_failures: list[str] = []
    for cmd in cmds["locked_build"]:
        proc = run_subprocess_safe(cmd, cwd=repo_root, timeout=900)
        if proc.returncode != 0:
            build_failures.append(f"{Path(cmd[1]).name} rc={proc.returncode}: {(proc.stderr or proc.stdout).strip()[:300]}")
    if not cmds["locked_build"]:
        build_failures.append("No buildable target modules or files specified")
    if build_failures:
        outcomes.append(
            CheckOutcome("T4-E2E-03", 4, "F9", "FAIL", "Locked Lean/Lake build failed: " + "; ".join(build_failures))
        )
    else:
        outcomes.append(
            CheckOutcome(
                "T4-E2E-03",
                4,
                "F9",
                "PASS",
                f"Serialized locked Lean/Lake build succeeded ({len(cmds['locked_build'])} command(s))",
            )
        )

    # T4-E2E-04: Kernel axiom check
    lib_modules = [t.module for t in targets if t.module]
    if not lib_modules:
        outcomes.append(
            CheckOutcome("T4-E2E-04", 4, "F9", "SKIP", "No library InfoGeometry.* modules for axiom_check.py")
        )
    else:
        ax_cmd = cmds["axiom_audit"][0]
        proc = run_subprocess_safe(ax_cmd, cwd=repo_root, timeout=300)
        if proc.returncode != 0:
            outcomes.append(
                CheckOutcome(
                    "T4-E2E-04",
                    4,
                    "F9",
                    "FAIL",
                    f"axiom_check.py failed (rc={proc.returncode}): {(proc.stdout + proc.stderr).strip()[:300]}",
                )
            )
        else:
            try:
                entries = parse_axiom_check_json_output(proc.stdout)
                ok_ax, ax_issues = validate_axiom_check_entries(entries, lib_modules)
            except (ValueError, json.JSONDecodeError) as exc:
                ok_ax, ax_issues = False, [str(exc)]
            if not ok_ax:
                outcomes.append(
                    CheckOutcome("T4-E2E-04", 4, "F9", "FAIL", "Kernel axiom check failed: " + "; ".join(ax_issues))
                )
            else:
                outcomes.append(
                    CheckOutcome(
                        "T4-E2E-04",
                        4,
                        "F9",
                        "PASS",
                        f"Kernel axiom_check.py passed for {len(lib_modules)} module(s) (permitted axioms only)",
                    )
                )

    # T4-E2E-05: Clean git delta check (no stray worktree changes outside scratch/)
    after_git = _git_status_snapshot(repo_root)
    new_entries = sorted(
        line for line in (after_git - before_git)
        if not _porcelain_path(line).startswith("scratch/")
    )
    if new_entries:
        outcomes.append(
            CheckOutcome(
                "T4-E2E-05",
                4,
                "F9",
                "FAIL",
                f"E2E run introduced unexpected git status changes: {new_entries}",
            )
        )
    else:
        outcomes.append(
            CheckOutcome(
                "T4-E2E-05",
                4,
                "F9",
                "PASS",
                "Clean git delta check passed (0 stray worktree changes)",
            )
        )

    return outcomes
