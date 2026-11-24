"""Tier 1 Epistemic Compilation, Contracts & Causal Poset checks (T1-EC-01 .. T1-EC-06)."""

from __future__ import annotations

import json
import re
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from tests.epistemic_compilation_e2e import (
    BASELINE_AUDIT_REPORT_REL,
    BASELINE_COMPILATION_DOC_REL,
    BASELINE_INTENT_ENVELOPE_REL,
    BASELINE_QA_REPORT_REL,
    BUCKET_ALLOWED_LABELS,
    CheckOutcome,
    REQUIRED_INTENT_ENVELOPE_KEYS,
    VALID_BUCKETS,
    VALID_RESULT_LABELS,
)

LABEL_RE = re.compile(
    r"\[(?:kernel_verified|accepted_limited_scope|bucket_2_conditional|bucket_3_open_debt|countermodel_found|documentation_only)\]"
)
BUCKET_RE = re.compile(r"\bBUCKET\s+[123]\b")
CLAIM_ID_TOKEN_RE = re.compile(r"`?([A-Za-z][A-Za-z0-9_./+-]{1,32})`?")
MERMAID_BLOCK_RE = re.compile(r"```mermaid\s*\n(.*?)```", re.S)
MERMAID_NODE_ID_RE = re.compile(r"[A-Za-z_](?:[A-Za-z0-9_]|-(?!-|\.))*" )
MERMAID_ARROW_RE = re.compile(
    r"(?:"
    r"(?:-->|-\.->|==>|---)\s*\|[^|\n]*\|(?:-->|-\.->|==>)?"
    r"|--\s*\|[^|\n]*\|-->"
    r"|--\s+[^\n]*?\s+-->"
    r"|-\.\s+[^\n]*?\s+\.->"
    r"|==\s+[^\n]*?\s+==>"
    r"|(?:--+>|-\.+->|==+>)"
    r")"
)


@dataclass
class ParsedClaimRow:
    doc_path: str
    line_no: int
    claim_id: str
    provenance: str
    statement: str
    carrier: str
    kind: str
    classification_col: str
    notes_col: str
    labels: list[str]
    explicit_buckets: list[str]
    implied_bucket: str | None


@dataclass
class DiscoveredArtifacts:
    compilation_docs: list[Path]
    intent_envelopes: list[Path]
    contract_jsons: list[Path]
    audit_reports: list[Path]
    qa_reports: list[Path]
    manifest_paths: list[Path]
    explicit_targets: list[str]


def _classify_json_artifact(path: Path, data: Any, out: DiscoveredArtifacts) -> None:
    if not isinstance(data, dict):
        return
    schema = str(data.get("schema", ""))
    if schema == "info_geometry.qms.intent_envelope.v1":
        if path not in out.intent_envelopes:
            out.intent_envelopes.append(path)
    elif schema == "info_geometry.opengauss.ground_truth_theorem_contract.v1":
        if path not in out.contract_jsons:
            out.contract_jsons.append(path)
    elif schema == "info_geometry.qms.audit_report.v1" or "audit_verdict" in data:
        if path not in out.audit_reports:
            out.audit_reports.append(path)
    elif "claims" in data or "target_artifacts" in data or "targets" in data:
        if path not in out.contract_jsons:
            out.contract_jsons.append(path)
    # Extract any target Lean paths/modules declared in JSON manifests
    for key in ("targets", "target_artifacts", "target_modules", "lean_targets"):
        val = data.get(key)
        if isinstance(val, list):
            for item in val:
                if isinstance(item, str) and (item.endswith(".lean") or item.startswith("InfoGeometry.")):
                    if item not in out.explicit_targets:
                        out.explicit_targets.append(item)
        elif isinstance(val, dict):
            for sub in val.values():
                if isinstance(sub, list):
                    for item in sub:
                        if isinstance(item, str) and (item.endswith(".lean") or item.startswith("InfoGeometry.")):
                            if item not in out.explicit_targets:
                                out.explicit_targets.append(item)
    owner_search = data.get("owner_search")
    if isinstance(owner_search, dict):
        for item in owner_search.get("target_artifacts", []):
            if isinstance(item, str) and item.endswith(".lean") and item not in out.explicit_targets:
                out.explicit_targets.append(item)


def _discover_qms_reports(
    repo_root: Path,
    out: DiscoveredArtifacts,
    *,
    only_audit_and_qa: bool,
    extra_target_refs: list[str] | None = None,
) -> None:
    qms_dir = repo_root / "artifacts" / "qms"
    if not qms_dir.is_dir():
        return
    is_full_repo = (repo_root / "lean" / "InfoGeometry.lean").is_file()
    patterns = ("*DRIVE*", "*AISTUDIO*", "*1v8J*", "*12bA*", "*1VUS*", "*1wzq*", "*CDE*")
    matched: list[Path] = []
    for pat in patterns:
        for p in sorted(qms_dir.glob(pat)):
            if p.is_file() and p not in matched:
                matched.append(p)
    # In synthetic temp repos, or in --manifest / --targets mode on a full repo for reports associated with the manifest/targets
    if not is_full_repo or only_audit_and_qa or bool(extra_target_refs):
        manifest_tokens: set[str] = set()
        manifest_refs: set[str] = set()
        for mp in out.manifest_paths:
            st = mp.stem.lower()
            manifest_tokens.add(st)
            if st.endswith("-intent_envelope"):
                manifest_tokens.add(st.removesuffix("-intent_envelope"))
            try:
                manifest_refs.add(mp.relative_to(repo_root).as_posix().lower())
            except ValueError:
                manifest_refs.add(mp.name.lower())
        for t_ref in (*out.explicit_targets, *(extra_target_refs or ())):
            t_str = str(t_ref).strip()
            if not t_str:
                continue
            p_ref = Path(t_str)
            try:
                if p_ref.is_absolute():
                    rel_p = p_ref.resolve().relative_to(repo_root.resolve())
                    manifest_refs.add(rel_p.as_posix().lower())
                else:
                    rel_p = p_ref
                    manifest_refs.add(p_ref.as_posix().lower())
            except ValueError:
                rel_p = p_ref
                manifest_refs.add(t_str.lower())
            manifest_tokens.add(p_ref.stem.lower())
            if t_str.startswith("InfoGeometry."):
                parts = t_str.split(".")
                manifest_refs.add(Path("lean", *parts).with_suffix(".lean").as_posix().lower())
                manifest_tokens.add(parts[-1].lower())
                manifest_refs.add(t_str.lower())
            elif "lean" in rel_p.parts:
                lean_idx = rel_p.parts.index("lean")
                mod_parts = rel_p.parts[lean_idx + 1 :]
                if mod_parts and mod_parts[-1].endswith(".lean"):
                    dotted = ".".join((*mod_parts[:-1], Path(mod_parts[-1]).stem)).lower()
                    manifest_refs.add(dotted)
        for jp in (*out.intent_envelopes, *out.contract_jsons):
            try:
                jdata = json.loads(jp.read_text(encoding="utf-8"))
            except (OSError, UnicodeDecodeError, json.JSONDecodeError):
                continue
            if isinstance(jdata, dict):
                for k in ("concept_id", "task_id", "contract_id"):
                    v = jdata.get(k)
                    if isinstance(v, str) and v.strip():
                        manifest_tokens.add(v.strip().lower())
        for pat in ("*audit_report*.json", "*qa_report*.md", "*-qa.md"):
            for p in sorted(qms_dir.glob(pat)):
                if not p.is_file() or p in matched:
                    continue
                if not is_full_repo:
                    matched.append(p)
                    continue
                name_l = p.name.lower()
                if any(
                    name_l.startswith(f"{tok}-")
                    or name_l.startswith(f"{tok}_")
                    or (len(tok) >= 2 and re.search(rf"(?<![a-z0-9]){re.escape(tok)}(?![a-z0-9])", name_l))
                    for tok in manifest_tokens
                    if tok
                ):
                    matched.append(p)
                    continue
                try:
                    txt_l = p.read_text(encoding="utf-8", errors="ignore").lower()
                except OSError:
                    continue
                if any(ref in txt_l for ref in manifest_refs if len(ref) >= 4):
                    matched.append(p)
    for p in matched:
        name_l = p.name.lower()
        is_qa_md = p.suffix.lower() == ".md" and ("qa_report" in name_l or name_l.endswith("-qa.md") or "qa" in name_l)
        if p.suffix.lower() == ".json":
            try:
                data = json.loads(p.read_text(encoding="utf-8"))
            except (OSError, UnicodeDecodeError, json.JSONDecodeError):
                continue
            is_audit = (
                isinstance(data, dict)
                and (
                    data.get("schema") == "info_geometry.qms.audit_report.v1"
                    or "audit_verdict" in data
                    or "audit_report" in name_l
                )
            )
            if only_audit_and_qa:
                if is_audit and p not in out.audit_reports:
                    out.audit_reports.append(p)
                    if p not in out.manifest_paths:
                        out.manifest_paths.append(p)
            else:
                if p not in out.manifest_paths:
                    out.manifest_paths.append(p)
                if is_audit and p not in out.audit_reports:
                    out.audit_reports.append(p)
                _classify_json_artifact(p, data, out)
        elif is_qa_md:
            if p not in out.qa_reports:
                out.qa_reports.append(p)
            if p not in out.manifest_paths:
                out.manifest_paths.append(p)


def discover_artifacts(
    repo_root: Path,
    manifest_args: list[str] | None = None,
    *,
    baseline_only: bool = False,
    raw_targets: list[str] | None = None,
) -> tuple[DiscoveredArtifacts, list[str]]:
    """Discover epistemic compilation docs, intent envelopes, contracts, and QA/audit reports."""
    out = DiscoveredArtifacts(
        compilation_docs=[],
        intent_envelopes=[],
        contract_jsons=[],
        audit_reports=[],
        qa_reports=[],
        manifest_paths=[],
        explicit_targets=[],
    )
    errors: list[str] = []

    if manifest_args:
        candidate_paths: list[Path] = []
        for raw in manifest_args:
            p = Path(raw)
            if not p.is_absolute():
                p = repo_root / p
            if not p.exists():
                errors.append(f"Manifest path not found: {raw}")
                continue
            if p.is_dir():
                candidate_paths.extend(sorted(p.rglob("*.json")))
                candidate_paths.extend(sorted(p.rglob("*.md")))
            else:
                candidate_paths.append(p)
        for p in candidate_paths:
            if p not in out.manifest_paths:
                out.manifest_paths.append(p)
            if p.suffix.lower() == ".md":
                name_l = p.name.lower()
                if "qa_report" in name_l or name_l.endswith("-qa.md"):
                    if p not in out.qa_reports:
                        out.qa_reports.append(p)
                elif p not in out.compilation_docs:
                    out.compilation_docs.append(p)
            elif p.suffix.lower() == ".json":
                try:
                    data = json.loads(p.read_text(encoding="utf-8"))
                except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
                    errors.append(f"Cannot parse manifest JSON {p}: {exc}")
                    continue
                _classify_json_artifact(p, data, out)
        if not out.compilation_docs:
            baseline_doc = repo_root / BASELINE_COMPILATION_DOC_REL
            if baseline_doc.is_file():
                out.compilation_docs.append(baseline_doc)
        # Always include active QMS audit/QA reports so T3-CONS-05 cannot be bypassed by --manifest
        _discover_qms_reports(repo_root, out, only_audit_and_qa=True, extra_target_refs=raw_targets)
        return out, errors

    if baseline_only:
        for rel, target_list in (
            (BASELINE_COMPILATION_DOC_REL, out.compilation_docs),
            (BASELINE_INTENT_ENVELOPE_REL, out.intent_envelopes),
            (BASELINE_AUDIT_REPORT_REL, out.audit_reports),
            (BASELINE_QA_REPORT_REL, out.qa_reports),
        ):
            p = repo_root / rel
            if p.is_file():
                target_list.append(p)
                if p not in out.manifest_paths:
                    out.manifest_paths.append(p)
        return out, errors

    # Auto-discovery across docs/, docs/contracts/, artifacts/qms/ for active run sources A..E
    docs_dir = repo_root / "docs"
    if docs_dir.is_dir():
        doc_globs = [
            "DRIVE_13ED_AISTUDIO_1v8J_EPISTEMIC_COMPILATION.md",
            "*1v8J*.md",
            "*13ED*.md",
            "*12bA*.md",
            "*1VUS*.md",
            "*1wzq*.md",
            "*CDE*.md",
            "*SOURCES_CDE*.md",
            "*TURNS46_84*.md",
        ]
        seen_docs: set[Path] = set()
        for pat in doc_globs:
            for p in sorted(docs_dir.glob(pat)):
                if p.is_file() and p not in seen_docs:
                    seen_docs.add(p)
                    out.compilation_docs.append(p)
                    out.manifest_paths.append(p)

    contracts_dir = docs_dir / "contracts"
    if contracts_dir.is_dir():
        for p in sorted(contracts_dir.glob("*.json")):
            if not p.is_file():
                continue
            try:
                data = json.loads(p.read_text(encoding="utf-8"))
            except (OSError, UnicodeDecodeError, json.JSONDecodeError):
                continue
            name_lower = p.name.lower()
            text_hint = any(k in name_lower for k in ("13ed", "1v8j", "12ba", "1vus", "1wzq", "cde", "drive", "aistudio", "epistemic"))
            if text_hint or data.get("schema") == "info_geometry.opengauss.ground_truth_theorem_contract.v1":
                if text_hint and p not in out.manifest_paths:
                    out.manifest_paths.append(p)
                if text_hint:
                    _classify_json_artifact(p, data, out)
                elif p not in out.contract_jsons:
                    out.contract_jsons.append(p)

    _discover_qms_reports(repo_root, out, only_audit_and_qa=False, extra_target_refs=raw_targets)

    # Ensure baseline files are included if present
    for rel, target_list in (
        (BASELINE_COMPILATION_DOC_REL, out.compilation_docs),
        (BASELINE_INTENT_ENVELOPE_REL, out.intent_envelopes),
        (BASELINE_AUDIT_REPORT_REL, out.audit_reports),
        (BASELINE_QA_REPORT_REL, out.qa_reports),
    ):
        p = repo_root / rel
        if p.is_file() and p not in target_list:
            target_list.append(p)
            if p not in out.manifest_paths:
                out.manifest_paths.append(p)

    return out, errors


def _split_markdown_table_row(raw_line: str) -> list[str]:
    """Split a Markdown table row on unescaped `|`, respecting `\\|` and inline code backticks."""
    s = raw_line.strip()
    if s.startswith("|"):
        s = s[1:]
    if s.endswith("|") and not s.endswith("\\|"):
        s = s[:-1]
    cells: list[str] = []
    buf: list[str] = []
    i = 0
    n = len(s)
    in_code = False
    while i < n:
        ch = s[i]
        if ch == "`":
            in_code = not in_code
            buf.append(ch)
            i += 1
            continue
        if ch == "\\" and not in_code and i + 1 < n:
            buf.append(ch)
            buf.append(s[i + 1])
            i += 2
            continue
        if ch == "|" and not in_code:
            cells.append("".join(buf).strip())
            buf.clear()
            i += 1
            continue
        buf.append(ch)
        i += 1
    cells.append("".join(buf).strip())
    return cells


def parse_claim_ledgers(compilation_docs: list[Path], repo_root: Path) -> list[ParsedClaimRow]:
    """Parse Markdown Claim Ledger tables across compilation docs."""
    rows: list[ParsedClaimRow] = []
    for doc in compilation_docs:
        try:
            rel = str(doc.relative_to(repo_root))
        except ValueError:
            rel = str(doc)
        lines = doc.read_text(encoding="utf-8").splitlines()
        in_claim_table = False
        header_cols: list[str] = []
        for idx, raw in enumerate(lines, 1):
            stripped = raw.strip()
            if not stripped.startswith("|"):
                in_claim_table = False
                header_cols = []
                continue
            cells = _split_markdown_table_row(stripped)
            if not in_claim_table:
                joined_lower = " ".join(cells).lower()
                if ("claim id" in joined_lower or (cells and cells[0].lower() == "id")) and (
                    "classification" in joined_lower or "bucket" in joined_lower or "status" in joined_lower
                ):
                    in_claim_table = True
                    header_cols = [c.lower() for c in cells]
                continue
            # Skip markdown separator row |---|---|
            if all(re.fullmatch(r":?-{2,}:?", c.replace(" ", "")) for c in cells if c):
                continue
            if len(cells) < 4:
                continue
            id_idx = next((i for i, h in enumerate(header_cols) if "claim id" in h or h == "id"), 0)
            prov_idx = next(
                (i for i, h in enumerate(header_cols) if i != id_idx and any(k in h for k in ("provenance", "turn", "source"))),
                1,
            )
            stmt_idx = next(
                (i for i, h in enumerate(header_cols) if i != id_idx and any(k in h for k in ("statement", "claim"))),
                2,
            )
            class_idx = next(
                (i for i, h in enumerate(header_cols) if any(k in h for k in ("classification", "label", "status"))),
                None,
            )
            bucket_idx = next(
                (i for i, h in enumerate(header_cols) if "bucket" in h and i != class_idx),
                None,
            )
            if class_idx is None:
                class_idx = bucket_idx if bucket_idx is not None else min(5, len(cells) - 1)
            carrier_idx = next(
                (i for i, h in enumerate(header_cols) if i != class_idx and any(k in h for k in ("carrier", "hypothes", "context", "disposition"))),
                3 if 3 != class_idx else None,
            )
            kind_idx = next(
                (i for i, h in enumerate(header_cols) if any(k in h for k in ("kind", "type"))),
                None,
            )
            notes_idx = next(
                (i for i, h in enumerate(header_cols) if i != class_idx and i != bucket_idx and any(k in h for k in ("note", "grounding", "owner", "gap", "reason"))),
                class_idx + 1 if class_idx + 1 < len(cells) else None,
            )

            id_cell = cells[id_idx] if len(cells) > id_idx else ""
            m_bt = re.match(r"^`([^`]+)`", id_cell)
            if m_bt:
                claim_id = m_bt.group(1).strip()
            else:
                m_id = CLAIM_ID_TOKEN_RE.search(id_cell)
                claim_id = m_id.group(1) if m_id else id_cell.strip("` ")
            prov = cells[prov_idx] if prov_idx is not None and len(cells) > prov_idx else ""
            stmt = cells[stmt_idx] if stmt_idx is not None and len(cells) > stmt_idx else ""
            carrier = cells[carrier_idx] if carrier_idx is not None and len(cells) > carrier_idx else ""
            kind = cells[kind_idx] if kind_idx is not None and len(cells) > kind_idx else ""
            class_col = cells[class_idx] if len(cells) > class_idx else ""
            if bucket_idx is not None and len(cells) > bucket_idx:
                class_col = f"{class_col} {cells[bucket_idx]}".strip()
            notes_col = cells[notes_idx] if notes_idx is not None and len(cells) > notes_idx else ""
            labels = LABEL_RE.findall(class_col)
            buckets = BUCKET_RE.findall(class_col)
            implied: str | None = buckets[0] if len(buckets) == 1 else None
            if implied is None and len(labels) == 1:
                if labels[0] == "[bucket_2_conditional]":
                    implied = "BUCKET 2"
                elif labels[0] == "[bucket_3_open_debt]":
                    implied = "BUCKET 3"
            rows.append(
                ParsedClaimRow(
                    doc_path=rel,
                    line_no=idx,
                    claim_id=claim_id,
                    provenance=prov,
                    statement=stmt,
                    carrier=carrier,
                    kind=kind,
                    classification_col=class_col,
                    notes_col=notes_col,
                    labels=labels,
                    explicit_buckets=buckets,
                    implied_bucket=implied,
                )
            )
    return rows


def check_t1_ec_01_claim_ledger(
    repo_root: Path,
    compilation_docs: list[Path],
) -> tuple[CheckOutcome, list[ParsedClaimRow]]:
    """T1-EC-01: Claim ledger completeness & exact single SKILL.md label + consistent bucket."""
    if not compilation_docs:
        return (
            CheckOutcome("T1-EC-01", 1, "F3", "FAIL", "No compilation documents discovered for claim ledger check"),
            [],
        )
    rows = parse_claim_ledgers(compilation_docs, repo_root)
    if not rows:
        return (
            CheckOutcome("T1-EC-01", 1, "F3", "FAIL", "No structured Claim Ledger tables parsed in compilation docs"),
            [],
        )
    bad: list[str] = []
    seen_ids: dict[str, str] = {}
    for row in rows:
        if not row.claim_id:
            bad.append(f"{row.doc_path}:{row.line_no}: empty Claim ID")
        elif row.claim_id in seen_ids:
            bad.append(f"{row.doc_path}:{row.line_no}: duplicate Claim ID {row.claim_id} (first at {seen_ids[row.claim_id]})")
        else:
            seen_ids[row.claim_id] = f"{row.doc_path}:{row.line_no}"
        if not row.provenance or not row.statement or not row.carrier:
            bad.append(f"{row.claim_id} ({row.doc_path}:{row.line_no}): empty provenance/statement/carrier")
        if len(row.labels) != 1:
            bad.append(f"{row.claim_id} ({row.doc_path}:{row.line_no}): expected exactly 1 label, found {row.labels}")
        if len(row.explicit_buckets) > 1:
            bad.append(f"{row.claim_id} ({row.doc_path}:{row.line_no}): multiple buckets {row.explicit_buckets}")
        elif len(row.explicit_buckets) == 0 and row.implied_bucket is None:
            bad.append(f"{row.claim_id} ({row.doc_path}:{row.line_no}): missing explicit BUCKET 1/2/3")
    if bad:
        return (
            CheckOutcome(
                "T1-EC-01",
                1,
                "F3",
                "FAIL",
                f"Claim ledger validation failed ({len(bad)} issues): " + "; ".join(bad[:5]),
                {"total_claims": len(rows), "issues": bad},
            ),
            rows,
        )
    return (
        CheckOutcome(
            "T1-EC-01",
            1,
            "F3",
            "PASS",
            f"Claim ledger verified ({len(rows)} atomic claims, each with unique ID, provenance, label, and bucket)",
            {"total_claims": len(rows)},
        ),
        rows,
    )


def check_t1_ec_02_owner_grounding(
    repo_root: Path,
    artifacts: DiscoveredArtifacts,
) -> CheckOutcome:
    """T1-EC-02: Owner-search paths (reused_owners & contract owner_declarations) resolve on disk."""
    checked = 0
    missing: list[str] = []
    for env_path in artifacts.intent_envelopes:
        data = json.loads(env_path.read_text(encoding="utf-8"))
        owner_search = data.get("owner_search", {})
        for raw in owner_search.get("reused_owners", []):
            checked += 1
            if not (repo_root / raw).is_file():
                missing.append(f"{env_path.name}: reused_owner missing -> {raw}")
    for c_path in artifacts.contract_jsons:
        data = json.loads(c_path.read_text(encoding="utf-8"))
        for decl in data.get("owner_declarations", []):
            sp = decl.get("source_path")
            if isinstance(sp, str) and sp.endswith(".lean"):
                checked += 1
                if not (repo_root / sp).is_file():
                    missing.append(f"{c_path.name}: owner_declaration source_path missing -> {sp}")
        for reused in data.get("reused_owners", []):
            if isinstance(reused, str) and reused.endswith(".lean"):
                checked += 1
                if not (repo_root / reused).is_file():
                    missing.append(f"{c_path.name}: reused_owner missing -> {reused}")
    if checked == 0:
        return CheckOutcome(
            "T1-EC-02",
            1,
            "F3",
            "FAIL",
            "No owner_search.reused_owners or contract owner_declarations found to verify",
        )
    if missing:
        return CheckOutcome(
            "T1-EC-02",
            1,
            "F3",
            "FAIL",
            f"Owner grounding failed ({len(missing)}/{checked} missing): " + "; ".join(missing[:5]),
            {"checked": checked, "missing": missing},
        )
    return CheckOutcome(
        "T1-EC-02",
        1,
        "F3",
        "PASS",
        f"Owner-search grounding verified ({checked}/{checked} owner .lean paths resolved on disk)",
        {"checked": checked},
    )


def check_t1_ec_03_theorem_contracts(
    repo_root: Path,
    artifacts: DiscoveredArtifacts,
) -> CheckOutcome:
    """T1-EC-03: Ground-truth theorem contracts (JSON schema or §4 contract sections) complete."""
    json_checked = 0
    md_checked = 0
    issues: list[str] = []

    for c_path in artifacts.contract_jsons:
        data = json.loads(c_path.read_text(encoding="utf-8"))
        if data.get("schema") == "info_geometry.opengauss.ground_truth_theorem_contract.v1":
            json_checked += 1
            for req in ("contract_id", "claim", "carrier", "owner_declarations", "smallest_gap", "out_of_scope"):
                if req not in data or not data[req]:
                    issues.append(f"{c_path.name}: missing contract field `{req}`")

    for doc in artifacts.compilation_docs:
        text = doc.read_text(encoding="utf-8")
        # Prefer #### Track ... leaf contract sections if present, else ### 4.\d+ / ### Target ... / ### Contract ...
        sub_sections = re.split(r"(?m)^####\s+", text)
        track_secs = [
            s for s in sub_sections[1:]
            if re.match(r"Track\b", s.splitlines()[0], re.I)
        ]
        if track_secs:
            for sec in track_secs:
                md_checked += 1
                heading = sec.splitlines()[0].strip()
                sec_lower = sec.lower()
                if ".lean" not in sec_lower and "target file" not in sec_lower:
                    issues.append(f"{doc.name} `#### {heading}` missing target `.lean` file")
                if not any(k in sec_lower for k in ("carrier", "over `[", "ring", "commring", "quadraticform", "matrix", "complex", "ℂ", "datum", "required imports")):
                    issues.append(f"{doc.name} `#### {heading}` missing carrier/typeclass clause")
                if not any(k in sec_lower for k in ("proposition", "signature", "ground-truth contracts", "prove")):
                    issues.append(f"{doc.name} `#### {heading}` missing exact theorem contract/proposition")
                if "excluded" not in sec_lower and "out of scope" not in sec_lower:
                    issues.append(f"{doc.name} `#### {heading}` missing excluded/out-of-scope clause")
        else:
            sections = re.split(r"(?m)^###\s+", text)
            contract_secs = [
                s for s in sections[1:]
                if re.match(r".*\bContract\b", s.splitlines()[0], re.I)
            ]
            for sec in contract_secs:
                md_checked += 1
                heading = sec.splitlines()[0].strip()
                sec_lower = sec.lower()
                for marker in ("target file", "carrier", "proposition", "excluded"):
                    if marker not in sec_lower and (marker != "proposition" or "signature" not in sec_lower):
                        issues.append(f"{doc.name} `### {heading}` missing `{marker}` contract clause")

    if json_checked == 0 and md_checked == 0:
        return CheckOutcome(
            "T1-EC-03",
            1,
            "F3",
            "FAIL",
            "No ground-truth theorem contracts found (neither v1 contract JSONs nor Markdown contract sections)",
        )
    if issues:
        return CheckOutcome(
            "T1-EC-03",
            1,
            "F3",
            "FAIL",
            "Theorem contract completeness failed: " + "; ".join(issues[:5]),
            {"json_contracts": json_checked, "md_contracts": md_checked, "issues": issues},
        )
    return CheckOutcome(
        "T1-EC-03",
        1,
        "F3",
        "PASS",
        f"Ground-truth theorem contracts verified ({json_checked} JSON contracts, {md_checked} Markdown contract sections)",
        {"json_contracts": json_checked, "md_contracts": md_checked},
    )


def _consume_mermaid_shape_blocks(line: str, pos: int) -> int:
    """Advance past Mermaid node shape annotations `[...]`, `(...)`, `{...}` and `:::cls`."""
    n = len(line)
    pairs = {"[": "]", "(": ")", "{": "}"}
    while pos < n and line[pos] in pairs:
        stack = [pairs[line[pos]]]
        pos += 1
        in_quote = False
        while pos < n and stack:
            ch = line[pos]
            if in_quote:
                if ch == "\\" and pos + 1 < n:
                    pos += 2
                    continue
                if ch == '"':
                    in_quote = False
            else:
                if ch == '"':
                    in_quote = True
                elif ch in pairs:
                    stack.append(pairs[ch])
                elif ch == stack[-1]:
                    stack.pop()
            pos += 1
    m_cls = re.match(r":::[A-Za-z0-9_-]+", line[pos:])
    if m_cls:
        pos += len(m_cls.group(0))
    return pos


def _consume_mermaid_node_group(line: str, pos: int) -> tuple[list[str], int]:
    """Parse one or more `&`-separated Mermaid node references at `pos`."""
    n = len(line)
    group: list[str] = []
    while pos < n:
        while pos < n and line[pos].isspace():
            pos += 1
        m_id = MERMAID_NODE_ID_RE.match(line, pos)
        if not m_id:
            break
        group.append(m_id.group(0))
        pos = _consume_mermaid_shape_blocks(line, m_id.end())
        while pos < n and line[pos].isspace():
            pos += 1
        if pos < n and line[pos] == "&":
            pos += 1
            continue
        break
    return group, pos


def parse_mermaid_dag(mermaid_text: str) -> tuple[set[str], list[tuple[str, str]]]:
    nodes: set[str] = set()
    edges: list[tuple[str, str]] = []
    for raw in mermaid_text.splitlines():
        line = raw.strip()
        if not line or line.startswith("%%"):
            continue
        if re.match(r"^(?:flowchart|graph|subgraph|end|style|classDef|class|click|linkStyle|direction)\b", line):
            continue
        if line.endswith(";"):
            line = line[:-1].rstrip()
        prev_group, pos = _consume_mermaid_node_group(line, 0)
        if not prev_group:
            continue
        nodes.update(prev_group)
        while pos < len(line):
            while pos < len(line) and line[pos].isspace():
                pos += 1
            m_arrow = MERMAID_ARROW_RE.match(line, pos)
            if not m_arrow:
                break
            next_group, pos = _consume_mermaid_node_group(line, m_arrow.end())
            if not next_group:
                break
            nodes.update(next_group)
            for u in prev_group:
                for v in next_group:
                    edges.append((u, v))
            prev_group = next_group
    return nodes, edges


def kahn_topological_sort(nodes: set[str], edges: list[tuple[str, str]]) -> tuple[bool, list[str], set[str]]:
    """Return (is_acyclic, topo_order, isolated_nodes)."""
    indeg: dict[str, int] = {n: 0 for n in nodes}
    outdeg: dict[str, int] = {n: 0 for n in nodes}
    adj: dict[str, list[str]] = {n: [] for n in nodes}
    for u, v in edges:
        indeg.setdefault(u, 0)
        indeg[v] = indeg.get(v, 0) + 1
        outdeg[u] = outdeg.get(u, 0) + 1
        outdeg.setdefault(v, 0)
        adj.setdefault(u, []).append(v)
        adj.setdefault(v, [])
    isolated = {n for n in nodes if indeg.get(n, 0) == 0 and outdeg.get(n, 0) == 0}
    q = deque(sorted(n for n, d in indeg.items() if d == 0))
    order: list[str] = []
    while q:
        u = q.popleft()
        order.append(u)
        for v in adj[u]:
            indeg[v] -= 1
            if indeg[v] == 0:
                q.append(v)
    return len(order) == len(indeg), order, isolated


def check_t1_ec_04_causal_poset_dag(compilation_docs: list[Path]) -> CheckOutcome:
    """T1-EC-04: Causal poset Mermaid DAG parses cleanly and is strictly acyclic (0 cycles, 0 isolated nodes)."""
    dags_checked = 0
    total_nodes = 0
    total_edges = 0
    issues: list[str] = []
    for doc in compilation_docs:
        text = doc.read_text(encoding="utf-8")
        for idx, block in enumerate(MERMAID_BLOCK_RE.findall(text), 1):
            nodes, edges = parse_mermaid_dag(block)
            if not nodes and not edges:
                continue
            dags_checked += 1
            total_nodes += len(nodes)
            total_edges += len(edges)
            acyclic, _order, isolated = kahn_topological_sort(nodes, edges)
            if not acyclic:
                issues.append(f"{doc.name} Mermaid #{idx}: cycle detected")
            if isolated:
                issues.append(f"{doc.name} Mermaid #{idx}: isolated nodes {sorted(isolated)}")
    if dags_checked == 0:
        return CheckOutcome("T1-EC-04", 1, "F3", "FAIL", "No Mermaid causal poset DAG found in compilation docs")
    if issues:
        return CheckOutcome(
            "T1-EC-04",
            1,
            "F3",
            "FAIL",
            "Causal poset DAG check failed: " + "; ".join(issues),
            {"dags": dags_checked, "nodes": total_nodes, "edges": total_edges},
        )
    return CheckOutcome(
        "T1-EC-04",
        1,
        "F3",
        "PASS",
        f"Causal poset DAG strictly acyclic via Kahn's topological sort ({dags_checked} DAG(s), {total_nodes} nodes, {total_edges} edges, 0 cycles, 0 isolated)",
        {"dags": dags_checked, "nodes": total_nodes, "edges": total_edges},
    )


def check_t1_ec_05_intent_envelope_schema(artifacts: DiscoveredArtifacts) -> CheckOutcome:
    """T1-EC-05: Formal intent envelope JSON(s) conform to info_geometry.qms.intent_envelope.v1 (§3.6)."""
    if not artifacts.intent_envelopes:
        return CheckOutcome(
            "T1-EC-05",
            1,
            "F3",
            "FAIL",
            "No intent envelope JSON found (expected info_geometry.qms.intent_envelope.v1)",
        )
    issues: list[str] = []
    for env_path in artifacts.intent_envelopes:
        data = json.loads(env_path.read_text(encoding="utf-8"))
        if data.get("schema") != "info_geometry.qms.intent_envelope.v1":
            issues.append(f"{env_path.name}: invalid schema {data.get('schema')!r}")
        for key in REQUIRED_INTENT_ENVELOPE_KEYS:
            if key not in data or data[key] in (None, "", [], {}):
                issues.append(f"{env_path.name}: missing or empty `{key}`")
        risk = str(data.get("risk_level", ""))
        if not re.fullmatch(r"R[0-5]", risk):
            issues.append(f"{env_path.name}: invalid risk_level {risk!r}")
    if issues:
        return CheckOutcome(
            "T1-EC-05",
            1,
            "F3",
            "FAIL",
            "Intent envelope schema validation failed: " + "; ".join(issues[:5]),
        )
    return CheckOutcome(
        "T1-EC-05",
        1,
        "F3",
        "PASS",
        f"Intent envelope schema verified ({len(artifacts.intent_envelopes)} envelope(s) conform to §3.6)",
    )


def check_t1_ec_06_open_debt_and_f8(
    compilation_docs: list[Path],
    rows: list[ParsedClaimRow],
    effective_mode: str,
) -> CheckOutcome:
    """T1-EC-06: Explicit BUCKET 3 open debt recorded; in live84, verify Chunks 64-66 & 70-83 (F8) grounding."""
    bucket3_rows = [r for r in rows if r.implied_bucket == "BUCKET 3" or "[bucket_3_open_debt]" in r.labels]
    if not bucket3_rows:
        return CheckOutcome(
            "T1-EC-06",
            1,
            "F8",
            "FAIL",
            "No [bucket_3_open_debt] / BUCKET 3 open-debt claims recorded in ledger",
        )
    if effective_mode == "live84":
        combined = "\n".join(p.read_text(encoding="utf-8") for p in compilation_docs).lower()
        required_f8_terms = (
            ("grh-lean-verification", "grh"),
            ("upstream/pr/24", "pr/24"),
            ("obstructed_by", "lifts_to_grade", "obstruction ladder", "3-rung"),
        )
        missing_groups = [
            "/".join(group) for group in required_f8_terms if not any(term in combined for term in group)
        ]
        if missing_groups:
            return CheckOutcome(
                "T1-EC-06",
                1,
                "F8",
                "FAIL",
                "live84 Turn 46-84 F8 grounding missing in compilation docs: " + ", ".join(missing_groups),
            )
    return CheckOutcome(
        "T1-EC-06",
        1,
        "F8",
        "PASS",
        f"Explicit BUCKET 3 open debt verified ({len(bucket3_rows)} BUCKET 3 rows; mode={effective_mode})",
        {"bucket3_count": len(bucket3_rows), "mode": effective_mode},
    )


def run_tier1_epistemic_checks(
    repo_root: Path,
    artifacts: DiscoveredArtifacts,
    effective_mode: str,
) -> tuple[list[CheckOutcome], list[ParsedClaimRow]]:
    ec01, rows = check_t1_ec_01_claim_ledger(repo_root, artifacts.compilation_docs)
    outcomes = [
        ec01,
        check_t1_ec_02_owner_grounding(repo_root, artifacts),
        check_t1_ec_03_theorem_contracts(repo_root, artifacts),
        check_t1_ec_04_causal_poset_dag(artifacts.compilation_docs),
        check_t1_ec_05_intent_envelope_schema(artifacts),
        check_t1_ec_06_open_debt_and_f8(artifacts.compilation_docs, rows, effective_mode),
    ]
    return outcomes, rows
