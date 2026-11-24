"""Tier 1 Source Intake & Provenance checks (T1-INTAKE-01 .. T1-INTAKE-06)."""

from __future__ import annotations

import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

from tests.epistemic_compilation_e2e import (
    ADDITIONAL_SOURCES,
    ALL_FIVE_SOURCE_IDS,
    BASELINE_COMPILATION_DOC_REL,
    CheckOutcome,
    SOURCE_A_ALT_RELS,
    SOURCE_A_BYTES,
    SOURCE_A_ID,
    SOURCE_A_LINES,
    SOURCE_A_REL,
    SOURCE_A_SHA256,
    SOURCE_B_BASELINE45_BYTES,
    SOURCE_B_BASELINE45_CHUNKS,
    SOURCE_B_BASELINE45_SHA256,
    SOURCE_B_EXTRACT_DIR_REL,
    SOURCE_B_ID,
    SOURCE_B_LIVE84_BYTES,
    SOURCE_B_LIVE84_MIN_CHUNKS,
    SOURCE_B_LIVE84_SHA256_PREFIX,
    SOURCE_B_REL,
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        while True:
            chunk = fh.read(65536)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()


def run_subprocess_safe(
    cmd: list[str],
    *,
    cwd: Path,
    timeout: int = 120,
) -> subprocess.CompletedProcess[str]:
    """Run subprocess in its own process group; forward SIGINT on timeout so no children leak."""
    popen_kwargs: dict[str, Any] = {
        "cwd": cwd,
        "stdout": subprocess.PIPE,
        "stderr": subprocess.PIPE,
        "text": True,
    }
    if os.name == "posix":
        popen_kwargs["start_new_session"] = True
    proc = subprocess.Popen(cmd, **popen_kwargs)
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
        return subprocess.CompletedProcess(cmd, proc.returncode, stdout, stderr)
    except subprocess.TimeoutExpired as exc:
        if os.name == "posix":
            try:
                os.killpg(proc.pid, signal.SIGINT)
            except ProcessLookupError:
                pass
        else:
            proc.terminate()
        try:
            stdout, stderr = proc.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            if os.name == "posix":
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            else:
                proc.kill()
            stdout, stderr = proc.communicate()
        raise subprocess.TimeoutExpired(cmd, timeout, output=stdout, stderr=stderr) from exc


def resolve_effective_source_b_mode(repo_root: Path, requested_mode: str) -> str:
    """Resolve 'auto' to 'live84' if >=84 chunks on disk else 'baseline45'."""
    if requested_mode in ("baseline45", "live84"):
        return requested_mode
    src_b = repo_root / SOURCE_B_REL
    if not src_b.is_file():
        return "baseline45"
    try:
        data = json.loads(src_b.read_text(encoding="utf-8"))
        if isinstance(data, dict):
            cp = data.get("chunkedPrompt")
            chunks = cp.get("chunks", []) if isinstance(cp, dict) else []
            if isinstance(chunks, list) and len(chunks) >= SOURCE_B_LIVE84_MIN_CHUNKS:
                return "live84"
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        pass
    return "baseline45"


def check_t1_intake_01_source_a(repo_root: Path) -> CheckOutcome:
    """T1-INTAKE-01: Source A (13ED) existence, UTF-8, byte size, line count, SHA256, and alt copies."""
    src_a = repo_root / SOURCE_A_REL
    if not src_a.is_file():
        return CheckOutcome(
            "T1-INTAKE-01",
            1,
            "F1",
            "FAIL",
            f"Missing Source A file: {SOURCE_A_REL}",
            {"path": str(src_a)},
        )
    raw = src_a.read_bytes()
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        return CheckOutcome(
            "T1-INTAKE-01",
            1,
            "F1",
            "FAIL",
            f"Source A is not valid UTF-8: {exc}",
        )
    digest = sha256_bytes(raw)
    lines = len(text.splitlines())
    mismatches: list[str] = []
    if len(raw) != SOURCE_A_BYTES:
        mismatches.append(f"bytes={len(raw)} (expected {SOURCE_A_BYTES})")
    if lines != SOURCE_A_LINES:
        mismatches.append(f"lines={lines} (expected {SOURCE_A_LINES})")
    if digest != SOURCE_A_SHA256:
        mismatches.append(f"sha256={digest} (expected {SOURCE_A_SHA256})")
    for alt_rel in SOURCE_A_ALT_RELS:
        alt_path = repo_root / alt_rel
        if alt_path.is_file() and alt_path.read_bytes() != raw:
            mismatches.append(f"bytewise mismatch against {alt_rel}")
    if mismatches:
        return CheckOutcome(
            "T1-INTAKE-01",
            1,
            "F1",
            "FAIL",
            "Source A parity check failed: " + "; ".join(mismatches),
            {"bytes": len(raw), "lines": lines, "sha256": digest},
        )
    return CheckOutcome(
        "T1-INTAKE-01",
        1,
        "F1",
        "PASS",
        f"Source A verified ({len(raw)} B, {lines} L, sha256={digest[:12]}...)",
        {"bytes": len(raw), "lines": lines, "sha256": digest},
    )


def check_t1_intake_02_source_b(repo_root: Path, effective_mode: str) -> CheckOutcome:
    """T1-INTAKE-02: Source B JSON schema, chunk count, byte size, SHA256, and monotonic timestamps."""
    src_b = repo_root / SOURCE_B_REL
    if not src_b.is_file():
        return CheckOutcome(
            "T1-INTAKE-02",
            1,
            "F2",
            "FAIL",
            f"Missing Source B JSON: {SOURCE_B_REL}",
        )
    raw = src_b.read_bytes()
    digest = sha256_bytes(raw)
    try:
        data = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        return CheckOutcome(
            "T1-INTAKE-02",
            1,
            "F2",
            "FAIL",
            f"Source B JSON parse error: {exc}",
        )
    if not isinstance(data, dict):
        return CheckOutcome("T1-INTAKE-02", 1, "F2", "FAIL", "Source B JSON root is not an object")
    required_top = {"runSettings", "systemInstruction", "chunkedPrompt"}
    missing_top = sorted(required_top - set(data.keys()))
    if missing_top:
        return CheckOutcome(
            "T1-INTAKE-02",
            1,
            "F2",
            "FAIL",
            f"Source B missing top-level keys: {missing_top}",
        )
    cp = data.get("chunkedPrompt")
    if not isinstance(cp, dict):
        return CheckOutcome(
            "T1-INTAKE-02",
            1,
            "F2",
            "FAIL",
            "Source B chunkedPrompt is not an object",
        )
    chunks = cp.get("chunks")
    if not isinstance(chunks, list) or not chunks:
        return CheckOutcome(
            "T1-INTAKE-02",
            1,
            "F2",
            "FAIL",
            "Source B chunkedPrompt.chunks is missing or empty",
        )
    issues: list[str] = []
    bad_ts = [
        i for i, c in enumerate(chunks)
        if not isinstance(c, dict) or (c.get("createTime") is not None and not isinstance(c.get("createTime"), str))
    ]
    if bad_ts:
        issues.append(f"non-string createTime at chunk index {bad_ts[0]}")
    else:
        timestamps = [c.get("createTime") for c in chunks if c.get("createTime")]
        non_monotonic = [
            (i, timestamps[i - 1], timestamps[i])
            for i in range(1, len(timestamps))
            if timestamps[i] < timestamps[i - 1]
        ]
        if non_monotonic:
            issues.append(f"non-monotonic createTime at index {non_monotonic[0]}")
    if effective_mode == "baseline45":
        if len(chunks) == SOURCE_B_BASELINE45_CHUNKS:
            if len(raw) != SOURCE_B_BASELINE45_BYTES:
                issues.append(f"bytes={len(raw)} (expected {SOURCE_B_BASELINE45_BYTES})")
            if digest != SOURCE_B_BASELINE45_SHA256:
                issues.append(f"sha256={digest} (expected {SOURCE_B_BASELINE45_SHA256})")
        elif len(chunks) >= SOURCE_B_LIVE84_MIN_CHUNKS:
            # Source B on disk was already refreshed to >=84 chunks; verify 45-chunk prefix + live84 integrity
            c44 = chunks[44]
            if not isinstance(c44, dict):
                issues.append("45-chunk prefix end chunk (index 44) is not an object")
            elif c44.get("createTime") != "2026-11-18T22:47:27.873Z":
                issues.append(f"45-chunk prefix end timestamp mismatch: {c44.get('createTime')!r}")
            if len(raw) != SOURCE_B_LIVE84_BYTES or not digest.startswith(SOURCE_B_LIVE84_SHA256_PREFIX):
                issues.append(f"refreshed >=84-chunk file failed live84 parity (bytes={len(raw)}, sha256={digest[:12]})")
        else:
            issues.append(f"chunks={len(chunks)} (expected {SOURCE_B_BASELINE45_CHUNKS} or refreshed >= {SOURCE_B_LIVE84_MIN_CHUNKS})")
    else:
        if len(chunks) < SOURCE_B_LIVE84_MIN_CHUNKS:
            issues.append(f"chunks={len(chunks)} (expected >= {SOURCE_B_LIVE84_MIN_CHUNKS} in live84)")
        if len(raw) != SOURCE_B_LIVE84_BYTES:
            issues.append(f"bytes={len(raw)} (expected {SOURCE_B_LIVE84_BYTES} in live84)")
        if not digest.startswith(SOURCE_B_LIVE84_SHA256_PREFIX):
            issues.append(
                f"sha256={digest} (expected prefix {SOURCE_B_LIVE84_SHA256_PREFIX} in live84)"
            )
    if issues:
        return CheckOutcome(
            "T1-INTAKE-02",
            1,
            "F2",
            "FAIL",
            f"Source B ({effective_mode}) check failed: " + "; ".join(issues),
            {"chunks": len(chunks), "bytes": len(raw), "sha256": digest, "mode": effective_mode},
        )
    return CheckOutcome(
        "T1-INTAKE-02",
        1,
        "F2",
        "PASS",
        f"Source B ({effective_mode}) verified ({len(chunks)} chunks, {len(raw)} B, sha256={digest[:12]}...)",
        {"chunks": len(chunks), "bytes": len(raw), "sha256": digest, "mode": effective_mode},
    )


def check_t1_intake_03_extract_parity(repo_root: Path) -> CheckOutcome:
    """T1-INTAKE-03: Deterministic extract_aistudio_math.py parity against cached manifest.json."""
    src_b = repo_root / SOURCE_B_REL
    extract_script = repo_root / "tools" / "infra" / "extract_aistudio_math.py"
    cached_manifest_path = repo_root / SOURCE_B_EXTRACT_DIR_REL / "manifest.json"
    if not src_b.is_file() or not extract_script.is_file() or not cached_manifest_path.is_file():
        return CheckOutcome(
            "T1-INTAKE-03",
            1,
            "F2",
            "FAIL",
            "Missing Source B JSON, extract_aistudio_math.py, or cached extract manifest.json",
        )
    try:
        cached_manifest = json.loads(cached_manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return CheckOutcome(
            "T1-INTAKE-03",
            1,
            "F2",
            "FAIL",
            f"Cannot parse cached manifest.json: {exc}",
        )
    with tempfile.TemporaryDirectory(prefix="epistemic_extract_parity_") as tmp_dir:
        proc = run_subprocess_safe(
            [sys.executable, str(extract_script), str(src_b), "--output-dir", tmp_dir],
            cwd=repo_root,
            timeout=60,
        )
        if proc.returncode != 0:
            return CheckOutcome(
                "T1-INTAKE-03",
                1,
                "F2",
                "FAIL",
                f"extract_aistudio_math.py failed (rc={proc.returncode}): {proc.stderr.strip()}",
            )
        stem = src_b.name.removesuffix(".json")
        regen_manifest_path = Path(tmp_dir) / stem / "manifest.json"
        if not regen_manifest_path.is_file():
            return CheckOutcome(
                "T1-INTAKE-03",
                1,
                "F2",
                "FAIL",
                "extract_aistudio_math.py did not produce manifest.json",
            )
        regen_manifest = json.loads(regen_manifest_path.read_text(encoding="utf-8"))
    keys_to_match = (
        "source_sha256",
        "source_bytes",
        "turn_count",
        "role_counts",
        "transcript_characters",
        "math_expression_count",
        "fence_count",
        "tagged_lean_fences",
        "unterminated_fences",
        "unlabelled_lean_candidates",
        "first_timestamp",
        "last_timestamp",
    )
    diffs = [
        f"{k}: cached={cached_manifest.get(k)!r} vs regen={regen_manifest.get(k)!r}"
        for k in keys_to_match
        if cached_manifest.get(k) != regen_manifest.get(k)
    ]
    if diffs:
        return CheckOutcome(
            "T1-INTAKE-03",
            1,
            "F2",
            "FAIL",
            "extract_aistudio_math.py parity mismatch: " + "; ".join(diffs),
        )
    return CheckOutcome(
        "T1-INTAKE-03",
        1,
        "F2",
        "PASS",
        f"extract_aistudio_math.py deterministic parity verified (turns={regen_manifest['turn_count']}, math={regen_manifest['math_expression_count']})",
        {"turn_count": regen_manifest["turn_count"], "math_expression_count": regen_manifest["math_expression_count"]},
    )


def check_t1_intake_04_transcript_turns(repo_root: Path) -> CheckOutcome:
    """T1-INTAKE-04: transcript.md has ## Turn 0001..N headers matching manifest turn_count and companion extract files."""
    extract_dir = repo_root / SOURCE_B_EXTRACT_DIR_REL
    manifest_path = extract_dir / "manifest.json"
    transcript_path = extract_dir / "transcript.md"
    required_files = (
        "manifest.json",
        "transcript.md",
        "math_expressions.md",
        "all_code_fences.jsonl",
        "lean_fences.md",
        "unlabelled_lean_candidates.md",
    )
    missing = [name for name in required_files if not (extract_dir / name).is_file()]
    if missing:
        return CheckOutcome(
            "T1-INTAKE-04",
            1,
            "F2",
            "FAIL",
            f"Missing extract artifact(s): {missing}",
        )
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    turn_count = int(manifest.get("turn_count", 0))
    transcript_text = transcript_path.read_text(encoding="utf-8")
    found_turns = [int(m.group(1)) for m in re.finditer(r"^## Turn (\d{4})\b", transcript_text, re.M)]
    expected_turns = list(range(1, turn_count + 1))
    if found_turns != expected_turns:
        return CheckOutcome(
            "T1-INTAKE-04",
            1,
            "F2",
            "FAIL",
            f"transcript.md turn headers mismatch: found {len(found_turns)} turns, expected 1..{turn_count}",
        )
    return CheckOutcome(
        "T1-INTAKE-04",
        1,
        "F2",
        "PASS",
        f"transcript.md verified with contiguous ## Turn 0001..{turn_count:04d} headers and all 6 extract files",
        {"turn_count": turn_count},
    )


def check_t1_intake_05_provenance_metadata(
    repo_root: Path,
    compilation_docs: list[Path],
    effective_mode: str,
) -> CheckOutcome:
    """T1-INTAKE-05: Compilation doc(s) record Source A & B IDs, byte sizes, SHA256s, and chunk/line counts."""
    if not compilation_docs:
        return CheckOutcome(
            "T1-INTAKE-05",
            1,
            "F1",
            "FAIL",
            "No epistemic compilation markdown documents found",
        )
    combined = "\n".join(p.read_text(encoding="utf-8") for p in compilation_docs)
    src_b = repo_root / SOURCE_B_REL
    if effective_mode == "baseline45":
        b_bytes = SOURCE_B_BASELINE45_BYTES
        b_sha = SOURCE_B_BASELINE45_SHA256
    else:
        b_bytes = src_b.stat().st_size if src_b.is_file() else SOURCE_B_BASELINE45_BYTES
        b_sha = sha256_file(src_b) if src_b.is_file() else SOURCE_B_BASELINE45_SHA256
    missing_items: list[str] = []
    if SOURCE_A_ID not in combined:
        missing_items.append(f"Source A ID {SOURCE_A_ID}")
    if SOURCE_B_ID not in combined:
        missing_items.append(f"Source B ID {SOURCE_B_ID}")
    if "36,955" not in combined and "36955" not in combined:
        missing_items.append("Source A byte size 36,955")
    if "288" not in combined:
        missing_items.append("Source A line count 288")
    if SOURCE_A_SHA256[:12] not in combined:
        missing_items.append(f"Source A SHA256 prefix {SOURCE_A_SHA256[:12]}")
    formatted_b = f"{b_bytes:,}"
    if formatted_b not in combined and str(b_bytes) not in combined:
        missing_items.append(f"Source B byte size {formatted_b}")
    if b_sha[:12] not in combined:
        missing_items.append(f"Source B SHA256 prefix {b_sha[:12]}")
    if effective_mode == "live84" and "84" not in combined:
        missing_items.append("live84 chunk count 84")
    if missing_items:
        return CheckOutcome(
            "T1-INTAKE-05",
            1,
            "F1",
            "FAIL",
            "Compilation doc provenance metadata incomplete: " + "; ".join(missing_items),
        )
    return CheckOutcome(
        "T1-INTAKE-05",
        1,
        "F1",
        "PASS",
        f"Compilation doc provenance matches Source A & Source B ({effective_mode}) IDs, sizes, and SHA256s",
        {"docs": [str(p.relative_to(repo_root)) for p in compilation_docs]},
    )


def check_t1_intake_06_access_blocker_note(
    repo_root: Path,
    compilation_docs: list[Path],
    effective_mode: str,
) -> CheckOutcome:
    """T1-INTAKE-06: Explicit reporting of aistudio.google.com Google Sign-In blocker vs Drive uc?export=download."""
    docs_to_scan = list(compilation_docs)
    export_doc = repo_root / "docs" / "AI_STUDIO_TRANSCRIPT_EXPORT.md"
    if effective_mode == "baseline45" and export_doc.is_file() and export_doc not in docs_to_scan:
        docs_to_scan.append(export_doc)
    if not docs_to_scan:
        return CheckOutcome(
            "T1-INTAKE-06",
            1,
            "F2",
            "FAIL",
            "No compilation or export docs available to verify access-blocker reporting",
        )
    # In live84 mode, require compilation docs themselves (not just historical export guide) to state the blocker
    text = "\n".join(p.read_text(encoding="utf-8") for p in (compilation_docs if effective_mode == "live84" else docs_to_scan))
    lowered = text.lower()
    has_sign_in_blocker = (
        ("sign-in" in lowered or "sign in" in lowered or "signed-in" in lowered or "login" in lowered or "google accounts" in lowered)
        and ("aistudio" in lowered or "browser" in lowered or "blocker" in lowered)
    )
    has_drive_uc = "uc?export=download" in lowered or "drive.google.com" in lowered
    if not (has_sign_in_blocker and has_drive_uc):
        return CheckOutcome(
            "T1-INTAKE-06",
            1,
            "F2",
            "FAIL",
            f"Access blocker reporting missing in {effective_mode} docs (sign_in_blocker={has_sign_in_blocker}, drive_uc={has_drive_uc})",
        )
    return CheckOutcome(
        "T1-INTAKE-06",
        1,
        "F2",
        "PASS",
        "Explicit aistudio.google.com Google Sign-In blocker vs Drive uc?export=download route documented",
    )


_LEADING_HTML_COMMENTS_RE = re.compile(r"^(?:\ufeff|\s|<!--[\s\S]*?-->)+")
_HTML_SIGNIN_TOKENS = (
    "accounts.google.com",
    "servicelogin",
    "sign in",
    "sign-in",
    "google drive",
    "you need access",
    "request access",
    "error 403",
    "error 401",
    "access denied",
)
_BLOCKER_REPORT_PATTERNS = (
    re.compile(r"\b(?:http\s*)?40[13]\b", re.I),
    re.compile(r"\baccess\s+denied\b", re.I),
    re.compile(r"\bpermission\s+denied\b", re.I),
    re.compile(r"\bsign[- ]in\b", re.I),
    re.compile(r"\bsigned[- ]in\b", re.I),
    re.compile(r"\byou\s+need\s+access\b", re.I),
    re.compile(r"\brequest\s+access\b", re.I),
    re.compile(r"\baccess[- ]blocker\b", re.I),
    re.compile(r"\bgoogle\s+accounts\b", re.I),
    re.compile(r"\bservicelogin\b", re.I),
    re.compile(r"\brequires?\s+(?:an?\s+)?auth(?:entication)?\b", re.I),
    re.compile(r"\b(?:requires?|required)\s+(?:a\s+)?(?:google\s+)?(?:login|credentials?)\b", re.I),
    re.compile(r"\bgoogle\s+verification\b", re.I),
    re.compile(r"\blogin\s+(?:page|screen|prompt|token|wall|required|redirect)\b", re.I),
    re.compile(r"\bnot\s+publicly\s+downloadable\b", re.I),
    re.compile(r"\binaccessible\b", re.I),
)
_CLAIM_ROW_LABEL_RE = re.compile(
    r"^\|[^|\n]+\|.*\[(?:kernel_verified|accepted_limited_scope|bucket_2_conditional|"
    r"bucket_3_open_debt|countermodel_found|documentation_only)\]",
    re.M,
)


def _looks_like_html_signin_blocker(raw_text: str) -> bool:
    stripped = _LEADING_HTML_COMMENTS_RE.sub("", raw_text.lstrip("\ufeff"))
    head = stripped[:4096].lower()
    if head.startswith("<!doctype html") or head.startswith("<html"):
        full_lower = raw_text.lower()
        if any(tok in full_lower for tok in _HTML_SIGNIN_TOKENS):
            return True
    return False


def _looks_like_json_api_error(raw_text: str) -> bool:
    stripped = raw_text.lstrip("\ufeff \t\r\n")
    if not stripped.startswith("{"):
        return False
    try:
        payload = json.loads(stripped)
    except json.JSONDecodeError:
        return False
    if not isinstance(payload, dict) or "error" not in payload or "chunkedPrompt" in payload:
        return False
    err = payload.get("error")
    if isinstance(err, dict):
        code = err.get("code")
        if code in (401, 403, 404):
            return True
        err_text = json.dumps(err).lower()
        if any(tok in err_text for tok in ("access denied", "permission", "unauthorized", "forbidden", "sign in", "sign-in", "unauthenticated")):
            return True
    elif isinstance(err, str) and err.strip():
        return True
    return False


def _find_cached_files_for_source(repo_root: Path, source_id: str) -> list[Path]:
    cached_dir = repo_root / "cached"
    if not cached_dir.is_dir():
        return []
    matches: list[Path] = []
    for p in sorted(cached_dir.rglob(f"*{source_id}*")):
        if not p.is_file():
            continue
        # Exclude extract subdirs when searching raw source payloads
        if "aistudio_extracts" in p.parts:
            continue
        matches.append(p)
    return matches


def _find_extract_dir_for_source(repo_root: Path, source_id: str) -> Path | None:
    extracts_root = repo_root / "cached" / "aistudio_extracts"
    if not extracts_root.is_dir():
        return None
    for d in sorted(extracts_root.iterdir()):
        if d.is_dir() and source_id in d.name:
            return d
    return None


_SOURCE_SHORT_PREFIXES = ("13ED", "1v8J", "12bA", "1VUS", "1wzq")
_SOURCE_LABELS = ("A", "B", "C", "D", "E")
_ALL_SOURCE_MARKERS_PAT = "|".join(re.escape(m) for m in (*ALL_FIVE_SOURCE_IDS, *_SOURCE_SHORT_PREFIXES))
_CLAUSE_SPLIT_RE = re.compile(
    rf"(\s*,\s*(?i:and|while|whereas|but)\s+|\s*,\s*|\s+(?i:and|while|whereas|but)\s+|\s+&\s+|\s*[—–]\s*|\s+-\s+|\s+/\s+|(?<!\bN)/(?![/])|\.\s+)"
    rf"(?=[*`_\[~]*?(?:(?i:Sources?)\s+[*`_~]*)?(?:[A-E](?=$|[\s:(,)=—–\-`*~\]]|_(?![A-Za-z0-9_])|['’](?:s(?![A-Za-z0-9_])|(?![A-Za-z0-9_]))|->|\.(?=\s|$))|{_ALL_SOURCE_MARKERS_PAT}))"
)
_TRAILING_CLAUSE_SPLIT_RE = re.compile(
    rf"(\s*,\s*(?i:and|while|whereas|but)\s+|\s*,\s*|\s+(?i:and|while|whereas|but)\s+|\s+&\s+|\s*[—–]\s*|\s+-\s+|\s+/\s+|(?<!\bN)/(?![/])|\.\s+)"
    rf"(?=[*`_\[~]*?(?:(?i:Sources?)\s+[*`_~]*)?(?:[A-E](?=$|[\s:(,)=—–\-`*~\]]|_(?![A-Za-z0-9_])|['’](?:s(?![A-Za-z0-9_])|(?![A-Za-z0-9_]))|->|\.(?=\s|$))|{_ALL_SOURCE_MARKERS_PAT}))"
)


_SOURCE_LBL_A_UNAMBIG_PRED_RE = re.compile(
    r"^\s*(?:[:(,)=—–→]|->|-\s|\b(?:"
    r"is|are|was|were|has|had|have|can|cannot|could|did|"
    r"remains|remained|requires|needs|returns|gives|yields|got|hit|not|"
    r"accessible|inaccessible|responded"
    r")\b)"
)
_SOURCE_LBL_A_PART_RE = re.compile(
    r"^\s*(?:(also|still|already|again|only|then|subsequently)\s+)?"
    r"(blocked|failed|saved|downloaded|returned|received|required|needed|triggered|caused)\b(.*)$",
    flags=re.S,
)
_ENGLISH_NP_HEAD_RE = re.compile(
    r"\b(?:responses?|downloads?|requests?|pages?|fetch(?:es)?|attempts?|connections?|sessions?|redirects?|"
    r"cop(?:y|ies)|files?|documents?|artifacts?|results?|screens?|portals?|messages?|notices?|prompts?|"
    r"errors?|logins?|auth|credentials?|tokens?|status(?:es)?|failures?|blockers?|bod(?:y|ies)|payloads?|"
    r"sign-ins?|signins?|warnings?|challenges?|access(?:es)?|permissions?|"
    r"walls?|verifications?|replies|reply|banners?|dialogs?|modals?|gates?|forms?)\b",
    flags=re.I,
)
_ENGLISH_FINITE_VERB_PAT = (
    r"(?:was|were|is|are|has|had|can|may|might|could|would|should|will|must|"
    r"occurred|happened|appeared|arrived|existed|persisted|expired|completed|started|ended|"
    r"prevented|blocked|stopped|remained|caused|triggered|resulted|led|"
    r"denied|rejected|failed|broke|forced|kept|halted|aborted|"
    r"blocks|prevents|causes|triggers|stops|indicates|returns|requires|denies|rejects|fails)"
)
_ENGLISH_FINITE_VERB_RE = re.compile(rf"\b{_ENGLISH_FINITE_VERB_PAT}\b", flags=re.I)
_SOURCE_A_BOUNDARY_RE = re.compile(
    rf"(?:,?\s*\b(?:so\s+that|even\s+though|in\s+case|because|when|after|before|since|while|if|as|where|although|though|unless|until|so\b(?!\s+(?:far|many|much|long|on)\b)|yet|hence|therefore|thus)\b|"
    rf"\s*[—–]\s*|\s+-\s+|"
    rf"(?:,?\s*\b(?:and|or|but)\b)\s+(?:(?:also|still|then|now|[a-z]{{2,}}ly)\s+)*(?={_ENGLISH_FINITE_VERB_PAT}\b)|"
    rf",\s*(?:blocked|denied|rejected|caused|triggered|followed|accompanied|flagged|logged|observed|returned)\s+(?:by|at|on|from|with|for|in|due|via)\b(?!.*,\s*(?:[a-z]+\s+)*{_ENGLISH_FINITE_VERB_PAT}\b))",
    flags=re.I,
)
_SOURCE_A_REL_SPLIT_RE = re.compile(r",?\s*\b(?:which|that)\b", flags=re.I)
_NESTED_SUBORD_START_RE = re.compile(
    r",?\s*\b(?:so\s+that|even\s+though|in\s+case|because|when|after|before|since|while|if|as|although|though|unless|until|so\b(?!\s+(?:far|many|much|long|on)\b)|yet|hence|therefore|thus)\b",
    flags=re.I,
)
_EMBEDDED_WH_START_RE = re.compile(r",?\s*\b(?:why|how|what|where)\b", flags=re.I)
_EMBEDDED_THAT_COMP_START_RE = re.compile(r",?\s*\bthat\b", flags=re.I)
_COMPLEMENT_TAKING_VERB_RE = re.compile(
    r"\b(?:indicates?|indicated|shows?|showed|means?|meant|proves?|proved|"
    r"confirms?|confirmed|implies?|implied|suggests?|suggested|"
    r"demonstrates?|demonstrated|notes?|noted|states?|stated|"
    r"reports?|reported|explains?|explained|reveals?|revealed)\b",
    flags=re.I,
)
_ENGLISH_AUX_VERB_RE = re.compile(
    r"^(?:is|are|was|were|has|had|can|may|might|could|would|should|will|must)$",
    flags=re.I,
)


def _strip_inline_parens_and_brackets(text: str) -> str:
    """Remove balanced `(...)` and `[...]` parenthetical notes from `text`."""
    out: list[str] = []
    p_depth = 0
    b_depth = 0
    for ch in text:
        if ch == "(":
            p_depth += 1
        elif ch == ")" and p_depth > 0:
            p_depth -= 1
        elif ch == "[":
            b_depth += 1
        elif ch == "]" and b_depth > 0:
            b_depth -= 1
        elif p_depth == 0 and b_depth == 0:
            out.append(ch)
    return "".join(out)


def _consume_vp_end(text: str, verbs: list[re.Match[str]]) -> int:
    """Return end index of the first (possibly auxiliary/coordinated) verb phrase in `text`."""
    vp_end = verbs[0].end()
    prev_was_aux = bool(_ENGLISH_AUX_VERB_RE.match(verbs[0].group(0)))
    for m_v in verbs[1:]:
        gap = text[vp_end : m_v.start()]
        gap_s = gap.strip()
        is_aux_chain = (
            prev_was_aux
            and len(gap_s) <= 45
            and bool(
                re.fullmatch(
                    r"(?:not|also|already|never|still|then|now|been|be|have|[a-z]{2,}ly|\s)*",
                    gap_s,
                    flags=re.I,
                )
            )
        )
        is_coord = bool(
            re.search(
                r"(?:^|,|\s)\b(?:and|or)\b\s*(?:(?:also|still|then|now|[a-z]{2,}ly)\s+)*$",
                gap,
                flags=re.I,
            )
        )
        if is_aux_chain or is_coord:
            vp_end = m_v.end()
            prev_was_aux = bool(_ENGLISH_AUX_VERB_RE.match(m_v.group(0)))
        else:
            break
    return vp_end


def _strip_nested_subord_clauses_in_rel(rel_tail: str) -> str:
    """Strip nested subordinate, embedded wh-complement, and finite complement clauses inside a relative clause."""
    s = re.split(r"\s*[—–]\s*|\s+-\s+", rel_tail, maxsplit=1)[0]
    comp_cursor = 0
    while True:
        m_sub = _NESTED_SUBORD_START_RE.search(s)
        best_kind = "sub" if m_sub is not None else ""
        best_match: re.Match[str] | None = m_sub

        for cand_wh in _EMBEDDED_WH_START_RE.finditer(s):
            if _ENGLISH_FINITE_VERB_RE.search(s[: cand_wh.start()]):
                if best_match is None or cand_wh.start() < best_match.start():
                    best_match = cand_wh
                    best_kind = "wh"
                break

        for cand_that in _EMBEDDED_THAT_COMP_START_RE.finditer(s):
            pre_that = s[: cand_that.start()]
            if _ENGLISH_FINITE_VERB_RE.search(pre_that) or _COMPLEMENT_TAKING_VERB_RE.search(pre_that):
                if best_match is None or cand_that.start() < best_match.start():
                    best_match = cand_that
                    best_kind = "that"
                break

        for cand_comp in _COMPLEMENT_TAKING_VERB_RE.finditer(s, comp_cursor):
            after_c = s[cand_comp.end() :]
            if re.match(
                r"^\s*(?:that|why|how|what|where|because|when|after|before|since|while|if|as|although|though|unless|until|whether)\b",
                after_c,
                flags=re.I,
            ):
                continue
            verbs_c = list(_ENGLISH_FINITE_VERB_RE.finditer(after_c))
            if not verbs_c:
                continue
            subj_span = after_c[: verbs_c[0].start()]
            if "," in subj_span or ";" in subj_span or len(subj_span.strip()) > 60:
                continue
            if best_match is None or cand_comp.start() < best_match.start():
                best_match = cand_comp
                best_kind = "comp"
            break

        if best_match is None:
            break

        after_sub = s[best_match.end() :]
        if best_kind in ("that", "comp", "wh", "sub"):
            for _ in range(8):
                verbs_chk = list(_ENGLISH_FINITE_VERB_RE.finditer(after_sub))
                if not verbs_chk:
                    break
                m_inner = _NESTED_SUBORD_START_RE.search(after_sub)
                if m_inner is None or m_inner.start() >= verbs_chk[0].start():
                    break
                inner_tail = after_sub[m_inner.end() :]
                inner_verbs = list(_ENGLISH_FINITE_VERB_RE.finditer(inner_tail))
                if not inner_verbs:
                    after_sub = after_sub[: m_inner.start()]
                    break
                inner_vp_end = _consume_vp_end(inner_tail, inner_verbs)
                after_sub = after_sub[: m_inner.start()] + " " + inner_tail[inner_vp_end:]
        verbs = list(_ENGLISH_FINITE_VERB_RE.finditer(after_sub))
        if not verbs:
            if best_kind == "comp":
                comp_cursor = best_match.end()
                continue
            s = s[: best_match.start()]
            break
        vp_end = _consume_vp_end(after_sub, verbs)
        if best_kind == "comp":
            s = s[: best_match.start()] + "indicates " + after_sub[vp_end:]
            comp_cursor = best_match.start() + len("indicates")
        else:
            prefix_s = s[: best_match.start()]
            if best_kind == "that" and not _ENGLISH_FINITE_VERB_RE.search(prefix_s):
                prefix_s = _COMPLEMENT_TAKING_VERB_RE.sub("indicates", prefix_s, count=1)
            s = prefix_s + " " + after_sub[vp_end:]
    return s


def _has_matrix_finite_verb_after_rel(rel_tail: str) -> bool:
    """Return True iff `rel_tail` (after `which`/`that`) contains a second, uncoordinated matrix finite VP."""
    rel_clean = _strip_nested_subord_clauses_in_rel(rel_tail)
    matches = list(_ENGLISH_FINITE_VERB_RE.finditer(rel_clean))
    if len(matches) < 2:
        return False
    vp_count = 0
    prev_end = 0
    prev_was_aux = False
    for m_v in matches:
        gap = rel_clean[prev_end : m_v.start()]
        gap_s = gap.strip()
        is_aux_chain = (
            vp_count > 0
            and prev_was_aux
            and len(gap_s) <= 45
            and bool(
                re.fullmatch(
                    r"(?:not|also|already|never|still|then|now|been|be|have|[a-z]{2,}ly|\s)*",
                    gap_s,
                    flags=re.I,
                )
            )
        )
        is_coord = vp_count > 0 and bool(
            re.search(
                r"(?:^|,|\s)\b(?:and|or)\b\s*(?:(?:also|still|then|now|[a-z]{2,}ly)\s+)*$",
                gap,
                flags=re.I,
            )
        )
        if not is_aux_chain and not is_coord:
            vp_count += 1
            if vp_count >= 2:
                return True
        prev_end = m_v.end()
        prev_was_aux = bool(_ENGLISH_AUX_VERB_RE.match(m_v.group(0)))
    return False


def _mask_bare_urls_intake(text: str) -> str:
    """Replace bare `https?://...` and `mailto:...` URLs (balanced parens/brackets) with spaces."""
    out: list[str] = []
    n = len(text)
    pos = 0
    for m in re.finditer(r"(?:https?|mailto):", text, flags=re.I):
        if m.start() < pos:
            continue
        out.append(text[pos : m.start()])
        end = m.end()
        paren_depth = 0
        bracket_depth = 0
        while end < n:
            ch = text[end]
            if ch.isspace() or ch in "<>|`":
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
    out.append(text[pos:])
    return "".join(out)


def _is_source_a_predicate(after_a: str) -> bool:
    """Return True iff text immediately following `A` looks like a Source-A predicate rather than an English NP."""
    s = after_a.lstrip("*`_~")
    if re.match(r"^['’]s(?![A-Za-z0-9_])", s):
        return True
    if _SOURCE_LBL_A_UNAMBIG_PRED_RE.match(s):
        return True
    m_part = _SOURCE_LBL_A_PART_RE.match(s)
    if not m_part:
        return False
    adv = m_part.group(1)
    word = m_part.group(2)
    rest = m_part.group(3)
    if adv:
        return True
    if word == "blocked":
        return bool(re.match(r"^\s*(?:$|[,;:.—–()\n]|(?:by|at|on|from|with|for|due|in|because|under|via)\b)", rest))
    if word == "failed":
        return bool(re.match(r"^\s*(?:$|[,;:.—–()\n]|(?:to|with|at|on|in|for|due|because|under|via)\b)", rest))
    if word in ("saved", "downloaded"):
        return bool(re.match(r"^\s*(?:$|[,;:.—–()\n]|(?:locally|to|at|in|as|on|under|into|via)\b)", rest))
    if re.match(r"^\s*(?:a|an|the)\b", rest, flags=re.I):
        return True
    clause_tail = re.split(r"[.;\n]", rest, maxsplit=1)[0]
    clause_tail = _strip_inline_parens_and_brackets(clause_tail)
    clause_tail = re.sub(
        r",\s*(?:blocked|denied|rejected|caused|triggered|followed|accompanied|flagged|logged|observed|returned)\s+"
        r"(?:by|at|on|from|with|for|in|due|via)\b[^,;.]*,",
        ",",
        clause_tail,
        flags=re.I,
    )
    m_bnd = _SOURCE_A_BOUNDARY_RE.search(clause_tail)
    m_rel = _SOURCE_A_REL_SPLIT_RE.search(clause_tail)
    if m_rel is not None and (m_bnd is None or m_rel.start() < m_bnd.start()):
        before_rel = clause_tail[: m_rel.start()]
        if _ENGLISH_NP_HEAD_RE.search(before_rel) and _ENGLISH_FINITE_VERB_RE.search(before_rel):
            return False
        if _ENGLISH_NP_HEAD_RE.search(before_rel) and _has_matrix_finite_verb_after_rel(clause_tail[m_rel.end() :]):
            return False
        return True
    matrix_region = clause_tail[: m_bnd.start()] if m_bnd is not None else clause_tail
    if _ENGLISH_NP_HEAD_RE.search(matrix_region) and _ENGLISH_FINITE_VERB_RE.search(matrix_region):
        return False
    return True


def _mentions_source_label(seg: str, lbl: str, *, allow_leading_A: bool = False) -> bool:
    if not lbl:
        return False
    seg_clean = _mask_bare_urls_intake(_unwrap_markdown_links(seg, keep_brackets=True))
    if re.search(rf"\bSources?\s+[*`_~]*{re.escape(lbl)}(?![A-Za-z0-9_])", seg_clean):
        return True
    if lbl == "A":
        # Avoid matching English indefinite article "A" (e.g. ": A blocked HTTP 403 response")
        leading_a = r"^\s*|" if allow_leading_A else ""
        intro_a = (
            r"^\s*(?:Per|In|On|At|For|From|After|Before|During|Currently|Initially|Originally|Later|Subsequently|Previously|Recently|Meanwhile|Overall|Historically|According\s+to)\b[^.;:\n]{0,45}\s+|"
            if allow_leading_A
            else ""
        )
        a_delim_pat = re.compile(
            rf"(?:{leading_a}{intro_a}^\s*(?:(?:[-*+]|\d+[.)])\s+)|[,;&—–|]\s*|\.\s+|(?<![A-Za-z0-9_])/\s*|(?<!\bN)/(?=[*`_~]*A)|\s+-\s+|\b(?i:and|while|whereas|but)\s+)[*`_~]*A(?![A-Za-z0-9_])"
        )
        for m_a in a_delim_pat.finditer(seg_clean):
            if _is_source_a_predicate(seg_clean[m_a.end() :]):
                return True
        return bool(
            re.search(
                r"(?<![A-Za-z0-9_.\-/:])A[*`_~]*?(?=\s*(?:[:(=—–→]|->|-\s))"
                r"|\[[*`_~]*A[*`_~]*(?:['’]s)?[*`_~]*(?:\s*\([^)\]]*\))?[*`_~]*\]",
                seg_clean,
            )
        )
    return bool(
        re.search(
            rf"(?<![A-Za-z0-9.\-/:])(?<![A-Za-z0-9]_){re.escape(lbl)}(?=$|[\s),:;\`*~\]—–'’=?!]|_(?![A-Za-z0-9_])|->|-\s|\.(?=\s|$))"
            rf"|\[[*`_~]*{re.escape(lbl)}[*`_~]*(?:['’]s)?[*`_~]*(?:\s*\([^)\]]*\))?[*`_~]*\]",
            seg_clean,
        )
    )


def _find_top_level_header_colon(line: str) -> tuple[int, int] | None:
    """Return `(colon_idx, body_start_idx)` for the first header colon outside `(...)`/`[...]`, ignoring URLs and `:=`."""
    depth = 0
    n = len(line)
    for idx, ch in enumerate(line):
        if ch in ("(", "["):
            depth += 1
        elif ch in (")", "]") and depth > 0:
            depth -= 1
        elif depth == 0 and ch == ":":
            if line.startswith("://", idx) or line.startswith(":=", idx):
                continue
            if idx + 1 == n or line[idx + 1].isspace():
                end = idx + 1
                while end < n and line[end].isspace():
                    end += 1
                return idx, end
    return None


def _split_top_level_parens(text: str) -> tuple[str, list[tuple[int, int, str]]]:
    """Return `(text_with_parens_and_notes_blanked, [(start, end, inner), ...])` for top-level `(...)` and non-link `[...]` spans."""
    spans: list[tuple[int, int, str]] = []
    out_chars: list[str] = []
    n = len(text)
    i = 0
    while i < n:
        ch = text[i]
        if ch in ("(", "["):
            open_ch = ch
            close_ch = ")" if ch == "(" else "]"
            depth = 1
            j = i + 1
            while j < n and depth > 0:
                if text[j] == open_ch:
                    depth += 1
                elif text[j] == close_ch:
                    depth -= 1
                j += 1
            if depth == 0:
                if open_ch == "[" and j < n and text[j] == "(":
                    out_chars.append(text[i:j])
                else:
                    out_chars.append(" ")
                    spans.append((i, j, text[i + 1 : j - 1]))
                i = j
                continue
        out_chars.append(ch)
        i += 1
    outside = re.sub(r"\s+", " ", "".join(out_chars)).strip()
    return outside, spans


def _unwrap_markdown_links(seg: str, *, keep_brackets: bool = False) -> str:
    """Strip Markdown `[label](url ...)` destinations, returning `label` (or `[label]` when `keep_brackets=True`)."""
    out: list[str] = []
    n = len(seg)
    i = 0
    while i < n:
        if seg[i] == "\\" and i + 1 < n:
            out.append(seg[i : i + 2])
            i += 2
            continue
        if seg[i] == "[":
            j = i + 1
            b_depth = 1
            while j < n and b_depth > 0:
                if seg[j] == "\\" and j + 1 < n:
                    j += 2
                    continue
                if seg[j] == "[":
                    b_depth += 1
                elif seg[j] == "]":
                    b_depth -= 1
                j += 1
            if b_depth == 0 and j < n and seg[j] == "(":
                dest_start = j + 1
                k = dest_start
                p_depth = 1
                in_quote: str | None = None
                in_angle = False
                while k < n and p_depth > 0:
                    ch = seg[k]
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
                    if ch == "<" and (k == dest_start or seg[k - 1].isspace()):
                        in_angle = True
                    elif ch in ('"', "'") and k > dest_start and seg[k - 1].isspace():
                        in_quote = ch
                    elif ch == "(":
                        p_depth += 1
                    elif ch == ")":
                        p_depth -= 1
                        if p_depth == 0:
                            break
                    k += 1
                if p_depth == 0:
                    out.append(seg[i:j] if keep_brackets else seg[i + 1 : j - 1])
                    i = k + 1
                    continue
        out.append(seg[i])
        i += 1
    return "".join(out)


def _strip_source_ref_tokens(seg: str) -> str:
    """Strip bullet markers, Markdown link URLs, source IDs/prefixes/labels, and joiners to see if any predicate words remain."""
    s = re.sub(r"^\s*(?:[-*+]|\d+[.)])\s+", "", seg)
    s = _unwrap_markdown_links(s)
    s = re.sub(rf"`?(?:{_ALL_SOURCE_MARKERS_PAT})`?", " ", s)
    s = re.sub(r"\(\s*\)", " ", s)
    s = re.sub(r"\bSources?\s+[*`_~]*[A-E][*`_~]*(?:['’]s)?(?![A-Za-z0-9_])", " ", s)
    s = re.sub(r"\b[A-E][*`_~]*(?:['’]s)?(?![A-Za-z0-9_])", " ", s)
    s = re.sub(r"\b(?:and|both|all)\b", " ", s, flags=re.I)
    s = re.sub(r"[`*_~()\[\],;&:—–\-\s]+", " ", s).strip()
    return s


_INDEF_QUANTIFIER_SOURCE_RE = re.compile(
    r"\b(?:One|Some|A|Another|Either|Neither|Only\s+one|Several|Multiple|Certain|At\s+least\s+one)\s+"
    r"(?:of\s+(?:(?:the|these|those)\s+)?)?(?:\w+\s+)?sources?\b",
    flags=re.I,
)


def _filter_indefinite_source_sents(text: str) -> tuple[list[str], bool]:
    """Split `text` into sentences/clauses (preserving URLs) and drop indefinite `A`/`An`/quantifier-source clauses."""
    url_spans = [(m_u.start(), m_u.end()) for m_u in re.finditer(r"(?:https?|mailto):[^\s)>\]]+", text, flags=re.I)]
    split_pat = re.compile(r"(?<=[.!?])\s+|\s*[;—–]\s+|\s+-\s+|(?<!:):(?!:|//|=)\s+")
    sents: list[str] = []
    pos_s = 0
    for m_sp in split_pat.finditer(text):
        if any(us <= m_sp.start() < ue for us, ue in url_spans):
            continue
        seg_s = text[pos_s : m_sp.start()].strip()
        if seg_s:
            sents.append(seg_s)
        pos_s = m_sp.end()
    tail_s = text[pos_s:].strip()
    if tail_s:
        sents.append(tail_s)
    kept_sents: list[str] = []
    dropped_indef = False
    for sent in sents:
        if _INDEF_QUANTIFIER_SOURCE_RE.search(sent):
            dropped_indef = True
            continue
        if re.search(r"(?<![A-Za-z0-9_/-])[*`_~]*An(?![A-Za-z0-9_-])", sent):
            dropped_indef = True
            continue
        has_indef_a = False
        for m_a in re.finditer(r"(?<![A-Za-z0-9_/-])([*`_~]*A(?![A-Za-z0-9_-]))", sent):
            if not _mentions_source_label(sent[m_a.start() :], "A", allow_leading_A=True):
                has_indef_a = True
                break
        if has_indef_a:
            dropped_indef = True
            continue
        kept_sents.append(sent)
    return kept_sents, dropped_indef


def _source_clause_for_id(
    line: str,
    source_id: str,
    other_source_re: re.Pattern[str] | None,
    *,
    _hdr_mentions_self: bool = False,
    _hdr_mentions_other: bool = False,
    _allow_leading_A: bool = False,
) -> str:
    """When multiple sources share a line, isolate clauses associated with `source_id`."""
    if source_id in ALL_FIVE_SOURCE_IDS:
        idx_s = ALL_FIVE_SOURCE_IDS.index(source_id)
        self_pref = _SOURCE_SHORT_PREFIXES[idx_s]
        self_lbl = _SOURCE_LABELS[idx_s]
    else:
        self_pref = source_id[:4]
        self_lbl = ""
    other_lbls = [lbl for sid, lbl in zip(ALL_FIVE_SOURCE_IDS, _SOURCE_LABELS) if sid != source_id]

    def _mentions_self(seg: str, *, allow_leading_A: bool = _allow_leading_A) -> bool:
        return (
            (source_id in seg)
            or (self_pref in seg)
            or _mentions_source_label(seg, self_lbl, allow_leading_A=allow_leading_A)
        )

    def _mentions_other(seg: str, *, allow_leading_A: bool = _allow_leading_A) -> bool:
        return (other_source_re is not None and bool(other_source_re.search(seg))) or any(
            _mentions_source_label(seg, ol, allow_leading_A=(allow_leading_A and ol == "A"))
            for ol in other_lbls
        )

    if not _hdr_mentions_other and not _mentions_other(line):
        return line

    # First isolate top-level `|` or `;` segments if present (preserving delimiters)
    top_parts = re.split(r"(\s*[;|]\s*)", line)
    if len(top_parts) > 1:
        kept_parts: list[str] = []
        for idx_t in range(0, len(top_parts), 2):
            seg = (top_parts[idx_t] or "").strip()
            if not seg:
                continue
            delim_before = top_parts[idx_t - 1] if idx_t > 0 else ""
            seg_allow_A = _allow_leading_A if idx_t == 0 else False
            has_self = _mentions_self(seg, allow_leading_A=seg_allow_A) or (
                bool(delim_before) and _mentions_self(delim_before + seg, allow_leading_A=False)
            )
            if has_self:
                seg_hdr_other = _hdr_mentions_other or any(
                    _mentions_other(top_parts[k_o], allow_leading_A=(_allow_leading_A if k_o == 0 else False))
                    for k_o in range(0, len(top_parts), 2)
                    if k_o != idx_t and top_parts[k_o].strip()
                )
                kept_parts.append(
                    _source_clause_for_id(
                        seg,
                        source_id,
                        other_source_re,
                        _hdr_mentions_self=_hdr_mentions_self,
                        _hdr_mentions_other=seg_hdr_other,
                        _allow_leading_A=seg_allow_A or bool(delim_before),
                    )
                )
        return " ; ".join(p for p in kept_parts if p)

    # Check `header : body` at paren-depth 0 (ignoring URLs like `https://` and inline parenthetical colons)
    colon_span = _find_top_level_header_colon(line)
    if colon_span is not None:
        c_start, c_end = colon_span
        hdr = line[:c_start].strip()
        hdr_with_colon = line[: c_start + 1].strip()
        body = line[c_end:].strip()
        if not body:
            if line.rstrip().endswith(":") and hdr:
                return _source_clause_for_id(
                    hdr,
                    source_id,
                    other_source_re,
                    _hdr_mentions_self=_hdr_mentions_self,
                    _hdr_mentions_other=_hdr_mentions_other,
                    _allow_leading_A=_allow_leading_A,
                )
            return ""
        hdr_no_parens, _ = _split_top_level_parens(hdr)
        hdr_clean_parens, _ = _split_top_level_parens(hdr_no_parens.replace("[", "(").replace("]", ")"))
        hdr_has_status = bool(
            any(pat.search(hdr_no_parens) for pat in _BLOCKER_REPORT_PATTERNS)
            or re.search(r"\b(?:saved|accessible|downloaded|preserved)\b", hdr_no_parens, re.I)
        )
        if not hdr_has_status and (not _CLAUSE_SPLIT_RE.search(hdr_no_parens) or _strip_source_ref_tokens(hdr_clean_parens) == ""):
            hdr_explicit_self = _mentions_self(hdr_with_colon)
            hdr_explicit_other = _mentions_other(hdr_with_colon)
            if hdr_explicit_self or hdr_explicit_other:
                hdr_self = hdr_explicit_self
                hdr_other = hdr_explicit_other
                hdr_allows_A = (
                    (SOURCE_A_ID in hdr)
                    or (_SOURCE_SHORT_PREFIXES[0] in hdr)
                    or _mentions_source_label(hdr_with_colon, "A")
                )
            else:
                hdr_self = _hdr_mentions_self
                hdr_other = _hdr_mentions_other
                hdr_allows_A = _allow_leading_A
            body_has_mentions = _mentions_self(body, allow_leading_A=hdr_allows_A) or _mentions_other(
                body, allow_leading_A=hdr_allows_A
            )
            if not body_has_mentions:
                if hdr_self and hdr_other:
                    kept_sents, dropped_indef = _filter_indefinite_source_sents(body)
                    if dropped_indef:
                        if not kept_sents:
                            return ""
                        return " ".join(kept_sents) if hdr_self else ""
                return body if hdr_self else ""
            first_clause = _CLAUSE_SPLIT_RE.split(body, maxsplit=1)[0]
            single_hdr_collides = (hdr_explicit_self != hdr_explicit_other) and (
                (hdr_self and _mentions_other(first_clause, allow_leading_A=hdr_allows_A))
                or (hdr_other and _mentions_self(first_clause, allow_leading_A=hdr_allows_A))
            )
            if not single_hdr_collides:
                return _source_clause_for_id(
                    body,
                    source_id,
                    other_source_re,
                    _hdr_mentions_self=hdr_self,
                    _hdr_mentions_other=hdr_other,
                    _allow_leading_A=hdr_allows_A,
                )

    # Split on _CLAUSE_SPLIT_RE while ignoring matches inside URLs or Markdown link destinations
    protected_spans: list[tuple[int, int]] = [(m_u.start(), m_u.end()) for m_u in re.finditer(r"https?://[^\s)>\]]+", line)]
    raw_parts: list[str] = []
    last_pos = 0
    for m_sp in _CLAUSE_SPLIT_RE.finditer(line):
        sp_s, sp_e = m_sp.span()
        if any(ps <= sp_s < pe for ps, pe in protected_spans):
            continue
        raw_parts.append(line[last_pos:sp_s])
        raw_parts.append(m_sp.group(1))
        last_pos = sp_e
    raw_parts.append(line[last_pos:])
    clause_pairs: list[tuple[str, str]] = []
    if raw_parts:
        c0 = raw_parts[0].strip()
        if c0:
            clause_pairs.append(("", c0))
        for k in range(1, len(raw_parts), 2):
            delim = raw_parts[k]
            ck = raw_parts[k + 1].strip() if k + 1 < len(raw_parts) else ""
            if ck:
                clause_pairs.append((delim, ck))
    clauses = [c for _, c in clause_pairs]
    flags: list[tuple[bool, bool]] = []
    for idx_c, (delim, c) in enumerate(clause_pairs):
        lead_a = _allow_leading_A if idx_c == 0 else False
        is_s = _mentions_self(c, allow_leading_A=lead_a) or (
            bool(delim) and _mentions_self(delim + c, allow_leading_A=False)
        )
        is_o = _mentions_other(c, allow_leading_A=lead_a) or (
            bool(delim) and _mentions_other(delim + c, allow_leading_A=False)
        )
        flags.append((is_s, is_o))

    # Shared subject list within a sentence: e.g. `- Sources C & E returned HTTP 403. A was saved locally.`
    def _is_bare_source_subject(clause: str) -> bool:
        if _strip_source_ref_tokens(clause) == "":
            return True
        outside, spans = _split_top_level_parens(clause)
        if _strip_source_ref_tokens(outside) != "":
            return False
        return not any(
            any(pat.search(inner) for pat in _BLOCKER_REPORT_PATTERNS)
            or re.search(
                r"\b(?:saved|accessible|downloaded|preserved|ok|valid|passed|failed|blocked|returned|required|received|needed)\b",
                inner,
                re.I,
            )
            for _, _, inner in spans
        )

    self_indices = [idx_c for idx_c, (is_s, is_o) in enumerate(flags) if is_s and not is_o]
    if self_indices and len(clauses) > 1:
        first_self = self_indices[0]
        if _is_bare_source_subject(clauses[first_self]):
            pred_idx: int | None = None
            valid_chain = True
            for k_c in range(first_self + 1, len(clauses)):
                delim_k = clause_pairs[k_c][0]
                if "." in delim_k or re.search(r"\b(?:while|whereas|but)\b", delim_k, re.I):
                    valid_chain = False
                    break
                if not _is_bare_source_subject(clauses[k_c]):
                    if flags[k_c][0] or flags[k_c][1]:
                        pred_idx = k_c
                    break
            if valid_chain and pred_idx is not None and pred_idx > first_self:
                shared_tail = _strip_source_ref_tokens(clauses[pred_idx])
                if shared_tail:
                    return shared_tail

    self_only: list[str] = []
    other_only: list[str] = []
    neutral: list[str] = []
    seen_any_explicit = False
    for idx_c, (c, (is_s, is_o)) in enumerate(zip(clauses, flags)):
        lead_a = _allow_leading_A if idx_c == 0 else False
        if is_s and is_o:
            outside, spans = _split_top_level_parens(c)
            if spans:
                out_s = _mentions_self(outside, allow_leading_A=lead_a)
                out_o = _mentions_other(outside, allow_leading_A=lead_a)
                self_spans = [
                    inner for _, _, inner in spans
                    if _mentions_self(inner, allow_leading_A=False) and not _mentions_other(inner, allow_leading_A=False)
                ]
                other_spans = [
                    (s_i, e_i) for s_i, e_i, inner in spans
                    if _mentions_other(inner, allow_leading_A=False) and not _mentions_self(inner, allow_leading_A=False)
                ]
                if out_s and not out_o and other_spans:
                    cleaned_parts: list[str] = []
                    prev_p = 0
                    for s_i, e_i in other_spans:
                        cleaned_parts.append(c[prev_p:s_i])
                        prev_p = e_i
                    cleaned_parts.append(c[prev_p:])
                    cleaned = re.sub(r"\s+", " ", "".join(cleaned_parts)).strip()
                    if cleaned:
                        seen_any_explicit = True
                        self_only.append(cleaned)
                    continue
                if out_o and not out_s and self_spans:
                    seen_any_explicit = True
                    other_only.append(outside)
                    self_only.extend(self_spans)
                    continue
        if is_s and not is_o:
            seen_any_explicit = True
            self_only.append(c)
        elif is_o and not is_s:
            seen_any_explicit = True
            other_only.append(c)
        elif not is_s and not is_o:
            if not seen_any_explicit and _hdr_mentions_self and not _hdr_mentions_other:
                self_only.append(c)
            elif not seen_any_explicit and _hdr_mentions_other and not _hdr_mentions_self:
                other_only.append(c)
            else:
                neutral.append(c)

    if _hdr_mentions_other and not _hdr_mentions_self:
        return " ; ".join(self_only)

    def _has_clause_status(clause: str) -> bool:
        outside, spans = _split_top_level_parens(clause)
        outside_clean, _ = _split_top_level_parens(outside.replace("[", " ").replace("]", " "))
        if _strip_source_ref_tokens(outside_clean) != "":
            return True
        return any(
            any(pat.search(inner) for pat in _BLOCKER_REPORT_PATTERNS)
            or re.search(r"\b(?:saved|accessible|downloaded|preserved)\b", inner, re.I)
            for _, _, inner in spans
        )

    self_has_status = any(_has_clause_status(c) for c in self_only)
    has_disambiguated_status = (
        any(_has_clause_status(c) for c in other_only)
        or len(other_only) >= 2
        or (self_has_status and (bool(other_only) or _hdr_mentions_other))
    )
    if has_disambiguated_status:
        return " ; ".join(self_only)
    return " ; ".join([*self_only, *neutral])


def _has_explicit_blocker_report(docs_and_manifests: list[Path], source_id: str) -> bool:
    other_markers = [
        marker
        for sid, pref in zip(ALL_FIVE_SOURCE_IDS, _SOURCE_SHORT_PREFIXES)
        if sid != source_id
        for marker in (sid, pref)
    ]
    other_source_re = re.compile("|".join(re.escape(m) for m in other_markers)) if other_markers else None
    if source_id in ALL_FIVE_SOURCE_IDS:
        idx_s = ALL_FIVE_SOURCE_IDS.index(source_id)
        self_pref = _SOURCE_SHORT_PREFIXES[idx_s]
        self_lbl = _SOURCE_LABELS[idx_s]
    else:
        self_pref = source_id[:4]
        self_lbl = ""
    other_lbls = [lbl for sid, lbl in zip(ALL_FIVE_SOURCE_IDS, _SOURCE_LABELS) if sid != source_id]

    def _nxt_mentions_self(seg: str) -> bool:
        return (source_id in seg) or (self_pref in seg) or _mentions_source_label(seg, self_lbl)

    def _nxt_mentions_other(seg: str) -> bool:
        return (other_source_re is not None and bool(other_source_re.search(seg))) or any(
            _mentions_source_label(seg, ol) for ol in other_lbls
        )

    bullet_start_re = re.compile(r"^\s*(?:[-*+]|\d+[.)])\s+")
    sub_label_colon_re = re.compile(
        r"^\s*(?:[*`_~]+\s*)*(?:Sources?\s+)?[*`_~]*[A-E][*`_~]*(?:\s*\([^)]*\))?(?:\s*[*`_~]+)*\s*:(?:\s*[*`_~]+)*"
    )
    for path in docs_and_manifests:
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        if source_id not in text:
            continue
        lines = text.splitlines()
        for idx, line in enumerate(lines):
            if source_id not in line:
                continue
            has_other_same_line = _nxt_mentions_other(line)
            head_segment = _source_clause_for_id(line, source_id, other_source_re)
            base_indent = len(line) - len(line.lstrip())
            colon_span = _find_top_level_header_colon(line)
            m_hdr_h = re.match(r"^(#{1,6})(?:\s|$)", line.lstrip())
            base_heading_level = len(m_hdr_h.group(1)) if m_hdr_h else 0
            is_heading = base_heading_level > 0

            def _has_hdr_status_text(txt: str) -> bool:
                return bool(
                    any(pat.search(txt) for pat in _BLOCKER_REPORT_PATTERNS)
                    or re.search(r"\b(?:saved|accessible|downloaded|preserved)\b", txt, re.I)
                )

            has_indented_source_subbullets = False
            if has_other_same_line and not line.lstrip().startswith("|"):
                if not is_heading:
                    for j_la in range(idx + 1, min(len(lines), idx + 12)):
                        la = lines[j_la]
                        la_s = la.strip()
                        if not la_s:
                            continue
                        la_ind = len(la) - len(la.lstrip())
                        if la_ind <= base_indent:
                            break
                        if (bullet_start_re.match(la) or sub_label_colon_re.match(la_s)) and (
                            _nxt_mentions_self(la) or _nxt_mentions_other(la)
                        ):
                            has_indented_source_subbullets = True
                            break
                else:
                    for j_la in range(idx + 1, min(len(lines), idx + 12)):
                        la = lines[j_la]
                        la_s = la.strip()
                        if not la_s:
                            continue
                        if la_s.startswith(("|", "---", "{", "}", "]")):
                            break
                        m_la_h = re.match(r"^(#{1,6})(?:\s|$)", la_s)
                        la_h_lvl = len(m_la_h.group(1)) if m_la_h else 0
                        if la_h_lvl > 0 and la_h_lvl <= base_heading_level:
                            break
                        if (
                            la_h_lvl > base_heading_level
                            or bullet_start_re.match(la)
                            or sub_label_colon_re.match(la_s)
                        ) and (_nxt_mentions_self(la) or _nxt_mentions_other(la)):
                            has_indented_source_subbullets = True
                            break

            suffix_after_colon = line[colon_span[1] :].strip() if colon_span is not None else ""
            is_multi_header = has_other_same_line and (
                line.rstrip().endswith(":")
                or (colon_span is not None and not _has_hdr_status_text(suffix_after_colon))
                or (is_heading and not _has_hdr_status_text(suffix_after_colon if colon_span is not None else line))
                or has_indented_source_subbullets
            )
            def _is_bare_source_ref_only(txt: str) -> bool:
                outside, spans = _split_top_level_parens(txt)
                if _strip_source_ref_tokens(outside) != "":
                    return False
                return not any(_has_hdr_status_text(inner) for _, _, inner in spans)

            def _sources_in_seg(seg: str) -> set[int]:
                out_srcs: set[int] = set()
                for idx_src, (sid, pref, lbl) in enumerate(zip(ALL_FIVE_SOURCE_IDS, _SOURCE_SHORT_PREFIXES, _SOURCE_LABELS)):
                    if (sid in seg) or (pref in seg) or _mentions_source_label(seg, lbl):
                        out_srcs.add(idx_src)
                return out_srcs

            _SHARED_TAIL_PER_SOURCE_OUTCOME_RE = re.compile(
                r"\b(?:ok|okay|valid|pass(?:ed|es|ing)?|succeed(?:ed|s|ing)?|"
                r"saved|downloaded|preserved|accessible|available|"
                r"done|checked|verified|verif(?:y|ies)|complete(?:d|s)?|"
                r"finished|resolved|clean|ready|intact|unchanged|unmodified|"
                r"present|found|locally|skip(?:ped)?|omitted|pending)\b",
                flags=re.I,
            )
            _SHARED_TAIL_FINITE_VERB_RE = re.compile(
                r"\b(?:is|are|was|were|be|been|being|has|had|have|do|does|did|"
                r"can|cannot|can't|could|may|might|must|shall|should|will|would|"
                r"returned|returns|return|received|receives|receive|"
                r"failed|fails|fail|errored|timed|hit|got|gets|gave|gives|"
                r"yielded|yields|remains|remained|remain|appears|appeared|"
                r"occurred|happened|logged|triggered|caused|rejected|"
                r"prevented|stopped|showed|shows|indicated|indicates|"
                r"needs|needed|requires|lacks|lacked|only)\b",
                flags=re.I,
            )

            def _is_shared_topic_tail(
                seg: str,
                *,
                has_prior_source_status: bool = False,
                joined_with_conj: bool = False,
            ) -> bool:
                outside_s, spans_s = _split_top_level_parens(seg)
                has_topic_dash = bool(re.search(r"[—–]|\s-\s", outside_s))
                for _, _, inner in spans_s:
                    if _SHARED_TAIL_PER_SOURCE_OUTCOME_RE.search(inner):
                        return False
                    if "=" in inner or ":=" in inner or ";" in inner:
                        return False
                    if _SHARED_TAIL_FINITE_VERB_RE.search(inner):
                        return False
                    if _has_hdr_status_text(inner):
                        if has_prior_source_status and not has_topic_dash and not joined_with_conj:
                            return False
                rem = _strip_source_ref_tokens(outside_s)
                if not rem:
                    return True
                rem_words = re.sub(r"[/]+", " ", rem).strip()
                if "=" in rem or ":=" in rem or ";" in rem:
                    return False
                if _SHARED_TAIL_FINITE_VERB_RE.search(rem_words):
                    return False
                if _SHARED_TAIL_PER_SOURCE_OUTCOME_RE.search(rem_words):
                    return False
                if re.match(r"^\s*(?:required|needed)\s+\S", rem_words, flags=re.I):
                    return False
                return True

            def _has_hdr_predicate_or_status(txt: str) -> bool:
                if _has_hdr_status_text(txt):
                    return True
                outside_t, _ = _split_top_level_parens(txt)
                if _ENGLISH_FINITE_VERB_RE.search(outside_t):
                    return True
                return bool(
                    re.search(
                        r"\b(?:ok|okay|valid|pass(?:ed|ing)?|succeed(?:ed|ing)?|fail(?:ed|s|ing|ure)?|error(?:ed)?|"
                        r"miss(?:ing|ed)?|available|unavailable|pending|verif(?:ied|y)|"
                        r"done|checked|complete(?:d)?|finished|resolved|clean|ready|audited|reviewed|"
                        r"intact|unchanged|unmodified|"
                        r"denied|blocked|skip(?:ped)?|omitted|present|absent|found|lost)\b",
                        txt,
                        flags=re.I,
                    )
                )

            def _is_continuing_comma_enum(before_comma: str, after_comma: str, *, is_final: bool = False) -> bool:
                ac_srcs = _sources_in_seg(after_comma)
                bc_srcs = _sources_in_seg(before_comma)
                if not ac_srcs or (ac_srcs & bc_srcs):
                    return False
                if _has_hdr_predicate_or_status(before_comma):
                    return False
                if _is_bare_source_ref_only(after_comma):
                    return True
                if len(ac_srcs) == 1:
                    if not _has_hdr_predicate_or_status(after_comma):
                        return True
                    if is_final and _is_shared_topic_tail(after_comma):
                        return True
                return False

            def _is_comma_bare_source_prefix(txt: str) -> bool:
                depth_c = 0
                last_comma: int | None = None
                for idx_c, ch_c in enumerate(txt):
                    if ch_c in ("(", "["):
                        depth_c += 1
                    elif ch_c in (")", "]") and depth_c > 0:
                        depth_c -= 1
                    elif depth_c == 0 and ch_c == ",":
                        last_comma = idx_c
                if last_comma is None:
                    return True
                pref = re.sub(r"^\s*[*`_~]*Sources?\b\s*", "", txt[:last_comma], flags=re.I)
                parts_c: list[str] = []
                cur_c: list[str] = []
                depth_p = 0
                for ch_c in pref:
                    if ch_c in ("(", "["):
                        depth_p += 1
                    elif ch_c in (")", "]") and depth_p > 0:
                        depth_p -= 1
                    elif depth_p == 0 and ch_c == ",":
                        parts_c.append("".join(cur_c).strip())
                        cur_c.clear()
                        continue
                    cur_c.append(ch_c)
                if cur_c:
                    parts_c.append("".join(cur_c).strip())
                nonempty_parts = [p for p in parts_c if p]
                if not nonempty_parts:
                    return False
                seen_srcs: set[int] = set()
                for p_idx, p in enumerate(nonempty_parts):
                    p_srcs = _sources_in_seg(p)
                    if len(p_srcs) != 1 or (p_srcs & seen_srcs):
                        return False
                    seen_srcs.update(p_srcs)
                    if p_idx == 0:
                        if _has_hdr_predicate_or_status(p):
                            return False
                    elif not (_is_bare_source_ref_only(p) or not _has_hdr_predicate_or_status(p)):
                        return False
                tail_item = re.sub(r"^\s*(?:and\b|&)\s*", "", txt[last_comma + 1 :], flags=re.I).strip()
                tail_srcs = _sources_in_seg(tail_item)
                if (
                    not tail_srcs
                    or (tail_srcs & seen_srcs)
                    or (_has_hdr_predicate_or_status(tail_item) and not _is_shared_topic_tail(tail_item))
                ):
                    return False
                return True

            def _split_top_level_first_sep(txt: str) -> str:
                depth_s = 0
                nt = len(txt)
                for idx_f, ch_f in enumerate(txt):
                    if ch_f in ("(", "["):
                        depth_s += 1
                    elif ch_f in (")", "]") and depth_s > 0:
                        depth_s -= 1
                    elif depth_s == 0:
                        if ch_f in ("—", "–", ";", "|", ","):
                            return txt[:idx_f].strip()
                        if (
                            ch_f == ":"
                            and not txt.startswith(("://", ":="), idx_f)
                            and (idx_f == 0 or txt[idx_f - 1] != ":")
                        ):
                            return txt[:idx_f].strip()
                        if ch_f == "-" and idx_f > 0 and txt[idx_f - 1].isspace() and idx_f + 1 < nt and txt[idx_f + 1].isspace():
                            return txt[:idx_f].strip()
                        if ch_f == "." and idx_f + 1 < nt and txt[idx_f + 1].isspace():
                            return txt[:idx_f].strip()
                return txt.strip()

            def _strip_leading_nonlist_dash_clauses(txt: str) -> str:
                parts: list[str] = []
                cur: list[str] = []
                depth_d = 0
                i_d = 0
                n_d = len(txt)
                while i_d < n_d:
                    ch_d = txt[i_d]
                    if ch_d in ("(", "["):
                        depth_d += 1
                        cur.append(ch_d)
                        i_d += 1
                    elif ch_d in (")", "]") and depth_d > 0:
                        depth_d -= 1
                        cur.append(ch_d)
                        i_d += 1
                    elif depth_d == 0:
                        m_d = re.match(r"\s*[—–]\s*|\s+-\s+", txt[i_d:])
                        if m_d:
                            parts.append("".join(cur))
                            parts.append(m_d.group(0))
                            cur.clear()
                            i_d += m_d.end()
                            continue
                        cur.append(ch_d)
                        i_d += 1
                    else:
                        cur.append(ch_d)
                        i_d += 1
                parts.append("".join(cur))
                if len(parts) < 3:
                    return txt.strip()
                num_chunks = (len(parts) + 1) // 2
                kept_start = 0
                kept_chunks: list[tuple[str, str]] = []  # (chunk_text, trailing_delim)
                for k_d in range(num_chunks - 1):
                    chunk_s = parts[2 * k_d].strip()
                    delim_s = parts[2 * k_d + 1]
                    has_srcs = bool(_sources_in_seg(chunk_s))
                    has_stat = _has_hdr_predicate_or_status(chunk_s)
                    if not has_srcs:
                        if not kept_chunks:
                            kept_start = k_d + 1
                        # Else neutral non-source middle topic segment (`C, D — access blocker — E`): drop this segment without dropping earlier `C, D`
                    elif has_stat:
                        kept_chunks.clear()
                        kept_start = k_d + 1
                        sub_parts = _TRAILING_CLAUSE_SPLIT_RE.split(chunk_s)
                        if len(sub_parts) >= 3:
                            sub_segs = [sub_parts[m].strip() for m in range(0, len(sub_parts), 2)]
                            sub_delims = [sub_parts[m].strip() for m in range(1, len(sub_parts), 2)]
                            sub_start = len(sub_segs)
                            for s_i in range(len(sub_segs) - 1, -1, -1):
                                if _has_hdr_predicate_or_status(sub_segs[s_i]) or not _sources_in_seg(sub_segs[s_i]):
                                    break
                                if s_i < len(sub_segs) - 1:
                                    d_s = sub_delims[s_i]
                                    if not (
                                        d_s in (",", "/", "—", "–", "-")
                                        or re.fullmatch(r"(?:,\s*)?(?:and\b|&)", d_s, flags=re.I)
                                    ):
                                        break
                                sub_start = s_i
                            if sub_start < len(sub_segs):
                                tail_sub = "".join(
                                    sub_parts[2 * sub_start :]
                                ).strip()
                                if tail_sub and _sources_in_seg(tail_sub):
                                    kept_chunks.append((tail_sub, delim_s))
                    else:
                        kept_chunks.append((chunk_s, delim_s))
                last_chunk = parts[2 * (num_chunks - 1)].strip()
                if kept_chunks:
                    return ("".join(c + d for c, d in kept_chunks) + last_chunk).strip()
                if kept_start > 0:
                    return "".join(parts[2 * kept_start :]).strip()
                return txt.strip()

            def _trailing_colon_owner_flags() -> tuple[bool, bool]:
                if not (is_multi_header and line.rstrip().endswith(":")):
                    return False, False
                before_trailing_colon = line.rstrip()[:-1].strip()
                body_after_sep = ""
                prior_prefix_for_status = ""
                scan_start = 0
                if colon_span is not None and colon_span[1] < len(before_trailing_colon):
                    before_colon = before_trailing_colon[: colon_span[0]]
                    cand_body = before_trailing_colon[colon_span[1] :].strip()
                    cand_head = re.split(r"[;|—–:]|\s+-\s+|\.\s+", cand_body, maxsplit=1)[0].strip()
                    cand_head_is_multi_hdr = (
                        _nxt_mentions_self(cand_head)
                        and _nxt_mentions_other(cand_head)
                        and (
                            _is_bare_source_ref_only(cand_head)
                            or bool(re.match(r"^\s*[*`_~]*Sources?\b", cand_head, flags=re.I))
                            or (
                                not _has_hdr_predicate_or_status(before_colon)
                                and _is_comma_bare_source_prefix(cand_head)
                            )
                        )
                    )
                    if (
                        (_nxt_mentions_self(before_colon) or _nxt_mentions_other(before_colon))
                        and not cand_head_is_multi_hdr
                    ):
                        body_after_sep = cand_body
                        prior_prefix_for_status = before_colon
                    else:
                        scan_start = colon_span[1]
                if not body_after_sep:
                    # Find first top-level separator (`—`, `–`, `;`, `|`, `:`, ` - `, `, `, `/`, `&`, `and` after status-bearing sources, or `. `) outside `(...)`/`[...]`
                    sep_depth = 0
                    btc_n = len(before_trailing_colon)
                    last_dash_end = scan_start
                    url_spans_btc = [
                        (m_u.start(), m_u.end())
                        for m_u in re.finditer(r"(?:https?|mailto):[^\s)>\]]+", before_trailing_colon, flags=re.I)
                    ]
                    for idx_s in range(scan_start, btc_n):
                        ch_s = before_trailing_colon[idx_s]
                        if ch_s in ("(", "["):
                            sep_depth += 1
                        elif ch_s in (")", "]") and sep_depth > 0:
                            sep_depth -= 1
                        elif sep_depth == 0:
                            if any(us <= idx_s < ue for us, ue in url_spans_btc):
                                continue
                            if ch_s in (";", "|"):
                                body_after_sep = before_trailing_colon[idx_s + 1 :].strip()
                                prior_prefix_for_status = before_trailing_colon[scan_start:idx_s]
                                break
                            if ch_s in ("—", "–"):
                                prefix_b = before_trailing_colon[scan_start:idx_s]
                                seg_before_dash = before_trailing_colon[last_dash_end:idx_s]
                                if (
                                    not (_nxt_mentions_self(prefix_b) or _nxt_mentions_other(prefix_b))
                                    or (_sources_in_seg(seg_before_dash) and _has_hdr_predicate_or_status(seg_before_dash))
                                ):
                                    body_after_sep = before_trailing_colon[idx_s + 1 :].strip()
                                    prior_prefix_for_status = before_trailing_colon[scan_start:idx_s]
                                    break
                                last_dash_end = idx_s + 1
                                continue
                            if (
                                ch_s == ":"
                                and idx_s > scan_start
                                and not before_trailing_colon.startswith(("://", ":="), idx_s)
                                and (idx_s == 0 or before_trailing_colon[idx_s - 1] != ":")
                                and (
                                    _nxt_mentions_self(before_trailing_colon[scan_start:idx_s])
                                    or _nxt_mentions_other(before_trailing_colon[scan_start:idx_s])
                                )
                            ):
                                body_after_sep = before_trailing_colon[idx_s + 1 :].strip()
                                prior_prefix_for_status = before_trailing_colon[scan_start:idx_s]
                                break
                            if (
                                ch_s == "-"
                                and idx_s > 0
                                and before_trailing_colon[idx_s - 1].isspace()
                                and idx_s + 1 < btc_n
                                and before_trailing_colon[idx_s + 1].isspace()
                            ):
                                prefix_b = before_trailing_colon[scan_start:idx_s]
                                seg_before_dash = before_trailing_colon[last_dash_end:idx_s]
                                if (
                                    not (_nxt_mentions_self(prefix_b) or _nxt_mentions_other(prefix_b))
                                    or (_sources_in_seg(seg_before_dash) and _has_hdr_predicate_or_status(seg_before_dash))
                                ):
                                    body_after_sep = before_trailing_colon[idx_s + 1 :].strip()
                                    prior_prefix_for_status = before_trailing_colon[scan_start:idx_s]
                                    break
                                last_dash_end = idx_s + 1
                                continue
                            if ch_s == "." and idx_s + 1 < btc_n and before_trailing_colon[idx_s + 1].isspace():
                                body_after_sep = before_trailing_colon[idx_s + 1 :].strip()
                                prior_prefix_for_status = before_trailing_colon[scan_start:idx_s]
                                break
                            if ch_s == "&":
                                seg_before_amp = before_trailing_colon[last_dash_end:idx_s]
                                if _sources_in_seg(seg_before_amp) and _has_hdr_predicate_or_status(seg_before_amp):
                                    body_after_sep = before_trailing_colon[idx_s + 1 :].strip()
                                    prior_prefix_for_status = before_trailing_colon[scan_start:idx_s]
                                    break
                            if (
                                ch_s == "/"
                                and not before_trailing_colon.startswith("//", idx_s)
                                and (idx_s == 0 or before_trailing_colon[idx_s - 1] not in (":", "/"))
                            ):
                                seg_before_slash = before_trailing_colon[last_dash_end:idx_s]
                                if _sources_in_seg(seg_before_slash) and _has_hdr_predicate_or_status(seg_before_slash):
                                    body_after_sep = before_trailing_colon[idx_s + 1 :].strip()
                                    prior_prefix_for_status = before_trailing_colon[scan_start:idx_s]
                                    break
                            if (
                                (idx_s == scan_start or not (before_trailing_colon[idx_s - 1].isalnum() or before_trailing_colon[idx_s - 1] == "_"))
                                and re.match(r"and(?=\s|$)", before_trailing_colon[idx_s:], flags=re.I)
                            ):
                                seg_before_and = before_trailing_colon[last_dash_end:idx_s]
                                if _sources_in_seg(seg_before_and) and _has_hdr_predicate_or_status(seg_before_and):
                                    body_after_sep = before_trailing_colon[idx_s + 3 :].strip()
                                    prior_prefix_for_status = before_trailing_colon[scan_start:idx_s]
                                    break
                            if ch_s == "," and idx_s + 1 < btc_n and before_trailing_colon[idx_s + 1].isspace():
                                before_comma = before_trailing_colon[scan_start:idx_s]
                                seg_before_comma = before_trailing_colon[last_dash_end:idx_s]
                                after_comma = before_trailing_colon[idx_s + 1 :].strip()
                                after_comma_head = _split_top_level_first_sep(after_comma)
                                if (
                                    _sources_in_seg(seg_before_comma)
                                    and _has_hdr_predicate_or_status(seg_before_comma)
                                ) or (
                                    (last_dash_end == scan_start or bool(_sources_in_seg(seg_before_comma)))
                                    and _nxt_mentions_self(before_comma)
                                    and _nxt_mentions_other(before_comma)
                                    and not re.match(r"^(?:and\b|&)", after_comma, flags=re.I)
                                    and not _is_continuing_comma_enum(
                                        before_comma,
                                        after_comma_head,
                                        is_final=(after_comma == after_comma_head),
                                    )
                                ):
                                    body_after_sep = after_comma
                                    prior_prefix_for_status = before_trailing_colon[scan_start:idx_s]
                                    break
                if not body_after_sep:
                    return False, False
                has_prior_src_status = bool(
                    prior_prefix_for_status
                    and _sources_in_seg(prior_prefix_for_status)
                    and _has_hdr_predicate_or_status(prior_prefix_for_status)
                )
                semi_last = _strip_leading_nonlist_dash_clauses(
                    re.split(r"\s*[;|]\s*|\.\s+", body_after_sep)[-1].strip()
                )
                if semi_last:
                    sl_parts = _TRAILING_CLAUSE_SPLIT_RE.split(semi_last)
                    if len(sl_parts) >= 3:
                        sl_segs = [sl_parts[k].strip() for k in range(0, len(sl_parts), 2)]
                        sl_delims = [sl_parts[k].strip() for k in range(1, len(sl_parts), 2)]
                        last_seg = sl_segs[-1]
                        last_srcs = _sources_in_seg(last_seg)
                        last_delim_conj = bool(
                            sl_delims and re.search(r"(?:^|\s)(?:and\b|&)$", sl_delims[-1], flags=re.I)
                        )
                        last_ok = bool(last_srcs) and (
                            not _has_hdr_predicate_or_status(last_seg)
                            or _is_shared_topic_tail(
                                last_seg,
                                has_prior_source_status=has_prior_src_status,
                                joined_with_conj=last_delim_conj,
                            )
                        )
                        if last_ok:
                            tail_start = len(sl_segs) - 1
                            for idx_sl in range(len(sl_segs) - 2, -1, -1):
                                d_sl = sl_delims[idx_sl]
                                if not (
                                    d_sl in (",", "/", "—", "–", "-")
                                    or re.fullmatch(r"(?:,\s*)?(?:and\b|&)", d_sl, flags=re.I)
                                ):
                                    break
                                seg_sl = sl_segs[idx_sl]
                                if _has_hdr_predicate_or_status(seg_sl) or not _sources_in_seg(seg_sl):
                                    break
                                tail_start = idx_sl
                            tail_segs = sl_segs[tail_start:]
                            if len(tail_segs) >= 2:
                                nonfinal_srcs: set[int] = set()
                                for seg in tail_segs[:-1]:
                                    nonfinal_srcs.update(_sources_in_seg(seg))
                                final_srcs = _sources_in_seg(tail_segs[-1])
                                if nonfinal_srcs and final_srcs and not (final_srcs & nonfinal_srcs):
                                    if any(_nxt_mentions_other(seg) for seg in tail_segs) and not any(
                                        _nxt_mentions_self(seg) for seg in tail_segs
                                    ):
                                        return False, True
                                    return False, False
                last_clause = _TRAILING_CLAUSE_SPLIT_RE.split(semi_last)[-1].strip() if semi_last else ""
                if not last_clause:
                    return False, False
                tc_self = _nxt_mentions_self(last_clause) and not _nxt_mentions_other(last_clause)
                tc_other = _nxt_mentions_other(last_clause) and not _nxt_mentions_self(last_clause)
                return tc_self, tc_other

            trailing_colon_is_self, trailing_colon_is_other = _trailing_colon_owner_flags()
            skip_other_indent: int | None = None
            skip_other_subheading: int | None = None
            self_subheading_level: int | None = None
            self_bullet_indent: int | None = None
            sub_lines: list[str] = []
            pre_breakdown_lines: list[str] = []
            saw_sub_breakdown = False
            seen_section_content = False
            in_sub_heading = False
            if not line.lstrip().startswith("|") and (not has_other_same_line or is_multi_header):
                win_limit = idx + (60 if (is_multi_header or is_heading) else 6)
                for j in range(idx + 1, min(len(lines), win_limit)):
                    nxt = lines[j]
                    nxt_s = nxt.strip()
                    nxt_indent = len(nxt) - len(nxt.lstrip())
                    is_bullet = bool(bullet_start_re.match(nxt))
                    is_sub_item = is_bullet or bool(sub_label_colon_re.match(nxt_s))
                    if not nxt_s:
                        if not is_heading:
                            if not is_multi_header:
                                break
                            next_nb = ""
                            next_nb_indent = -1
                            for k_nb in range(j + 1, min(len(lines), win_limit)):
                                cand_nb_raw = lines[k_nb]
                                cand_nb = cand_nb_raw.strip()
                                if cand_nb:
                                    next_nb = cand_nb
                                    next_nb_indent = len(cand_nb_raw) - len(cand_nb_raw.lstrip())
                                    break
                            if next_nb_indent <= base_indent or not (
                                bullet_start_re.match(next_nb)
                                or sub_label_colon_re.match(next_nb)
                                or _nxt_mentions_self(next_nb)
                                or _nxt_mentions_other(next_nb)
                                or self_bullet_indent is not None
                                or skip_other_indent is not None
                            ):
                                break
                            continue
                        if seen_section_content:
                            # Under headings, bridge blank lines for sub-heading prose or continuing breakdown lines
                            next_nonblank = ""
                            next_nonblank_indent = -1
                            for k_nb in range(j + 1, min(len(lines), win_limit)):
                                cand_nb_raw = lines[k_nb]
                                cand_nb = cand_nb_raw.strip()
                                if cand_nb:
                                    next_nonblank = cand_nb
                                    next_nonblank_indent = len(cand_nb_raw) - len(cand_nb_raw.lstrip())
                                    break
                            m_nb_h = re.match(r"^(#{1,6})(?:\s|$)", next_nonblank)
                            nb_h_lvl = len(m_nb_h.group(1)) if m_nb_h else 0
                            if (
                                not next_nonblank
                                or next_nonblank.startswith(("|", "---", "{", "}", "]"))
                                or (nb_h_lvl > 0 and nb_h_lvl <= base_heading_level)
                                or (next_nonblank.startswith("#") and nb_h_lvl == 0)
                                or (
                                    not in_sub_heading
                                    and not (
                                        nb_h_lvl > base_heading_level
                                        or bullet_start_re.match(next_nonblank)
                                        or sub_label_colon_re.match(next_nonblank)
                                        or _nxt_mentions_self(next_nonblank)
                                        or _nxt_mentions_other(next_nonblank)
                                        or (self_bullet_indent is not None and next_nonblank_indent > self_bullet_indent)
                                    )
                                )
                            ):
                                break
                        continue
                    m_nxt_h = re.match(r"^(#{1,6})(?:\s|$)", nxt_s)
                    nxt_h_lvl = len(m_nxt_h.group(1)) if m_nxt_h else 0
                    is_sub_heading = is_heading and nxt_h_lvl > base_heading_level
                    if is_sub_heading:
                        in_sub_heading = True
                    if (
                        nxt_s.startswith("|")
                        or (nxt_s.startswith("#") and not is_sub_heading)
                        or (is_bullet and not is_heading and nxt_indent <= base_indent)
                        or nxt_s.startswith(("{", "}", "]", "---"))
                    ):
                        break
                    seen_section_content = True
                    mentions_other = _nxt_mentions_other(nxt)
                    mentions_self = _nxt_mentions_self(nxt)
                    if is_multi_header and trailing_colon_is_other and not mentions_self and not is_sub_heading and not is_sub_item and self_bullet_indent is None and self_subheading_level is None:
                        continue
                    if is_multi_header and trailing_colon_is_self and mentions_other and not mentions_self and not is_sub_heading and not is_sub_item:
                        continue
                    if mentions_other or mentions_self:
                        saw_sub_breakdown = True
                    if is_multi_header and not is_heading and not is_sub_item and nxt_indent <= base_indent and not mentions_self:
                        break
                    if is_multi_header and is_sub_heading and self_subheading_level is not None and nxt_h_lvl <= self_subheading_level:
                        self_subheading_level = None
                    if is_multi_header and skip_other_subheading is not None:
                        if not is_sub_heading:
                            if not (is_sub_item and (mentions_self or mentions_other)):
                                continue
                            skip_other_subheading = None
                        elif nxt_h_lvl > skip_other_subheading:
                            continue
                        else:
                            skip_other_subheading = None
                    if is_multi_header and not is_sub_heading and skip_other_indent is not None:
                        if nxt_indent > skip_other_indent or (
                            nxt_indent == skip_other_indent and not is_sub_item and not mentions_self
                        ):
                            continue
                        if is_sub_item and nxt_indent <= skip_other_indent and not mentions_self:
                            skip_other_indent = nxt_indent
                            continue
                        skip_other_indent = None
                    if mentions_other and not mentions_self:
                        if is_multi_header:
                            # Multi-source header sub-bullets/subheadings/prose: skip other sources' lines and continuations
                            if is_sub_heading:
                                skip_other_subheading = nxt_h_lvl
                                if self_subheading_level is not None and nxt_h_lvl <= self_subheading_level:
                                    self_subheading_level = None
                            else:
                                skip_other_indent = nxt_indent
                            self_bullet_indent = None
                            continue
                        break
                    if is_multi_header and not is_sub_heading and self_bullet_indent is not None and nxt_indent <= self_bullet_indent and not mentions_self:
                        if not is_sub_item and not is_heading and nxt_indent <= base_indent:
                            break
                        self_bullet_indent = None
                        skip_other_indent = nxt_indent
                        continue
                    if is_multi_header and is_sub_heading:
                        if mentions_self:
                            self_subheading_level = nxt_h_lvl
                        elif self_subheading_level is not None and nxt_h_lvl > self_subheading_level:
                            # Child subheading nested inside an active self-subheading (e.g. `##### Access Blocker` under `#### Source E`)
                            pass
                        else:
                            self_bullet_indent = None
                            skip_other_subheading = nxt_h_lvl
                            continue
                    if mentions_other and mentions_self:
                        sub_seg = _source_clause_for_id(nxt, source_id, other_source_re)
                        if sub_seg:
                            sub_lines.append(sub_seg)
                    else:
                        has_heading_subcont = False
                        if is_multi_header and mentions_self and is_heading and not (is_sub_item or nxt_indent > base_indent):
                            if nxt_s.endswith(":"):
                                has_heading_subcont = True
                            else:
                                for k_sub in range(j + 1, min(len(lines), win_limit)):
                                    la_sub = lines[k_sub]
                                    la_sub_s = la_sub.strip()
                                    if not la_sub_s:
                                        continue
                                    la_sub_ind = len(la_sub) - len(la_sub.lstrip())
                                    if (
                                        la_sub_ind > nxt_indent
                                        and not la_sub_s.startswith(("|", "#", "---", "{", "}", "]"))
                                    ):
                                        has_heading_subcont = True
                                    break
                        if is_multi_header and mentions_self and (is_sub_item or nxt_indent > base_indent or has_heading_subcont):
                            self_bullet_indent = nxt_indent
                        if is_multi_header and not saw_sub_breakdown:
                            pre_breakdown_lines.append(nxt)
                        elif (
                            not is_multi_header
                            or mentions_self
                            or is_sub_heading
                            or self_bullet_indent is not None
                            or self_subheading_level is not None
                            or trailing_colon_is_self
                        ):
                            sub_lines.append(nxt)
            if is_multi_header:
                matched_trailing_colon = trailing_colon_is_self and bool(pre_breakdown_lines)
                hdr_mentions_A = (
                    (SOURCE_A_ID in line)
                    or (_SOURCE_SHORT_PREFIXES[0] in line)
                    or _mentions_source_label(line, "A")
                )
                head_is_neutral = (not head_segment) or (
                    not _has_hdr_status_text(head_segment)
                    and not re.search(
                        r"\b(?:ok|okay|valid|pass(?:ed|ing)?|succeed(?:ed|ing)?|done|checked|"
                        r"verif(?:ied|y)|complete(?:d)?|finished|resolved|clean|ready|audited|reviewed|"
                        r"intact|unchanged|unmodified|available|present|found|skip(?:ped)?|omitted|pending)\b",
                        head_segment,
                        re.I,
                    )
                )
                has_a_prefixed_blocker = (
                    source_id != SOURCE_A_ID
                    and hdr_mentions_A
                    and any(
                        re.match(
                            r"^\s*(?:[-*+]|\d+[.)])?\s*[*`_~]*A(?![A-Za-z0-9_'])\s+"
                            r"(?:blocked|failed|saved|downloaded|returned|received|required|needed|"
                            r"is|was|had|has|timed|errored|could|cannot|can't|did)\b",
                            pl,
                        )
                        for pl in pre_breakdown_lines
                    )
                )
                if matched_trailing_colon:
                    context_lines = ([head_segment] if head_segment else []) + pre_breakdown_lines + sub_lines
                elif saw_sub_breakdown:
                    context_lines = sub_lines
                elif (
                    not trailing_colon_is_other
                    and head_is_neutral
                    and pre_breakdown_lines
                    and not has_a_prefixed_blocker
                ):
                    filtered_pre: list[str] = []
                    for pl in pre_breakdown_lines:
                        kept_pl, dropped_pl = _filter_indefinite_source_sents(pl)
                        if dropped_pl:
                            if kept_pl:
                                filtered_pre.append(" ".join(kept_pl))
                        else:
                            filtered_pre.append(pl)
                    context_lines = filtered_pre if filtered_pre else ([head_segment] if head_segment else [])
                else:
                    context_lines = [head_segment] if head_segment else []
            else:
                context_lines = ([head_segment] if head_segment else []) + sub_lines
            window = "\n".join(context_lines)
            if window and any(pat.search(window) for pat in _BLOCKER_REPORT_PATTERNS):
                return True
    return False


def _has_provenance_in_docs(
    docs_and_manifests: list[Path],
    source_id: str,
    byte_size: int,
    sha256_hex: str,
    *,
    count_value: int | None = None,
) -> bool:
    formatted_bytes = f"{byte_size:,}"
    sha_prefix = sha256_hex[:12]
    for path in docs_and_manifests:
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        if source_id not in text:
            continue
        has_bytes = (str(byte_size) in text) or (formatted_bytes in text)
        has_sha = sha_prefix in text
        has_count = count_value is None or (str(count_value) in text)
        if has_bytes and has_sha and has_count:
            return True
    return False


def _has_claims_and_open_debt_for_source(
    compilation_docs: list[Path],
    source_id: str,
) -> tuple[bool, bool]:
    """Verify accessible F10 source has claim-table and BUCKET 3 open-debt coverage in compilation docs."""
    has_claims = False
    has_open_debt = False
    for path in compilation_docs:
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        if source_id not in text:
            continue
        if _CLAIM_ROW_LABEL_RE.search(text):
            has_claims = True
        if "BUCKET 3" in text or "[bucket_3_open_debt]" in text:
            has_open_debt = True
    return has_claims, has_open_debt


def check_t1_intake_07_additional_sources_f10(
    repo_root: Path,
    compilation_docs: list[Path],
    manifest_paths: list[Path],
    effective_mode: str,
    *,
    require_all_sources: bool = False,
    extract_script_override: Path | None = None,
) -> CheckOutcome:
    """T1-INTAKE-07 (F10): Verify Sources C, D, E are preserved+digested with provenance or explicitly blocker-reported."""
    enforce = require_all_sources or (effective_mode == "live84")
    docs_and_manifests = list(dict.fromkeys([*compilation_docs, *manifest_paths]))
    per_source: dict[str, str] = {}
    failures: list[str] = []

    for spec in ADDITIONAL_SOURCES:
        label = spec["label"]
        sid = spec["id"]
        kind = spec["kind"]
        cached_files = _find_cached_files_for_source(repo_root, sid)
        non_html_files: list[Path] = []
        html_blocker_files: list[Path] = []
        json_blocker_files: list[Path] = []
        for cf in cached_files:
            raw_bytes = cf.read_bytes()
            text = raw_bytes.decode("utf-8", errors="replace")
            if _looks_like_html_signin_blocker(text):
                html_blocker_files.append(cf)
            elif _looks_like_json_api_error(text):
                json_blocker_files.append(cf)
            else:
                non_html_files.append(cf)

        if non_html_files:
            primary = non_html_files[0]
            raw_bytes = primary.read_bytes()
            if not raw_bytes:
                failures.append(f"Source {label} ({sid}): cached file {primary.name} is empty")
                continue
            digest = sha256_bytes(raw_bytes)
            if kind == "drive":
                if primary.suffix.lower() == ".pdf" and not raw_bytes.lstrip().startswith(b"%PDF-"):
                    failures.append(
                        f"Source {label} ({sid}): Drive .pdf file {primary.name} lacks %PDF- magic header"
                    )
                    continue
                try:
                    decoded = raw_bytes.decode("utf-8")
                    line_count: int | None = len(decoded.splitlines())
                except UnicodeDecodeError:
                    # Non-UTF-8 binary Drive payload (e.g., .pdf): verify byte size & sha256 provenance
                    line_count = None
                if enforce:
                    if not _has_provenance_in_docs(docs_and_manifests, sid, len(raw_bytes), digest, count_value=line_count):
                        count_desc = f"{line_count} L" if line_count is not None else "binary"
                        failures.append(
                            f"Source {label} ({sid}): preserved ({len(raw_bytes)} B, {count_desc}, {digest[:12]}...) "
                            "but M1b docs/manifests lack matching provenance metadata"
                        )
                        continue
                    has_claims, has_debt = _has_claims_and_open_debt_for_source(compilation_docs, sid)
                    if not has_claims or not has_debt:
                        failures.append(
                            f"Source {label} ({sid}): M1b compilation docs missing extracted claims ({has_claims}) or BUCKET 3 open-debt ({has_debt}) coverage"
                        )
                        continue
                count_desc = f"{line_count} L" if line_count is not None else "binary"
                suffix = "" if enforce else " [baseline45-unverified-docs]"
                per_source[label] = f"accessible ({len(raw_bytes)} B, {count_desc}, sha256={digest[:12]}...){suffix}"
            else:
                # AI Studio JSON source D
                try:
                    payload = json.loads(raw_bytes.decode("utf-8"))
                except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                    failures.append(f"Source {label} ({sid}): invalid JSON ({exc})")
                    continue
                if not isinstance(payload, dict):
                    failures.append(f"Source {label} ({sid}): JSON root is not an object")
                    continue
                required_top = {"runSettings", "systemInstruction", "chunkedPrompt"}
                missing_top = sorted(required_top - set(payload.keys()))
                if missing_top:
                    failures.append(f"Source {label} ({sid}): missing top-level keys {missing_top}")
                    continue
                cp = payload.get("chunkedPrompt")
                if not isinstance(cp, dict):
                    failures.append(f"Source {label} ({sid}): chunkedPrompt is not an object")
                    continue
                chunks = cp.get("chunks")
                if not isinstance(chunks, list) or not chunks:
                    failures.append(f"Source {label} ({sid}): missing non-empty chunkedPrompt.chunks")
                    continue
                bad_chunks = [
                    i for i, c in enumerate(chunks)
                    if not isinstance(c, dict)
                    or not isinstance(c.get("role"), str)
                    or not c["role"].strip()
                    or not isinstance(c.get("createTime"), str)
                    or not c["createTime"].strip()
                ]
                if bad_chunks:
                    failures.append(
                        f"Source {label} ({sid}): chunk(s) {bad_chunks[:3]} missing non-empty role/createTime"
                    )
                    continue
                timestamps = [c["createTime"] for c in chunks]
                if any(timestamps[i] < timestamps[i - 1] for i in range(1, len(timestamps))):
                    failures.append(f"Source {label} ({sid}): non-monotonic createTime timestamps")
                    continue
                extract_dir = _find_extract_dir_for_source(repo_root, sid)
                has_extract = (
                    extract_dir is not None
                    and (extract_dir / "manifest.json").is_file()
                    and (extract_dir / "transcript.md").is_file()
                )
                if enforce and not has_extract:
                    failures.append(f"Source {label} ({sid}): missing cached/aistudio_extracts/*{sid}*/ manifest/transcript")
                    continue
                if has_extract:
                    assert extract_dir is not None
                    extract_script = extract_script_override or (repo_root / "tools" / "infra" / "extract_aistudio_math.py")
                    if extract_script.is_file():
                        with tempfile.TemporaryDirectory(prefix=f"epistemic_extract_{label}_") as tmp_dir:
                            proc = run_subprocess_safe(
                                [sys.executable, str(extract_script), str(primary), "--output-dir", tmp_dir],
                                cwd=repo_root,
                                timeout=60,
                            )
                            if proc.returncode != 0:
                                failures.append(f"Source {label} ({sid}): extract_aistudio_math.py failed (rc={proc.returncode})")
                                continue
                            regen_manifest = json.loads((Path(tmp_dir) / primary.name.removesuffix(".json") / "manifest.json").read_text(encoding="utf-8"))
                            cached_manifest = json.loads((extract_dir / "manifest.json").read_text(encoding="utf-8"))
                            if regen_manifest.get("source_sha256") != cached_manifest.get("source_sha256") or regen_manifest.get("turn_count") != cached_manifest.get("turn_count"):
                                failures.append(f"Source {label} ({sid}): extract manifest parity mismatch")
                                continue
                if enforce:
                    if not _has_provenance_in_docs(docs_and_manifests, sid, len(raw_bytes), digest, count_value=len(chunks)):
                        failures.append(
                            f"Source {label} ({sid}): preserved ({len(raw_bytes)} B, {len(chunks)} chunks, {digest[:12]}...) "
                            "but M1b docs/manifests lack matching provenance metadata"
                        )
                        continue
                    has_claims, has_debt = _has_claims_and_open_debt_for_source(compilation_docs, sid)
                    if not has_claims or not has_debt:
                        failures.append(
                            f"Source {label} ({sid}): M1b compilation docs missing extracted claims ({has_claims}) or BUCKET 3 open-debt ({has_debt}) coverage"
                        )
                        continue
                suffix = "" if enforce else " [baseline45-unverified-docs]"
                per_source[label] = f"accessible ({len(chunks)} chunks, {len(raw_bytes)} B, sha256={digest[:12]}...){suffix}"
        else:
            # No valid non-blocker payload on disk -> must have explicit access-blocker report if enforced
            if _has_explicit_blocker_report(docs_and_manifests, sid):
                per_source[label] = "access_blocker_reported"
            elif enforce:
                reasons: list[str] = []
                if html_blocker_files:
                    reasons.append("cached file was HTML sign-in page")
                if json_blocker_files:
                    reasons.append("cached file was JSON API error payload")
                extra = f" ({'; '.join(reasons)})" if reasons else ""
                failures.append(
                    f"Source {label} ({sid}): neither preserved+digested with provenance nor explicitly blocker-reported{extra}"
                )
            else:
                per_source[label] = "pending_m1b_baseline45"

    if failures:
        return CheckOutcome(
            "T1-INTAKE-07",
            1,
            "F10",
            "FAIL",
            "Additional sources C/D/E (F10) check failed: " + "; ".join(failures),
            {"per_source": per_source, "enforced": enforce},
        )
    mode_note = "enforced" if enforce else "baseline45-ready"
    return CheckOutcome(
        "T1-INTAKE-07",
        1,
        "F10",
        "PASS",
        f"Additional sources C/D/E ({mode_note}): " + ", ".join(f"{k}={v}" for k, v in per_source.items()),
        {"per_source": per_source, "enforced": enforce},
    )


def run_tier1_intake_checks(
    repo_root: Path,
    compilation_docs: list[Path],
    effective_mode: str,
    *,
    manifest_paths: list[Path] | None = None,
    require_all_sources: bool = False,
) -> list[CheckOutcome]:
    return [
        check_t1_intake_01_source_a(repo_root),
        check_t1_intake_02_source_b(repo_root, effective_mode),
        check_t1_intake_03_extract_parity(repo_root),
        check_t1_intake_04_transcript_turns(repo_root),
        check_t1_intake_05_provenance_metadata(repo_root, compilation_docs, effective_mode),
        check_t1_intake_06_access_blocker_note(repo_root, compilation_docs, effective_mode),
        check_t1_intake_07_additional_sources_f10(
            repo_root,
            compilation_docs,
            manifest_paths or [],
            effective_mode,
            require_all_sources=require_all_sources,
        ),
    ]
