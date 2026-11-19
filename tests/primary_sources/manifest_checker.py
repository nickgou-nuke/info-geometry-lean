"""Tier 1 & M1 validation: primary-source archive, MANIFEST.json, git hygiene, and archetypes traceability."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from collections.abc import Iterable, Set as AbstractSet
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from tests.primary_sources import (
    ARCHETYPES_DOC_REL,
    EXPECTED_M1_WORK_IDS,
    FOUNDER_YEAR_SPEC,
    MANIFEST_REL,
    PAPERS_ROOT_REL,
    PILLAR_DIR_MAP,
    PILLAR_DIR_TO_KEY,
    PILLAR_HEADING_PATTERNS,
    REPO_ROOT,
)

VALID_R3_TAGS: frozenset[str] = frozenset({"R3.1", "R3.2", "R3.3", "R3.4"})
VALID_WORK_STATUSES: frozenset[str] = frozenset(
    {
        "downloaded",
        "substituted",
        "gap_recorded",
        "exact_primary_cached",
        "exact_primary_downloaded",
        "paywalled_with_oa_substitute",
        "oa_translation_or_substitute",
    }
)
SUBSTITUTE_OR_GAP_STATUSES: frozenset[str] = frozenset(
    {
        "substituted",
        "gap_recorded",
        "paywalled_with_oa_substitute",
        "oa_translation_or_substitute",
    }
)
SHA256_HEX_RX = re.compile(r"^[0-9a-f]{64}$")
PLACEHOLDER_CELL_VALUES: frozenset[str] = frozenset({"", "-", "--", "n/a", "na", "none", "tbd", "todo", "pending"})


@dataclass
class CheckOutcome:
    check_id: str
    tier: int
    milestone: str
    pillar: str
    status: str  # "PASS" | "FAIL" | "PENDING_MISSING" | "SKIPPED"
    summary: str
    details: dict[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class TraceabilityRow:
    work_id: str
    pillar: str
    author_year: str
    archetype: str
    r3_principle: str
    lean_module: str
    declarations: tuple[str, ...]
    status: str
    line_no: int
    lean_modules: tuple[str, ...] = ()
    module_errors: tuple[str, ...] = ()


def _run_git(args: list[str], repo_root: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=repo_root,
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
    )


def check_papers_git_hygiene(repo_root: Path = REPO_ROOT) -> CheckOutcome:
    """Verify .papers/ is git-ignored, untracked, unstaged, and tests/primary_sources/ has 0 .lean files."""
    errors: list[str] = []
    if (repo_root / ".git").exists():
        ig = _run_git(["check-ignore", "-q", MANIFEST_REL], repo_root)
        if ig.returncode != 0:
            errors.append(f"{MANIFEST_REL} is NOT ignored by .gitignore (rc={ig.returncode})")

        ls = _run_git(["ls-files", ".papers/"], repo_root)
        tracked = [ln for ln in ls.stdout.splitlines() if ln.strip()]
        if tracked:
            errors.append(f"Tracked files found under .papers/: {tracked[:10]}")

        diff_cached = _run_git(["diff", "--cached", "--name-only", "--", ".papers/"], repo_root)
        staged = [ln for ln in diff_cached.stdout.splitlines() if ln.strip()]
        if staged:
            errors.append(f"Staged files found under .papers/: {staged[:10]}")

        st = _run_git(["status", "--porcelain", "--", ".papers/"], repo_root)
        dirty = [ln for ln in st.stdout.splitlines() if ln.strip()]
        if dirty:
            errors.append(f"Non-empty git status under .papers/: {dirty[:10]}")
    else:
        gitignore_path = repo_root / ".gitignore"
        if not gitignore_path.is_file() or ".papers/" not in gitignore_path.read_text(encoding="utf-8", errors="replace"):
            errors.append(".gitignore missing '.papers/' entry")

    ps_tests_dir = repo_root / "tests" / "primary_sources"
    if ps_tests_dir.is_dir():
        stray_lean = [
            p.relative_to(repo_root).as_posix()
            for p in sorted(ps_tests_dir.rglob("*.lean"))
        ]
        if stray_lean:
            errors.append(f"Forbidden .lean files inside tests/primary_sources/: {stray_lean}")

    if errors:
        return CheckOutcome(
            check_id="T2-GIT-HYGIENE",
            tier=2,
            milestone="GLOBAL",
            pillar="all",
            status="FAIL",
            summary="; ".join(errors),
            details={"errors": errors},
        )
    return CheckOutcome(
        check_id="T2-GIT-HYGIENE",
        tier=2,
        milestone="GLOBAL",
        pillar="all",
        status="PASS",
        summary=".papers/ git-ignored & clean; zero .lean files in tests/primary_sources/",
        details={},
    )


def _check_magic_bytes(path: Path) -> str | None:
    raw = path.read_bytes()
    if len(raw) == 0:
        return "empty file (0 bytes)"
    ext = path.suffix.lower()
    if ext == ".pdf":
        if not raw.lstrip().startswith(b"%PDF-"):
            return f"invalid PDF magic bytes ({raw[:16]!r})"
    elif ext == ".djvu":
        if not raw.startswith(b"AT&TFORM"):
            return f"invalid DjVu magic bytes ({raw[:16]!r})"
    elif ext in {".txt", ".md", ".tex", ".html", ".htm"}:
        if len(raw.strip()) < 20:
            return f"text artifact suspiciously tiny ({len(raw)} bytes)"
    return None


def _normalize_pillar_name(raw_pillar: str) -> str:
    s = raw_pillar.strip()
    if s in PILLAR_DIR_TO_KEY:
        return s
    if s in PILLAR_DIR_MAP:
        return PILLAR_DIR_MAP[s]
    return s


def _work_matches_spec(work: dict[str, Any], spec_author_patterns: tuple[str, ...]) -> str:
    author_text = " ".join(
        str(work.get(k, "")) for k in ("author_year", "author", "authors", "title", "id", "citation", "notes", "gap_or_paywall_note")
    ).lower()
    if all(re.search(pat, author_text, re.IGNORECASE) for pat in spec_author_patterns):
        return (
            f"{work.get('author_year', '')} {work.get('year', '')} {work.get('title', '')} "
            f"{work.get('id', '')} {work.get('citation', '')} {work.get('notes', '')}"
        )
    return ""


def _work_matches_spec_and_years(work: dict[str, Any], spec: Any) -> bool:
    blob = _work_matches_spec(work, spec.author_patterns)
    if not blob:
        return False
    return all(any(y in blob for y in ygroup) for ygroup in spec.required_year_groups)


def _validate_artifact_on_disk(
    wid: str,
    local_rel: str,
    expected_bytes: Any,
    expected_sha: str,
    *,
    pdir: str,
    repo_root: Path,
    papers_root: Path,
    errors: list[str],
) -> None:
    if not local_rel:
        errors.append(f"works[{wid}] missing 'local_path'")
        return
    if pdir not in PILLAR_DIR_TO_KEY:
        return
    candidate = Path(local_rel)
    if candidate.is_absolute():
        errors.append(f"works[{wid}] local_path must be relative, got {local_rel!r}")
        return
    resolved = (repo_root / candidate).resolve()
    if not resolved.exists():
        alt = (papers_root / candidate).resolve()
        if alt.exists():
            resolved = alt
    expected_dir = (papers_root / pdir).resolve()
    try:
        resolved.relative_to(expected_dir)
    except ValueError:
        errors.append(f"works[{wid}] local_path {local_rel!r} escapes {PAPERS_ROOT_REL}/{pdir}")
        return
    if not resolved.is_file():
        errors.append(f"works[{wid}] missing file on disk: {local_rel}")
        return
    magic_err = _check_magic_bytes(resolved)
    if magic_err:
        errors.append(f"works[{wid}] {local_rel}: {magic_err}")
    actual_bytes = resolved.stat().st_size
    if expected_bytes is None or isinstance(expected_bytes, bool):
        errors.append(f"works[{wid}] missing 'bytes'/'size_bytes' on {local_rel}")
    else:
        try:
            exp_int = int(expected_bytes)
        except (TypeError, ValueError):
            errors.append(f"works[{wid}] invalid 'bytes'/'size_bytes'={expected_bytes!r} on {local_rel}")
        else:
            if exp_int <= 0 or exp_int != actual_bytes:
                errors.append(
                    f"works[{wid}] size_bytes mismatch on {local_rel}: manifest={expected_bytes} disk={actual_bytes}"
                )
    if not SHA256_HEX_RX.match(expected_sha):
        errors.append(f"works[{wid}] invalid sha256 format on {local_rel}: {expected_sha!r}")
    else:
        actual_sha = hashlib.sha256(resolved.read_bytes()).hexdigest()
        if actual_sha != expected_sha:
            errors.append(
                f"works[{wid}] sha256 mismatch on {local_rel}: manifest={expected_sha[:12]}... disk={actual_sha[:12]}..."
            )


def validate_manifest(repo_root: Path = REPO_ROOT, pillar_filter: str = "all") -> tuple[CheckOutcome, dict[str, Any] | None]:
    """Validate .papers/primary_sources/ directory structure, MANIFEST.json schema, SHA-256, and 46-work coverage."""
    papers_root = repo_root / PAPERS_ROOT_REL
    manifest_path = repo_root / MANIFEST_REL
    if not manifest_path.is_file():
        return (
            CheckOutcome(
                check_id="T1-M1-MANIFEST",
                tier=1,
                milestone="M1",
                pillar=pillar_filter,
                status="FAIL",
                summary=f"Missing {MANIFEST_REL}",
                details={"missing": MANIFEST_REL},
            ),
            None,
        )

    errors: list[str] = []
    for pdir in PILLAR_DIR_MAP.values():
        if not (papers_root / pdir).is_dir():
            errors.append(f"Missing pillar directory: {PAPERS_ROOT_REL}/{pdir}")

    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except Exception as exc:
        return (
            CheckOutcome(
                check_id="T1-M1-MANIFEST",
                tier=1,
                milestone="M1",
                pillar=pillar_filter,
                status="FAIL",
                summary=f"Invalid JSON in {MANIFEST_REL}: {exc}",
                details={"error": str(exc)},
            ),
            None,
        )

    if not isinstance(manifest, dict):
        return (
            CheckOutcome(
                check_id="T1-M1-MANIFEST",
                tier=1,
                milestone="M1",
                pillar=pillar_filter,
                status="FAIL",
                summary=f"{MANIFEST_REL} top-level must be a JSON object",
                details={},
            ),
            None,
        )

    works = manifest.get("works") if "works" in manifest else manifest.get("entries")
    if not isinstance(works, list) or not works:
        return (
            CheckOutcome(
                check_id="T1-M1-MANIFEST",
                tier=1,
                milestone="M1",
                pillar=pillar_filter,
                status="FAIL",
                summary=f"{MANIFEST_REL} must define a non-empty 'works' or 'entries' list",
                details={},
            ),
            manifest,
        )

    if "total_works" in manifest and manifest["total_works"] != len(works):
        errors.append(f"total_works={manifest['total_works']} != len(works)={len(works)}")
    if isinstance(manifest.get("pillars"), dict):
        p_total = sum(
            int(v.get("work_count", 0))
            for v in manifest["pillars"].values()
            if isinstance(v, dict)
        )
        if p_total and p_total != len(works):
            errors.append(f"pillars work_count sum={p_total} != len(entries)={len(works)}")

    if len(works) != 46:
        errors.append(f"Expected exactly 46 works covering all 46 founder specs, found {len(works)}")

    seen_ids: set[str] = set()
    works_by_pdir: dict[str, list[dict[str, Any]]] = {d: [] for d in PILLAR_DIR_MAP.values()}
    status_counts: dict[str, int] = {}

    for idx, entry in enumerate(works):
        if not isinstance(entry, dict):
            errors.append(f"works[{idx}] is not a JSON object")
            continue
        wid = str(entry.get("id", "")).strip()
        if not wid:
            errors.append(f"works[{idx}] missing non-empty 'id'")
        elif wid in seen_ids:
            errors.append(f"Duplicate work id: {wid}")
        seen_ids.add(wid)

        raw_pillar = str(entry.get("pillar", "")).strip()
        pdir = _normalize_pillar_name(raw_pillar)
        if pdir not in PILLAR_DIR_TO_KEY:
            errors.append(f"works[{wid or idx}] invalid pillar {raw_pillar!r}")
        else:
            works_by_pdir[pdir].append(entry)

        author_val = entry.get("author") or entry.get("authors") or entry.get("author_year")
        if not str(author_val or "").strip():
            errors.append(f"works[{wid or idx}] missing non-empty 'author'/'author_year'")
        year_val = entry.get("year") or entry.get("author_year")
        if not str(year_val or "").strip():
            errors.append(f"works[{wid or idx}] missing non-empty 'year'/'author_year'")
        if not str(entry.get("title", "")).strip():
            errors.append(f"works[{wid or idx}] missing non-empty 'title'")

        r3_vals = entry.get("r3_principles")
        if not isinstance(r3_vals, list) or not r3_vals:
            errors.append(f"works[{wid or idx}] missing non-empty 'r3_principles' list")
        else:
            bad_r3 = [v for v in r3_vals if not isinstance(v, str) or v.strip() not in VALID_R3_TAGS]
            if bad_r3:
                errors.append(f"works[{wid or idx}] invalid r3_principles {bad_r3!r}")

        status = str(entry.get("status") or entry.get("availability_status") or "").strip()
        if status not in VALID_WORK_STATUSES:
            errors.append(f"works[{wid or idx}] invalid status {status!r}")
            continue
        status_counts[status] = status_counts.get(status, 0) + 1

        if status != "gap_recorded":
            artifacts = entry.get("artifacts")
            if isinstance(artifacts, list):
                if not artifacts:
                    errors.append(f"works[{wid}] status={status} has empty 'artifacts' list")
                for a_idx, art in enumerate(artifacts):
                    if not isinstance(art, dict):
                        errors.append(f"works[{wid}] artifacts[{a_idx}] is not a JSON object")
                        continue
                    src_ref = art.get("source_origin") or art.get("source_url") or art.get("local_collection_ref") or art.get("url")
                    if not str(src_ref or "").strip():
                        errors.append(f"works[{wid}] artifacts[{a_idx}] missing 'source_origin'/'source_url'")
                    _validate_artifact_on_disk(
                        wid,
                        str(art.get("local_path", "")).strip(),
                        art.get("bytes") if "bytes" in art else art.get("size_bytes"),
                        str(art.get("sha256", "")).strip(),
                        pdir=pdir,
                        repo_root=repo_root,
                        papers_root=papers_root,
                        errors=errors,
                    )
            else:
                src_ref = entry.get("source_url") or entry.get("local_collection_ref") or entry.get("url")
                if not str(src_ref or "").strip():
                    errors.append(f"works[{wid}] status={status} missing 'source_url' or 'local_collection_ref'")
                _validate_artifact_on_disk(
                    wid,
                    str(entry.get("local_path", "")).strip(),
                    entry.get("size_bytes") if "size_bytes" in entry else entry.get("bytes"),
                    str(entry.get("sha256", "")).strip(),
                    pdir=pdir,
                    repo_root=repo_root,
                    papers_root=papers_root,
                    errors=errors,
                )

            if status == "substituted":
                if not str(entry.get("substitute", "")).strip():
                    errors.append(f"works[{wid}] status=substituted missing non-empty 'substitute'")
                if not str(entry.get("gap_reason", "")).strip():
                    errors.append(f"works[{wid}] status=substituted missing non-empty 'gap_reason'")
            elif status in {"paywalled_with_oa_substitute", "oa_translation_or_substitute"}:
                note = str(entry.get("gap_or_paywall_note") or entry.get("gap_reason") or "").strip()
                if len(note) < 20:
                    errors.append(f"works[{wid}] status={status} missing non-empty 'gap_or_paywall_note' (>= 20 chars)")
        else:  # gap_recorded
            gap_reason = str(entry.get("gap_reason") or entry.get("gap_or_paywall_note") or "").strip()
            if len(gap_reason) < 20:
                errors.append(f"works[{wid}] status=gap_recorded requires 'gap_reason' >= 20 chars")

    expected_spec_ids = {s.spec_id for s in FOUNDER_YEAR_SPEC}
    if seen_ids != EXPECTED_M1_WORK_IDS and seen_ids != expected_spec_ids:
        missing_m1_ids = sorted(EXPECTED_M1_WORK_IDS - seen_ids)
        extra_m1_ids = sorted(seen_ids - EXPECTED_M1_WORK_IDS)
        errors.append(f"M1 work ID mismatch: missing={missing_m1_ids[:5]}, extra={extra_m1_ids[:5]}")

    works_by_id: dict[str, dict[str, Any]] = {
        str(w.get("id", "")).strip(): w
        for w in works
        if isinstance(w, dict) and str(w.get("id", "")).strip()
    }

    # Check 46 founder-year specs 1-to-1 bound to spec.work_id (or spec.spec_id in synthetic fixtures)
    missing_specs: list[str] = []
    for spec in FOUNDER_YEAR_SPEC:
        if pillar_filter != "all" and spec.pillar != pillar_filter:
            continue
        bound_id = spec.work_id if (spec.work_id and spec.work_id in works_by_id) else spec.spec_id
        bound_work = works_by_id.get(bound_id)
        if bound_work is not None:
            w_pdir = _normalize_pillar_name(str(bound_work.get("pillar", "")))
            if w_pdir != spec.pillar_dir:
                missing_specs.append(f"{spec.label} ({bound_id} has pillar {w_pdir!r} != {spec.pillar_dir!r})")
            elif not _work_matches_spec(bound_work, spec.author_patterns):
                missing_specs.append(f"{spec.label} ({bound_id} does not match author in {spec.pillar_dir})")
            elif not _work_matches_spec_and_years(bound_work, spec):
                missing_specs.append(f"{spec.label} ({bound_id} missing year token {spec.required_year_groups})")
        else:
            candidates = works_by_pdir.get(spec.pillar_dir, [])
            author_hits = [w for w in candidates if _work_matches_spec(w, spec.author_patterns)]
            if not author_hits:
                missing_specs.append(f"{spec.label} (missing bound work {spec.work_id or spec.spec_id})")
            elif not any(_work_matches_spec_and_years(w, spec) for w in author_hits):
                missing_specs.append(f"{spec.label} missing year token {spec.required_year_groups}")

    if missing_specs:
        errors.append(f"Missing founder-year specs ({len(missing_specs)}): {missing_specs[:10]}")

    if errors:
        return (
            CheckOutcome(
                check_id="T1-M1-MANIFEST",
                tier=1,
                milestone="M1",
                pillar=pillar_filter,
                status="FAIL",
                summary=f"{len(errors)} manifest error(s): {'; '.join(errors[:3])}",
                details={"errors": errors, "status_counts": status_counts, "total_works": len(works)},
            ),
            manifest,
        )

    status_summary = ", ".join(f"{k}={v}" for k, v in sorted(status_counts.items()))
    return (
        CheckOutcome(
            check_id="T1-M1-MANIFEST",
            tier=1,
            milestone="M1",
            pillar=pillar_filter,
            status="PASS",
            summary=f"MANIFEST.json valid ({len(works)} works: {status_summary}; all founder-year specs covered)",
            details={"status_counts": status_counts, "total_works": len(works)},
        ),
        manifest,
    )


_RANGE_ITEM_RX = re.compile(r"^(S\d+)-(\d+)\.\.(?:(S\d+)-)?(\d+)(?=$|[\s,])")
_SINGLE_ID_RX = re.compile(r"^(S\d+-\d+)(?=$|[\s,])")


def _validate_work_id_bounds(wid: str, valid_ids: AbstractSet[str] | None, raw_work_id: str) -> None:
    if valid_ids is not None:
        if wid not in valid_ids:
            raise ValueError(f"Out-of-manifest work ID {wid!r} in {raw_work_id!r}")
        return
    if re.fullmatch(r"S\d+-\d+", wid) and wid not in EXPECTED_M1_WORK_IDS:
        raise ValueError(f"Out-of-manifest work ID {wid!r} in {raw_work_id!r}")


def expand_traceability_work_ids(
    raw_work_id: str,
    valid_ids: AbstractSet[str] | None = None,
) -> list[str]:
    """Expand single, ranged ('S2-03..04', 'S2-03..S2-04'), or comma-separated source IDs.

    Raises ValueError on reversed ranges, cross-prefix ranges, malformed ranges, or out-of-manifest IDs.
    """
    cleaned = re.sub(r"[`*]", "", raw_work_id).strip()
    if not cleaned:
        return []

    def _consume_one(text: str) -> tuple[list[str], str]:
        m_range = _RANGE_ITEM_RX.match(text)
        if m_range:
            p1, start_s, p2, end_s = m_range.groups()
            if p2 and p2 != p1:
                raise ValueError(f"Cross-prefix work ID range in {raw_work_id!r}")
            start_n, end_n = int(start_s), int(end_s)
            if start_n > end_n:
                raise ValueError(f"Reversed work ID range {m_range.group(0)!r} in {raw_work_id!r}")
            if end_n - start_n > 100:
                raise ValueError(f"Over-wide work ID range {m_range.group(0)!r} in {raw_work_id!r}")
            width = max(len(start_s), len(end_s))
            ids = [f"{p1}-{n:0{width}d}" for n in range(start_n, end_n + 1)]
            for wid in ids:
                _validate_work_id_bounds(wid, valid_ids, raw_work_id)
            return ids, text[m_range.end() :]

        head_tok = text.split(None, 1)[0].rstrip(",")
        if ".." in head_tok:
            raise ValueError(f"Malformed work ID range {head_tok!r} in {raw_work_id!r}")

        m_single = _SINGLE_ID_RX.match(text)
        if m_single:
            wid = m_single.group(1)
            _validate_work_id_bounds(wid, valid_ids, raw_work_id)
            return [wid], text[m_single.end() :]
        return [], text

    first_ids, rest = _consume_one(cleaned)
    if not first_ids:
        return [cleaned]

    expanded: list[str] = list(first_ids)
    while True:
        m_comma = re.match(r"^\s*,\s*(.+)$", rest)
        if not m_comma:
            break
        nxt = m_comma.group(1).strip()
        if not (re.match(r"^S\d+-", nxt) or ".." in nxt.split(None, 1)[0]):
            break
        more_ids, rest = _consume_one(nxt)
        if not more_ids:
            raise ValueError(f"Malformed comma-separated work ID in {raw_work_id!r}")
        expanded.extend(more_ids)

    return expanded


def _normalize_traceability_modules(raw_mod: str) -> tuple[tuple[str, ...], tuple[str, ...]]:
    cleaned = re.sub(r"[`*]", "", raw_mod).strip()
    cleaned = re.sub(r"^M\d+\s*:\s*", "", cleaned).strip()
    if not cleaned:
        return (), ("empty Lean Module cell",)
    mods: list[str] = []
    errors: list[str] = []
    last_pkg = ""
    for part in re.split(r"(?:<br\s*/?>|[,\n;])+", cleaned):
        tok = part.strip()
        if not tok:
            continue
        m_full_path = re.fullmatch(r"(?:lean/)?(InfoGeometry(?:/[A-Za-z0-9_]+)+)\.lean", tok)
        if m_full_path:
            mod = m_full_path.group(1).replace("/", ".")
            mods.append(mod)
            last_pkg = mod.rsplit(".", 1)[0]
            continue
        m_mod = re.fullmatch(r"(InfoGeometry(?:\.[A-Za-z0-9_]+)+)", tok)
        if m_mod:
            mod = m_mod.group(1)
            mods.append(mod)
            last_pkg = mod.rsplit(".", 1)[0]
            continue
        m_rel_lean = re.fullmatch(r"([A-Za-z0-9_]+)\.lean", tok)
        if m_rel_lean and last_pkg:
            mods.append(f"{last_pkg}.{m_rel_lean.group(1)}")
            continue
        if re.fullmatch(r"docs/[A-Za-z0-9_./-]+\.md", tok):
            continue
        errors.append(f"unparsed/invalid module token {tok!r}")
    return tuple(dict.fromkeys(mods)), tuple(errors)


def _normalize_traceability_module(raw_mod: str) -> str:
    mods, errs = _normalize_traceability_modules(raw_mod)
    if mods and not errs:
        return mods[0]
    cleaned = re.sub(r"[`*]", "", raw_mod).strip()
    return cleaned


def parse_traceability_matrix(doc_text: str) -> list[TraceabilityRow]:
    """Parse Markdown Source-to-Declaration traceability table(s) from PRIMARY_SOURCE_ARCHETYPES.md."""
    rows: list[TraceabilityRow] = []
    lines = doc_text.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        if line.startswith("|") and line.endswith("|") and i + 1 < len(lines):
            sep = lines[i + 1].strip()
            if sep.startswith("|") and set(sep.replace("|", "").replace(":", "").replace("-", "").strip()) == set():
                headers = [re.sub(r"[`*]", "", h).strip().lower() for h in line.strip("|").split("|")]
                has_work = any("work" in h or "source id" in h or h == "id" for h in headers)
                has_mod = any("module" in h for h in headers)
                has_decl = any("decl" in h for h in headers)
                if has_work and has_mod and has_decl:
                    col_idx = {h: idx for idx, h in enumerate(headers)}
                    def _find_col(*substrs: str) -> int | None:
                        for key, idx in col_idx.items():
                            if any(s in key for s in substrs):
                                return idx
                        return None

                    c_work = _find_col("work id", "work_id", "source id", "id")
                    c_pillar = _find_col("pillar")
                    c_author = _find_col("author")
                    c_arch = _find_col("archetype", "anchor")
                    c_r3 = _find_col("r3")
                    c_mod = _find_col("lean module", "target module", "module")
                    c_decl = _find_col("declaration")
                    c_status = _find_col("status")

                    j = i + 2
                    while j < len(lines):
                        row_line = lines[j].strip()
                        if not (row_line.startswith("|") and row_line.endswith("|")):
                            break
                        cells = [c.strip() for c in row_line.strip("|").split("|")]
                        if len(cells) < len(headers):
                            cells.extend([""] * (len(headers) - len(cells)))
                        work_id = re.sub(r"[`*]", "", cells[c_work] if c_work is not None else "").strip()
                        if work_id and not set(work_id) <= {"-", ":"}:
                            raw_mod_cell = cells[c_mod] if c_mod is not None else ""
                            lean_mods, mod_errs = _normalize_traceability_modules(raw_mod_cell)
                            primary_mod = lean_mods[0] if (lean_mods and not mod_errs) else re.sub(r"[`*]", "", raw_mod_cell).strip()
                            raw_decl = cells[c_decl] if c_decl is not None else ""
                            decls: list[str] = []
                            for tok in re.split(r"(?:<br\s*/?>|[,;\n])+", raw_decl):
                                clean = re.sub(r"[`*]", "", tok).strip()
                                low = clean.lower()
                                if (
                                    clean
                                    and low not in PLACEHOLDER_CELL_VALUES
                                    and not re.fullmatch(r"\[m\d+\s+tbd\]", low)
                                ):
                                    decls.append(clean)
                            rows.append(
                                TraceabilityRow(
                                    work_id=work_id,
                                    pillar=re.sub(r"[`*]", "", cells[c_pillar] if c_pillar is not None else "").strip(),
                                    author_year=re.sub(r"[`*]", "", cells[c_author] if c_author is not None else "").strip(),
                                    archetype=cells[c_arch].strip() if c_arch is not None else "",
                                    r3_principle=re.sub(r"[`*]", "", cells[c_r3] if c_r3 is not None else "").strip(),
                                    lean_module=primary_mod,
                                    declarations=tuple(decls),
                                    status=re.sub(r"[`*]", "", cells[c_status] if c_status is not None else "").strip(),
                                    line_no=j + 1,
                                    lean_modules=lean_mods,
                                    module_errors=mod_errs,
                                )
                            )
                        j += 1
                    i = j
                    continue
        i += 1
    return rows


def _extract_pillar_sections(text: str) -> dict[str, str]:
    sections = re.split(r"(?m)^(?=##\s+)", text)
    by_pillar: dict[str, list[str]] = {k: [] for k in PILLAR_HEADING_PATTERNS}
    for sec in sections:
        heading = sec.splitlines()[0] if sec else ""
        if not heading.startswith("## "):
            continue
        for pkey, pats in PILLAR_HEADING_PATTERNS.items():
            # Match heading using marker + founder patterns (pats[0] & pats[2]) so section body text isn't required on heading
            if re.search(pats[0], heading, re.IGNORECASE) and re.search(pats[2], heading, re.IGNORECASE):
                by_pillar[pkey].append(sec)
    return {k: "\n".join(v) for k, v in by_pillar.items()}


def validate_archetypes_doc(
    repo_root: Path = REPO_ROOT,
    manifest: dict[str, Any] | None = None,
    pillar_filter: str = "all",
) -> tuple[CheckOutcome, list[TraceabilityRow]]:
    """Validate docs/PRIMARY_SOURCE_ARCHETYPES.md pillars, 1:1 manifest sync, honest gap parity, and R3 tags."""
    doc_path = repo_root / ARCHETYPES_DOC_REL
    if not doc_path.is_file():
        return (
            CheckOutcome(
                check_id="T1-M1-ARCHETYPES-DOC",
                tier=1,
                milestone="M1",
                pillar=pillar_filter,
                status="FAIL",
                summary=f"Missing {ARCHETYPES_DOC_REL}",
                details={"missing": ARCHETYPES_DOC_REL},
            ),
            [],
        )

    text = doc_path.read_text(encoding="utf-8", errors="replace")
    if len(text.strip()) < 200:
        return (
            CheckOutcome(
                check_id="T1-M1-ARCHETYPES-DOC",
                tier=1,
                milestone="M1",
                pillar=pillar_filter,
                status="FAIL",
                summary=f"{ARCHETYPES_DOC_REL} is empty or too short ({len(text.strip())} chars)",
                details={},
            ),
            [],
        )

    errors: list[str] = []
    for pkey, pats in PILLAR_HEADING_PATTERNS.items():
        if pillar_filter != "all" and pkey != pillar_filter:
            continue
        if not all(re.search(pat, text, re.IGNORECASE) for pat in pats):
            errors.append(f"Missing pillar section/markers for {pkey} in {ARCHETYPES_DOC_REL}")

    for r3_tag in ("R3.1", "R3.2", "R3.3", "R3.4"):
        if r3_tag not in text:
            errors.append(f"Missing {r3_tag} tag in {ARCHETYPES_DOC_REL}")

    manifest_works = None
    manifest_ids: set[str] | None = None
    work_pillar_by_id: dict[str, str] = {}
    if manifest:
        manifest_works = manifest.get("works") if "works" in manifest else manifest.get("entries")
        if isinstance(manifest_works, list):
            manifest_ids = set()
            for w in manifest_works:
                if isinstance(w, dict):
                    wid = str(w.get("id", "")).strip()
                    if wid:
                        manifest_ids.add(wid)
                        wpk = PILLAR_DIR_TO_KEY.get(_normalize_pillar_name(str(w.get("pillar", ""))), "")
                        if wpk:
                            work_pillar_by_id[wid] = wpk

    rows = parse_traceability_matrix(text)
    rows_by_id: dict[str, list[TraceabilityRow]] = {}
    row_lines_by_pillar: dict[str, list[str]] = {k: [] for k in PILLAR_HEADING_PATTERNS}
    doc_lines = text.splitlines()

    for row in rows:
        if not re.search(r"\bR3\.[1-4]\b", row.r3_principle):
            errors.append(
                f"Traceability row {row.work_id} (line {row.line_no}) missing valid R3.1-R3.4 tag (got {row.r3_principle!r})"
            )
        try:
            expanded = expand_traceability_work_ids(row.work_id, valid_ids=manifest_ids)
        except ValueError as exc:
            errors.append(f"Traceability row {row.work_id} (line {row.line_no}): {exc}")
            expanded = []
        row_pillar = PILLAR_DIR_TO_KEY.get(_normalize_pillar_name(row.pillar), "")
        for wid_item in expanded:
            rows_by_id.setdefault(wid_item, []).append(row)
            if not row_pillar and wid_item in work_pillar_by_id:
                row_pillar = work_pillar_by_id[wid_item]
        if row_pillar in row_lines_by_pillar and 1 <= row.line_no <= len(doc_lines):
            row_lines_by_pillar[row_pillar].append(doc_lines[row.line_no - 1])

    pillar_sections = _extract_pillar_sections(text)
    for spec in FOUNDER_YEAR_SPEC:
        if pillar_filter != "all" and spec.pillar != pillar_filter:
            continue
        scope_text = pillar_sections.get(spec.pillar, "") + "\n" + "\n".join(row_lines_by_pillar.get(spec.pillar, []))
        scope_lines = [ln for ln in scope_text.splitlines() if ln.strip()]
        author_lines = [
            ln for ln in scope_lines
            if all(re.search(pat, ln, re.IGNORECASE) for pat in spec.author_patterns)
        ]
        if not author_lines:
            errors.append(f"Archetypes doc missing author for {spec.label} in {spec.pillar} section")
            continue
        if not any(
            all(any(y in ln for y in ygroup) for ygroup in spec.required_year_groups)
            for ln in author_lines
        ):
            errors.append(f"Archetypes doc missing year {spec.required_year_groups} for {spec.label} in {spec.pillar} section")

    if isinstance(manifest_works, list):
        for w in manifest_works:
            if not isinstance(w, dict):
                continue
            wid = str(w.get("id", "")).strip()
            wpillar = PILLAR_DIR_TO_KEY.get(_normalize_pillar_name(str(w.get("pillar", ""))), "")
            if pillar_filter != "all" and wpillar != pillar_filter:
                continue
            if wid and not re.search(rf"(?<![A-Za-z0-9_-]){re.escape(wid)}(?![A-Za-z0-9_-])", text):
                errors.append(f"Work id {wid!r} from MANIFEST.json missing in {ARCHETYPES_DOC_REL}")
            wstatus = str(w.get("status") or w.get("availability_status") or "").strip()
            if wstatus in SUBSTITUTE_OR_GAP_STATUSES:
                matched_rows = rows_by_id.get(wid, [])
                single_work_rows = [
                    r for r in matched_rows
                    if len(expand_traceability_work_ids(r.work_id, valid_ids=manifest_ids)) == 1
                ]
                matching_lines = [
                    ln for ln in doc_lines
                    if re.search(rf"(?<![A-Za-z0-9_-]){re.escape(wid)}(?![A-Za-z0-9_-])", ln)
                ]
                line_blob = " ".join(matching_lines).lower()
                single_row_blob = " ".join(f"{r.status} {r.archetype}" for r in single_work_rows).lower()
                combined_gap = f"{single_row_blob} {line_blob}"
                if wstatus == "gap_recorded":
                    negated_gap_rx = (
                        r"\b(?:not|never|no|without|isn't|aren't)\s+"
                        r"(?:(?:actually|currently|really|longer)\s+)?"
                        r"(?:gap_recorded|gap|unavailable|paywall(?:ed)?|omitted|restricted)\b"
                    )
                    if re.search(r"\b(?:exact_primary_downloaded|exact_primary_cached|downloaded)\b", combined_gap):
                        errors.append(
                            f"Honest gap parity violation for {wid!r} (status=gap_recorded): doc claims exact/downloaded status"
                        )
                    elif re.search(negated_gap_rx, combined_gap):
                        errors.append(
                            f"Honest gap parity violation for {wid!r} (status={wstatus}): negated gap/unavailable phrasing in {ARCHETYPES_DOC_REL}"
                        )
                    elif not re.search(r"\b(?:gap_recorded|gap|unavailable|paywall(?:ed)?|omitted|restricted)\b", combined_gap):
                        errors.append(
                            f"Honest gap parity violation for {wid!r} (status={wstatus}): no gap/unavailable note on work's own row/line in {ARCHETYPES_DOC_REL}"
                        )
                else:
                    if re.search(r"\b(?:exact_primary_downloaded|exact_primary_cached)\b", line_blob):
                        errors.append(
                            f"Honest gap parity violation for {wid!r} (status={wstatus}): doc claims exact_primary status"
                        )
                    elif not re.search(
                        r"\b(?:substituted|substitute[ds]?|paywalled_with_oa_substitute|oa_translation_or_substitute|paywall(?:ed)?|oa_substitute|unavailable)\b",
                        combined_gap,
                    ):
                        errors.append(
                            f"Honest gap parity violation for {wid!r} (status={wstatus}): no substitute/paywall note on work's own row/line in {ARCHETYPES_DOC_REL}"
                        )

    if errors:
        return (
            CheckOutcome(
                check_id="T1-M1-ARCHETYPES-DOC",
                tier=1,
                milestone="M1",
                pillar=pillar_filter,
                status="FAIL",
                summary=f"{len(errors)} archetypes doc error(s): {errors[0]}",
                details={"errors": errors, "traceability_rows": len(rows)},
            ),
            rows,
        )

    return (
        CheckOutcome(
            check_id="T1-M1-ARCHETYPES-DOC",
            tier=1,
            milestone="M1",
            pillar=pillar_filter,
            status="PASS",
            summary=f"{ARCHETYPES_DOC_REL} valid (4 pillars, R3.1-R3.4, manifest sync, {len(rows)} traceability rows)",
            details={"traceability_rows": len(rows)},
        ),
        rows,
    )
