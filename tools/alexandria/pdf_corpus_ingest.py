#!/usr/bin/env python3
"""Resilient PDF corpus inventory, deduplication, archetypal/DAG extraction, and Alexandria ingestion.

Records emitted by this pipeline are retrieval/navigation context only
(``sourceAuthority: "retrieval_context_only"``), never verified Lean proof evidence.
"""
from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import math
import os
import re
import subprocess
import sys
import unicodedata
from collections import Counter, defaultdict, deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable
from urllib.request import Request, urlopen

REPO_ROOT = Path(__file__).resolve().parents[2]
for _p in (REPO_ROOT, REPO_ROOT / "src"):
    if str(_p) not in sys.path:
        sys.path.insert(0, str(_p))

from igf.common.json_io import write_jsonl  # noqa: E402
from igf.graph.arango_http import ArangoHttpTarget  # noqa: E402
from tools.alexandria import arango_ingest  # noqa: E402
from tools.alexandria.schema import (  # noqa: E402
    SCHEMA_VERSION,
    content_hash,
    source_uri,
    stable_key,
)
from tools.alexandria.structural_chunking import ident_terms, tokenize  # noqa: E402
from tools.infra.arango_env import (  # noqa: E402
    alexandria_arango_database,
    alexandria_arango_endpoint,
    alexandria_arango_password,
    alexandria_arango_username,
    guard_alexandria_target,
    load_alexandria_arango_env,
)

SOURCE_AUTHORITY = "retrieval_context_only"
SEMANTIC_MODE_DETERMINISTIC = "deterministic_pdf_archetypal_v1"

OUTCOME_KEYS = (
    "ingested",
    "duplicate_skipped",
    "empty_0_bytes",
    "scanned_no_text",
    "encrypted_no_text",
    "very_low_text_skipped",
    "parse_error",
    "limit_skipped",
)

DAG_EDGE_TYPES = (
    "section_precedes_section",
    "proof_proves_theorem",
    "chunk_uses_definition",
    "chunk_references_result",
    "chunk_cites_entry",
    "document_cites_document",
)

DAG_EDGE_PRIORITY = {
    "section_precedes_section": 1,
    "proof_proves_theorem": 2,
    "chunk_cites_entry": 3,
    "chunk_uses_definition": 4,
    "chunk_references_result": 5,
    "document_cites_document": 6,
}

LIGATURE_MAP = str.maketrans(
    {
        "\ufb00": "ff",
        "\ufb01": "fi",
        "\ufb02": "fl",
        "\ufb03": "ffi",
        "\ufb04": "ffl",
        "\ufb05": "ft",
        "\ufb06": "st",
        "\u00a0": " ",
        "\u00ad": "",
    }
)

CONTROL_CHARS_RE = re.compile(r"[\x00-\x08\x0b\x0e-\x1f]")
TYPE3_LIGATURE_RE = re.compile(r"[A-Za-z][\u2026\u00a4][A-Za-z]")
STANDALONE_PAGENUM_RE = re.compile(
    r"^\s*(?:\d{1,4}|[-–—]\s*\d{1,4}\s*[-–—]|page\s+\d{1,4})\s*$",
    re.IGNORECASE,
)

SECTION_HEADER_RE = re.compile(
    r"^(?:"
    r"Abstract\.?|"
    r"Introduction\.?|Preliminaries\.?|Conclusion\.?|Conclusions\.?|Discussion\.?|"
    r"References\.?|REFERENCES\.?|Bibliography\.?|BIBLIOGRAPHY\.?|Acknowledgements?\.?|Acknowledgments?\.?|"
    r"Appendix\s+[A-Z0-9][^\n]{0,80}|"
    r"Chapter\s+(?:\d+|[IVXLCDM]+)\b[^\n]{0,80}|"
    r"Part\s+(?:\d+|[IVXLCDM]+)\b[^\n]{0,80}|"
    r"§\s*\d+(?:\.\d+)*\.?\s+[^\n]{2,90}|"
    r"[IVX]{1,5}\.\s+[A-Z][A-Za-z0-9\s,\-:]{2,80}|"
    r"(?:0|[1-9]\d?)(?:\.\d+){0,3}\.?\s+[A-Z][A-Z0-9\s,\-:]{2,80}|"
    r"(?:0|[1-9]\d?)(?:\.\d+){0,3}\.?\s+[A-Z][^\n]{2,90}"
    r")\s*$"
)
SECTION_NUM_ONLY_RE = re.compile(r"^([1-9]\d?(?:\.\d{1,2}){0,3})\.?$")
SECTION_TITLE_NEXT_RE = re.compile(r"^([A-Z][A-Za-z0-9\s,\-:]{2,80}\.?)$")
MATH_NOISE_IN_HEADING_RE = re.compile(r"[=<>≤≥∈⊂⊃∑∏∫⊗⊕†⋆πζ\\]")
ARXIV_STAMP_LINE_RE = re.compile(
    r"^(?:arXiv:|(?:hep-th|hep-ph|math|quant-ph|cond-mat|gr-qc|physics)/|[A-Z]{2,6}-NF-|[A-Z]{2,6}\s+\d{2,})",
    re.IGNORECASE,
)
THEOREM_HEADER_RE = re.compile(
    r"^(Theorem|Lemma|Proposition|Corollary|Conjecture|Claim)"
    r"(?:\s+(\d+(?:\.\d+)*|[A-Z](?:\.\d+)*))?"
    r"(?:\s*\([^)]+\))?\s*[\.:]",
    re.IGNORECASE,
)
DEFINITION_HEADER_RE = re.compile(
    r"^(Definition|Notation|Axiom|Hypothesis|Assumption)"
    r"(?:\s+(\d+(?:\.\d+)*|[A-Z](?:\.\d+)*))?"
    r"(?:\s*\([^)]+\))?\s*[\.:]",
    re.IGNORECASE,
)
REMARK_HEADER_RE = re.compile(
    r"^(Remark|Example|Observation|Note)"
    r"(?:\s+(\d+(?:\.\d+)*|[A-Z](?:\.\d+)*))?"
    r"(?:\s*\([^)]+\))?\s*[\.:]",
    re.IGNORECASE,
)
PROOF_HEADER_RE = re.compile(
    r"^(Proof(?:\s+of\s+(?:Theorem|Lemma|Proposition|Corollary|Conjecture|Claim)\s+[A-Za-z0-9.]+)?)\s*[\.:]",
    re.IGNORECASE,
)
EQUATION_END_RE = re.compile(r"\((\d+(?:\.\d+)*)\)\s*$")
INTERNAL_REF_RE = re.compile(
    r"\b(Theorem|Lemma|Proposition|Corollary|Conjecture|Claim|Definition|Notation|Remark|Section|Eq\.?|Equation)\s+"
    r"(\(?\d+(?:\.\d+)*\)?)",
    re.IGNORECASE,
)
BRACKET_CITE_RE = re.compile(r"\[([0-9][0-9,\s\-–]*|[A-Z][A-Za-z0-9]{1,8}\d{2,4}[a-z]?)\]")
BIB_ENTRY_START_RE = re.compile(r"^\s*(?:\[([^\]]{1,24})\]|(\d{1,4})\.)\s+(.*)$")
ARXIV_ID_RE = re.compile(r"\b(?:arXiv:\s*)?(\d{4}\.\d{4,5}(?:v\d+)?|[a-z-]+/\d{7}(?:v\d+)?)\b", re.IGNORECASE)
DOI_RE = re.compile(r"\b(10\.\d{4,9}/[^\s,;\]\"'<>]+)")

UNICODE_MATH_RE = re.compile(r"[α-ωΑ-Ωℓℏ∂∇⊗⊕∑∏∫⊂⊆⊃⊇∈∉∀∃⇒⇔≅≃≈≤≥≠∞]+")
SYMBOLIC_EXPR_RE = re.compile(
    r"\b(?:Cl|Cℓ|Spin|Pin|SO|SU|SL|GL|KK|Hom|End|Ext|Tor)\s*\([^)\n]{1,24}\)"
    r"|KK\^[A-Za-z0-9_]+"
    r"|C\*-algebra"
)
DOMAIN_TERMS_RE = re.compile(
    r"\b(?:"
    r"Clifford|Krein|Souriau|Bost-Connes|Drazin|Moore-Penrose|Kasparov|"
    r"Dirac-Hestenes|Dirac|Hestenes|Hilbert|Banach|Frechet|Fréchet|"
    r"spinor|manifold|symplectic|metriplectic|Yang-Mills|twistor|"
    r"foliation|colimit|functor|topos|sheaf|cohomology|homology|"
    r"Cuntz|Toeplitz|K-theory|Fredholm|spectral|projector|idempotent|"
    r"nilpotent|noncommutative|exterior algebra|Grassmannian|quaternion|"
    r"octonion|Lipschitz|Riemann-Cartan|Lorentzian|modular"
    r")\b",
    re.IGNORECASE,
)

DEFAULT_NOISE_EXCLUDE_GLOBS: tuple[str, ...] = (
    "*Isabelle2025*",
    "*Act_Content*",
    "*OV2640_DS*",
    "*JFETS_The_New_Frontier*",
)

NON_CROSS_DOC_ENTITY_TYPES = frozenset({"math_label", "math_reference", "bib_entry"})

EQUATION_PROSE_REF_RE = re.compile(
    r"\b(?:see|by|in|from|of|and|or|to|with|into|eq\.?|equation|equations|cf\.?|thm\.?|theorem|lemma|prop\.?|proposition|ref\.?)\s*$",
    re.IGNORECASE,
)

EQUATION_MATH_OP_RE = re.compile(
    r"[=<>≤≥≠≈≅≃∈⊂⊆⊗⊕∑∏∫↦→⇒⇔∂∇+*/^]|(?:\s|^)-[A-Za-z0-9(\\ ]"
)

MATH_ARCHETYPE_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    (
        "z2_graded_polarization",
        re.compile(
            r"\b(?:Z/2|ℤ/2|chiral\s+grading|Peirce\s+decomposition|isotropic\s+null|nullcone|gamma5|Krein\s+involution)\b",
            re.IGNORECASE,
        ),
    ),
    (
        "curved_dga_differential",
        re.compile(
            r"\b(?:graded\s+differential|curved\s+DG|Maurer-Cartan|Bianchi\s+identity|Cartan\s+curvature|soldering)\b",
            re.IGNORECASE,
        ),
    ),
    (
        "clifford_spinor_tower",
        re.compile(
            r"\b(?:Clifford\s+algebra|Cl\s*\([0-9,\s]+\)|spinor|Dirac-Hestenes|Lochak|Daviau|Jordan-Wigner|Pin\s*\()\b",
            re.IGNORECASE,
        ),
    ),
    (
        "krein_indefinite_metric",
        re.compile(
            r"\b(?:Krein\s+space|fundamental\s+symmetry|indefinite\s+inner\s+product|Pontryagin\s+space|J-self-adjoint)\b",
            re.IGNORECASE,
        ),
    ),
    (
        "drazin_riesz_spectral",
        re.compile(
            r"\b(?:Drazin\s+inverse|Riesz\s+projector|Riesz\s+decomposition|Moore-Penrose|Fredholm|generalized\s+inverse)\b",
            re.IGNORECASE,
        ),
    ),
    (
        "souriau_metriplectic_thermo",
        re.compile(
            r"\b(?:Souriau|coadjoint\s+orbit|moment\s+map|Massieu|Gibbs\s+state|Casimir|Onsager|metriplectic)\b",
            re.IGNORECASE,
        ),
    ),
    (
        "modular_kms_monodromy",
        re.compile(
            r"\b(?:Tomita-Takesaki|modular\s+flow|modular\s+automorphism|KMS\s+state|Bost-Connes|thermal\s+time|monodromy|de\s+Rham)\b",
            re.IGNORECASE,
        ),
    ),
    (
        "categorical_colimit_tower",
        re.compile(
            r"\b(?:direct\s+limit|colimit|inductive\s+limit|functor|natural\s+transformation|adjunction|topos|sheaf)\b",
            re.IGNORECASE,
        ),
    ),
    (
        "noncommutative_k_theory",
        re.compile(
            r"\b(?:C\*-algebra|KK-theory|Kasparov|spectral\s+triple|cyclic\s+cohomology|Cuntz|Toeplitz)\b",
            re.IGNORECASE,
        ),
    ),
    (
        "yang_mills_gauge_holonomy",
        re.compile(
            r"\b(?:Yang-Mills|gauge\s+connection|Wilson\s+loop|holonomy|Berry\s+curvature|principal\s+bundle|Chern-Simons)\b",
            re.IGNORECASE,
        ),
    ),
)


def _extract_math_archetypes(text: str) -> list[str]:
    return [name for name, pat in MATH_ARCHETYPE_PATTERNS if pat.search(text)]


def _is_displayed_equation_block(text: str) -> bool:
    s = text.strip()
    if not s or len(s) >= 600:
        return False
    m = EQUATION_END_RE.search(s)
    if not m:
        return False
    body = s[: m.start()].strip()
    if len(body) < 3:
        return False
    if EQUATION_PROSE_REF_RE.search(body):
        return False
    return bool(EQUATION_MATH_OP_RE.search(body))


@dataclass
class DiscoveredPdf:
    path: Path
    rel_path: str
    size_bytes: int
    sha256: str
    is_magic_non_pdf_ext: bool
    read_error: str = ""


@dataclass
class DedupGroup:
    sha256: str
    size_bytes: int
    canonical: DiscoveredPdf
    duplicates: list[DiscoveredPdf] = field(default_factory=list)


@dataclass
class InventoryResult:
    input_dir: Path
    total_entries_seen: int
    symlinks_skipped: int
    total_scanned_files: int
    non_pdf_skipped: int
    non_pdf_by_extension: dict[str, int]
    pdf_extension_count: int
    magic_header_non_pdf_ext_count: int
    total_pdf_files: int
    groups: list[DedupGroup]


@dataclass
class ExtractionResult:
    sha256: str
    canonical_path: Path
    rel_path: str
    duplicate_paths: list[str]
    size_bytes: int
    outcome: str
    reason: str
    page_count: int
    char_count: int
    parser: str
    warnings: list[str]
    title: str
    author: str
    encrypted: bool
    encoding_noise_ratio: float
    pages: list[tuple[int, str]]


def _is_magic_pdf(path: Path) -> bool:
    try:
        with path.open("rb") as fh:
            head = fh.read(1024)
        return b"%PDF-" in head.lstrip()[:32]
    except OSError:
        return False


def _stream_sha256(path: Path, chunk_size: int = 1024 * 1024) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        while True:
            chunk = fh.read(chunk_size)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()


def _canonical_sort_key(item: DiscoveredPdf) -> tuple[int, int, int, int, str]:
    rel_lower = item.rel_path.lower()
    is_isabelle = 1 if "isabelle" in rel_lower else 0
    not_pdf_ext = 0 if item.path.suffix.lower() == ".pdf" else 1
    is_browser_copy = 1 if re.search(r"\s\(\d+\)(?:\.[^./]+)?$", item.path.name) else 0
    depth = len(Path(item.rel_path).parts)
    return (is_isabelle, not_pdf_ext, is_browser_copy, depth, item.rel_path)


def _matches_exclude_glob(rel_posix: str, exclude_patterns: tuple[str, ...]) -> bool:
    if not exclude_patterns:
        return False
    parts = Path(rel_posix).parts
    name = Path(rel_posix).name
    for pat in exclude_patterns:
        if fnmatch.fnmatch(rel_posix, pat) or fnmatch.fnmatch(name, pat) or any(fnmatch.fnmatch(p, pat) for p in parts):
            return True
    return False


def scan_and_deduplicate_corpus(
    input_dir: Path,
    *,
    exclude_globs: Iterable[str] = (),
) -> InventoryResult:
    if not input_dir.exists():
        raise FileNotFoundError(f"Input path does not exist: {input_dir}")

    exclude_patterns = tuple(str(p).strip() for p in exclude_globs if str(p).strip())
    symlinks_skipped = 0
    total_scanned_files = 0
    non_pdf_skipped = 0
    non_pdf_by_ext: Counter[str] = Counter()
    pdf_extension_count = 0
    magic_header_non_pdf_ext_count = 0
    discovered: list[DiscoveredPdf] = []

    def _inspect_file(file_path: Path, rel_posix: str) -> None:
        nonlocal symlinks_skipped, total_scanned_files, non_pdf_skipped
        nonlocal pdf_extension_count, magic_header_non_pdf_ext_count
        if file_path.is_symlink():
            symlinks_skipped += 1
            return
        if not file_path.is_file():
            return
        total_scanned_files += 1
        if exclude_patterns and _matches_exclude_glob(rel_posix, exclude_patterns):
            non_pdf_skipped += 1
            non_pdf_by_ext["<excluded>"] += 1
            return
        suffix = file_path.suffix.lower()
        is_pdf_ext = suffix == ".pdf"
        is_magic = False if is_pdf_ext else _is_magic_pdf(file_path)
        if not is_pdf_ext and not is_magic:
            non_pdf_skipped += 1
            non_pdf_by_ext[suffix or "<none>"] += 1
            return
        if is_pdf_ext:
            pdf_extension_count += 1
        else:
            magic_header_non_pdf_ext_count += 1
        read_error = ""
        try:
            size_bytes = file_path.stat().st_size
        except OSError as exc:
            size_bytes = 0
            read_error = f"{type(exc).__name__}: {exc}"
        if read_error:
            digest = hashlib.sha256(f"error:{file_path.as_posix()}".encode("utf-8")).hexdigest()
        elif size_bytes == 0:
            digest = hashlib.sha256(b"").hexdigest()
        else:
            try:
                digest = _stream_sha256(file_path)
            except OSError as exc:
                read_error = f"{type(exc).__name__}: {exc}"
                digest = hashlib.sha256(f"error:{file_path.as_posix()}".encode("utf-8")).hexdigest()
        discovered.append(
            DiscoveredPdf(
                path=file_path,
                rel_path=rel_posix,
                size_bytes=size_bytes,
                sha256=digest,
                is_magic_non_pdf_ext=not is_pdf_ext,
                read_error=read_error,
            )
        )

    if input_dir.is_file():
        _inspect_file(input_dir, input_dir.name)
    else:
        for root, dirs, files in os.walk(input_dir, followlinks=False):
            dirs[:] = sorted(d for d in dirs if not (Path(root) / d).is_symlink())
            for name in sorted(files):
                fp = Path(root) / name
                rel_posix = fp.relative_to(input_dir).as_posix()
                _inspect_file(fp, rel_posix)

    grouped: dict[str, list[DiscoveredPdf]] = defaultdict(list)
    for item in discovered:
        grouped[item.sha256].append(item)

    groups: list[DedupGroup] = []
    for sha256, items in grouped.items():
        ordered = sorted(items, key=_canonical_sort_key)
        canonical = ordered[0]
        duplicates = sorted(ordered[1:], key=lambda x: x.rel_path)
        groups.append(
            DedupGroup(
                sha256=sha256,
                size_bytes=canonical.size_bytes,
                canonical=canonical,
                duplicates=duplicates,
            )
        )
    groups.sort(key=lambda g: (g.canonical.rel_path, g.sha256))

    return InventoryResult(
        input_dir=input_dir,
        total_entries_seen=total_scanned_files + symlinks_skipped,
        symlinks_skipped=symlinks_skipped,
        total_scanned_files=total_scanned_files,
        non_pdf_skipped=non_pdf_skipped,
        non_pdf_by_extension=dict(sorted(non_pdf_by_ext.items())),
        pdf_extension_count=pdf_extension_count,
        magic_header_non_pdf_ext_count=magic_header_non_pdf_ext_count,
        total_pdf_files=pdf_extension_count + magic_header_non_pdf_ext_count,
        groups=groups,
    )


def _run_pdfinfo(path: Path, timeout: float) -> tuple[dict[str, str], list[str]]:
    info: dict[str, str] = {}
    warnings: list[str] = []
    try:
        proc = subprocess.run(
            ["pdfinfo", str(path)],
            capture_output=True,
            text=True,
            errors="replace",
            timeout=timeout,
            check=False,
        )
        for line in proc.stdout.splitlines():
            if ":" in line:
                k, v = line.split(":", 1)
                info[k.strip()] = v.strip()
        if proc.stderr.strip():
            for line in proc.stderr.splitlines()[:5]:
                cleaned = line.strip()
                if cleaned and cleaned not in warnings:
                    warnings.append(f"pdfinfo: {cleaned[:160]}")
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError) as exc:
        warnings.append(f"pdfinfo_unavailable: {exc}")
    return info, warnings


def _run_pdftotext(path: Path, timeout: float) -> tuple[str | None, list[str]]:
    warnings: list[str] = []
    try:
        proc = subprocess.run(
            ["pdftotext", "-enc", "UTF-8", str(path), "-"],
            capture_output=True,
            timeout=timeout,
            check=False,
        )
        stderr_txt = proc.stderr.decode("utf-8", errors="replace").strip()
        if stderr_txt:
            for line in stderr_txt.splitlines()[:5]:
                cleaned = line.strip()
                if cleaned and cleaned not in warnings:
                    warnings.append(f"pdftotext: {cleaned[:160]}")
        if proc.returncode != 0:
            warnings.append(f"pdftotext_exit_{proc.returncode}")
            return None, warnings
        return proc.stdout.decode("utf-8", errors="replace"), warnings
    except subprocess.TimeoutExpired:
        warnings.append(f"pdftotext_timeout_{timeout}s")
        return None, warnings
    except (FileNotFoundError, OSError) as exc:
        warnings.append(f"pdftotext_error: {exc}")
        return None, warnings


_PYPDF_WORKER_CODE = """
import json
import sys

def _clean_surrogates(value: str) -> str:
    return value.encode("utf-8", errors="replace").decode("utf-8")

def _main() -> int:
    path = sys.argv[1]
    warnings = []
    meta = {}
    encrypted = False
    real_stdout = sys.stdout
    sys.stdout = sys.stderr
    try:
        from pypdf import PdfReader
        reader = PdfReader(path, strict=False)
        encrypted = bool(reader.is_encrypted)
        if encrypted:
            try:
                res = reader.decrypt("")
                if res == 0:
                    warnings.append("pypdf_encrypted_password_required")
                    real_stdout.write(json.dumps({
                        "text": None,
                        "pages": len(reader.pages),
                        "encrypted": True,
                        "meta": meta,
                        "warnings": warnings,
                    }, ensure_ascii=True))
                    return 0
            except Exception as exc:
                warnings.append(f"pypdf_decrypt_failed: {exc}")
                real_stdout.write(json.dumps({
                    "text": None,
                    "pages": 0,
                    "encrypted": True,
                    "meta": meta,
                    "warnings": warnings,
                }, ensure_ascii=True))
                return 0
        if reader.metadata:
            if getattr(reader.metadata, "title", None):
                meta["Title"] = _clean_surrogates(str(reader.metadata.title).strip())
            if getattr(reader.metadata, "author", None):
                meta["Author"] = _clean_surrogates(str(reader.metadata.author).strip())
        pages_text = [_clean_surrogates(page.extract_text() or "") for page in reader.pages]
        real_stdout.write(json.dumps({
            "text": "\\x0c".join(pages_text),
            "pages": len(reader.pages),
            "encrypted": encrypted,
            "meta": meta,
            "warnings": warnings,
        }, ensure_ascii=True))
        return 0
    except Exception as exc:
        warnings.append(f"pypdf_error: {exc}")
        real_stdout.write(json.dumps({
            "text": None,
            "pages": 0,
            "encrypted": encrypted,
            "meta": meta,
            "warnings": warnings,
        }, ensure_ascii=True))
        return 0

if __name__ == "__main__":
    raise SystemExit(_main())
"""


def _run_pypdf_fallback(path: Path, timeout: float = 30.0) -> tuple[str | None, int, bool, dict[str, str], list[str]]:
    warnings: list[str] = []
    try:
        proc = subprocess.run(
            [sys.executable, "-c", _PYPDF_WORKER_CODE, str(path)],
            capture_output=True,
            text=True,
            errors="replace",
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired:
        warnings.append(f"pypdf_timeout_{timeout}s")
        return None, 0, False, {}, warnings
    except (OSError, ValueError) as exc:
        warnings.append(f"pypdf_error: {exc}")
        return None, 0, False, {}, warnings

    if proc.returncode != 0:
        err_snip = (proc.stderr or "").strip().splitlines()[-1:] or []
        detail = f": {err_snip[0][:160]}" if err_snip else ""
        warnings.append(f"pypdf_exit_{proc.returncode}{detail}")
        return None, 0, False, {}, warnings

    try:
        payload = json.loads(proc.stdout)
    except Exception as exc:  # noqa: BLE001
        warnings.append(f"pypdf_invalid_output: {exc}")
        return None, 0, False, {}, warnings

    return (
        payload.get("text"),
        int(payload.get("pages") or 0),
        bool(payload.get("encrypted")),
        dict(payload.get("meta") or {}),
        list(payload.get("warnings") or []),
    )


def _compute_encoding_noise(raw_text: str) -> tuple[float, int]:
    if not raw_text:
        return 0.0, 0
    noisy = 0
    for ch in raw_text:
        if ch == "\ufffd":
            noisy += 1
        elif unicodedata.category(ch) == "Co":
            noisy += 1
        elif ord(ch) < 32 and ch not in ("\n", "\r", "\t", "\x0c"):
            noisy += 1
    type3_hits = len(TYPE3_LIGATURE_RE.findall(raw_text))
    return noisy / max(1, len(raw_text)), type3_hits


def _normalize_header_sig(line: str) -> str:
    stripped = line.strip()
    if not stripped or len(stripped) > 120:
        return ""
    sig = re.sub(r"\d+", "#", stripped)
    return re.sub(r"\s+", " ", sig).strip()


def normalize_pages(raw_text: str, expected_pages: int = 0) -> tuple[list[tuple[int, str]], float, list[str]]:
    noise_ratio, type3_hits = _compute_encoding_noise(raw_text)
    warnings: list[str] = []
    if noise_ratio > 0.005:
        warnings.append("encoding_noise")
    if type3_hits >= 5:
        warnings.append("type3_ligature_remap")

    raw_pages = raw_text.split("\x0c")
    if len(raw_pages) > 1 and not raw_pages[-1].strip() and (expected_pages <= 0 or len(raw_pages) > expected_pages):
        raw_pages = raw_pages[:-1]

    cleaned_pages_lines: list[list[str]] = []
    for page_raw in raw_pages:
        txt = page_raw.translate(LIGATURE_MAP)
        txt = txt.replace("\r\n", "\n").replace("\r", "\n")
        txt = CONTROL_CHARS_RE.sub("", txt)
        lines = [line.rstrip() for line in txt.split("\n")]
        cleaned_pages_lines.append(lines)

    num_pages = len(cleaned_pages_lines)
    if num_pages >= 3:
        top_sigs: Counter[str] = Counter()
        bot_sigs: Counter[str] = Counter()
        for lines in cleaned_pages_lines:
            non_empty = [ln for ln in lines if ln.strip()]
            if non_empty:
                top_sig = _normalize_header_sig(non_empty[0])
                bot_sig = _normalize_header_sig(non_empty[-1])
                if top_sig and not STANDALONE_PAGENUM_RE.match(non_empty[0]):
                    top_sigs[top_sig] += 1
                if bot_sig and not STANDALONE_PAGENUM_RE.match(non_empty[-1]):
                    bot_sigs[bot_sig] += 1
        threshold = max(3, math.ceil(num_pages * 0.4))
        repeated_tops = {sig for sig, cnt in top_sigs.items() if cnt >= threshold}
        repeated_bots = {sig for sig, cnt in bot_sigs.items() if cnt >= threshold}

        for idx, lines in enumerate(cleaned_pages_lines):
            # Strip top standalone page numbers and repeated running headers
            while lines and not lines[0].strip():
                lines.pop(0)
            while lines and (
                STANDALONE_PAGENUM_RE.match(lines[0])
                or _normalize_header_sig(lines[0]) in repeated_tops
            ):
                lines.pop(0)
                while lines and not lines[0].strip():
                    lines.pop(0)
            # Strip bottom standalone page numbers and repeated running footers
            while lines and not lines[-1].strip():
                lines.pop()
            while lines and (
                STANDALONE_PAGENUM_RE.match(lines[-1])
                or _normalize_header_sig(lines[-1]) in repeated_bots
            ):
                lines.pop()
                while lines and not lines[-1].strip():
                    lines.pop()
            cleaned_pages_lines[idx] = lines

    pages: list[tuple[int, str]] = []
    for page_num, lines in enumerate(cleaned_pages_lines, start=1):
        # Collapse runs of >2 blank lines
        collapsed: list[str] = []
        blank_run = 0
        for ln in lines:
            if not ln.strip():
                blank_run += 1
                if blank_run <= 1:
                    collapsed.append("")
            else:
                blank_run = 0
                collapsed.append(ln)
        pages.append((page_num, "\n".join(collapsed).strip()))
    return pages, noise_ratio, warnings


def _infer_title(path: Path, info: dict[str, str], pages: list[tuple[int, str]]) -> str:
    candidate = str(info.get("Title") or "").strip()
    generic_titles = {"untitled", "document", path.name.lower(), path.stem.lower()}
    if candidate and candidate.lower() not in generic_titles and not candidate.lower().startswith("microsoft word"):
        if len(candidate) >= 4:
            return re.sub(r"\s+", " ", candidate)[:240]
    if pages:
        first_page_lines = [ln.strip() for ln in pages[0][1].splitlines() if ln.strip()]
        title_lines: list[str] = []
        for ln in first_page_lines[:12]:
            if SECTION_HEADER_RE.match(ln) or ln.lower().startswith(("abstract", "keywords")):
                break
            if ARXIV_STAMP_LINE_RE.match(ln):
                continue
            if len(ln) < 4:
                continue
            title_lines.append(ln)
            if len(" ".join(title_lines)) >= 80 or len(title_lines) >= 2:
                break
        if title_lines:
            return re.sub(r"\s+", " ", " ".join(title_lines))[:240]
    return path.stem


def extract_pdf_group(
    group: DedupGroup,
    *,
    per_file_timeout: float,
    min_text_chars: int,
) -> ExtractionResult:
    path = group.canonical.path
    dup_paths = [d.path.as_posix() for d in group.duplicates]
    if group.canonical.read_error:
        return ExtractionResult(
            sha256=group.sha256,
            canonical_path=path,
            rel_path=group.canonical.rel_path,
            duplicate_paths=dup_paths,
            size_bytes=group.size_bytes,
            outcome="parse_error",
            reason=group.canonical.read_error,
            page_count=0,
            char_count=0,
            parser="none",
            warnings=[group.canonical.read_error],
            title=path.stem,
            author="",
            encrypted=False,
            encoding_noise_ratio=0.0,
            pages=[],
        )
    if group.size_bytes == 0:
        return ExtractionResult(
            sha256=group.sha256,
            canonical_path=path,
            rel_path=group.canonical.rel_path,
            duplicate_paths=dup_paths,
            size_bytes=0,
            outcome="empty_0_bytes",
            reason="0-byte file",
            page_count=0,
            char_count=0,
            parser="none",
            warnings=[],
            title=path.stem,
            author="",
            encrypted=False,
            encoding_noise_ratio=0.0,
            pages=[],
        )

    info, info_warnings = _run_pdfinfo(path, timeout=min(15.0, per_file_timeout))
    warnings = list(info_warnings)
    encrypted = str(info.get("Encrypted", "")).lower().startswith("yes")
    page_count = 0
    if info.get("Pages", "").isdigit():
        page_count = int(info["Pages"])

    raw_text, txt_warnings = _run_pdftotext(path, timeout=per_file_timeout)
    warnings.extend(w for w in txt_warnings if w not in warnings)
    parser = "pdftotext"

    if raw_text is None or (not raw_text.strip()):
        pypdf_text, pypdf_pages, pypdf_enc, pypdf_meta, pypdf_warnings = _run_pypdf_fallback(
            path, timeout=per_file_timeout
        )
        warnings.extend(w for w in pypdf_warnings if w not in warnings)
        encrypted = encrypted or pypdf_enc
        if page_count == 0 and pypdf_pages > 0:
            page_count = pypdf_pages
        for k, v in pypdf_meta.items():
            info.setdefault(k, v)
        if pypdf_text is not None and (raw_text is None or pypdf_text.strip()):
            raw_text = pypdf_text
            parser = "pypdf"
        elif raw_text is None and pypdf_text is None:
            if encrypted:
                return ExtractionResult(
                    sha256=group.sha256,
                    canonical_path=path,
                    rel_path=group.canonical.rel_path,
                    duplicate_paths=dup_paths,
                    size_bytes=group.size_bytes,
                    outcome="encrypted_no_text",
                    reason="encrypted PDF failed extraction",
                    page_count=page_count,
                    char_count=0,
                    parser="none",
                    warnings=warnings,
                    title=_infer_title(path, info, []),
                    author=info.get("Author", ""),
                    encrypted=True,
                    encoding_noise_ratio=0.0,
                    pages=[],
                )
            return ExtractionResult(
                sha256=group.sha256,
                canonical_path=path,
                rel_path=group.canonical.rel_path,
                duplicate_paths=dup_paths,
                size_bytes=group.size_bytes,
                outcome="parse_error",
                reason="; ".join(warnings[-2:]) or "both pdftotext and pypdf failed",
                page_count=page_count,
                char_count=0,
                parser="none",
                warnings=warnings,
                title=_infer_title(path, info, []),
                author=info.get("Author", ""),
                encrypted=encrypted,
                encoding_noise_ratio=0.0,
                pages=[],
            )

    assert raw_text is not None
    pages, noise_ratio, norm_warnings = normalize_pages(raw_text, expected_pages=page_count)
    warnings.extend(w for w in norm_warnings if w not in warnings)
    if page_count == 0:
        page_count = len(pages)
    char_count = sum(len(text.strip()) for _, text in pages)
    title = _infer_title(path, info, pages)
    author = str(info.get("Author") or "").strip()

    if char_count == 0:
        outcome = "encrypted_no_text" if encrypted else "scanned_no_text"
        reason = "encrypted PDF with zero extractable text" if encrypted else "zero extractable text (scanned/image PDF)"
    elif char_count < min_text_chars:
        outcome = "very_low_text_skipped"
        reason = f"extracted {char_count} chars < min_text_chars={min_text_chars}"
    elif (
        page_count >= 10
        and len(pages) >= 10
        and (sum(1 for _, t in pages[2:] if len(t.strip()) < 10) / max(1, len(pages) - 2)) >= 0.85
        and (char_count / max(1, page_count)) < 25.0
    ):
        outcome = "scanned_no_text"
        reason = "cover-only or sparse scanned PDF"
        if "cover_only_scanned_pdf" not in warnings:
            warnings.append("cover_only_scanned_pdf")
    else:
        outcome = "ingested"
        reason = "ok"

    return ExtractionResult(
        sha256=group.sha256,
        canonical_path=path,
        rel_path=group.canonical.rel_path,
        duplicate_paths=dup_paths,
        size_bytes=group.size_bytes,
        outcome=outcome,
        reason=reason,
        page_count=page_count,
        char_count=char_count,
        parser=parser,
        warnings=warnings,
        title=title,
        author=author,
        encrypted=encrypted,
        encoding_noise_ratio=noise_ratio,
        pages=pages,
    )


def _section_level(title: str) -> int:
    m = re.match(r"^(\d+(?:\.\d+)*)", title.strip())
    if not m:
        return 1
    return m.group(1).count(".") + 1


def _is_section_header(line: str) -> bool:
    s = line.strip()
    if not s or len(s) > 100:
        return False
    if THEOREM_HEADER_RE.match(s) or DEFINITION_HEADER_RE.match(s) or REMARK_HEADER_RE.match(s) or PROOF_HEADER_RE.match(s):
        return False
    if s.lower().startswith(("table ", "figure ", "fig. ")):
        return False
    if MATH_NOISE_IN_HEADING_RE.search(s):
        return False
    if not SECTION_HEADER_RE.match(s):
        return False
    words = s.split()
    if len(words) > 11:
        return False
    if s.endswith((".", ",", ";")) and len(words) > 4:
        return False
    return True


BIB_HEADING_CUTOFF_RE = re.compile(
    r"^(?:(?:\d+(?:\.\d+)*|[IVX]{1,5})\.?\s+)?(?:references|bibliography)"
    r"(?:\s+(?:and|&)\s+(?:notes|bibliography|further\s+reading))?\s*[:.]?\s*$",
    re.IGNORECASE,
)
TOC_HEADER_RE = re.compile(r"^(?:table\s+of\s+)?contents\s*[:.]?\s*$", re.IGNORECASE)
TOC_LINE_PAGENUM_RE = re.compile(r"(?:\.{2,}|\s{2,})\d{1,4}\s*$")
FIRST_BODY_SECTION_RE = re.compile(
    r"^(?:1|[I])\.?\s+(?:Introduction|Preliminaries|Background|Overview|Notation|Setup|Motivation)\b",
    re.IGNORECASE,
)


def _is_bib_section(title: str) -> bool:
    return bool(BIB_HEADING_CUTOFF_RE.match(title.strip()))


def _is_abstract_section(title: str) -> bool:
    return bool(re.match(r"^(?:\d+(?:\.\d+)*\.?\s+)?abstract\b", title.strip().lower()))


def _looks_like_toc_line(line: str) -> bool:
    s = line.strip()
    if not s:
        return False
    return bool(
        STANDALONE_PAGENUM_RE.match(s)
        or TOC_LINE_PAGENUM_RE.search(s)
        or _is_section_header(s)
        or BIB_HEADING_CUTOFF_RE.match(s)
        or _is_abstract_section(s)
        or re.match(r"^(?:\d+(?:\.\d+)*|[IVX]+)\.\s+", s)
    )


def _pre_bibliography_head_sample(all_lines: list[str], max_chars: int = 4000) -> str:
    in_toc = False
    cutoff = len(all_lines)
    for idx, raw_line in enumerate(all_lines):
        s = raw_line.strip()
        if not s:
            continue
        if TOC_HEADER_RE.match(s):
            in_toc = True
            continue

        upcoming = [ln.strip() for ln in all_lines[idx + 1 : idx + 15] if ln.strip()]
        next_line = upcoming[0] if upcoming else ""

        if in_toc:
            if BIB_HEADING_CUTOFF_RE.match(s):
                if (
                    next_line
                    and BIB_ENTRY_START_RE.match(next_line)
                    and not _is_section_header(next_line)
                    and not FIRST_BODY_SECTION_RE.match(next_line)
                ):
                    cutoff = idx
                    break
                continue

            if _is_abstract_section(s) or (
                (FIRST_BODY_SECTION_RE.match(s) or re.match(r"^(?:1|[I])\.?\s+[A-Z]", s))
                and not TOC_LINE_PAGENUM_RE.search(s)
            ):
                if next_line and _looks_like_toc_line(next_line):
                    continue
                in_toc = False
            elif (
                THEOREM_HEADER_RE.match(s)
                or DEFINITION_HEADER_RE.match(s)
                or PROOF_HEADER_RE.match(s)
                or (
                    not _looks_like_toc_line(s)
                    and (len(s) >= 40 or "doi:" in s.lower() or "arxiv:" in s.lower())
                )
            ):
                in_toc = False
            else:
                continue

        if BIB_HEADING_CUTOFF_RE.match(s):
            is_toc_like = False
            for nxt in upcoming[:10]:
                if BIB_ENTRY_START_RE.match(nxt):
                    break
                if (
                    STANDALONE_PAGENUM_RE.match(nxt)
                    or _is_abstract_section(nxt)
                    or _is_section_header(nxt)
                    or FIRST_BODY_SECTION_RE.match(nxt)
                ):
                    is_toc_like = True
                    break
            if is_toc_like:
                continue
            cutoff = idx
            break
    return "\n".join(all_lines[:cutoff])[:max_chars]


def _classify_archetype_line(line: str, section_title: str) -> str | None:
    s = line.strip()
    if not s:
        return None
    if _is_bib_section(section_title):
        return None
    if THEOREM_HEADER_RE.match(s):
        return "theorem"
    if DEFINITION_HEADER_RE.match(s):
        return "definition"
    if REMARK_HEADER_RE.match(s):
        return "remark"
    if PROOF_HEADER_RE.match(s):
        return "proof"
    if (
        len(s) <= 140
        and EQUATION_END_RE.search(s)
        and ("=" in s or any(sym in s for sym in ("⊗", "⊕", "∑", "∏", "∫", "↦", "⇒", "⇔", "≅", "≃")))
    ):
        return "equation"
    return None


def _split_oversized_text(
    lines: list[str],
    line_start_base: int,
    max_chars: int,
) -> list[tuple[int, int, str]]:
    text = "\n".join(lines).strip()
    if not text:
        return []
    if len(text) <= max_chars:
        return [(line_start_base, line_start_base + len(lines) - 1, text)]

    pieces: list[tuple[int, int, str]] = []
    cur_lines: list[str] = []
    cur_len = 0
    cur_start = line_start_base
    for offset, ln in enumerate(lines):
        add_len = len(ln) + (1 if cur_lines else 0)
        if cur_lines and cur_len + add_len > max_chars:
            chunk_txt = "\n".join(cur_lines).strip()
            if chunk_txt:
                pieces.append((cur_start, line_start_base + offset - 1, chunk_txt))
            cur_lines = [ln]
            cur_len = len(ln)
            cur_start = line_start_base + offset
        else:
            cur_lines.append(ln)
            cur_len += add_len
    if cur_lines:
        chunk_txt = "\n".join(cur_lines).strip()
        if chunk_txt:
            pieces.append((cur_start, line_start_base + len(lines) - 1, chunk_txt))
    return pieces


def _canonical_label(kind: str, num: str | None) -> str:
    k = kind.strip().rstrip(".").lower()
    if k in {"eq", "equation"}:
        k = "equation"
    n = (num or "").strip().strip("()")
    return f"{k} {n}".strip() if n else k


def _extract_labels(chunk_kind: str, text: str) -> list[str]:
    if chunk_kind == "bibliography":
        return []
    labels: list[str] = []
    seen: set[str] = set()
    first_line = text.splitlines()[0].strip() if text.splitlines() else ""
    for pat in (THEOREM_HEADER_RE, DEFINITION_HEADER_RE, REMARK_HEADER_RE):
        m = pat.match(first_line)
        if m:
            lbl = _canonical_label(m.group(1), m.group(2))
            if lbl not in seen:
                seen.add(lbl)
                labels.append(lbl)
    if chunk_kind == "equation":
        eq_m = EQUATION_END_RE.search(text.strip())
        if eq_m:
            lbl = _canonical_label("equation", eq_m.group(1))
            if lbl not in seen:
                seen.add(lbl)
                labels.append(lbl)
    if chunk_kind in {"equation", "theorem", "definition"}:
        for line in text.splitlines():
            stripped_line = line.strip()
            if _is_displayed_equation_block(stripped_line):
                eq_m = EQUATION_END_RE.search(stripped_line)
                if eq_m and len(stripped_line) < 160:
                    lbl = _canonical_label("equation", eq_m.group(1))
                    if lbl not in seen:
                        seen.add(lbl)
                        labels.append(lbl)
    return labels


def _extract_refs(text: str, own_labels: list[str]) -> list[str]:
    own = {lbl.lower() for lbl in own_labels}
    refs: list[str] = []
    seen: set[str] = set()
    for m in INTERNAL_REF_RE.finditer(text):
        lbl = _canonical_label(m.group(1), m.group(2))
        if lbl in own or lbl in seen:
            continue
        seen.add(lbl)
        refs.append(lbl)
    return refs


def _extract_citations(text: str) -> list[str]:
    cites: list[str] = []
    seen: set[str] = set()
    for m in BRACKET_CITE_RE.finditer(text):
        inner = m.group(1).strip()
        if re.fullmatch(r"[0-9,\s\-–]+", inner):
            for part in inner.split(","):
                part = part.strip()
                if not part:
                    continue
                range_m = re.fullmatch(r"(\d+)\s*[-–]\s*(\d+)", part)
                if range_m:
                    lo, hi = int(range_m.group(1)), int(range_m.group(2))
                    if 0 < hi - lo <= 20:
                        for n in range(lo, hi + 1):
                            key = str(n)
                            if key not in seen:
                                seen.add(key)
                                cites.append(key)
                    else:
                        for key in (str(lo), str(hi)):
                            if key not in seen:
                                seen.add(key)
                                cites.append(key)
                elif part.isdigit() and part not in seen:
                    seen.add(part)
                    cites.append(part)
        else:
            if inner not in seen:
                seen.add(inner)
                cites.append(inner)
    return cites


def _extract_symbolic_terms(text: str, limit: int = 24) -> list[str]:
    found: list[str] = []
    seen: set[str] = set()
    for pattern in (SYMBOLIC_EXPR_RE, DOMAIN_TERMS_RE, UNICODE_MATH_RE):
        for m in pattern.finditer(text):
            val = re.sub(r"\s+", " ", m.group(0)).strip()
            if not val:
                continue
            key = val.lower()
            if key not in seen:
                seen.add(key)
                found.append(val)
                if len(found) >= limit:
                    return found
    return found


def _extract_defined_terms(text: str) -> list[str]:
    terms: list[str] = []
    seen: set[str] = set()
    first_line = text.splitlines()[0].strip() if text.splitlines() else ""
    paren_m = re.match(r"^(?:Definition|Notation)\s*(?:\d+(?:\.\d+)*)?\s*\(([^)]{3,60})\)", first_line, re.IGNORECASE)
    if paren_m:
        t = re.sub(r"\s+", " ", paren_m.group(1)).strip()
        if t.lower() not in seen:
            seen.add(t.lower())
            terms.append(t)
    for m in re.finditer(r"\b(?:called|termed|denoted by|defined as)\s+(?:a|an|the)?\s*([A-Za-z][A-Za-z0-9\-\s]{2,40}?)(?:[.,;:\)]|\s+(?:if|when|where|which|that)\b)", text, re.IGNORECASE):
        t = re.sub(r"\s+", " ", m.group(1)).strip()
        if 3 <= len(t) <= 45 and t.lower() not in seen:
            seen.add(t.lower())
            terms.append(t)
    return terms


def _normalize_title_for_match(title: str) -> str:
    cleaned = re.sub(r"[^a-z0-9]+", " ", title.lower()).strip()
    return re.sub(r"\s+", " ", cleaned)


def _clean_doi(raw: str) -> str:
    doi = raw.strip().rstrip(".,;:")
    while doi.endswith(")") and doi.count(")") > doi.count("("):
        doi = doi[:-1].rstrip(".,;:")
    return doi.lower()


def _parse_bibliography_entries(text: str) -> list[dict[str, str]]:
    entries: list[dict[str, str]] = []
    cur_key = ""
    cur_lines: list[str] = []

    def _flush() -> None:
        if not cur_key or not cur_lines:
            return
        raw = re.sub(r"\s+", " ", " ".join(cur_lines)).strip()
        arxiv_m = ARXIV_ID_RE.search(raw)
        doi_m = DOI_RE.search(raw)
        entries.append(
            {
                "cite_key": cur_key,
                "raw_entry": raw[:600],
                "arxiv_id": re.sub(r"v\d+$", "", arxiv_m.group(1).lower()) if arxiv_m else "",
                "doi": _clean_doi(doi_m.group(1)) if doi_m else "",
            }
        )

    for line in text.splitlines():
        m = BIB_ENTRY_START_RE.match(line)
        if m:
            _flush()
            cur_key = (m.group(1) or m.group(2) or "").strip()
            rest = (m.group(3) or "").strip()
            cur_lines = [rest] if rest else []
        elif cur_key and line.strip():
            cur_lines.append(line.strip())
        elif cur_key and not line.strip() and cur_lines:
            _flush()
            cur_key = ""
            cur_lines = []
    _flush()
    return entries


def _chunk_summary(text: str, max_len: int = 260) -> str:
    compact = re.sub(r"\s+", " ", text).strip()
    if len(compact) <= max_len:
        return compact
    cut = compact[:max_len].rsplit(" ", 1)[0]
    return (cut or compact[:max_len]) + "..."


def _proof_target_label(text: str) -> str | None:
    first_line = text.splitlines()[0].strip() if text.splitlines() else ""
    m = re.match(
        r"^Proof\s+of\s+(Theorem|Lemma|Proposition|Corollary|Conjecture|Claim)\s+(\d+(?:\.\d+)*|[A-Z](?:\.\d+)*)",
        first_line,
        re.IGNORECASE,
    )
    if m:
        return _canonical_label(m.group(1), m.group(2))
    return None


def _canonical_entity_key(entity_type: str, normalized: str) -> str:
    if entity_type in NON_CROSS_DOC_ENTITY_TYPES:
        return ""
    norm = normalized.strip().lower()
    if not norm:
        return ""
    return stable_key("concept", entity_type, norm)


def _entity_row(
    *,
    document_key: str,
    chunk_key: str,
    entity_type: str,
    surface: str,
    normalized: str,
    confidence: float,
    metadata: dict[str, Any] | None = None,
) -> dict[str, Any]:
    key = stable_key("ent", document_key, chunk_key, entity_type, normalized.lower())
    canonical_key = _canonical_entity_key(entity_type, normalized)
    return {
        "_key": key,
        "canonicalKey": canonical_key,
        "documentKey": document_key,
        "chunkKey": chunk_key,
        "entityType": entity_type,
        "surface": surface,
        "normalized": normalized,
        "confidence": confidence,
        "sourceAuthority": SOURCE_AUTHORITY,
        "metadata": {
            "documentKey": document_key,
            "chunkKey": chunk_key,
            "canonicalKey": canonical_key,
            **(metadata or {}),
        },
    }


def _dag_edge(
    *,
    document_key: str,
    from_id: str,
    to_id: str,
    edge_type: str,
    evidence: str,
    confidence: float,
) -> dict[str, Any]:
    return {
        "_key": stable_key("dag", document_key, edge_type, from_id, to_id),
        "_from": from_id,
        "_to": to_id,
        "documentKey": document_key,
        "edgeType": edge_type,
        "evidence": evidence[:240],
        "confidence": round(confidence, 3),
        "sourceAuthority": SOURCE_AUTHORITY,
    }


def verify_and_prune_dag(edges: list[dict[str, Any]]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Ensure ``alexandria_dag_edges`` is strictly acyclic by pruning cycle-closing edges."""
    ordered = sorted(
        edges,
        key=lambda e: (
            DAG_EDGE_PRIORITY.get(str(e.get("edgeType") or ""), 99),
            str(e.get("_from") or ""),
            str(e.get("_to") or ""),
            str(e.get("edgeType") or ""),
            str(e.get("_key") or ""),
        ),
    )
    adj: dict[str, set[str]] = defaultdict(set)
    kept: list[dict[str, Any]] = []
    pruned: list[dict[str, Any]] = []
    seen_pairs: set[tuple[str, str, str]] = set()

    def _can_reach(src: str, target: str) -> bool:
        if src == target:
            return True
        visited: set[str] = {src}
        queue: deque[str] = deque([src])
        while queue:
            cur = queue.popleft()
            for nxt in adj.get(cur, ()):
                if nxt == target:
                    return True
                if nxt not in visited:
                    visited.add(nxt)
                    queue.append(nxt)
        return False

    for edge in ordered:
        src = str(edge.get("_from") or "")
        dst = str(edge.get("_to") or "")
        etype = str(edge.get("edgeType") or "")
        if not src or not dst or src == dst:
            pruned.append(edge)
            continue
        pair_key = (src, dst, etype)
        if pair_key in seen_pairs:
            continue
        if _can_reach(dst, src):
            pruned.append(edge)
            continue
        seen_pairs.add(pair_key)
        adj[src].add(dst)
        kept.append(edge)

    # Independent Kahn topological verification over unique (u, v) pairs in adj
    nodes: set[str] = set()
    indeg: Counter[str] = Counter()
    for u, targets in adj.items():
        nodes.add(u)
        indeg.setdefault(u, 0)
        for v in targets:
            nodes.add(v)
            indeg[v] += 1
    q: deque[str] = deque(sorted(n for n in nodes if indeg[n] == 0))
    visited_count = 0
    while q:
        u = q.popleft()
        visited_count += 1
        for v in sorted(adj.get(u, ())):
            indeg[v] -= 1
            if indeg[v] == 0:
                q.append(v)
    if visited_count != len(nodes):
        raise RuntimeError("verify_and_prune_dag failed acyclic invariant check")
    return kept, pruned


def build_document_artifacts(
    ext: ExtractionResult,
    *,
    max_chunk_chars: int = 3200,
) -> dict[str, Any]:
    doc_key = f"doc_{ext.sha256[:20]}"
    doc_row = {
        "_key": doc_key,
        "path": ext.canonical_path.as_posix(),
        "relativePath": ext.rel_path,
        "title": ext.title,
        "author": ext.author,
        "sourceType": "pdf",
        "sourceFormat": "pdf",
        "sourceUri": source_uri(ext.canonical_path),
        "contentHash": ext.sha256,
        "domain": "math_paper",
        "parser": f"pdf_corpus_ingest.{ext.parser}_v1",
        "sourceAuthority": SOURCE_AUTHORITY,
        "duplicatePaths": ext.duplicate_paths,
        "pageCount": ext.page_count,
        "warnings": ext.warnings,
        "encodingNoiseRatio": round(ext.encoding_noise_ratio, 6),
    }

    # Build global line list with exact 1-based page mapping
    all_lines: list[str] = []
    line_pages: list[int] = []
    for page_num, page_text in ext.pages:
        lines = page_text.splitlines()
        if not lines:
            continue
        all_lines.extend(lines)
        line_pages.extend([page_num] * len(lines))
        all_lines.append("")
        line_pages.append(page_num)

    if not all_lines:
        all_lines = [""]
        line_pages = [1]

    # Segment into sections (also merging split two-line numbered headings like "1\nIntroduction")
    raw_sections: list[tuple[str, int, int, list[str]]] = []
    cur_sec_title = "Preamble"
    cur_sec_start = 1
    cur_sec_lines: list[str] = []
    found_explicit_section = False

    idx_zero = 0
    while idx_zero < len(all_lines):
        idx = idx_zero + 1
        line = all_lines[idx_zero]
        stripped = line.strip()
        merged_heading = None
        if SECTION_NUM_ONLY_RE.match(stripped) and idx_zero + 1 < len(all_lines):
            nxt = all_lines[idx_zero + 1].strip()
            nxt_words = nxt.split()
            if (
                SECTION_TITLE_NEXT_RE.match(nxt)
                and 1 <= len(nxt_words) <= 9
                and not MATH_NOISE_IN_HEADING_RE.search(nxt)
                and not (nxt.endswith(".") and len(nxt_words) > 4)
            ):
                cand = f"{stripped} {nxt}"
                if _is_section_header(cand):
                    merged_heading = cand

        if merged_heading is not None:
            if cur_sec_lines and any(ln.strip() for ln in cur_sec_lines):
                raw_sections.append((cur_sec_title, cur_sec_start, idx - 1, cur_sec_lines))
            cur_sec_title = merged_heading
            cur_sec_start = idx
            cur_sec_lines = []
            found_explicit_section = True
            idx_zero += 2
            continue

        if _is_section_header(line):
            if cur_sec_lines and any(ln.strip() for ln in cur_sec_lines):
                raw_sections.append((cur_sec_title, cur_sec_start, idx - 1, cur_sec_lines))
            cur_sec_title = stripped
            cur_sec_start = idx
            cur_sec_lines = []
            found_explicit_section = True
        else:
            cur_sec_lines.append(line)
        idx_zero += 1

    if cur_sec_lines and any(ln.strip() for ln in cur_sec_lines):
        raw_sections.append((cur_sec_title if found_explicit_section else "Document", cur_sec_start, len(all_lines), cur_sec_lines))

    if not raw_sections:
        raw_sections = [("Document", 1, len(all_lines), all_lines)]

    sections_rows: list[dict[str, Any]] = []
    chunks_rows: list[dict[str, Any]] = []
    entities_by_key: dict[str, dict[str, Any]] = {}
    doc_sec_edges: list[dict[str, Any]] = []
    sec_chunk_edges: list[dict[str, Any]] = []
    chunk_adj_edges: list[dict[str, Any]] = []
    chunk_ent_edges_by_key: dict[str, dict[str, Any]] = {}
    ent_rel_edges_by_key: dict[str, dict[str, Any]] = {}
    dag_edges_by_key: dict[str, dict[str, Any]] = {}
    bib_entries_parsed: list[dict[str, Any]] = []

    prev_sec_key: str | None = None
    prev_chunk_key: str | None = None
    chunk_ordinal = 0

    for sec_ordinal, (sec_title, sec_lstart, sec_lend, sec_lines) in enumerate(raw_sections, start=1):
        sec_key = stable_key("sec", doc_key, sec_ordinal, sec_title)
        sec_pstart = line_pages[min(max(0, sec_lstart - 1), len(line_pages) - 1)]
        sec_pend = line_pages[min(max(0, sec_lend - 1), len(line_pages) - 1)]
        sections_rows.append(
            {
                "_key": sec_key,
                "documentKey": doc_key,
                "title": sec_title,
                "level": _section_level(sec_title),
                "ordinal": sec_ordinal,
                "lineStart": sec_lstart,
                "lineEnd": sec_lend,
                "pageStart": sec_pstart,
                "pageEnd": sec_pend,
                "sourceAuthority": SOURCE_AUTHORITY,
            }
        )
        doc_sec_edges.append(
            {
                "_key": stable_key("docsec", doc_key, sec_key),
                "_from": f"alexandria_documents/{doc_key}",
                "_to": f"alexandria_sections/{sec_key}",
                "documentKey": doc_key,
                "ordinal": sec_ordinal,
                "sourceAuthority": SOURCE_AUTHORITY,
            }
        )
        if prev_sec_key is not None:
            sec_edge = _dag_edge(
                document_key=doc_key,
                from_id=f"alexandria_sections/{prev_sec_key}",
                to_id=f"alexandria_sections/{sec_key}",
                edge_type="section_precedes_section",
                evidence=f"section {sec_ordinal - 1} -> {sec_ordinal}",
                confidence=1.0,
            )
            dag_edges_by_key.setdefault(sec_edge["_key"], sec_edge)
        prev_sec_key = sec_key

        # Split section into archetype blocks
        blocks: list[tuple[str, int, list[str]]] = []
        if _is_bib_section(sec_title):
            # Group lines into entry paragraphs
            cur_b_lines: list[str] = []
            cur_b_start = sec_lstart
            for off, ln in enumerate(sec_lines):
                abs_line = sec_lstart + off
                if BIB_ENTRY_START_RE.match(ln) and cur_b_lines:
                    blocks.append(("bibliography", cur_b_start, cur_b_lines))
                    cur_b_lines = [ln]
                    cur_b_start = abs_line
                else:
                    if not cur_b_lines:
                        cur_b_start = abs_line
                    cur_b_lines.append(ln)
            if cur_b_lines and any(item.strip() for item in cur_b_lines):
                blocks.append(("bibliography", cur_b_start, cur_b_lines))
        else:
            default_kind = "abstract" if _is_abstract_section(sec_title) else "prose"
            cur_kind = default_kind
            cur_b_lines = []
            cur_b_start = sec_lstart
            blank_continuations = 0
            for off, ln in enumerate(sec_lines):
                abs_line = sec_lstart + off
                detected = _classify_archetype_line(ln, sec_title)
                if detected is not None:
                    if cur_b_lines and any(item.strip() for item in cur_b_lines):
                        blocks.append((cur_kind, cur_b_start, cur_b_lines))
                    cur_kind = detected
                    cur_b_lines = [ln]
                    cur_b_start = abs_line
                    blank_continuations = 0
                elif not ln.strip():
                    should_continue = False
                    if (
                        cur_kind in {"theorem", "definition", "remark", "proof"}
                        and cur_b_lines
                        and any(item.strip() for item in cur_b_lines)
                        and (cur_kind == "proof" or blank_continuations < 2)
                        and sum(len(x) + 1 for x in cur_b_lines) < 1200
                        and not re.search(r"(?:□|■|∎|Q\.E\.D\.?|QED)\s*$", "\n".join(cur_b_lines).strip())
                    ):
                        next_para: list[str] = []
                        started_para = False
                        for look_ln in sec_lines[off + 1 :]:
                            if not look_ln.strip():
                                if started_para:
                                    break
                                continue
                            started_para = True
                            next_para.append(look_ln)
                            if len(next_para) >= 12:
                                break
                        next_first = next_para[0] if next_para else ""
                        if (
                            next_first
                            and _classify_archetype_line(next_first, sec_title) is None
                            and not _is_displayed_equation_block("\n".join(next_para))
                            and not BIB_HEADING_CUTOFF_RE.match(next_first.strip())
                        ):
                            should_continue = True
                    if should_continue:
                        cur_b_lines.append(ln)
                        blank_continuations += 1
                        continue
                    if cur_b_lines and any(item.strip() for item in cur_b_lines):
                        # Keep equation blocks isolated on blank lines
                        joined = "\n".join(cur_b_lines).strip()
                        if cur_kind == "prose" and _is_displayed_equation_block(joined):
                            blocks.append(("equation", cur_b_start, cur_b_lines))
                        else:
                            blocks.append((cur_kind, cur_b_start, cur_b_lines))
                        cur_b_lines = []
                    cur_kind = default_kind
                    cur_b_start = abs_line + 1
                    blank_continuations = 0
                else:
                    if not cur_b_lines:
                        cur_b_start = abs_line
                    cur_b_lines.append(ln)
            if cur_b_lines and any(item.strip() for item in cur_b_lines):
                joined = "\n".join(cur_b_lines).strip()
                if cur_kind == "prose" and _is_displayed_equation_block(joined):
                    blocks.append(("equation", cur_b_start, cur_b_lines))
                else:
                    blocks.append((cur_kind, cur_b_start, cur_b_lines))

        # Coalesce consecutive short prose/abstract/bibliography blocks up to max_chunk_chars
        coalesced_blocks: list[tuple[str, int, list[str]]] = []
        abstract_chars_seen = 0
        for b_kind, b_start, b_lines in blocks:
            b_text = "\n".join(b_lines).strip()
            if not b_text:
                continue
            if b_kind == "abstract":
                if abstract_chars_seen >= 2500:
                    b_kind = "prose"
                else:
                    abstract_chars_seen += len(b_text)
            if b_kind in {"prose", "abstract", "bibliography"} and coalesced_blocks and coalesced_blocks[-1][0] == b_kind:
                prev_text_len = sum(len(x) + 1 for x in coalesced_blocks[-1][2])
                if prev_text_len + len(b_text) + 2 <= max_chunk_chars:
                    coalesced_blocks[-1][2].append("")
                    coalesced_blocks[-1][2].extend(b_lines)
                    continue
            coalesced_blocks.append((b_kind, b_start, b_lines))

        for b_kind, b_start, b_lines in coalesced_blocks:
            for lstart, lend, chunk_text in _split_oversized_text(b_lines, b_start, max_chunk_chars):
                chunk_ordinal += 1
                pstart = line_pages[min(max(0, lstart - 1), len(line_pages) - 1)]
                pend = line_pages[min(max(0, lend - 1), len(line_pages) - 1)]
                chunk_key = stable_key("chunk", doc_key, chunk_ordinal, b_kind, content_hash(chunk_text)[:16])

                labels = _extract_labels(b_kind, chunk_text)
                refs = _extract_refs(chunk_text, labels)
                citations = _extract_citations(chunk_text) if b_kind != "bibliography" else []
                symbolic_terms = _extract_symbolic_terms(chunk_text)
                defined_terms = _extract_defined_terms(chunk_text) if b_kind == "definition" else []
                archetypes = _extract_math_archetypes(chunk_text)

                if labels:
                    chunk_title = f"{sec_title}: {labels[0].title()}"
                else:
                    chunk_title = f"{sec_title} ({b_kind} {chunk_ordinal})"

                summary = _chunk_summary(chunk_text)
                math_entities = list(
                    dict.fromkeys([*labels, *refs, *[f"cite:{c}" for c in citations], *symbolic_terms, *archetypes])
                )[:24]
                triplets: list[list[str]] = []
                subj = labels[0] if labels else chunk_title
                for r in refs[:6]:
                    triplets.append([subj, "references", r])
                for c in citations[:6]:
                    triplets.append([subj, "cites", f"[{c}]"])
                for s in symbolic_terms[:6]:
                    triplets.append([subj, "mentions", s])
                for arch in archetypes[:6]:
                    triplets.append([subj, "exhibits_archetype", arch])

                semantic = {
                    "summary": summary,
                    "assumed_definitions": [r for r in refs if r.startswith("definition ")] + defined_terms,
                    "mathematical_entities": math_entities,
                    "mathematical_archetypes": archetypes,
                    "graph_triplets": triplets,
                    "symbolic_terms": symbolic_terms,
                    "semantic_mode": SEMANTIC_MODE_DETERMINISTIC,
                }
                search_terms = ident_terms(
                    "\n".join(
                        [
                            chunk_title,
                            ext.title,
                            " ".join(labels),
                            " ".join(refs),
                            " ".join(symbolic_terms),
                            " ".join(defined_terms),
                            " ".join(archetypes),
                            summary,
                        ]
                    )
                )
                provenance = {
                    "path": ext.canonical_path.as_posix(),
                    "sourceUri": doc_row["sourceUri"],
                    "contentHash": ext.sha256,
                    "sourceKind": "paper",
                    "sourceFormat": "pdf",
                    "schema": SCHEMA_VERSION,
                    "pageStart": pstart,
                    "pageEnd": pend,
                    "lineStart": lstart,
                    "lineEnd": lend,
                    "section": sec_title,
                    "labels": labels,
                    "refs": refs,
                    "citations": citations,
                    "definedTerms": defined_terms,
                    "archetypes": archetypes,
                    "encodingNoiseRatio": round(ext.encoding_noise_ratio, 6),
                    "corpusTags": ["pdf_corpus", b_kind],
                }
                chunk_row = {
                    "_key": chunk_key,
                    "documentKey": doc_key,
                    "sectionKey": sec_key,
                    "ordinal": chunk_ordinal,
                    "chunkKind": b_kind,
                    "title": chunk_title,
                    "text": chunk_text,
                    "rawContent": chunk_text,
                    "tokens": tokenize(chunk_title + "\n" + chunk_text),
                    "searchTerms": search_terms,
                    "sourceAuthority": SOURCE_AUTHORITY,
                    "provenance": provenance,
                    "semantic": semantic,
                }
                chunks_rows.append(chunk_row)
                sec_chunk_edges.append(
                    {
                        "_key": stable_key("secchunk", sec_key, chunk_key),
                        "_from": f"alexandria_sections/{sec_key}",
                        "_to": f"alexandria_chunks/{chunk_key}",
                        "documentKey": doc_key,
                        "ordinal": chunk_ordinal,
                        "chunkKind": b_kind,
                        "sourceAuthority": SOURCE_AUTHORITY,
                    }
                )
                if prev_chunk_key is not None:
                    chunk_adj_edges.append(
                        {
                            "_key": stable_key("adj", prev_chunk_key, chunk_key),
                            "_from": f"alexandria_chunks/{prev_chunk_key}",
                            "_to": f"alexandria_chunks/{chunk_key}",
                            "documentKey": doc_key,
                            "kind": "adjacent",
                            "weight": 1.0,
                            "sourceAuthority": SOURCE_AUTHORITY,
                        }
                    )
                prev_chunk_key = chunk_key

                # Emit entities with chunkKey and documentKey (arango_ingest.py compatibility)
                chunk_entities: list[dict[str, Any]] = []
                for lbl in labels:
                    chunk_entities.append(
                        _entity_row(
                            document_key=doc_key,
                            chunk_key=chunk_key,
                            entity_type="math_label",
                            surface=lbl,
                            normalized=lbl,
                            confidence=1.0,
                        )
                    )
                for r in refs:
                    chunk_entities.append(
                        _entity_row(
                            document_key=doc_key,
                            chunk_key=chunk_key,
                            entity_type="math_reference",
                            surface=r,
                            normalized=r,
                            confidence=0.92,
                        )
                    )
                for sym in symbolic_terms:
                    chunk_entities.append(
                        _entity_row(
                            document_key=doc_key,
                            chunk_key=chunk_key,
                            entity_type="math_symbol",
                            surface=sym,
                            normalized=sym.lower(),
                            confidence=0.75,
                        )
                    )
                for dterm in defined_terms:
                    chunk_entities.append(
                        _entity_row(
                            document_key=doc_key,
                            chunk_key=chunk_key,
                            entity_type="defined_term",
                            surface=dterm,
                            normalized=dterm.lower(),
                            confidence=0.9,
                        )
                    )
                for arch in archetypes:
                    chunk_entities.append(
                        _entity_row(
                            document_key=doc_key,
                            chunk_key=chunk_key,
                            entity_type="math_archetype",
                            surface=arch,
                            normalized=f"archetype:{arch}",
                            confidence=0.93,
                        )
                    )

                if b_kind == "bibliography":
                    parsed_bib = _parse_bibliography_entries(chunk_text)
                    for entry in parsed_bib:
                        ent = _entity_row(
                            document_key=doc_key,
                            chunk_key=chunk_key,
                            entity_type="bib_entry",
                            surface=f"[{entry['cite_key']}]",
                            normalized=f"bib:{entry['cite_key']}",
                            confidence=0.95,
                            metadata={
                                "citeKey": entry["cite_key"],
                                "rawEntry": entry["raw_entry"],
                                "arxivId": entry["arxiv_id"],
                                "doi": entry["doi"],
                            },
                        )
                        chunk_entities.append(ent)
                        bib_entries_parsed.append(
                            {
                                "cite_key": entry["cite_key"],
                                "entity_key": ent["_key"],
                                "raw_entry": entry["raw_entry"],
                                "arxiv_id": entry["arxiv_id"],
                                "doi": entry["doi"],
                            }
                        )

                ent_by_key_in_chunk: dict[str, dict[str, Any]] = {}
                ent_by_norm: dict[str, dict[str, Any]] = {}
                for ent in chunk_entities:
                    ent_by_key_in_chunk.setdefault(ent["_key"], ent)
                    entities_by_key.setdefault(ent["_key"], ent)
                    ent_by_norm.setdefault(ent["normalized"], ent)
                    chunk_ent_edge = {
                        "_key": stable_key("chunkent", chunk_key, ent["_key"]),
                        "_from": f"alexandria_chunks/{chunk_key}",
                        "_to": f"alexandria_entities/{ent['_key']}",
                        "documentKey": doc_key,
                        "chunkKey": chunk_key,
                        "entityType": ent["entityType"],
                        "confidence": ent["confidence"],
                        "sourceAuthority": SOURCE_AUTHORITY,
                    }
                    chunk_ent_edges_by_key.setdefault(chunk_ent_edge["_key"], chunk_ent_edge)

                # Emit entity relation edges if >=2 entities exist in chunk
                if labels and ent_by_key_in_chunk:
                    head_ent = ent_by_norm.get(labels[0].lower())
                    if head_ent is not None:
                        for target_ent in ent_by_key_in_chunk.values():
                            if target_ent["_key"] == head_ent["_key"]:
                                continue
                            rel_type = {
                                "math_reference": "references",
                                "math_symbol": "uses_symbol",
                                "defined_term": "defines",
                            }.get(target_ent["entityType"], "related_to")
                            rel_edge = {
                                "_key": stable_key("rel", head_ent["_key"], rel_type, target_ent["_key"], chunk_key),
                                "_from": f"alexandria_entities/{head_ent['_key']}",
                                "_to": f"alexandria_entities/{target_ent['_key']}",
                                "documentKey": doc_key,
                                "chunkKey": chunk_key,
                                "relationType": rel_type,
                                "evidence": chunk_title,
                                "weight": 0.8,
                                "sourceAuthority": SOURCE_AUTHORITY,
                            }
                            ent_rel_edges_by_key.setdefault(rel_edge["_key"], rel_edge)

    # Second pass over chunks of this document to build intra-document DAG edges
    label_to_chunk: dict[str, dict[str, Any]] = {}
    def_term_to_chunk: dict[str, dict[str, Any]] = {}
    bib_by_cite_key: dict[str, str] = {b["cite_key"]: b["entity_key"] for b in bib_entries_parsed}

    for ch in chunks_rows:
        prov = ch["provenance"]
        for lbl in prov.get("labels", []):
            label_to_chunk.setdefault(lbl.lower(), ch)
        for dterm in prov.get("definedTerms", []):
            def_term_to_chunk.setdefault(dterm.lower(), ch)

    last_theorem_in_sec: dict[str, dict[str, Any]] = {}
    last_theorem_in_doc: dict[str, Any] | None = None

    for ch in chunks_rows:
        ckey = ch["_key"]
        kind = ch["chunkKind"]
        skey = ch["sectionKey"]
        prov = ch["provenance"]

        if kind == "theorem":
            last_theorem_in_sec[skey] = ch
            last_theorem_in_doc = ch

        if kind == "proof":
            target_lbl = _proof_target_label(ch["text"])
            target_chunk = label_to_chunk.get(target_lbl) if target_lbl else None
            if target_chunk is None:
                target_chunk = last_theorem_in_sec.get(skey) or last_theorem_in_doc
            if target_chunk is not None and target_chunk["_key"] != ckey:
                edge = _dag_edge(
                    document_key=doc_key,
                    from_id=f"alexandria_chunks/{ckey}",
                    to_id=f"alexandria_chunks/{target_chunk['_key']}",
                    edge_type="proof_proves_theorem",
                    evidence=target_lbl or target_chunk["title"],
                    confidence=0.95 if target_lbl else 0.8,
                )
                dag_edges_by_key.setdefault(edge["_key"], edge)

        # chunk_uses_definition & chunk_references_result
        used_def_chunks: set[str] = set()
        for ref in prov.get("refs", []):
            target_chunk = label_to_chunk.get(ref.lower())
            if target_chunk is None or target_chunk["_key"] == ckey:
                continue
            if ref.lower().startswith(("definition ", "notation ")) or target_chunk["chunkKind"] == "definition":
                if target_chunk["_key"] not in used_def_chunks:
                    used_def_chunks.add(target_chunk["_key"])
                    edge = _dag_edge(
                        document_key=doc_key,
                        from_id=f"alexandria_chunks/{ckey}",
                        to_id=f"alexandria_chunks/{target_chunk['_key']}",
                        edge_type="chunk_uses_definition",
                        evidence=ref,
                        confidence=0.92,
                    )
                    dag_edges_by_key.setdefault(edge["_key"], edge)
            else:
                edge = _dag_edge(
                    document_key=doc_key,
                    from_id=f"alexandria_chunks/{ckey}",
                    to_id=f"alexandria_chunks/{target_chunk['_key']}",
                    edge_type="chunk_references_result",
                    evidence=ref,
                    confidence=0.9,
                )
                dag_edges_by_key.setdefault(edge["_key"], edge)

        text_low = ch["text"].lower()
        for dterm, def_chunk in def_term_to_chunk.items():
            if def_chunk["_key"] == ckey or def_chunk["_key"] in used_def_chunks:
                continue
            if def_chunk["ordinal"] < ch["ordinal"] and re.search(rf"\b{re.escape(dterm)}\b", text_low):
                used_def_chunks.add(def_chunk["_key"])
                edge = _dag_edge(
                    document_key=doc_key,
                    from_id=f"alexandria_chunks/{ckey}",
                    to_id=f"alexandria_chunks/{def_chunk['_key']}",
                    edge_type="chunk_uses_definition",
                    evidence=f"term:{dterm}",
                    confidence=0.78,
                )
                dag_edges_by_key.setdefault(edge["_key"], edge)

        # chunk_cites_entry
        for cite_key in prov.get("citations", []):
            bib_ent_key = bib_by_cite_key.get(cite_key)
            if bib_ent_key:
                edge = _dag_edge(
                    document_key=doc_key,
                    from_id=f"alexandria_chunks/{ckey}",
                    to_id=f"alexandria_entities/{bib_ent_key}",
                    edge_type="chunk_cites_entry",
                    evidence=f"[{cite_key}]",
                    confidence=0.95,
                )
                dag_edges_by_key.setdefault(edge["_key"], edge)

    # Extract identifiers for cross-document citation matching
    head_sample = _pre_bibliography_head_sample(all_lines, max_chars=4000)
    doc_arxiv_versions: dict[str, int] = {}
    for m in ARXIV_ID_RE.finditer(ext.canonical_path.name + "\n" + head_sample):
        raw_id = m.group(1).lower()
        ver_m = re.search(r"v(\d+)$", raw_id)
        ver_num = int(ver_m.group(1)) if ver_m else 0
        base_id = re.sub(r"v\d+$", "", raw_id)
        if base_id not in doc_arxiv_versions or ver_num > doc_arxiv_versions[base_id]:
            doc_arxiv_versions[base_id] = ver_num
    doc_arxiv_ids = set(doc_arxiv_versions.keys())
    doc_dois = {d for d in (_clean_doi(m.group(1)) for m in DOI_RE.finditer(head_sample)) if d}
    doc_norm_title = _normalize_title_for_match(ext.title)

    return {
        "document": doc_row,
        "sections": sections_rows,
        "chunks": chunks_rows,
        "entities": list(entities_by_key.values()),
        "document_section_edges": doc_sec_edges,
        "section_chunk_edges": sec_chunk_edges,
        "chunk_adjacent_edges": chunk_adj_edges,
        "chunk_entity_edges": list(chunk_ent_edges_by_key.values()),
        "entity_relation_edges": list(ent_rel_edges_by_key.values()),
        "dag_edges": list(dag_edges_by_key.values()),
        "bib_entries": bib_entries_parsed,
        "doc_arxiv_ids": sorted(doc_arxiv_ids),
        "doc_arxiv_versions": doc_arxiv_versions,
        "doc_dois": sorted(doc_dois),
        "doc_norm_title": doc_norm_title,
    }


def link_cross_document_citations(doc_packets: list[dict[str, Any]]) -> list[dict[str, Any]]:
    arxiv_to_best: dict[str, tuple[int, str]] = {}
    doi_to_doc: dict[str, str] = {}
    title_to_doc: dict[str, str] = {}

    for pkt in doc_packets:
        dkey = pkt["document"]["_key"]
        versions = pkt.get("doc_arxiv_versions") or {}
        for aid in pkt.get("doc_arxiv_ids") or ():
            ver = int(versions.get(aid, 0))
            if aid not in arxiv_to_best:
                arxiv_to_best[aid] = (ver, dkey)
            else:
                cur_ver, cur_dkey = arxiv_to_best[aid]
                if ver > cur_ver or (ver == cur_ver and dkey < cur_dkey):
                    arxiv_to_best[aid] = (ver, dkey)
        for doi in pkt.get("doc_dois") or ():
            doi_to_doc.setdefault(doi, dkey)
        norm_title = pkt["doc_norm_title"]
        if len(norm_title) >= 20:
            title_to_doc.setdefault(norm_title, dkey)

    arxiv_to_doc = {aid: dkey for aid, (_ver, dkey) in arxiv_to_best.items()}
    title_anchor_index: dict[str, list[tuple[str, str]]] = defaultdict(list)
    for norm_title, cand_doc in title_to_doc.items():
        tokens = [tok for tok in norm_title.split() if len(tok) >= 4]
        if not tokens:
            tokens = norm_title.split()
        if tokens:
            anchor = max(tokens, key=len)
            title_anchor_index[anchor].append((norm_title, cand_doc))

    cross_edges: list[dict[str, Any]] = []
    seen_pairs: set[tuple[str, str]] = set()
    for pkt in doc_packets:
        src_doc = pkt["document"]["_key"]
        for entry in pkt["bib_entries"]:
            dst_doc: str | None = None
            evidence = ""
            if entry["arxiv_id"] and entry["arxiv_id"] in arxiv_to_doc:
                dst_doc = arxiv_to_doc[entry["arxiv_id"]]
                evidence = f"arXiv:{entry['arxiv_id']}"
            elif entry["doi"] and entry["doi"] in doi_to_doc:
                dst_doc = doi_to_doc[entry["doi"]]
                evidence = f"doi:{entry['doi']}"
            else:
                norm_entry = _normalize_title_for_match(entry["raw_entry"])
                entry_tokens = set(norm_entry.split())
                seen_cands: set[str] = set()
                for tok in entry_tokens:
                    for norm_title, cand_doc in title_anchor_index.get(tok, ()):
                        if cand_doc in seen_cands or cand_doc == src_doc:
                            continue
                        seen_cands.add(cand_doc)
                        if norm_title in norm_entry:
                            dst_doc = cand_doc
                            evidence = f"title:{norm_title[:60]}"
                            break
                    if dst_doc:
                        break
            if dst_doc and dst_doc != src_doc and (src_doc, dst_doc) not in seen_pairs:
                seen_pairs.add((src_doc, dst_doc))
                cross_edges.append(
                    _dag_edge(
                        document_key=src_doc,
                        from_id=f"alexandria_documents/{src_doc}",
                        to_id=f"alexandria_documents/{dst_doc}",
                        edge_type="document_cites_document",
                        evidence=evidence,
                        confidence=0.9,
                    )
                )
    return cross_edges


THINK_BLOCK_RE = re.compile(r"<think>[\s\S]*?</think>", re.IGNORECASE)
UNCLOSED_THINK_RE = re.compile(r"<think>[\s\S]*?(?=\{)", re.IGNORECASE)


def _resolve_llm_api_key(api_key: str = "") -> str:
    return (
        api_key.strip()
        or os.environ.get("ALEXANDRIA_LLM_API_KEY", "").strip()
        or os.environ.get("OPENAI_API_KEY", "").strip()
    )


def _extract_json_object(raw: str) -> dict[str, Any]:
    cleaned = THINK_BLOCK_RE.sub("", raw).strip()
    cleaned = UNCLOSED_THINK_RE.sub("", cleaned).strip()
    cleaned = re.sub(r"^\s*```(?:json)?\s*|\s*```\s*$", "", cleaned, flags=re.IGNORECASE).strip()

    decoder = json.JSONDecoder()
    idx = 0
    while True:
        brace = cleaned.find("{", idx)
        if brace == -1:
            break
        try:
            obj, _end = decoder.raw_decode(cleaned, brace)
            if isinstance(obj, dict):
                return obj
        except ValueError:
            pass
        idx = brace + 1

    parsed = json.loads(cleaned)
    if not isinstance(parsed, dict):
        raise ValueError("LLM response JSON is not an object")
    return parsed


def _ollama_preflight(endpoint: str, timeout: float = 3.0, *, api_key: str = "") -> tuple[bool, str]:
    base = endpoint.rstrip("/")
    url = f"{base}/models" if base.endswith("/v1") else f"{base}/api/tags"
    try:
        req = Request(url, method="GET")
        req.add_header("Accept", "application/json")
        token = _resolve_llm_api_key(api_key)
        if token:
            req.add_header("Authorization", f"Bearer {token}")
        with urlopen(req, timeout=timeout) as resp:
            if resp.status != 200:
                return False, f"http_{resp.status}"
            payload = json.loads(resp.read().decode("utf-8"))
        if base.endswith("/v1"):
            models = payload.get("data", [])
        else:
            models = payload.get("models", [])
        if not models:
            return False, "no_models_available"
        return True, f"ok ({len(models)} model(s))"
    except Exception as exc:  # noqa: BLE001
        return False, str(exc)


def _ollama_request_chunk(
    chunk: dict[str, Any],
    *,
    endpoint: str,
    model: str,
    timeout: float,
    api_key: str = "",
    max_tokens: int = 1024,
    disable_thinking: bool = True,
) -> dict[str, Any]:
    base = endpoint.rstrip("/")
    system_prompt = (
        "You are a mathematical knowledge extractor. Summarize and extract mathematical entities "
        "strictly from the provided excerpt without modifying the excerpt. Return ONLY valid JSON."
    )
    user_prompt = (
        'Return JSON object with keys: "summary" (string), "assumed_definitions" (list of strings), '
        '"mathematical_entities" (list of strings), "symbolic_terms" (list of strings), '
        '"graph_triplets" (list of [subject, predicate, object] string triples).\n\n'
        f"TITLE: {chunk.get('title', '')}\nKIND: {chunk.get('chunkKind', '')}\nTEXT:\n{chunk['text'][:4000]}"
    )
    if base.endswith("/v1"):
        url = f"{base}/chat/completions"
        body: dict[str, Any] = {
            "model": model,
            "messages": [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ],
            "temperature": 0.1,
            "max_tokens": max(1, int(max_tokens)),
            "response_format": {"type": "json_object"},
        }
        if disable_thinking:
            body["chat_template_kwargs"] = {"enable_thinking": False}
    else:
        url = f"{base}/api/chat"
        body = {
            "model": model,
            "messages": [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ],
            "stream": False,
            "format": "json",
            "options": {"temperature": 0.1, "num_predict": max(1, int(max_tokens))},
        }
    req = Request(url, data=json.dumps(body).encode("utf-8"), method="POST")
    req.add_header("Content-Type", "application/json")
    req.add_header("Accept", "application/json")
    token = _resolve_llm_api_key(api_key)
    if token:
        req.add_header("Authorization", f"Bearer {token}")
    with urlopen(req, timeout=timeout) as resp:
        payload = json.loads(resp.read().decode("utf-8"))

    if base.endswith("/v1"):
        msg = (payload.get("choices") or [{}])[0].get("message") or {}
        raw = str(msg.get("content") or msg.get("reasoning_content") or "").strip()
    else:
        raw = str((payload.get("message") or {}).get("content") or payload.get("response") or "").strip()

    return _extract_json_object(raw)


def _materialize_enriched_chunk_to_collections(
    chunk: dict[str, Any],
    *,
    cleaned_entities: list[str],
    valid_triplets: list[list[str]],
    collections: dict[str, list[dict[str, Any]]],
    seen_entity_keys: set[str],
    seen_chunk_ent_keys: set[str],
    seen_rel_keys: set[str],
) -> None:
    doc_key = str(chunk.get("documentKey") or "")
    chunk_key = str(chunk.get("_key") or "")
    if not doc_key or not chunk_key:
        return

    ent_by_norm: dict[str, dict[str, Any]] = {}

    def _ensure_llm_entity(surface: str, confidence: float = 0.88) -> dict[str, Any]:
        norm = surface.strip().lower()
        existing = ent_by_norm.get(norm)
        if existing is not None:
            return existing
        ent = _entity_row(
            document_key=doc_key,
            chunk_key=chunk_key,
            entity_type="llm_entity",
            surface=surface.strip(),
            normalized=norm,
            confidence=confidence,
        )
        ent_by_norm[norm] = ent
        if ent["_key"] not in seen_entity_keys:
            seen_entity_keys.add(ent["_key"])
            collections.setdefault("alexandria_entities", []).append(ent)
        ce_key = stable_key("chunkent", chunk_key, ent["_key"])
        if ce_key not in seen_chunk_ent_keys:
            seen_chunk_ent_keys.add(ce_key)
            collections.setdefault("alexandria_chunk_entity_edges", []).append(
                {
                    "_key": ce_key,
                    "_from": f"alexandria_chunks/{chunk_key}",
                    "_to": f"alexandria_entities/{ent['_key']}",
                    "documentKey": doc_key,
                    "chunkKey": chunk_key,
                    "entityType": "llm_entity",
                    "confidence": confidence,
                    "sourceAuthority": SOURCE_AUTHORITY,
                }
            )
        return ent

    for name in cleaned_entities:
        _ensure_llm_entity(name, confidence=0.88)

    for subj, pred, obj in valid_triplets:
        s_ent = _ensure_llm_entity(subj, confidence=0.85)
        o_ent = _ensure_llm_entity(obj, confidence=0.85)
        if s_ent["_key"] == o_ent["_key"]:
            continue
        rel_type = pred.strip()[:64] or "related_to"
        rel_key = stable_key("rel", s_ent["_key"], rel_type.lower(), o_ent["_key"], chunk_key)
        if rel_key not in seen_rel_keys:
            seen_rel_keys.add(rel_key)
            collections.setdefault("alexandria_entity_relation_edges", []).append(
                {
                    "_key": rel_key,
                    "_from": f"alexandria_entities/{s_ent['_key']}",
                    "_to": f"alexandria_entities/{o_ent['_key']}",
                    "documentKey": doc_key,
                    "chunkKey": chunk_key,
                    "relationType": rel_type,
                    "evidence": str(chunk.get("title") or "")[:200],
                    "weight": 0.85,
                    "sourceAuthority": SOURCE_AUTHORITY,
                }
            )


def enrich_chunks_with_ollama(
    chunks: list[dict[str, Any]],
    *,
    endpoint: str,
    model: str,
    max_chunks: int,
    timeout: float,
    max_failures: int,
    workers: int = 1,
    api_key: str = "",
    max_tokens: int = 1024,
    disable_thinking: bool = True,
    collections: dict[str, list[dict[str, Any]]] | None = None,
) -> dict[str, Any]:
    ok, reason = _ollama_preflight(endpoint, timeout=min(3.0, timeout), api_key=api_key)
    stats: dict[str, Any] = {
        "enabled": True,
        "endpoint": endpoint,
        "model": model,
        "preflight_ok": ok,
        "preflight_status": reason,
        "max_chunks": max_chunks,
        "workers": max(1, int(workers)),
        "attempted": 0,
        "enriched": 0,
        "fallbacks": 0,
        "materialized_entities": 0,
        "materialized_relations": 0,
        "circuit_breaker_tripped": False,
    }
    if not ok or max_chunks <= 0 or not chunks:
        return stats

    priority_rank = {"theorem": 0, "definition": 1, "abstract": 2, "remark": 3, "proof": 4, "equation": 5, "prose": 6}
    candidates = sorted(
        chunks,
        key=lambda c: (priority_rank.get(str(c.get("chunkKind") or ""), 9), int(c.get("ordinal") or 0)),
    )[:max_chunks]

    seen_entity_keys: set[str] = set()
    seen_chunk_ent_keys: set[str] = set()
    seen_rel_keys: set[str] = set()
    if collections is not None:
        seen_entity_keys = {str(r.get("_key") or "") for r in collections.get("alexandria_entities", [])}
        seen_chunk_ent_keys = {str(r.get("_key") or "") for r in collections.get("alexandria_chunk_entity_edges", [])}
        seen_rel_keys = {str(r.get("_key") or "") for r in collections.get("alexandria_entity_relation_edges", [])}
    initial_ent_count = len(seen_entity_keys)
    initial_rel_count = len(seen_rel_keys)

    def _apply_enrichment(chunk: dict[str, Any], enriched: dict[str, Any]) -> None:
        base_sem = dict(chunk["semantic"])
        if isinstance(enriched.get("summary"), str) and enriched["summary"].strip():
            base_sem["summary"] = enriched["summary"].strip()[:600]
        cleaned_map: dict[str, list[str]] = {}
        for list_key in ("assumed_definitions", "mathematical_entities", "symbolic_terms"):
            val = enriched.get(list_key)
            if isinstance(val, list):
                cleaned = [str(x).strip() for x in val if str(x).strip()]
                if cleaned:
                    cleaned_map[list_key] = cleaned
                    base_sem[list_key] = list(dict.fromkeys([*base_sem.get(list_key, []), *cleaned]))[:32]
        valid_triplets: list[list[str]] = []
        triplets = enriched.get("graph_triplets")
        if isinstance(triplets, list):
            valid_triplets = [
                [str(t[0]).strip(), str(t[1]).strip(), str(t[2]).strip()]
                for t in triplets
                if isinstance(t, (list, tuple)) and len(t) == 3 and all(str(x).strip() for x in t)
            ]
            if valid_triplets:
                base_sem["graph_triplets"] = valid_triplets[:24]
        base_sem["semantic_mode"] = f"ollama_{model}_v1"
        chunk["semantic"] = base_sem

        ent_terms = list(
            dict.fromkeys(
                [
                    *cleaned_map.get("mathematical_entities", []),
                    *cleaned_map.get("assumed_definitions", []),
                    *cleaned_map.get("symbolic_terms", []),
                ]
            )
        )
        if ent_terms:
            chunk["searchTerms"] = sorted(set(chunk.get("searchTerms") or []) | set(ident_terms(" ".join(ent_terms))))
        if collections is not None:
            _materialize_enriched_chunk_to_collections(
                chunk,
                cleaned_entities=cleaned_map.get("mathematical_entities", []),
                valid_triplets=valid_triplets[:24],
                collections=collections,
                seen_entity_keys=seen_entity_keys,
                seen_chunk_ent_keys=seen_chunk_ent_keys,
                seen_rel_keys=seen_rel_keys,
            )

    consecutive_failures = 0
    worker_count = max(1, int(workers))
    if worker_count == 1 or len(candidates) <= 1:
        for chunk in candidates:
            stats["attempted"] += 1
            try:
                enriched = _ollama_request_chunk(
                    chunk,
                    endpoint=endpoint,
                    model=model,
                    timeout=timeout,
                    api_key=api_key,
                    max_tokens=max_tokens,
                    disable_thinking=disable_thinking,
                )
                _apply_enrichment(chunk, enriched)
                stats["enriched"] += 1
                consecutive_failures = 0
            except Exception:  # noqa: BLE001
                stats["fallbacks"] += 1
                consecutive_failures += 1
                if consecutive_failures >= max(1, max_failures):
                    stats["circuit_breaker_tripped"] = True
                    break
    else:
        with ThreadPoolExecutor(max_workers=worker_count) as pool:
            for start in range(0, len(candidates), worker_count):
                wave = candidates[start : start + worker_count]
                futs = [
                    (
                        chunk,
                        pool.submit(
                            _ollama_request_chunk,
                            chunk,
                            endpoint=endpoint,
                            model=model,
                            timeout=timeout,
                            api_key=api_key,
                            max_tokens=max_tokens,
                            disable_thinking=disable_thinking,
                        ),
                    )
                    for chunk in wave
                ]
                for chunk, fut in futs:
                    stats["attempted"] += 1
                    try:
                        enriched = fut.result()
                        _apply_enrichment(chunk, enriched)
                        stats["enriched"] += 1
                        consecutive_failures = 0
                    except Exception:  # noqa: BLE001
                        stats["fallbacks"] += 1
                        consecutive_failures += 1
                        if consecutive_failures >= max(1, max_failures):
                            stats["circuit_breaker_tripped"] = True
                if stats["circuit_breaker_tripped"]:
                    break

    if collections is not None:
        stats["materialized_entities"] = len(seen_entity_keys) - initial_ent_count
        stats["materialized_relations"] = len(seen_rel_keys) - initial_rel_count
    return stats


def ingest_pdf_artifacts_to_arango(
    *,
    output_dir: Path,
    endpoint: str,
    database: str,
    username: str,
    password: str,
    replace_documents: bool,
    skip_unchanged: bool,
) -> dict[str, Any]:
    guard_alexandria_target(endpoint, database)
    doc_cols = list(arango_ingest.DOCUMENT_COLLECTIONS)
    edge_cols = list(dict.fromkeys([*arango_ingest.EDGE_COLLECTIONS, "alexandria_dag_edges"]))
    arango_ingest.ensure_database(endpoint, database, username, password)
    for name in doc_cols:
        arango_ingest.ensure_collection(endpoint, database, username, password, name, edge=False)
    for name in edge_cols:
        arango_ingest.ensure_collection(endpoint, database, username, password, name, edge=True)
    for collection, fields_list in arango_ingest.INDEXES.items():
        for fields in fields_list:
            arango_ingest.ensure_index(endpoint, database, username, password, collection, fields)

    rows = arango_ingest.load_artifacts(output_dir, doc_cols + edge_cols)
    target = ArangoHttpTarget(endpoint.rstrip("/"), database, username, password)
    documents = rows.get("alexandria_documents", [])
    skipped: set[str] = set()
    if skip_unchanged and documents:
        stored = arango_ingest.existing_content_hashes(target, [row["_key"] for row in documents])
        skipped = {
            row["_key"] for row in documents if row.get("contentHash") and stored.get(row["_key"]) == row["contentHash"]
        }
        arango_ingest.drop_rows_for_documents(rows, skipped)
    if replace_documents and rows.get("alexandria_documents"):
        doc_keys = [row["_key"] for row in rows["alexandria_documents"]]
        arango_ingest.remove_documents(target, doc_keys)

    rows["alexandria_chunks"] = [arango_ingest.add_search_terms(row) for row in rows.get("alexandria_chunks", [])]
    for collection in doc_cols + edge_cols:
        arango_ingest.import_rows(endpoint, database, username, password, collection, rows.get(collection, []))

    view_status = arango_ingest.ensure_search_view(endpoint, database, username, password)
    return {
        "endpoint": endpoint,
        "database": database,
        "documents": len(documents),
        "skippedUnchanged": len(skipped),
        "imported": {name: len(value) for name, value in rows.items() if value},
        "searchView": {arango_ingest.SEARCH_VIEW: view_status},
    }


def _render_inventory_markdown(report: dict[str, Any]) -> str:
    lines = [
        "# Alexandria PDF Corpus Inventory & Ingestion Report",
        "",
        f"- **Input directory**: `{report['input_dir']}`",
        f"- **Output directory**: `{report['output_dir']}`",
        f"- **Source authority**: `{report['source_authority']}`",
        f"- **Total scanned regular files**: {report['total_scanned_files']}",
        f"- **Symlinks skipped**: {report['symlinks_skipped']}",
        f"- **Non-PDF files skipped**: {report['non_pdf_skipped']}",
        f"- **PDF extension files**: {report['pdf_extension_count']}",
        f"- **Magic-header `%PDF-` non-`.pdf` files**: {report['magic_header_non_pdf_ext_count']}",
        f"- **Total PDF files**: {report['total_pdf_files']}",
        f"- **Unique SHA-256 hashes**: {report['unique_sha256_count']}",
        f"- **Duplicate copies skipped**: {report['duplicate_skipped_count']}",
        "",
        "## Outcome Counts",
        "",
    ]
    for k, v in report["outcome_counts"].items():
        lines.append(f"- `{k}`: {v}")
    lines.extend(["", "## Artifact Counts", ""])
    for k, v in report["artifact_counts"].items():
        lines.append(f"- `{k}`: {v}")
    lines.extend(["", "## Chunk Archetype Counts", ""])
    for k, v in report["chunk_kind_counts"].items():
        lines.append(f"- `{k}`: {v}")
    lines.extend(["", "## DAG Edge Type Counts", ""])
    for k, v in report["dag_edge_type_counts"].items():
        lines.append(f"- `{k}`: {v}")
    return "\n".join(lines) + "\n"


def _extract_and_build_group(
    group: DedupGroup,
    *,
    per_file_timeout: float,
    min_text_chars: int,
    max_chunk_chars: int,
    cache_dir: Path | None,
) -> tuple[dict[str, Any], dict[str, Any] | None]:
    dup_paths = [d.path.as_posix() for d in group.duplicates]
    dup_cnt = len(group.duplicates)
    cache_path = (cache_dir / f"{group.sha256}_{max_chunk_chars}.json") if cache_dir is not None else None
    if cache_path is not None and cache_path.exists():
        try:
            cached = json.loads(cache_path.read_text(encoding="utf-8"))
            if (
                isinstance(cached, dict)
                and cached.get("cache_schema") == SCHEMA_VERSION
                and isinstance(cached.get("meta"), dict)
            ):
                meta = dict(cached["meta"])
                meta["canonicalPath"] = group.canonical.path.as_posix()
                meta["relativePath"] = group.canonical.rel_path
                meta["duplicatePaths"] = dup_paths
                meta["duplicateCount"] = dup_cnt
                pkt = cached.get("packet")
                if isinstance(pkt, dict) and isinstance(pkt.get("document"), dict):
                    pkt["document"]["path"] = group.canonical.path.as_posix()
                    pkt["document"]["relativePath"] = group.canonical.rel_path
                    pkt["document"]["duplicatePaths"] = dup_paths
                    pkt["document"]["sourceUri"] = source_uri(group.canonical.path)
                return meta, pkt if isinstance(pkt, dict) else None
        except Exception:  # noqa: BLE001
            pass

    res = extract_pdf_group(group, per_file_timeout=per_file_timeout, min_text_chars=min_text_chars)
    pkt: dict[str, Any] | None = None
    doc_key = ""
    if res.outcome == "ingested":
        pkt = build_document_artifacts(res, max_chunk_chars=max_chunk_chars)
        doc_key = str(pkt["document"]["_key"])
    res.pages = []
    meta = {
        "sha256": group.sha256,
        "canonicalPath": res.canonical_path.as_posix(),
        "relativePath": res.rel_path,
        "duplicatePaths": res.duplicate_paths,
        "duplicateCount": dup_cnt,
        "sizeBytes": res.size_bytes,
        "outcome": res.outcome,
        "reason": res.reason,
        "pageCount": res.page_count,
        "charCount": res.char_count,
        "parser": res.parser,
        "warnings": res.warnings,
        "encodingNoiseRatio": round(res.encoding_noise_ratio, 6),
        "documentKey": doc_key,
    }
    if cache_path is not None:
        tmp_cache = cache_path.with_suffix(".tmp")
        tmp_cache.write_text(
            json.dumps({"cache_schema": SCHEMA_VERSION, "meta": meta, "packet": pkt}, ensure_ascii=False),
            encoding="utf-8",
        )
        tmp_cache.replace(cache_path)
    return meta, pkt


def run_pdf_corpus_pipeline(
    *,
    input_dir: Path,
    output_dir: Path,
    ingest_arango: bool = False,
    endpoint: str = "",
    database: str = "",
    username: str = "",
    password: str = "",
    replace_documents: bool = False,
    skip_unchanged: bool = False,
    limit: int = 0,
    enrich_ollama: bool = False,
    ollama_endpoint: str = "http://127.0.0.1:11434",
    ollama_model: str = "leanstral:latest",
    enrich_ollama_max_chunks: int = 20,
    enrich_ollama_timeout: float = 20.0,
    enrich_ollama_max_failures: int = 3,
    workers: int = 4,
    min_text_chars: int = 100,
    per_file_timeout: float = 30.0,
    max_chunk_chars: int = 3200,
    enrich_ollama_workers: int = 1,
    enrich_ollama_max_tokens: int = 1024,
    enrich_ollama_api_key: str = "",
    enrich_ollama_disable_thinking: bool = True,
    exclude_globs: Iterable[str] = (),
    exclude_default_noise: bool = False,
    resume: bool = False,
) -> dict[str, Any]:
    if limit < 0:
        raise ValueError(f"--limit must be >= 0 (0 = all); got {limit}")
    if workers < 1:
        raise ValueError(f"--workers must be >= 1; got {workers}")
    if enrich_ollama_workers < 1:
        raise ValueError(f"--enrich-ollama-workers must be >= 1; got {enrich_ollama_workers}")
    if enrich_ollama_max_tokens < 1:
        raise ValueError(f"--enrich-ollama-max-tokens must be >= 1; got {enrich_ollama_max_tokens}")
    if per_file_timeout <= 0 or not math.isfinite(per_file_timeout):
        raise ValueError(f"--per-file-timeout must be > 0; got {per_file_timeout}")
    if max_chunk_chars < 1:
        raise ValueError(f"--max-chunk-chars must be >= 1; got {max_chunk_chars}")
    if min_text_chars < 0:
        raise ValueError(f"--min-text-chars must be >= 0; got {min_text_chars}")
    if ingest_arango:
        guard_alexandria_target(endpoint, database)

    output_dir.mkdir(parents=True, exist_ok=True)
    cache_dir: Path | None = None
    if resume:
        cache_dir = output_dir / ".doc_cache"
        cache_dir.mkdir(parents=True, exist_ok=True)

    active_excludes = tuple(DEFAULT_NOISE_EXCLUDE_GLOBS if exclude_default_noise else ()) + tuple(exclude_globs)
    inventory = scan_and_deduplicate_corpus(input_dir, exclude_globs=active_excludes)

    selected_groups = inventory.groups[:limit] if limit and limit > 0 else inventory.groups
    skipped_limit_groups = inventory.groups[len(selected_groups) :]

    processed_by_sha: dict[str, tuple[dict[str, Any], dict[str, Any] | None]] = {}
    max_workers = max(1, workers)
    if max_workers == 1 or len(selected_groups) <= 1:
        for group in selected_groups:
            processed_by_sha[group.sha256] = _extract_and_build_group(
                group,
                per_file_timeout=per_file_timeout,
                min_text_chars=min_text_chars,
                max_chunk_chars=max_chunk_chars,
                cache_dir=cache_dir,
            )
    else:
        with ThreadPoolExecutor(max_workers=max_workers) as pool:
            futs = {
                pool.submit(
                    _extract_and_build_group,
                    group,
                    per_file_timeout=per_file_timeout,
                    min_text_chars=min_text_chars,
                    max_chunk_chars=max_chunk_chars,
                    cache_dir=cache_dir,
                ): group
                for group in selected_groups
            }
            for fut in as_completed(futs):
                group = futs[fut]
                try:
                    processed_by_sha[group.sha256] = fut.result()
                except Exception as exc:  # noqa: BLE001
                    processed_by_sha[group.sha256] = (
                        {
                            "sha256": group.sha256,
                            "canonicalPath": group.canonical.path.as_posix(),
                            "relativePath": group.canonical.rel_path,
                            "duplicatePaths": [d.path.as_posix() for d in group.duplicates],
                            "duplicateCount": len(group.duplicates),
                            "sizeBytes": group.size_bytes,
                            "outcome": "parse_error",
                            "reason": f"worker_exception: {exc}",
                            "pageCount": 0,
                            "charCount": 0,
                            "parser": "none",
                            "warnings": [f"worker_exception: {exc}"],
                            "encodingNoiseRatio": 0.0,
                            "documentKey": "",
                        },
                        None,
                    )

    doc_packets: list[dict[str, Any]] = []
    unique_records: list[dict[str, Any]] = []
    outcome_counts: dict[str, int] = {k: 0 for k in OUTCOME_KEYS}
    duplicate_skipped_count = 0

    for group in selected_groups:
        meta, pkt = processed_by_sha[group.sha256]
        outcome = str(meta["outcome"])
        outcome_counts[outcome] = outcome_counts.get(outcome, 0) + 1
        dup_cnt = len(group.duplicates)
        duplicate_skipped_count += dup_cnt
        outcome_counts["duplicate_skipped"] += dup_cnt
        if pkt is not None and outcome == "ingested":
            doc_packets.append(pkt)
        unique_records.append(meta)

    for group in skipped_limit_groups:
        dup_cnt = len(group.duplicates)
        duplicate_skipped_count += dup_cnt
        outcome_counts["limit_skipped"] += 1
        outcome_counts["duplicate_skipped"] += dup_cnt
        unique_records.append(
            {
                "sha256": group.sha256,
                "canonicalPath": group.canonical.path.as_posix(),
                "relativePath": group.canonical.rel_path,
                "duplicatePaths": [d.path.as_posix() for d in group.duplicates],
                "duplicateCount": dup_cnt,
                "sizeBytes": group.size_bytes,
                "outcome": "limit_skipped",
                "reason": f"deferred by --limit {limit}",
                "pageCount": 0,
                "charCount": 0,
                "parser": "none",
                "warnings": [],
                "encodingNoiseRatio": 0.0,
                "documentKey": "",
            }
        )

    # Assemble collections
    collections: dict[str, list[dict[str, Any]]] = {
        "alexandria_documents": [],
        "alexandria_sections": [],
        "alexandria_chunks": [],
        "alexandria_entities": [],
        "alexandria_document_section_edges": [],
        "alexandria_section_chunk_edges": [],
        "alexandria_chunk_adjacent_edges": [],
        "alexandria_chunk_entity_edges": [],
        "alexandria_entity_relation_edges": [],
        "alexandria_dag_edges": [],
    }
    for pkt in doc_packets:
        collections["alexandria_documents"].append(pkt["document"])
        collections["alexandria_sections"].extend(pkt["sections"])
        collections["alexandria_chunks"].extend(pkt["chunks"])
        collections["alexandria_entities"].extend(pkt["entities"])
        collections["alexandria_document_section_edges"].extend(pkt["document_section_edges"])
        collections["alexandria_section_chunk_edges"].extend(pkt["section_chunk_edges"])
        collections["alexandria_chunk_adjacent_edges"].extend(pkt["chunk_adjacent_edges"])
        collections["alexandria_chunk_entity_edges"].extend(pkt["chunk_entity_edges"])
        collections["alexandria_entity_relation_edges"].extend(pkt["entity_relation_edges"])
        collections["alexandria_dag_edges"].extend(pkt["dag_edges"])

    collections["alexandria_dag_edges"].extend(link_cross_document_citations(doc_packets))
    verified_dag_edges, pruned_dag_edges = verify_and_prune_dag(collections["alexandria_dag_edges"])
    collections["alexandria_dag_edges"] = verified_dag_edges

    ollama_stats: dict[str, Any] = {"enabled": False}
    if enrich_ollama:
        ollama_stats = enrich_chunks_with_ollama(
            collections["alexandria_chunks"],
            endpoint=ollama_endpoint,
            model=ollama_model,
            max_chunks=enrich_ollama_max_chunks,
            timeout=enrich_ollama_timeout,
            max_failures=enrich_ollama_max_failures,
            workers=enrich_ollama_workers,
            api_key=enrich_ollama_api_key,
            max_tokens=enrich_ollama_max_tokens,
            disable_thinking=enrich_ollama_disable_thinking,
            collections=collections,
        )

    for col_name, rows in collections.items():
        write_jsonl(output_dir / f"{col_name}.jsonl", rows)

    arango_report: dict[str, Any] | None = None
    if ingest_arango:
        arango_report = ingest_pdf_artifacts_to_arango(
            output_dir=output_dir,
            endpoint=endpoint,
            database=database,
            username=username,
            password=password,
            replace_documents=replace_documents,
            skip_unchanged=skip_unchanged,
        )

    duplicate_groups = [
        {
            "sha256": g.sha256,
            "canonicalPath": g.canonical.path.as_posix(),
            "duplicatePaths": [d.path.as_posix() for d in g.duplicates],
            "sizeBytes": g.size_bytes,
            "count": 1 + len(g.duplicates),
        }
        for g in inventory.groups
        if g.duplicates
    ]
    chunk_kind_counts = dict(sorted(Counter(r["chunkKind"] for r in collections["alexandria_chunks"]).items()))
    dag_edge_type_counts = dict(sorted(Counter(r["edgeType"] for r in collections["alexandria_dag_edges"]).items()))

    report = {
        "schema": "info_geometry.alexandria.pdf_corpus_inventory.v1",
        "source_authority": SOURCE_AUTHORITY,
        "input_dir": input_dir.as_posix(),
        "output_dir": output_dir.as_posix(),
        "limit": limit,
        "total_entries_seen": inventory.total_entries_seen,
        "symlinks_skipped": inventory.symlinks_skipped,
        "total_scanned_files": inventory.total_scanned_files,
        "non_pdf_skipped": inventory.non_pdf_skipped,
        "non_pdf_by_extension": inventory.non_pdf_by_extension,
        "pdf_extension_count": inventory.pdf_extension_count,
        "magic_header_non_pdf_ext_count": inventory.magic_header_non_pdf_ext_count,
        "total_pdf_files": inventory.total_pdf_files,
        "unique_sha256_count": len(inventory.groups),
        "unique_pdfs_selected": len(selected_groups),
        "duplicate_skipped_count": duplicate_skipped_count,
        "outcome_counts": outcome_counts,
        "duplicate_groups": duplicate_groups,
        "unique_documents": unique_records,
        "artifact_counts": {k: len(v) for k, v in collections.items()},
        "chunk_kind_counts": chunk_kind_counts,
        "dag_edge_type_counts": dag_edge_type_counts,
        "dag_edges_pruned_for_cycles": len(pruned_dag_edges),
        "ollama_enrichment": ollama_stats,
        "arango_ingest": arango_report,
    }
    (output_dir / "corpus_inventory_report.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    (output_dir / "corpus_inventory_report.md").write_text(
        _render_inventory_markdown(report),
        encoding="utf-8",
    )
    return report


def build_arg_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--input-dir", required=True, type=Path, help="Read-only PDF corpus directory")
    ap.add_argument("--output-dir", required=True, type=Path, help="Output directory for JSONL + inventory reports")
    ap.add_argument("--ingest-arango", action="store_true", help="Ingest emitted JSONL into Alexandria ArangoDB (:8532)")
    ap.add_argument("--endpoint", default=alexandria_arango_endpoint())
    ap.add_argument("--database", default=alexandria_arango_database())
    ap.add_argument("--username", default=alexandria_arango_username())
    ap.add_argument("--password", default=alexandria_arango_password("alexandria_root"))
    mode_group = ap.add_mutually_exclusive_group()
    mode_group.add_argument("--replace-documents", action="store_true")
    mode_group.add_argument("--skip-unchanged", action="store_true")
    ap.add_argument("--limit", type=int, default=0, help="Process at most N unique PDFs (0 = all)")
    ap.add_argument("--enrich-ollama", action="store_true", help="Enable bounded local Ollama semantic enrichment")
    ap.add_argument("--ollama-endpoint", default="http://127.0.0.1:11434")
    ap.add_argument("--ollama-model", default="leanstral:latest")
    ap.add_argument("--enrich-ollama-max-chunks", type=int, default=20)
    ap.add_argument("--enrich-ollama-timeout", type=float, default=20.0)
    ap.add_argument("--enrich-ollama-max-failures", type=int, default=3)
    ap.add_argument("--enrich-ollama-workers", type=int, default=1)
    ap.add_argument("--enrich-ollama-max-tokens", type=int, default=1024)
    ap.add_argument("--enrich-ollama-api-key", default="")
    ap.add_argument("--allow-thinking", action="store_false", dest="enrich_ollama_disable_thinking", default=True)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--min-text-chars", type=int, default=100)
    ap.add_argument("--per-file-timeout", type=float, default=30.0)
    ap.add_argument("--max-chunk-chars", type=int, default=3200)
    ap.add_argument("--exclude-glob", action="append", default=[])
    ap.add_argument("--exclude-default-noise", action="store_true")
    ap.add_argument("--resume", action="store_true")
    return ap


def main(argv: list[str] | None = None) -> int:
    load_alexandria_arango_env(REPO_ROOT)
    ap = build_arg_parser()
    args = ap.parse_args(argv)
    if args.limit < 0:
        ap.error(f"--limit must be >= 0 (0 = all); got {args.limit}")
    if args.workers < 1:
        ap.error(f"--workers must be >= 1; got {args.workers}")
    if args.enrich_ollama_workers < 1:
        ap.error(f"--enrich-ollama-workers must be >= 1; got {args.enrich_ollama_workers}")
    if args.enrich_ollama_max_tokens < 1:
        ap.error(f"--enrich-ollama-max-tokens must be >= 1; got {args.enrich_ollama_max_tokens}")
    if args.per_file_timeout <= 0 or not math.isfinite(args.per_file_timeout):
        ap.error(f"--per-file-timeout must be > 0; got {args.per_file_timeout}")
    if args.max_chunk_chars < 1:
        ap.error(f"--max-chunk-chars must be >= 1; got {args.max_chunk_chars}")
    if args.min_text_chars < 0:
        ap.error(f"--min-text-chars must be >= 0; got {args.min_text_chars}")
    if args.ingest_arango:
        guard_alexandria_target(args.endpoint, args.database)

    report = run_pdf_corpus_pipeline(
        input_dir=args.input_dir,
        output_dir=args.output_dir,
        ingest_arango=bool(args.ingest_arango),
        endpoint=args.endpoint,
        database=args.database,
        username=args.username,
        password=args.password,
        replace_documents=bool(args.replace_documents),
        skip_unchanged=bool(args.skip_unchanged),
        limit=int(args.limit),
        enrich_ollama=bool(args.enrich_ollama),
        ollama_endpoint=args.ollama_endpoint,
        ollama_model=args.ollama_model,
        enrich_ollama_max_chunks=int(args.enrich_ollama_max_chunks),
        enrich_ollama_timeout=float(args.enrich_ollama_timeout),
        enrich_ollama_max_failures=int(args.enrich_ollama_max_failures),
        workers=int(args.workers),
        min_text_chars=int(args.min_text_chars),
        per_file_timeout=float(args.per_file_timeout),
        max_chunk_chars=int(args.max_chunk_chars),
        enrich_ollama_workers=int(args.enrich_ollama_workers),
        enrich_ollama_max_tokens=int(args.enrich_ollama_max_tokens),
        enrich_ollama_api_key=args.enrich_ollama_api_key,
        enrich_ollama_disable_thinking=bool(args.enrich_ollama_disable_thinking),
        exclude_globs=args.exclude_glob,
        exclude_default_noise=bool(args.exclude_default_noise),
        resume=bool(args.resume),
    )
    print(
        json.dumps(
            {
                "total_scanned_files": report["total_scanned_files"],
                "total_pdf_files": report["total_pdf_files"],
                "unique_sha256_count": report["unique_sha256_count"],
                "outcome_counts": report["outcome_counts"],
                "artifact_counts": report["artifact_counts"],
                "chunk_kind_counts": report["chunk_kind_counts"],
                "dag_edge_type_counts": report["dag_edge_type_counts"],
                "dag_edges_pruned_for_cycles": report["dag_edges_pruned_for_cycles"],
                "ollama_enrichment": report["ollama_enrichment"],
                "arango_ingest": report["arango_ingest"],
            },
            indent=2,
            ensure_ascii=False,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
