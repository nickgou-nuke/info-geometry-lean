"""Shared fixtures, synthetic PDF builders, ArangoDB :8532 isolation, and CLI runners."""
from __future__ import annotations

import base64
import hashlib
import io
import json
import os
import subprocess
import sys
import uuid
from pathlib import Path
from typing import Any
from urllib.error import HTTPError, URLError
from urllib.parse import quote, urlparse
from urllib.request import Request, urlopen

import pytest
from PIL import Image, ImageDraw
from pypdf import PdfReader, PdfWriter
from reportlab.lib.pagesizes import letter
from reportlab.lib.utils import ImageReader
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.pdfgen import canvas

REPO_ROOT = Path(__file__).resolve().parents[2]
SAGE_PYTHON = Path("/home/goutev/miniforge3/envs/sage/bin/python")
PYTHON_EXE = str(SAGE_PYTHON if SAGE_PYTHON.exists() else Path(sys.executable))

ALEXANDRIA_ENDPOINT = "http://127.0.0.1:8532"
ALEXANDRIA_PROD_DB = "alexandria"
INFOGEOMETRY_ENDPOINT = "http://127.0.0.1:8530"
HIVE_ENDPOINT = "http://127.0.0.1:8540"

PROTECTED_PORTS = {8530, 8540}
PROTECTED_DATABASES = {
    "alexandria",
    "infogeometry",
    "darwin_commits",
    "hive_live",
    "aiclaw_auto_rag",
}

REAL_CORPUS_DIR = Path("/home/goutev/Downloads/collection_for_formalization")
DEFAULT_CORPUS_REPORT = REPO_ROOT / "artifacts" / "alexandria_pdf_corpus" / "corpus_inventory_report.json"

PDF_CORPUS_INGEST_SCRIPT = REPO_ROOT / "tools" / "alexandria" / "pdf_corpus_ingest.py"
ARANGO_INGEST_SCRIPT = REPO_ROOT / "tools" / "alexandria" / "arango_ingest.py"
RETRIEVE_CONTEXT_SCRIPT = REPO_ROOT / "tools" / "alexandria" / "retrieve_context.py"
GRAPH_CONTEXT_RANK_SCRIPT = REPO_ROOT / "tools" / "alexandria" / "graph_context_rank.py"
GRAPH_RAG_QUERY_SCRIPT = REPO_ROOT / "tools" / "infra" / "graph_rag_query.py"
ASK_REPO_SCRIPT = REPO_ROOT / "tools" / "infra" / "ask_repo.py"

DEJAVU_TTF = Path("/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf")
_FONT_REGISTERED = False


def pytest_configure(config: pytest.Config) -> None:
    config.addinivalue_line("markers", "tier1: Tier 1 isolated happy-path feature tests (F1-F7)")
    config.addinivalue_line("markers", "tier2: Tier 2 boundary, corner, and negative tests (F1-F7)")
    config.addinivalue_line("markers", "tier3: Tier 3 pairwise combinatorial cross-feature tests")
    config.addinivalue_line("markers", "tier4: Tier 4 read-only real-world corpus & formalization scenarios")
    config.addinivalue_line("markers", "tier5: Tier 5 white-box adversarial coverage hardening tests")


def _ensure_unicode_font() -> str:
    global _FONT_REGISTERED
    if DEJAVU_TTF.exists():
        if not _FONT_REGISTERED:
            pdfmetrics.registerFont(TTFont("DejaVuSans", str(DEJAVU_TTF)))
            _FONT_REGISTERED = True
        return "DejaVuSans"
    return "Helvetica"


# ---------------------------------------------------------------------------
# Credentials, URL guards, and raw Arango HTTP helpers (no test-skip fallbacks)
# ---------------------------------------------------------------------------

def _parse_env_file(path: Path) -> dict[str, str]:
    out: dict[str, str] = {}
    if not path.exists():
        return out
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        out[key.strip()] = value.strip().strip('"').strip("'")
    return out


def alexandria_credentials() -> tuple[str, str]:
    env_data = _parse_env_file(REPO_ROOT / "configs" / "alexandria" / ".env")
    if not env_data:
        env_data = _parse_env_file(REPO_ROOT / "configs" / "alexandria" / ".env.example")
    user = (
        os.environ.get("ALEXANDRIA_ARANGO_USERNAME")
        or env_data.get("ALEXANDRIA_ARANGO_USERNAME")
        or "root"
    )
    password = (
        os.environ.get("ALEXANDRIA_ARANGO_PASSWORD")
        or env_data.get("ALEXANDRIA_ARANGO_PASSWORD")
        or env_data.get("ARANGO_ROOT_PASSWORD")
        or "alexandria_root"
    )
    return user, password


def assert_safe_test_target(endpoint: str, database: str) -> None:
    parsed = urlparse(endpoint)
    port = parsed.port
    assert port == 8532, f"Refusing non-8532 endpoint for mutating E2E test: {endpoint!r}"
    assert port not in PROTECTED_PORTS, f"Refusing protected port {port}"
    db_norm = database.strip().lower()
    assert db_norm not in PROTECTED_DATABASES, (
        f"Refusing protected database {database!r} in mutating E2E test"
    )
    assert db_norm.startswith("alexandria_e2e_test_"), (
        f"Mutating E2E DB must match alexandria_e2e_test_*, got {database!r}"
    )


def _auth_header(username: str, password: str) -> str:
    token = base64.b64encode(f"{username}:{password}".encode("utf-8")).decode("ascii")
    return f"Basic {token}"


def arango_http_json(
    method: str,
    url: str,
    username: str,
    password: str,
    payload: Any | None = None,
    *,
    timeout: float = 10.0,
) -> tuple[int, dict[str, Any]]:
    body = json.dumps(payload, ensure_ascii=False).encode("utf-8") if payload is not None else None
    req = Request(url, data=body, method=method)
    req.add_header("Authorization", _auth_header(username, password))
    req.add_header("Accept", "application/json")
    if body is not None:
        req.add_header("Content-Type", "application/json")
    try:
        with urlopen(req, timeout=timeout) as resp:
            raw = resp.read().decode("utf-8")
            return int(resp.status), (json.loads(raw) if raw else {})
    except HTTPError as exc:
        raw = exc.read().decode("utf-8", errors="replace")
        try:
            parsed = json.loads(raw) if raw else {}
        except Exception:
            parsed = {"raw": raw}
        return int(exc.code), parsed


def require_alexandria_8532() -> tuple[str, str]:
    user, pw = alexandria_credentials()
    url = f"{ALEXANDRIA_ENDPOINT}/_api/version"
    try:
        status, payload = arango_http_json("GET", url, user, pw, timeout=3.0)
    except (URLError, OSError) as exc:
        pytest.fail(
            f"Alexandria ArangoDB at {ALEXANDRIA_ENDPOINT} is unreachable ({exc}). "
            "M1/M2 must provision the dedicated :8532 container (arango_alexandria_pdf)."
        )
    if status != 200:
        pytest.fail(
            f"Alexandria ArangoDB at {ALEXANDRIA_ENDPOINT}/_api/version returned HTTP {status}: {payload}"
        )
    return user, pw


def arango_aql(
    endpoint: str,
    database: str,
    username: str,
    password: str,
    query: str,
    bind_vars: dict[str, Any] | None = None,
    *,
    timeout: float = 30.0,
) -> list[Any]:
    url = f"{endpoint.rstrip('/')}/_db/{quote(database)}/_api/cursor"
    rows: list[Any] = []
    status, cursor = arango_http_json(
        "POST",
        url,
        username,
        password,
        {"query": query, "bindVars": bind_vars or {}},
        timeout=timeout,
    )
    assert status in (200, 201), f"AQL failed HTTP {status} on {database}: {cursor}"
    rows.extend(cursor.get("result", []))
    while cursor.get("hasMore"):
        cid = cursor["id"]
        status, cursor = arango_http_json(
            "PUT",
            f"{endpoint.rstrip('/')}/_db/{quote(database)}/_api/cursor/{quote(str(cid))}",
            username,
            password,
            timeout=timeout,
        )
        assert status in (200, 201), f"AQL cursor continuation failed HTTP {status}: {cursor}"
        rows.extend(cursor.get("result", []))
    return rows


def arango_list_databases(endpoint: str, username: str, password: str) -> list[str]:
    status, data = arango_http_json("GET", f"{endpoint.rstrip('/')}/_api/database", username, password, timeout=3.0)
    assert status == 200, f"GET /_api/database failed on {endpoint}: HTTP {status} {data}"
    return list(data.get("result", []))


def arango_list_collections(endpoint: str, database: str, username: str, password: str) -> set[str]:
    status, data = arango_http_json(
        "GET",
        f"{endpoint.rstrip('/')}/_db/{quote(database)}/_api/collection?excludeSystem=true",
        username,
        password,
        timeout=5.0,
    )
    assert status == 200, f"GET /_api/collection failed on {database}: HTTP {status} {data}"
    return {row["name"] for row in data.get("result", []) if isinstance(row, dict) and row.get("name")}


def arango_list_views(endpoint: str, database: str, username: str, password: str) -> set[str]:
    status, data = arango_http_json(
        "GET",
        f"{endpoint.rstrip('/')}/_db/{quote(database)}/_api/view",
        username,
        password,
        timeout=5.0,
    )
    assert status == 200, f"GET /_api/view failed on {database}: HTTP {status} {data}"
    return {row["name"] for row in data.get("result", []) if isinstance(row, dict) and row.get("name")}


def arango_collection_count(endpoint: str, database: str, username: str, password: str, collection: str) -> int:
    status, data = arango_http_json(
        "GET",
        f"{endpoint.rstrip('/')}/_db/{quote(database)}/_api/collection/{quote(collection)}/count",
        username,
        password,
        timeout=5.0,
    )
    assert status == 200, f"GET count failed for {database}.{collection}: HTTP {status} {data}"
    return int(data["count"])


@pytest.fixture()
def isolated_alexandria_db() -> dict[str, str]:
    """Provide an ephemeral alexandria_e2e_test_<uuid8> DB on :8532 and drop it on teardown."""
    user, pw = require_alexandria_8532()
    db_name = f"alexandria_e2e_test_{uuid.uuid4().hex[:8]}"
    assert_safe_test_target(ALEXANDRIA_ENDPOINT, db_name)

    drop_url = f"{ALEXANDRIA_ENDPOINT}/_api/database/{quote(db_name)}"
    arango_http_json("DELETE", drop_url, user, pw, timeout=5.0)
    try:
        yield {
            "endpoint": ALEXANDRIA_ENDPOINT,
            "database": db_name,
            "username": user,
            "password": pw,
        }
    finally:
        assert_safe_test_target(ALEXANDRIA_ENDPOINT, db_name)
        arango_http_json("DELETE", drop_url, user, pw, timeout=5.0)


# ---------------------------------------------------------------------------
# Subprocess CLI runner & script/artifact helpers
# ---------------------------------------------------------------------------

def require_script(script_path: Path) -> Path:
    assert script_path.exists(), (
        f"Required CLI script missing: {script_path.relative_to(REPO_ROOT)}. "
        "Target milestone deliverable has not been implemented yet."
    )
    return script_path


def run_cli(
    args: list[str],
    *,
    env_overrides: dict[str, str | None] | None = None,
    clear_arango_env: bool = False,
    timeout: float = 120.0,
) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    if clear_arango_env:
        for key in list(env):
            if key.startswith(("ARANGO_", "ALEXANDRIA_ARANGO_", "HIVE_ARANGO_", "DARWIN_ARANGO_")):
                env.pop(key, None)
    env["PYTHONPATH"] = f"{REPO_ROOT}:{REPO_ROOT / 'src'}"
    if env_overrides:
        for k, v in env_overrides.items():
            if v is None:
                env.pop(k, None)
            else:
                env[k] = v
    return subprocess.run(
        [PYTHON_EXE, *args],
        cwd=str(REPO_ROOT),
        env=env,
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    assert path.exists(), f"Expected JSONL artifact missing: {path}"
    rows: list[dict[str, Any]] = []
    for idx, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not line.strip():
            continue
        try:
            rows.append(json.loads(line))
        except json.JSONDecodeError as exc:
            raise AssertionError(f"Invalid JSON on line {idx} of {path}: {exc}") from exc
    return rows


def read_inventory_report(out_dir: Path) -> dict[str, Any]:
    path = out_dir / "corpus_inventory_report.json"
    assert path.exists(), f"Expected inventory report missing: {path}"
    data = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(data, dict), f"Inventory report must be JSON object, got {type(data)}"
    return data


def report_metric(report: dict[str, Any], *keys: str) -> Any:
    """Read a metric from top-level or nested summary/counts dict."""
    containers = [report]
    for sub in ("summary", "counts", "totals", "inventory"):
        val = report.get(sub)
        if isinstance(val, dict):
            containers.append(val)
    for container in containers:
        for k in keys:
            if k in container:
                return container[k]
    raise AssertionError(f"Missing any of keys {keys!r} in inventory report keys={sorted(report.keys())}")


def report_entries(report: dict[str, Any]) -> list[dict[str, Any]]:
    for key in ("entries", "files", "items", "records", "pdfs", "uniquePdfs", "unique_documents", "outcomes"):
        val = report.get(key)
        if isinstance(val, list):
            return [x for x in val if isinstance(x, dict)]
        if isinstance(val, dict) and key == "outcomes":
            # Outcomes may be a dict of status -> list or count
            collected: list[dict[str, Any]] = []
            for v in val.values():
                if isinstance(v, list):
                    collected.extend(x for x in v if isinstance(x, dict))
            if collected:
                return collected
    return []


def assert_retrieval_authority(packet: dict[str, Any]) -> None:
    assert packet.get("authority") == "retrieval_context_only", (
        f"Retrieval packet missing top-level authority='retrieval_context_only': "
        f"got {packet.get('authority')!r} (keys={sorted(packet.keys())})"
    )
    assert packet.get("sourceAuthority") == "retrieval_context_only", (
        f"Retrieval packet missing sourceAuthority='retrieval_context_only': "
        f"got {packet.get('sourceAuthority')!r}"
    )
    disclaimer = str(packet.get("disclaimer", "") or packet.get("note", "")).lower()
    assert "retrieval" in disclaimer and "not" in disclaimer and "proof" in disclaimer, (
        f"Retrieval output lacks non-proof disclaimer: {disclaimer!r}"
    )
    hits = packet.get("hits", [])
    for idx, h in enumerate(hits):
        assert isinstance(h, dict), f"Hit[{idx}] is not a dict: {type(h)!r}"
        assert h.get("authority") == "retrieval_context_only", (
            f"Hit[{idx}] authority={h.get('authority')!r} != 'retrieval_context_only'"
        )
        assert h.get("sourceAuthority") == "retrieval_context_only", (
            f"Hit[{idx}] sourceAuthority={h.get('sourceAuthority')!r} != 'retrieval_context_only'"
        )


def hit_field(hit: dict[str, Any], *keys: str) -> Any:
    containers = [hit]
    for sub in ("source", "chunk", "provenance", "document", "metadata"):
        val = hit.get(sub)
        if isinstance(val, dict):
            containers.append(val)
    chunk = hit.get("chunk")
    if isinstance(chunk, dict) and isinstance(chunk.get("provenance"), dict):
        containers.append(chunk["provenance"])
    for container in containers:
        for k in keys:
            if k in container and container[k] is not None:
                return container[k]
    return None


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        while True:
            chunk = fh.read(65536)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()


def snapshot_tree(root: Path) -> list[tuple[str, int, int, str]]:
    snap: list[tuple[str, int, int, str]] = []
    for p in sorted(root.rglob("*")):
        rel = p.relative_to(root).as_posix()
        if p.is_symlink():
            snap.append((rel, -1, -1, f"symlink:{os.readlink(p)}"))
        elif p.is_file():
            st = p.stat()
            snap.append((rel, st.st_mtime_ns, st.st_size, sha256_file(p)))
        elif p.is_dir():
            snap.append((rel, 0, 0, "dir"))
    return snap


# ---------------------------------------------------------------------------
# Deterministic Synthetic PDF Builders (reportlab + PIL + pypdf)
# ---------------------------------------------------------------------------

def _draw_lines(c: canvas.Canvas, lines: list[str], *, font_name: str, font_size: int = 10, start_y: int = 740) -> None:
    y = start_y
    c.setFont(font_name, font_size)
    for line in lines:
        if y < 60:
            c.showPage()
            c.setFont(font_name, font_size)
            y = 740
        c.drawString(56, y, line)
        y -= 15


def build_structured_math_pdf(
    dest: Path,
    *,
    title: str = "Clifford Spinors and Krein Completion",
    topic: str = "clifford",
    pages: int = 2,
    include_ligatures: bool = False,
    include_running_header: bool = False,
    running_header: str = "Journal of Mathematical Physics Vol 12",
    mutual_cycle: bool = False,
    extra_body_chars: int = 0,
) -> Path:
    dest.parent.mkdir(parents=True, exist_ok=True)
    font_name = _ensure_unicode_font()
    c = canvas.Canvas(str(dest), pagesize=letter)
    c.setTitle(title)

    if topic == "clifford":
        page1_lines = [
            title,
            "1. Introduction",
            "We analyze Dirac-Hestenes spinor fields and Krein tripartite completion on Cl(1,1).",
            "\\label{sec:intro}",
            "Definition 1.1 (Clifford Algebra): Let (V, q) be a quadratic space over R.",
            "The Clifford algebra Cl(V, q) satisfies v^2 = q(v) * 1 for all v in V. \\label{def:clifford}",
            "Theorem 1.2 (Hestenes Spinor Decomposition): Every even multivector decomposes",
            "into a rotor and a Krein-self-adjoint factor using Definition 1.1. \\label{thm:hestenes}",
            "Proof. By Definition 1.1 and Ref. \\ref{def:clifford}, apply the canonical involution",
            "on Cl(1,1) to verify idempotent spinor projection and parity invariance. QED.",
            "(1) D_H psi = m psi gamma_0",
        ]
        page2_lines = [
            "2. Modular Spectral Context",
            "Theorem 2.1 (Krein Spectral Bridge): As shown in Theorem 1.2 (\\ref{thm:hestenes}),",
            "the Krein space inner product induces a non-degenerate fundamental symmetry J.",
            "Proof. Follow Theorem 1.2 directly via orthogonal projections P_+ and P_-. QED.",
            "References",
            "[1] D. Hestenes and G. Sobczyk, Clifford Algebra to Geometric Calculus (1984) \\cite{Hestenes1984}.",
            "[2] J.-M. Souriau, Structure des systemes dynamiques (1970) \\cite{Souriau1970}.",
        ]
    elif topic == "octonions":
        page1_lines = [
            title,
            "1. Split Octonions and G2 Automorphisms",
            "Definition 1.1 (Albert Vector): An Albert vector lies in the exceptional Jordan algebra J_3(O).",
            "Theorem 1.2 (G2 Orbit Stability): The automorphism group of split octonions is non-compact G2.",
            "Proof. Using Definition 1.1, compute the cubic norm invariance under split G2 generators. QED.",
            "(1) N(x) = det_3(x)",
        ]
        page2_lines = [
            "2. Exceptional Jordan Triality",
            "Remark 2.1: Compare Dray and Manogue [1] \\cite{Dray2015} and McCrimmon [2].",
            "References",
            "[1] T. Dray, The Geometry of the Octonions (2015).",
            "[2] K. McCrimmon, A Taste of Jordan Algebras (2004).",
        ]
    elif topic == "peirce":
        page1_lines = [
            title,
            "1. Peirce Projections and Drazin Inverse",
            "Definition 1.1 (Peirce Projector): Let P and Q be orthogonal projections in a von Neumann algebra.",
            "Theorem 1.2 (Drazin Factorization): By Definition 1.1, the product P Q admits a Drazin inverse.",
            "Proof. The idempotent decomposition on the Peirce corner yields zero nilpotent index drift. QED.",
        ]
        page2_lines = [
            "2. Souriau Thermodynamics",
            "Theorem 2.1 (Metriplectic Bracket): Following Theorem 1.2, Fisher-Rao entropy flow commutes.",
            "References",
            "[1] F. Barbaresco, Souriau Lie group thermodynamics, SPILG (2020) \\cite{Souriau1970}.",
        ]
    else:
        page1_lines = [
            title,
            "1. Mathematical Preliminaries",
            "Definition 1.1 (Spectral Triple): A triple (A, H, D) with bounded commutators.",
            "Theorem 1.2 (Main Convergence): By Definition 1.1, the KMS modular flow stabilizes.",
            "Proof. Apply Tomita-Takesaki modular conjugation J to conclude Theorem 1.2. QED.",
        ]
        page2_lines = [
            "2. Further Consequences",
            "References",
            "[1] A. Connes, Noncommutative Geometry (1994).",
        ]

    if include_ligatures:
        page1_lines.append("We study arti\ufb01cial gauge \ufb01elds and \ufb02ow \ufb00ects in Souriau mechanics.")
        page1_lines.append("Page break marker check and \ufb01ber bundle normalization.")

    if mutual_cycle:
        page1_lines = [
            title,
            "1. Cyclic Cross-References",
            "Theorem 1 (Mutual Alpha): Follows from Lemma 2 (\\ref{lem:two}). \\label{thm:one}",
            "Lemma 2 (Mutual Beta): Follows from Theorem 1 (\\ref{thm:one}). \\label{lem:two}",
            "Proof. Combine Theorem 1 and Lemma 2. QED.",
        ]

    if extra_body_chars > 0:
        sentence = "Theorem 3.1 (Large Formalization Block): Every split Krein projector preserves the quadratic form. "
        repeats = max(1, (extra_body_chars // len(sentence)) + 1)
        huge = sentence * repeats
        # Wrap into 85-char lines across multiple pages
        wrapped = [huge[i : i + 85] for i in range(0, min(len(huge), extra_body_chars + 200), 85)]
        page_blocks = [page1_lines + wrapped]
    else:
        page_blocks = [page1_lines, page2_lines]
        for extra_idx in range(3, pages + 1):
            page_blocks.append([
                f"{extra_idx}. Continuation Section {extra_idx}",
                f"Proposition {extra_idx}.1: Additional spectral property on page {extra_idx}.",
                "Proof. Immediate from earlier estimates. QED.",
            ])

    for idx, block in enumerate(page_blocks, start=1):
        if include_running_header:
            c.setFont(font_name, 9)
            c.drawString(56, 770, running_header)
            c.drawString(480, 30, f"Page {idx}")
        _draw_lines(c, block, font_name=font_name, start_y=735 if include_running_header else 750)
        c.showPage()
    c.save()
    return dest


def build_text_pdf(dest: Path, pages_lines: list[list[str]], *, title: str = "Synthetic PDF") -> Path:
    dest.parent.mkdir(parents=True, exist_ok=True)
    font_name = _ensure_unicode_font()
    c = canvas.Canvas(str(dest), pagesize=letter)
    c.setTitle(title)
    for lines in pages_lines:
        _draw_lines(c, lines, font_name=font_name, start_y=740)
        c.showPage()
    c.save()
    return dest


def build_scanned_zero_text_pdf(dest: Path, *, pages: int = 2) -> Path:
    dest.parent.mkdir(parents=True, exist_ok=True)
    c = canvas.Canvas(str(dest), pagesize=letter)
    for idx in range(pages):
        img = Image.new("RGB", (300, 120), color=(245, 245, 245))
        draw = ImageDraw.Draw(img)
        draw.rectangle([10, 10, 290, 110], outline=(30, 30, 30), width=3)
        draw.line([10, 10, 290, 110], fill=(80, 80, 80), width=2)
        buf = io.BytesIO()
        img.save(buf, format="PNG")
        buf.seek(0)
        c.drawImage(ImageReader(buf), 72, 500, width=300, height=120)
        c.showPage()
    c.save()
    return dest


def build_permission_encrypted_pdf(dest: Path, lines: list[str] | None = None, owner_pw: str = "owner_only_secret") -> Path:
    raw = dest.with_suffix(".tmp_plain.pdf")
    build_text_pdf(
        raw,
        [lines or [
            "1. Permission Protected Section",
            "Definition 1.1 (Symplectic Moment Map): Souriau coadjoint orbit action on Poisson manifold.",
            "Theorem 1.2: Permission-encrypted PDFs with empty user password remain readable.",
            "Proof. Standard coadjoint equivariance completes the argument. QED.",
        ]],
        title="Permission Protected Math PDF",
    )
    reader = PdfReader(str(raw))
    writer = PdfWriter()
    for page in reader.pages:
        writer.add_page(page)
    # Empty user password + owner password => encrypted metadata but readable without password
    writer.encrypt(user_password="", owner_password=owner_pw, permissions_flag=0)
    with dest.open("wb") as fh:
        writer.write(fh)
    raw.unlink(missing_ok=True)
    return dest


def build_user_locked_encrypted_pdf(dest: Path, user_pw: str = "e2e_locked_secret") -> Path:
    raw = dest.with_suffix(".tmp_plain.pdf")
    build_text_pdf(raw, [["Locked content that cannot be extracted without user password."]], title="Locked PDF")
    reader = PdfReader(str(raw))
    writer = PdfWriter()
    for page in reader.pages:
        writer.add_page(page)
    writer.encrypt(user_password=user_pw, owner_password=user_pw + "_owner")
    with dest.open("wb") as fh:
        writer.write(fh)
    raw.unlink(missing_ok=True)
    return dest


def build_zero_byte_pdf(dest: Path) -> Path:
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(b"")
    return dest


def build_corrupt_pdf(dest: Path) -> Path:
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(b"%PDF-1.4\n1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n%truncated_corrupt_xref\n\xff\xfe\x00")
    return dest


def build_pua_noise_pdf(dest: Path) -> Path:
    pua_block = "".join(chr(code) for code in range(0xF000, 0xF020)) * 4
    rep_block = "\ufffd" * 80
    return build_text_pdf(
        dest,
        [[
            "1. Noisy OCR Encoding Artifact",
            f"Corrupted glyph stream: {rep_block}",
            f"Private use area glyphs: {pua_block}",
            "Theorem 1.1: Residual readable statement about Krein spaces and projections.",
        ]],
        title="PUA Encoding Noise PDF",
    )


def build_png_file(dest: Path) -> Path:
    dest.parent.mkdir(parents=True, exist_ok=True)
    img = Image.new("RGB", (64, 64), color=(200, 210, 220))
    img.save(dest, format="PNG")
    return dest
