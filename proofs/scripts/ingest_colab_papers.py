#!/usr/bin/env python3
"""Ingest papers from CoLab/Crossref links into ArangoDB.

Pipeline:
1. Ensure ArangoDB is running (best-effort start if possible).
2. Ensure `aiclaw_rag` DB exists with collections:
   - literature_nodes (document)
   - citation_edges (edge)
3. Resolve paper metadata from a CoLab article page.
4. Resolve references via Crossref when available.
5. For each paper DOI:
   - skip if already present in ArangoDB by DOI
   - resolve best paper URL
   - try to download PDF (if possible)
   - chunk text using lightweight section-based chunking
   - ingest one document per paper with chunked content into `literature_nodes`
6. Create citation edges where possible.
"""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import os
import re
import subprocess
import sys
import textwrap
import time
import urllib.parse
from dataclasses import dataclass, field
from typing import Dict, List, Optional

import requests
from requests.auth import HTTPBasicAuth
from xml.etree import ElementTree as ET

ARANGO_URL = os.environ.get("ARANGO_URL", "http://localhost:8529")
ARANGO_USER = os.environ.get("ARANGO_USER", "root")
ARANGO_PASSWORD = os.environ.get("ARANGO_PASSWORD", "")
ARANGO_DB = os.environ.get("ARANGO_DB", "aiclaw_rag")
NODE_COLL = "literature_nodes"
EDGE_COLL = "citation_edges"


auth = HTTPBasicAuth(ARANGO_USER, ARANGO_PASSWORD)


def _safe_get(path: str):
    return requests.get(ARANGO_URL + path, auth=auth, timeout=20)


def _safe_post(path: str, payload):
    return requests.post(
        ARANGO_URL + path,
        json=payload,
        auth=auth,
        headers={"Content-Type": "application/json"},
        timeout=20,
    )


def _safe_delete(path: str):
    return requests.delete(ARANGO_URL + path, auth=auth, timeout=20)


def ensure_arango_running():
    url = f"{ARANGO_URL}/_api/version"
    try:
        r = requests.get(url, auth=auth, timeout=3)
        if r.status_code == 200:
            print(f"✅ ArangoDB reachable: {r.json().get('version')}")
            return True
        print(f"⚠️ ArangoDB reachable but unauthorized or bad auth: {r.status_code} {r.text[:120]}")
    except Exception as e:
        print(f"⚠️ ArangoDB not reachable: {e}")

    # best-effort start attempt
    print("ℹ️ Trying to start ArangoDB service...")
    for cmd in [
        ["systemctl", "start", "arangodb3"],
        ["arangod", "--daemon"],
    ]:
        try:
            proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
            if proc.returncode == 0:
                time.sleep(1)
                r = requests.get(url, auth=auth, timeout=10)
                if r.status_code == 200:
                    print("✅ ArangoDB started")
                    return True
        except Exception:
            pass
    return False


def ensure_db_and_collections():
    base = f"{ARANGO_URL}/_api/database"
    data = _safe_get(f"/_api/database")
    dbs = []
    if data.status_code == 200:
        dbs = data.json().get("result", [])
    else:
        raise RuntimeError(f"Cannot list databases: {data.status_code} {data.text}")

    if ARANGO_DB not in dbs:
        print(f"🛠️ Creating database {ARANGO_DB}")
        r = _safe_post(f"/_api/database", {"name": ARANGO_DB})
        if r.status_code not in (200, 201):
            raise RuntimeError(f"Cannot create database: {r.status_code} {r.text}")

    # collection creation helper
    def db_get(route):
        return requests.get(
            f"{ARANGO_URL}/_db/{ARANGO_DB}{route}",
            auth=auth,
            timeout=20,
        )

    def db_post(route, payload):
        return requests.post(
            f"{ARANGO_URL}/_db/{ARANGO_DB}{route}",
            json=payload,
            auth=auth,
            headers={"Content-Type": "application/json"},
            timeout=20,
        )

    existing = [c["name"] for c in db_get("/_api/collection").json().get("result", [])]

    if NODE_COLL not in existing:
        print(f"🧱 creating collection {NODE_COLL}")
        r = db_post("/_api/collection", {"name": NODE_COLL, "type": 2})
        if r.status_code not in (200, 201):
            raise RuntimeError(f"Cannot create {NODE_COLL}: {r.status_code} {r.text}")

    if EDGE_COLL not in existing:
        print(f"🧱 creating collection {EDGE_COLL}")
        r = db_post("/_api/collection", {"name": EDGE_COLL, "type": 3})
        if r.status_code not in (200, 201):
            raise RuntimeError(f"Cannot create {EDGE_COLL}: {r.status_code} {r.text}")


def db_collection_exists(collection: str, key: str) -> bool:
    r = requests.head(
        f"{ARANGO_URL}/_db/{ARANGO_DB}/_api/document/{collection}/{urllib.parse.quote(key, safe='')}" ,
        auth=auth,
        timeout=10,
    )
    return r.status_code == 200


def upsert_node(doc: dict):
    collection = NODE_COLL
    db_url = f"{ARANGO_URL}/_db/{ARANGO_DB}/_api/document/{collection}/{doc['_key']}"
    existing = requests.get(db_url, auth=auth, timeout=10)

    if existing.status_code == 200:
        r = requests.patch(
            db_url,
            json=doc,
            headers={"Content-Type": "application/json"},
            auth=auth,
            timeout=10,
        )
    else:
        r = requests.post(
            f"{ARANGO_URL}/_db/{ARANGO_DB}/_api/document/{collection}",
            json=doc,
            headers={"Content-Type": "application/json"},
            auth=auth,
            timeout=10,
        )

    if r.status_code not in (200, 201, 202):
        raise RuntimeError(f"Cannot write node {doc.get('_key')}: {r.status_code} {r.text}")


def add_edge(fr: str, to: str, relation: str):
    edge_key = hashlib.sha1((fr + '|' + to + '|' + relation).encode()).hexdigest()[:24]
    key = f"{fr.replace('/', '_')}__{to.replace('/', '_')}__{relation}"
    key = key[:64]

    edge_doc = {
        "_key": key,
        "_from": fr,
        "_to": to,
        "relation": relation,
        "created_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    db_url = f"{ARANGO_URL}/_db/{ARANGO_DB}/_api/document/{EDGE_COLL}/{edge_key}"
    r = requests.get(db_url, auth=auth, timeout=10)
    if r.status_code == 200:
        return
    requests.post(
        f"{ARANGO_URL}/_db/{ARANGO_DB}/_api/document/{EDGE_COLL}",
        json=edge_doc,
        headers={"Content-Type": "application/json"},
        auth=auth,
        timeout=10,
    )


def to_key(s: str) -> str:
    s = (s or "")[:128].lower().strip()
    s = re.sub(r"[^a-z0-9._-]", "_", s)
    s = re.sub(r"_+", "_", s)
    return s[:120] or "paper"


def normalize_doi(v: str) -> str:
    return v.strip().lower().replace("http://", "").replace("https://", "")


def find_paper_by_doi(doi: str) -> bool:
    query = "FOR d IN literature_nodes FILTER d.doi == @doi LIMIT 1 RETURN d._key"
    r = requests.post(
        f"{ARANGO_URL}/_db/{ARANGO_DB}/_api/cursor",
        json={"query": query, "bindVars": {"doi": doi}},
        headers={"Content-Type": "application/json"},
        auth=auth,
        timeout=10,
    )
    if r.status_code != 201:
        raise RuntimeError(f"Lookup failed: {r.status_code} {r.text}")
    return bool(r.json().get("result"))


def parse_colab_item(url: str) -> dict:
    r = requests.get(url, timeout=40)
    r.raise_for_status()
    html_text = r.text

    marker = ' item="'
    candidates = []
    idx = 0
    while True:
        i = html_text.find(marker, idx)
        if i == -1:
            break
        start = i + len(marker)
        end = html_text.find('"', start)
        if end == -1:
            break
        raw = html_text[start:end]
        if raw.startswith("{&quot;id&quot;"):
            obj_json = html.unescape(raw)
            try:
                obj = json.loads(obj_json)
                if "doi" in obj:
                    candidates.append(obj)
            except Exception:
                pass
        idx = end + 1

    if candidates:
        return candidates[0]

    raise RuntimeError("Could not parse CoLab article metadata JSON")


def extract_doi_from_url(url: str) -> str:
    parsed = urllib.parse.urlparse(url)
    parts = parsed.path.split("/")
    if len(parts) >= 3:
        return urllib.parse.unquote(parts[-1]).strip()
    m = re.search(r"doi[:/]+([0-9][^/?#]+)", url)
    if not m:
        raise ValueError("No DOI found in URL")
    return m.group(1)


def crossref_metadata(doi: str) -> dict:
    encoded = urllib.parse.quote(doi, safe="")
    r = requests.get(f"https://api.crossref.org/works/{encoded}", timeout=30)
    if r.status_code != 200:
        raise RuntimeError(f"Crossref failed for {doi}: {r.status_code}")
    return r.json().get("message", {})


def crossref_references(doi: str, max_items: int) -> List[str]:
    refs = crossref_metadata(doi).get("reference", [])
    out = []
    for ref in refs:
        d = ref.get("DOI")
        if d:
            out.append(str(d).lower())
        if len(out) >= max_items:
            break
    return out


def parse_arxiv_from_crossref(doi: str, title: str, authors: List[str]) -> Optional[str]:
    # Crossref sometimes stores arXiv relation
    try:
        msg = crossref_metadata(doi)
        relation = msg.get("relation", {})
        for rels in relation.values():
            for rel in rels or []:
                idx = rel.get("id") or ""
                if idx.lower().startswith("arxiv:"):
                    return idx.split(":", 1)[-1]
    except Exception:
        pass

    # Query arxiv by title, limited to 5 results, pick first
    if not title:
        return None

    q = urllib.parse.quote(f'ti:"{title}"')
    url = f"https://export.arxiv.org/api/query?search_query={q}&max_results=1"
    r = requests.get(url, timeout=30)
    if r.status_code != 200:
        return None

    try:
        root = ET.fromstring(r.text)
        ns = {"atom": "http://www.w3.org/2005/Atom"}
        entry = root.find("atom:entry", ns)
        if entry is None:
            return None
        arxiv_id_url = entry.findtext("atom:id", namespaces=ns) or ""
        m = re.search(r"arxiv\.org/abs/(.+)$", arxiv_id_url)
        if m:
            return m.group(1)
    except Exception:
        pass
    return None


def discover_pdf_url(doi: str, meta: dict) -> Optional[str]:
    # 1) direct URL/pdf hints
    for candidate in [
        meta.get("url"),
        meta.get("link", [{}])[0].get("URL") if isinstance(meta.get("link"), list) and meta.get("link") else None,
        f"https://doi.org/{doi}",
    ]:
        if not candidate:
            continue
        try:
            r = requests.get(candidate, allow_redirects=True, timeout=30)
            ctype = (r.headers.get("content-type") or "").lower()
            final = r.url.lower()
            if final.endswith('.pdf') or 'pdf' in ctype:
                return final
            html = r.text[:8000].lower()
            m = re.search(r'href="([^"]+\.pdf[^"]*)"', html)
            if m:
                return urllib.parse.urljoin(candidate, m.group(1))
        except Exception:
            pass

    # 2) arXiv lookup if available
    arxiv_id = parse_arxiv_from_crossref(doi, meta.get("title", [""])[0] if isinstance(meta.get("title"), list) else "", [])
    if arxiv_id:
        return f"https://arxiv.org/pdf/{arxiv_id}.pdf"

    # 3) query unpaywall-ish endpoint for OA pdf requires email, but many works may work anyway
    return None


def clean_text(t: str) -> str:
    t = html.unescape(t or "")
    t = re.sub(r"\r", "", t)
    t = re.sub(r"\n{3,}", "\n\n", t)
    return t.strip()


def chunk_ast_like(text: str, max_chars: int = 2400) -> List[Dict[str, str]]:
    text = clean_text(text)
    if not text:
        return []

    section_break = re.compile(
        r"(?m)^(?:\d+\.?\s*)?(?:Abstract|Introduction|Methods|Results|Discussion|Conclusion|References|Appendix|Summary|Background|Theory|Model|Experiment|Conclusion|Acknowledgements)\b"
    )
    lines = text.splitlines()
    chunks: List[Dict[str, str]] = []
    current_title = "Frontmatter"
    current_lines: List[str] = []

    def flush():
        if not current_lines:
            return
        body = "\n".join(current_lines).strip()
        if not body:
            return
        chunks.append({"section": current_title, "text": body[:max_chars] if len(body) > max_chars * 1.2 else body})

    for line in lines:
        if section_break.match(line.strip() or ""):
            flush()
            current_title = line.strip()[:120] or "Section"
            current_lines = []
        else:
            current_lines.append(line)
            if sum(len(x) + 1 for x in current_lines) > max_chars:
                body = "\n".join(current_lines).strip()
                # split by paragraph if needed
                parts = body.split("\n\n")
                if len(parts) > 1:
                    for p in parts:
                        if p.strip():
                            chunks.append({"section": current_title, "text": p.strip()[:max_chars]})
                    current_lines = []

    flush()

    # fallback split if still empty
    if not chunks:
        words = text.split()
        cur = []
        length = 0
        idx = 0
        for w in words:
            if length + len(w) + 1 > max_chars:
                chunks.append({"section": f"chunk_{idx}", "text": " ".join(cur)})
                idx += 1
                cur = [w]
                length = len(w) + 1
            else:
                cur.append(w)
                length += len(w) + 1
        if cur:
            chunks.append({"section": f"chunk_{idx}", "text": " ".join(cur)})

    return chunks


def download_and_extract(doi: str, pdf_url: Optional[str]) -> str:
    if not pdf_url:
        return ""

    out_dir = "/tmp/paper_ingest"
    os.makedirs(out_dir, exist_ok=True)
    pdf_path = os.path.join(out_dir, to_key(doi)[:64] + ".pdf")

    try:
        r = requests.get(pdf_url, stream=True, timeout=45, allow_redirects=True)
        if r.status_code != 200 or not r.headers.get("content-type", "").lower().startswith("application/pdf"):
            return ""
        with open(pdf_path, "wb") as f:
            for chunk in r.iter_content(chunk_size=1 << 16):
                if chunk:
                    f.write(chunk)
    except Exception:
        return ""

    # convert to text via pdftotext
    txt_path = pdf_path + ".txt"
    try:
        cp = subprocess.run([
            "pdftotext",
            pdf_path,
            txt_path,
        ], capture_output=True, text=True, timeout=60)
        if cp.returncode != 0:
            return ""
        with open(txt_path, "r", encoding="utf-8", errors="ignore") as f:
            return f.read()
    except Exception:
        return ""


def ingest_single_paper(paper: dict):
    doi = normalize_doi(paper.get("doi", ""))
    if not doi:
        return

    try:
        if find_paper_by_doi(doi):
            print(f"⏭️ already in DB: {doi}")
            return
    except Exception as e:
        print(f"lookup failed for {doi}: {e}")

    meta = {}
    abstract = paper.get("abstract") or paper.get("description") or ""
    if not abstract and paper.get("doi"):
        try:
            meta = crossref_metadata(doi)
            abstract = meta.get("abstract") or abstract
        except Exception:
            meta = {}

    pdf_url = discover_pdf_url(doi, meta)
    text = download_and_extract(doi, pdf_url)

    chunks = chunk_ast_like(text if text else (clean_text(abstract) or "No full-text content available."), max_chars=2200)

    paper_key = to_key(f"doi_{doi}")
    doc = {
        "_key": paper_key,
        "title": paper.get("title", "Unknown")[:500],
        "doi": doi,
        "arxiv_id": paper.get("arxiv_id") or meta.get("arxiv_id"),
        "year": paper.get("year") or meta.get("published-print", {}).get("date-parts", [[None]])[0][0],
        "journal": paper.get("journal", {}).get("name") if isinstance(paper.get("journal"), dict) else None,
        "authors_string": paper.get("authors_string"),
        "source": paper.get("source", "colab/crossref"),
        "published_date": paper.get("published_date"),
        "url": paper.get("url_primary") or paper.get("url") or paper.get("link") or None,
        "pdf_url": pdf_url,
        "status": "literature",
        "chunks": chunks,
        "chunk_count": len(chunks),
        "created_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }

    # remove huge None values
    doc = {k: v for k, v in doc.items() if v is not None and v != ""}
    upsert_node(doc)

    # add edge from chunks omitted: chunks kept inline
    print(f"✅ ingested {doi} ({len(chunks)} chunks)")


def gather_all_targets(url: str, max_refs: int) -> List[str]:
    item = parse_colab_item(url)
    dois = [normalize_doi(item.get("doi", ""))]

    if max_refs > 0 and item.get("doi"):
        try:
            refs = crossref_references(item["doi"], max_refs)
            for d in refs:
                if d and d not in dois:
                    dois.append(normalize_doi(d))
        except Exception as e:
            print(f"crossref refs unavailable: {e}")

    return list(dict.fromkeys([d for d in dois if d]))


def paper_metadata_from_doi(doi: str) -> dict:
    meta = crossref_metadata(doi)
    title = ""
    if isinstance(meta.get("title"), list) and meta["title"]:
        title = meta["title"][0]

    # Authors as short string
    authors = []
    for a in meta.get("author", [])[:8]:
        name = [a.get("family", ""), a.get("given", "")]
        authors.append(" ".join([p for p in name if p]).strip())
    return {
        "doi": doi,
        "title": title,
        "abstract": meta.get("abstract", ""),
        "year": (meta.get("published-print") or meta.get("published-online") or {}).get("date-parts", [[None]])[0][0],
        "published_date": (meta.get("published-print") or meta.get("published-online") or {}).get("date-parts", [[None]])[0][0],
        "journal": (meta.get("container-title") or [None])[0],
        "authors_string": ", ".join(authors),
        "source": meta.get("container-title", [None])[0] or "crossref",
        "url": meta.get("URL"),
        "arxiv_id": None,
    }


def build_paper_payload(doi: str, fallback_title: Optional[str] = None) -> dict:
    try:
        return paper_metadata_from_doi(doi)
    except Exception:
        # fallback only DOI only
        return {
            "doi": doi,
            "title": fallback_title or doi,
            "source": "colab/crossref",
        }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--url", default="https://colab.ws/articles/10.1103%2Ffdqr-mnch", help="CoLab article URL")
    parser.add_argument("--max-refs", type=int, default=5, help="How many references to pull from Crossref")
    parser.add_argument("--dry-run", action="store_true", help="parse only, do not write DB")
    args = parser.parse_args()

    if not ensure_arango_running():
        print("❌ Could not ensure ArangoDB running")
        return 1

    ensure_db_and_collections()

    try:
        dois = gather_all_targets(args.url, args.max_refs)
    except Exception as e:
        print(f"❌ Failed to read source URL: {e}")
        return 1

    print(f"🔎 Target DOIs ({len(dois)}):")
    for d in dois:
        print(" -", d)

    if args.dry_run:
        print("DRY RUN: no writes performed")
        return 0

    for doi in dois:
        try:
            paper = build_paper_payload(doi)
            ingest_single_paper(paper)

            # create citation edges for reference chain
            try:
                refs = crossref_references(doi, max_items=3)
                for rdoi in refs:
                    if find_paper_by_doi(rdoi):
                        add_edge(f"literature_nodes/{to_key('doi_'+doi)}", f"literature_nodes/{to_key('doi_'+rdoi)}", "cites")
            except Exception:
                pass
        except Exception as e:
            print(f"⚠️ Failed ingest for {doi}: {e}")

    print("✅ done")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
