#!/usr/bin/env python3
"""Index Lean corpora into an OpenClaw-compatible Arango memory graph.

The output schema mirrors ``arango-solutions/openclaw``:

- vertex collections: ``memories``, ``entities``, ``sessions``, ``daily_logs``
- edge collections: ``memory_edges``, ``entity_edges``
- graph: ``brain_graph``

This importer is intentionally a context layer. It does not promote graph
proximity, embeddings, or imported external code into proof authority. Lean
source files and compiled declarations remain the owner surface.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Iterator


if __package__ in (None, ""):
    ROOT = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(ROOT))
    sys.path.insert(0, str(ROOT / "src"))
else:
    ROOT = Path(__file__).resolve().parents[2]

from igf.config import (  # noqa: E402
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from igf.graph import (  # noqa: E402
    ArangoHttpTarget,
    collection_count,
    create_collection,
    db_url,
    ensure_database,
    ensure_index,
    import_jsonl,
    list_collections,
    request_json,
    truncate_collection,
)
from tools.pathing import normalize_user_path, repo_root  # noqa: E402


DECL_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|coinductive|instance|axiom|opaque|constant|example)"
    r"(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?"
)
IMPORT_RE = re.compile(r"^\s*import\s+(.+?)\s*$")
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*|\d+")
SKIP_DIR_NAMES = {
    ".git",
    ".hg",
    ".svn",
    "__pycache__",
    ".pytest_cache",
    ".mypy_cache",
    ".venv",
    ".venv-py312",
    ".venv-123",
    ".runtime",
    "build",
    ".build",
    "lake-packages",
    "node_modules",
}


@dataclass(frozen=True)
class CorpusRoot:
    path: Path
    corpus: str
    package: str
    include_nested_lake: bool = False


@dataclass(frozen=True)
class LeanDecl:
    kind: str
    name: str
    line: int


@dataclass(frozen=True)
class LeanChunk:
    path: Path
    corpus: str
    package: str
    module: str
    line_start: int
    line_end: int
    content: str
    decls: list[LeanDecl]
    imports: list[str]
    ordinal: int


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def stable_key(*parts: object, prefix: str = "") -> str:
    raw = "\x1f".join(str(part) for part in parts)
    digest = hashlib.sha256(raw.encode("utf-8")).hexdigest()[:32]
    return f"{prefix}{digest}" if prefix else digest


def rel_path(path: Path) -> str:
    try:
        return path.resolve().relative_to(repo_root().resolve()).as_posix()
    except ValueError:
        return path.resolve().as_posix()


def safe_module_from_path(path: Path, root: CorpusRoot) -> str:
    try:
        rel = path.resolve().relative_to(root.path.resolve())
    except ValueError:
        rel = path.name
        parts = [Path(str(rel)).stem]
    else:
        if rel.name == "lakefile.lean":
            return f"{root.package}.lakefile"
        parts = list(rel.with_suffix("").parts)

    if not isinstance(parts, list):
        parts = [str(parts)]
    cleaned = [part.replace("-", "_") for part in parts if part and part != "."]
    if not cleaned:
        cleaned = [path.stem.replace("-", "_")]
    module = ".".join(cleaned)
    if root.corpus == "external_refs" and cleaned[0] == root.package.replace("-", "_"):
        return module
    return module


def detect_external_package(path: Path) -> str:
    try:
        rel = path.resolve().relative_to((repo_root() / "external_refs").resolve())
    except ValueError:
        return ""
    return rel.parts[0] if rel.parts else ""


def classify_corpus(path: Path, root: CorpusRoot) -> tuple[str, str]:
    path_s = rel_path(path)
    if "/.lake/packages/mathlib/" in path_s or path_s.startswith(".lake/packages/mathlib/"):
        return "mathlib", "mathlib"
    if path_s.startswith("external_refs/atlas-lean/.lake/packages/mathlib/"):
        return "mathlib", "mathlib"
    if path_s.startswith("external_refs/"):
        package = detect_external_package(path)
        return "external_refs", package or root.package
    return root.corpus, root.package


def iter_lean_files(root: CorpusRoot) -> Iterator[Path]:
    if root.path.is_file():
        if root.path.suffix == ".lean":
            yield root.path
        return
    if not root.path.exists():
        return

    stack = [root.path]
    while stack:
        current = stack.pop()
        try:
            entries = sorted(current.iterdir(), key=lambda p: p.name)
        except OSError:
            continue
        for entry in reversed(entries):
            if entry.is_dir():
                if entry.name == ".lake" and not root.include_nested_lake:
                    continue
                if entry.name in SKIP_DIR_NAMES:
                    continue
                stack.append(entry)
            elif entry.is_file() and entry.suffix == ".lean":
                yield entry


def parse_imports(lines: list[str]) -> list[str]:
    imports: list[str] = []
    for line in lines:
        match = IMPORT_RE.match(line)
        if not match:
            continue
        imports.extend(part.strip() for part in match.group(1).split() if part.strip())
    return imports


def parse_decls(lines: list[str]) -> list[LeanDecl]:
    decls: list[LeanDecl] = []
    anon = 0
    for idx, line in enumerate(lines, start=1):
        match = DECL_RE.match(line)
        if not match:
            continue
        kind = match.group(1)
        name = match.group(2)
        if not name:
            anon += 1
            name = f"<anonymous-{kind}-{idx}-{anon}>"
        decls.append(LeanDecl(kind=kind, name=name, line=idx))
    return decls


def chunk_windows(lines: list[str], decls: list[LeanDecl], chunk_lines: int) -> list[tuple[int, int]]:
    total = len(lines)
    if total == 0:
        return []
    starts = [decl.line for decl in decls]
    windows: list[tuple[int, int]] = []
    if not starts:
        for start in range(1, total + 1, chunk_lines):
            windows.append((start, min(total, start + chunk_lines - 1)))
        return windows

    first = starts[0]
    if first > 1:
        windows.append((1, first - 1))

    for idx, start in enumerate(starts):
        end = starts[idx + 1] - 1 if idx + 1 < len(starts) else total
        while start <= end:
            chunk_end = min(end, start + chunk_lines - 1)
            windows.append((start, chunk_end))
            start = chunk_end + 1
    return windows


def iter_chunks(root: CorpusRoot, *, chunk_lines: int, max_files: int) -> Iterator[LeanChunk]:
    file_count = 0
    for path in iter_lean_files(root):
        file_count += 1
        if max_files > 0 and file_count > max_files:
            break
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        lines = text.splitlines()
        imports = parse_imports(lines)
        decls = parse_decls(lines)
        corpus, package = classify_corpus(path, root)
        classified_root = CorpusRoot(root.path, corpus, package, root.include_nested_lake)
        module = safe_module_from_path(path, classified_root)
        windows = chunk_windows(lines, decls, max(1, chunk_lines))
        decls_by_line = sorted(decls, key=lambda d: d.line)
        ordinal = 0
        for start, end in windows:
            ordinal += 1
            content = "\n".join(lines[start - 1 : end]).strip()
            if not content:
                continue
            contained = [decl for decl in decls_by_line if start <= decl.line <= end]
            yield LeanChunk(
                path=path,
                corpus=corpus,
                package=package,
                module=module,
                line_start=start,
                line_end=end,
                content=content,
                decls=contained,
                imports=imports,
                ordinal=ordinal,
            )


def tokenize(text: str) -> list[str]:
    return [tok.lower() for tok in TOKEN_RE.findall(text)]


def hash_embedding(text: str, *, dim: int) -> list[float]:
    if dim <= 0:
        return []
    vec = [0.0] * dim
    for tok in tokenize(text):
        digest = hashlib.blake2b(tok.encode("utf-8"), digest_size=8).digest()
        raw = int.from_bytes(digest, "big")
        index = raw % dim
        sign = 1.0 if (raw >> 8) & 1 else -1.0
        vec[index] += sign
    norm = math.sqrt(sum(v * v for v in vec))
    if norm == 0:
        return vec
    return [round(v / norm, 8) for v in vec]


def collection_names(prefix: str) -> dict[str, str]:
    def name(base: str) -> str:
        return f"{prefix}_{base}" if prefix else base

    return {
        "memories": name("memories"),
        "entities": name("entities"),
        "sessions": name("sessions"),
        "daily_logs": name("daily_logs"),
        "memory_edges": name("memory_edges"),
        "entity_edges": name("entity_edges"),
    }


def graph_name(prefix: str) -> str:
    return f"{prefix}_brain_graph" if prefix else "brain_graph"


def jsonl_payload(rows: list[dict[str, Any]]) -> bytes:
    return ("\n".join(json.dumps(row, ensure_ascii=True, sort_keys=True) for row in rows) + "\n").encode("utf-8")


class OpenClawWriter:
    def __init__(
        self,
        *,
        target: ArangoHttpTarget | None,
        names: dict[str, str],
        dry_run: bool,
        batch_size: int,
    ) -> None:
        self.target = target
        self.names = names
        self.dry_run = dry_run
        self.batch_size = max(1, batch_size)
        self.pending: dict[str, list[dict[str, Any]]] = {name: [] for name in names.values()}
        self.counts: dict[str, int] = {name: 0 for name in names.values()}
        self.samples: dict[str, list[dict[str, Any]]] = {name: [] for name in names.values()}
        self.seen_entities: set[str] = set()
        self.seen_entity_edges: set[str] = set()
        self.seen_memory_edges: set[str] = set()

    def add(self, collection: str, row: dict[str, Any], *, dedupe_key: str | None = None) -> None:
        if dedupe_key is not None:
            if collection == self.names["entities"]:
                if dedupe_key in self.seen_entities:
                    return
                self.seen_entities.add(dedupe_key)
            elif collection == self.names["entity_edges"]:
                if dedupe_key in self.seen_entity_edges:
                    return
                self.seen_entity_edges.add(dedupe_key)
            elif collection == self.names["memory_edges"]:
                if dedupe_key in self.seen_memory_edges:
                    return
                self.seen_memory_edges.add(dedupe_key)

        self.counts[collection] += 1
        if len(self.samples[collection]) < 3:
            self.samples[collection].append(row)
        if self.dry_run:
            return
        self.pending[collection].append(row)
        if len(self.pending[collection]) >= self.batch_size:
            self.flush_collection(collection)

    def flush_collection(self, collection: str) -> None:
        rows = self.pending.get(collection, [])
        if not rows:
            return
        if self.target is None:
            raise RuntimeError("non-dry-run writer requires an Arango target")
        result = import_jsonl(self.target, collection, jsonl_payload(rows), on_duplicate="replace")
        if int(result.get("errors", 0) or 0) > 0:
            raise RuntimeError(f"Arango import errors for {collection}: {result}")
        self.pending[collection] = []

    def flush(self) -> None:
        if self.dry_run:
            return
        for collection in list(self.pending):
            self.flush_collection(collection)


def entity_doc(key: str, name: str, entity_type: str, now: str, *, tags: list[str], metadata: dict[str, Any]) -> dict[str, Any]:
    return {
        "_key": key,
        "name": name,
        "entity_type": entity_type,
        "source": "info-geometry-lean-openclaw-adapter",
        "created_at": now,
        "tags": tags,
        "metadata": metadata,
    }


def edge_doc(key: str, from_id: str, to_id: str, relation: str, now: str, *, weight: float = 1.0) -> dict[str, Any]:
    return {
        "_key": key,
        "_from": from_id,
        "_to": to_id,
        "relation": relation,
        "weight": weight,
        "created_at": now,
        "source": "info-geometry-lean-openclaw-adapter",
    }


def memory_doc(chunk: LeanChunk, now: str, *, embedding_mode: str, embedding_dim: int) -> dict[str, Any]:
    key = stable_key(chunk.corpus, rel_path(chunk.path), chunk.line_start, chunk.line_end, prefix="mem_")
    tags = ["lean", chunk.corpus, chunk.package]
    if chunk.decls:
        tags.append("declaration")
    if chunk.imports:
        tags.append("imports")
    doc: dict[str, Any] = {
        "_key": key,
        "content": chunk.content,
        "memory_type": "fact",
        "tags": sorted({tag for tag in tags if tag}),
        "source": "lean_source_file",
        "session_id": None,
        "agent_id": "info-geometry-openclaw-lean-indexer",
        "created_at": now,
        "confidence": 1.0,
        "access_count": 0,
        "last_accessed": now,
        "expires_at": None,
        "path": rel_path(chunk.path),
        "corpus": chunk.corpus,
        "package": chunk.package,
        "module": chunk.module,
        "line_start": chunk.line_start,
        "line_end": chunk.line_end,
        "ordinal": chunk.ordinal,
        "imports": chunk.imports,
        "decls": [{"kind": d.kind, "name": d.name, "line": d.line} for d in chunk.decls],
        "authority": "navigation_context_only_not_proof_authority",
        "schema": "info_geometry.openclaw_lean_brain.v1",
    }
    if embedding_mode == "hash":
        doc["embedding"] = hash_embedding(chunk.content, dim=embedding_dim)
        doc["embedding_model"] = f"feature_hashing_v1_dim_{embedding_dim}"
    else:
        doc["embedding"] = None
        doc["embedding_model"] = None
    return doc


def add_chunk_entities(
    writer: OpenClawWriter,
    chunk: LeanChunk,
    mem_key: str,
    now: str,
    *,
    include_imports: bool,
) -> None:
    names = writer.names
    memory_id = f"{names['memories']}/{mem_key}"
    base_tags = ["lean", chunk.corpus]

    def add_entity(name: str, entity_type: str, relation: str, metadata: dict[str, Any]) -> str:
        ent_key = stable_key(entity_type, name, prefix="ent_")
        writer.add(
            names["entities"],
            entity_doc(ent_key, name, entity_type, now, tags=base_tags, metadata=metadata),
            dedupe_key=ent_key,
        )
        edge_key = stable_key(ent_key, relation, mem_key, prefix="ee_")
        writer.add(
            names["entity_edges"],
            edge_doc(edge_key, f"{names['entities']}/{ent_key}", memory_id, relation, now),
            dedupe_key=edge_key,
        )
        return ent_key

    add_entity(chunk.corpus, "corpus", "corpus_chunk", {"corpus": chunk.corpus})
    add_entity(chunk.package, "package", "package_chunk", {"package": chunk.package})
    add_entity(rel_path(chunk.path), "file", "file_chunk", {"path": rel_path(chunk.path)})
    add_entity(chunk.module, "module", "module_chunk", {"module": chunk.module})
    if include_imports:
        for imp in chunk.imports:
            add_entity(imp, "import", "imported_by_file", {"import": imp})
    for decl in chunk.decls:
        add_entity(
            decl.name,
            f"lean_{decl.kind}",
            "declared_in_chunk",
            {
                "kind": decl.kind,
                "line": decl.line,
                "module": chunk.module,
                "path": rel_path(chunk.path),
            },
        )


def ensure_openclaw_schema(target: ArangoHttpTarget, names: dict[str, str], *, prefix: str, drop_existing: bool) -> None:
    ensure_database(target)
    existing = list_collections(target)
    edge_collections = {names["memory_edges"], names["entity_edges"]}
    for collection in names.values():
        if collection not in existing:
            create_collection(target, collection, edge=collection in edge_collections)
        elif drop_existing:
            truncate_collection(target, collection)

    ensure_index(target, names["memories"], ["memory_type", "created_at"], name=f"{names['memories']}_type_created")
    ensure_index(target, names["memories"], ["corpus", "module"], name=f"{names['memories']}_corpus_module")
    ensure_index(target, names["memories"], ["path", "line_start"], name=f"{names['memories']}_path_line")
    ensure_index(target, names["entities"], ["name", "entity_type"], unique=True, sparse=True, name=f"{names['entities']}_name_type")
    ensure_index(target, names["entity_edges"], ["relation"], name=f"{names['entity_edges']}_relation")
    ensure_index(target, names["memory_edges"], ["relation"], name=f"{names['memory_edges']}_relation")
    ensure_graph(target, names, graph_name(prefix))


def ensure_graph(target: ArangoHttpTarget, names: dict[str, str], name: str) -> None:
    out = request_json("GET", db_url(target, "/_api/gharial"), target)
    graphs = out.get("graphs", []) if isinstance(out, dict) else []
    for graph in graphs:
        if isinstance(graph, dict) and graph.get("name") == name:
            return
        if isinstance(graph, dict) and graph.get("_key") == name:
            return

    payload = {
        "name": name,
        "edgeDefinitions": [
            {
                "collection": names["memory_edges"],
                "from": [names["memories"], names["daily_logs"], names["sessions"]],
                "to": [names["memories"], names["daily_logs"], names["sessions"]],
            },
            {
                "collection": names["entity_edges"],
                "from": [names["entities"]],
                "to": [names["entities"], names["memories"]],
            },
        ],
    }
    request_json("POST", db_url(target, "/_api/gharial"), target, payload)


def has_lean_payload(path: Path) -> bool:
    if path.is_file():
        return path.suffix == ".lean"
    if not path.exists():
        return False
    if (path / "Mathlib").exists() or (path / "Mathlib.lean").exists():
        return True
    try:
        return any(child.is_file() and child.suffix == ".lean" for child in path.iterdir())
    except OSError:
        return False


def default_mathlib_roots(root: Path) -> list[Path]:
    candidates = [
        root / ".lake" / "packages" / "mathlib",
        root / "external_refs" / "atlas-lean" / ".lake" / "packages" / "mathlib",
        root / "external_refs" / "mathlib",
    ]
    for candidate in candidates:
        if has_lean_payload(candidate):
            return [candidate]
    return []


def build_roots(args: argparse.Namespace) -> list[CorpusRoot]:
    root = repo_root()
    roots: list[CorpusRoot] = []
    requested_roots = args.root if args.root else ["lean"]
    for raw in requested_roots:
        path = normalize_user_path(raw, root)
        roots.append(CorpusRoot(path=path, corpus="repo", package="info-geometry-lean"))

    if args.include_mathlib:
        for raw in args.mathlib_root:
            path = normalize_user_path(raw, root)
            roots.append(CorpusRoot(path=path, corpus="mathlib", package="mathlib", include_nested_lake=True))
        if not args.mathlib_root:
            for path in default_mathlib_roots(root):
                roots.append(CorpusRoot(path=path, corpus="mathlib", package="mathlib", include_nested_lake=True))

    if args.include_external_refs:
        roots.append(
            CorpusRoot(
                path=normalize_user_path(args.external_root, root),
                corpus="external_refs",
                package="external_refs",
                include_nested_lake=args.include_nested_lake,
            )
        )

    deduped: list[CorpusRoot] = []
    seen: set[Path] = set()
    for item in roots:
        try:
            resolved = item.path.resolve()
        except OSError:
            resolved = item.path
        if resolved in seen:
            continue
        seen.add(resolved)
        deduped.append(item)
    return deduped


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", action="append", default=[], help="Lean source root to index. Repeatable. Defaults to lean.")
    parser.add_argument("--include-mathlib", action="store_true", help="Also index detected or explicit Mathlib roots.")
    parser.add_argument("--mathlib-root", action="append", default=[], help="Explicit Mathlib root. Repeatable.")
    parser.add_argument("--include-external-refs", action="store_true", help="Also index external_refs/*.lean corpora.")
    parser.add_argument("--external-root", default="external_refs")
    parser.add_argument("--include-nested-lake", action="store_true", help="When indexing external_refs, include nested .lake directories.")
    parser.add_argument("--chunk-lines", type=int, default=120)
    parser.add_argument("--max-files", type=int, default=0, help="Max files per root; 0 means unlimited.")
    parser.add_argument("--embedding-mode", choices=["none", "hash"], default="hash")
    parser.add_argument("--embedding-dim", type=int, default=384)
    parser.add_argument("--endpoint", default=arango_endpoint())
    parser.add_argument("--database", default="openclaw_brain")
    parser.add_argument("--username", default=arango_username())
    parser.add_argument("--password", default=arango_password("alexandria_root"))
    parser.add_argument("--collection-prefix", default="", help="Use exact OpenClaw names by default; prefix for isolated test graphs.")
    parser.add_argument("--batch-size", type=int, default=1000)
    parser.add_argument("--drop-existing", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--progress-every", type=int, default=1000, help="Print scan progress every N files; 0 disables progress.")
    parser.add_argument("--json-out", type=Path, default=Path("artifacts/openclaw/lean_brain_ingest_report.json"))
    return parser.parse_args()


def main() -> int:
    load_repo_arango_env()
    args = parse_args()
    names = collection_names(str(args.collection_prefix).strip())
    target: ArangoHttpTarget | None = None
    if not args.dry_run:
        target = ArangoHttpTarget(
            endpoint=str(args.endpoint).rstrip("/"),
            database=str(args.database or arango_database()),
            username=str(args.username),
            password=str(args.password),
        )
        ensure_openclaw_schema(target, names, prefix=str(args.collection_prefix).strip(), drop_existing=bool(args.drop_existing))

    writer = OpenClawWriter(target=target, names=names, dry_run=bool(args.dry_run), batch_size=int(args.batch_size))
    now = utc_now()
    roots = build_roots(args)
    stats = {
        "roots_requested": [
            {
                "path": rel_path(root.path),
                "exists": root.path.exists(),
                "corpus": root.corpus,
                "package": root.package,
                "include_nested_lake": root.include_nested_lake,
            }
            for root in roots
        ],
        "files_seen": 0,
        "chunks_seen": 0,
        "decls_seen": 0,
        "imports_seen": 0,
    }

    previous_memory_by_file: dict[str, str] = {}
    file_imports_linked: set[str] = set()
    for root in roots:
        if not root.path.exists():
            continue
        seen_files_for_root: set[Path] = set()
        for chunk in iter_chunks(root, chunk_lines=int(args.chunk_lines), max_files=int(args.max_files)):
            resolved = chunk.path.resolve()
            if resolved not in seen_files_for_root:
                seen_files_for_root.add(resolved)
                stats["files_seen"] += 1
                progress_every = int(args.progress_every)
                if progress_every > 0 and stats["files_seen"] % progress_every == 0:
                    print(
                        "[openclaw-lean-brain] "
                        f"progress files={stats['files_seen']} chunks={stats['chunks_seen']} "
                        f"decls={stats['decls_seen']} root={rel_path(root.path)}",
                        file=sys.stderr,
                        flush=True,
                    )
            stats["chunks_seen"] += 1
            stats["decls_seen"] += len(chunk.decls)
            stats["imports_seen"] += len(chunk.imports)
            mem = memory_doc(chunk, now, embedding_mode=str(args.embedding_mode), embedding_dim=int(args.embedding_dim))
            writer.add(names["memories"], mem)

            path_key = rel_path(chunk.path)
            include_imports = path_key not in file_imports_linked
            add_chunk_entities(writer, chunk, str(mem["_key"]), now, include_imports=include_imports)
            if include_imports:
                file_imports_linked.add(path_key)

            previous = previous_memory_by_file.get(path_key)
            if previous:
                edge_key = stable_key(previous, "next_chunk", mem["_key"], prefix="me_")
                writer.add(
                    names["memory_edges"],
                    edge_doc(edge_key, f"{names['memories']}/{previous}", f"{names['memories']}/{mem['_key']}", "next_chunk", now),
                    dedupe_key=edge_key,
                )
            previous_memory_by_file[path_key] = str(mem["_key"])

    writer.flush()

    collection_counts = {}
    if target is not None:
        for collection in names.values():
            collection_counts[collection] = collection_count(target, collection)

    report = {
        "schema": "info_geometry.openclaw_lean_brain.ingest_report.v1",
        "generated_at": now,
        "dry_run": bool(args.dry_run),
        "database": str(args.database or arango_database()),
        "graph": graph_name(str(args.collection_prefix).strip()),
        "collections": names,
        "stats": stats,
        "rows_prepared": writer.counts,
        "collection_counts": collection_counts,
        "samples": writer.samples,
        "authority": "navigation_context_only_not_proof_authority",
        "openclaw_upstream": "https://github.com/arango-solutions/openclaw",
    }
    out_path = normalize_user_path(str(args.json_out), repo_root())
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(report, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "[openclaw-lean-brain] "
        f"dry_run={args.dry_run} files={stats['files_seen']} chunks={stats['chunks_seen']} "
        f"decls={stats['decls_seen']} memories={writer.counts[names['memories']]} "
        f"entities={writer.counts[names['entities']]} report={out_path}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
