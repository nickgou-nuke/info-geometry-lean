#!/usr/bin/env python3
"""
External repository indexer for RAG knowledge-base retrieval.

Scans external reference directories (.lean, .py, .thy, .md files) and
indexes them into a knowledge base suitable for DAG-grounded LLM queries.

This reimplements the old external repository indexer with support for:
- Incremental indexing (skip already-indexed files by checksum)
- Structural chunking (split large files at declaration boundaries)
- ArangoDB output format for hive ingestion

Usage:
  # Index all configured repos
  python3 tools/leantrail/external_index.py

  # Index a specific repo
  python3 tools/leantrail/external_index.py --repo lean/atlas-lean

  # Index with structural chunking for Lean files
  python3 tools/leantrail/external_index.py --chunk --format arango
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Set

REPO_ROOT = Path(__file__).resolve().parents[2]

# ---------------------------------------------------------------------------
# Default repository configuration
# ---------------------------------------------------------------------------

DEFAULT_REPO_CONFIG: Dict[str, Dict[str, Any]] = {
    "lean/atlas-lean": {
        "files": 200, "max_lines": 100, "max_bytes": 8000,
        "extensions": [".lean"],
    },
    "lean/VirasoroProject": {
        "files": 50, "max_lines": 200, "max_bytes": 8000,
        "extensions": [".lean", ".md"],
    },
    "python/sympy": {
        "files": 100, "max_lines": 100, "max_bytes": 5000,
        "extensions": [".py", ".md"],
    },
    "python/PauLie": {
        "files": 30, "max_lines": 200, "max_bytes": 5000,
        "extensions": [".py", ".md"],
    },
    "python/SymPy-LieAlgebras": {
        "files": 30, "max_lines": 200, "max_bytes": 5000,
        "extensions": [".py", ".md"],
    },
    "formal/isabelle/afp": {
        "files": 100, "max_lines": 100, "max_bytes": 8000,
        "extensions": [".thy", ".md"],
    },
    "math/affine-charform": {
        "files": 30, "max_lines": 200, "max_bytes": 5000,
        "extensions": [".py", ".sage", ".md"],
    },
    "math/Semisimple-Lie-Algebras": {
        "files": 50, "max_lines": 200, "max_bytes": 5000,
        "extensions": [".py", ".sage", ".md"],
    },
    "python/quantum/QuAIRKit": {
        "files": 50, "max_lines": 200, "max_bytes": 5000,
        "extensions": [".py", ".md"],
    },
    "python/quantum/qutip": {
        "files": 50, "max_lines": 200, "max_bytes": 5000,
        "extensions": [".py", ".md"],
    },
}

# Directories to search for external repos
EXTERNAL_SEARCH_DIRS = [
    REPO_ROOT / "external_refs",
]

# ---------------------------------------------------------------------------
# Structural chunking for Lean files
# ---------------------------------------------------------------------------

LEAN_DECL_CHUNK_RE = re.compile(
    r"^(\s*(?:theorem|lemma|def|structure|inductive|class|instance|abbrev)\s+\S+)",
    re.MULTILINE,
)

LEAN_SECTION_RE = re.compile(
    r"^(\s*(?:section|namespace|open|import)\s+)",
    re.MULTILINE,
)


def chunk_lean_text(text: str, max_chunk_lines: int = 80) -> List[str]:
    """Split a Lean file into chunks at declaration boundaries."""
    lines = text.split("\n")
    if len(lines) <= max_chunk_lines:
        return [text]

    chunks: List[str] = []
    current: List[str] = []
    current_lines = 0

    for line in lines:
        if LEAN_DECL_CHUNK_RE.match(line) and current_lines >= max_chunk_lines // 2:
            chunks.append("\n".join(current))
            current = [line]
            current_lines = 1
        else:
            current.append(line)
            current_lines += 1

    if current:
        chunks.append("\n".join(current))
    return chunks


def extract_lean_metadata(content: str) -> Dict[str, Any]:
    """Extract theorem names and imports."""
    return {
        "theorems": re.findall(
            r"(?:theorem|lemma|def)\s+([a-zA-Z0-9_']+)", content
        )[:50],
        "imports": re.findall(
            r"^\s*import\s+([a-zA-Z0-9_.]+)", content, re.MULTILINE
        )[:20],
    }


# ---------------------------------------------------------------------------
# Indexer
# ---------------------------------------------------------------------------


def _find_external_dir() -> Optional[Path]:
    for d in EXTERNAL_SEARCH_DIRS:
        if d.exists() and d.is_dir():
            return d
    return None


def _resolve_repo_path(external_dir: Path, repo_name: str) -> Optional[Path]:
    direct = external_dir / repo_name
    if direct.exists():
        return direct

    basename = repo_name.rstrip("/").split("/")[-1]
    for candidate in [basename, *({"afp": ["mirror-afp-devel"]}.get(basename, []))]:
        by_basename = external_dir / candidate
        if by_basename.exists():
            return by_basename

    literal = Path(repo_name)
    if literal.exists():
        return literal
    return None


def _collect_files(
    root: Path,
    extensions: List[str],
    max_files: int,
) -> Iterable[Tuple[Path, str]]:
    """Walk a directory tree, yielding (full_path, rel_path) for matching files."""
    count = 0
    for dirpath, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if not d.startswith(".") and d != ".git"]
        for fn in sorted(files):
            if count >= max_files:
                return
            if not any(fn.endswith(ext) for ext in extensions):
                continue
            full = Path(dirpath) / fn
            rel = str(full.relative_to(root))
            yield full, rel
            count += 1


def _compute_key(source: str, rel_path: str, content: str) -> str:
    digest = hashlib.sha1(content.encode("utf-8")).hexdigest()
    return f"ext_{digest[:20]}"


def index_repos(
    external_dir: Path,
    repos: Optional[Dict[str, Dict[str, Any]]] = None,
    *,
    chunk: bool = False,
    existing_keys: Optional[Set[str]] = None,
) -> List[Dict[str, Any]]:
    """Index all configured external repositories.

    Returns a list of knowledge-base entries.
    """
    repos = repos or DEFAULT_REPO_CONFIG
    existing_keys = existing_keys or set()
    entries: List[Dict[str, Any]] = []

    for repo_name, config in repos.items():
        repo_path = _resolve_repo_path(external_dir, repo_name)
        if not repo_path:
            print(f"  SKIP {repo_name}: not found under {external_dir}")
            continue

        extensions = config.get("extensions", [".lean"])
        max_files = config.get("files", 100)
        max_bytes = config.get("max_bytes", 5000)

        count = 0
        for full_path, rel_path in _collect_files(repo_path, extensions, max_files):
            try:
                content = full_path.read_text(encoding="utf-8", errors="ignore")
            except Exception:
                continue
            if not content.strip():
                continue

            # Truncate
            if len(content) > max_bytes:
                content = content[:max_bytes] + "\n\n... [truncated]"

            metadata = {}
            if full_path.suffix == ".lean":
                metadata = extract_lean_metadata(content)

            # Chunk if requested
            texts = [content]
            if chunk and full_path.suffix == ".lean":
                texts = chunk_lean_text(content)

            for ci, chunk_text in enumerate(texts):
                chunk_suffix = f"_chunk{ci}" if len(texts) > 1 else ""
                key = _compute_key(repo_name, rel_path, chunk_text)
                if key in existing_keys:
                    continue
                entry = {
                    "_key": key,
                    "title": f"{repo_name}/{Path(rel_path).stem}{chunk_suffix}",
                    "content": chunk_text,
                    "source": f"external/{repo_name}",
                    "file": rel_path,
                    "tags": [repo_name.split("/")[0], full_path.suffix.lstrip(".")],
                    "status": "literature",
                }
                if metadata.get("theorems"):
                    entry["theorems"] = metadata["theorems"]
                if metadata.get("imports"):
                    entry["imports"] = metadata["imports"]

                entries.append(entry)
                existing_keys.add(key)
                count += 1

        print(f"  {repo_name}: indexed {count} entries")

    return entries


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Index external repositories for RAG knowledge base."
    )
    parser.add_argument("--external-dir", default=None,
                        help="Path to external/ directory")
    parser.add_argument("--repo", default=None,
                        help="Specific repo to index (e.g., lean/atlas-lean)")
    parser.add_argument("--limit", type=int, default=0,
                        help="Override file limit per repo")
    parser.add_argument("--out", default="artifacts/leantrail/external_index.json",
                        help="Output JSON path")
    parser.add_argument("--format", choices=["json", "arango", "jsonl"],
                        default="json", help="Output format")
    parser.add_argument("--chunk", action="store_true",
                        help="Enable structural chunking for Lean files")
    parser.add_argument("--merge", default=None,
                        help="Merge into an existing knowledge base file")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()

    if args.external_dir:
        external_dir = Path(args.external_dir)
    elif args.repo and Path(args.repo).exists():
        # Allow indexing a repository-local path such as `lean/InfoGeometry/Algebra`
        # without requiring an external reference directory.
        external_dir = Path(".")
    else:
        external_dir = _find_external_dir()
    if not external_dir:
        print("Error: no external/ directory found. Use --external-dir or --repo <existing-path>.",
              file=__import__("sys").stderr)
        return 1

    # Load existing if merging
    existing_keys: Set[str] = set()
    existing_entries: List[Dict[str, Any]] = []
    if args.merge:
        merge_path = Path(args.merge)
        if merge_path.exists():
            existing_entries = json.loads(merge_path.read_text(encoding="utf-8"))
            existing_keys = {e.get("_key", "") for e in existing_entries}
            print(f"Loaded {len(existing_entries)} existing entries from {merge_path}")

    # Select repos
    repos = DEFAULT_REPO_CONFIG
    if args.repo:
        repos = {args.repo: DEFAULT_REPO_CONFIG.get(
            args.repo, {"files": args.limit or 100, "extensions": [".lean", ".py", ".md"]}
        )}
    if args.limit > 0:
        for cfg in repos.values():
            cfg["files"] = args.limit

    print(f"Indexing from: {external_dir}")
    entries = index_repos(external_dir, repos, chunk=args.chunk,
                          existing_keys=existing_keys)

    # Merge
    all_entries = existing_entries + entries
    print(f"\nTotal entries: {len(all_entries)} (new: {len(entries)})")

    out_path = Path(args.out).resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)

    if args.format == "jsonl":
        with out_path.open("w", encoding="utf-8") as f:
            for e in all_entries:
                f.write(json.dumps(e, ensure_ascii=True) + "\n")
    elif args.format == "arango":
        payload = {
            "collection": "alexandria_chunks",
            "documents": all_entries,
            "meta": {
                "format": "arango_documents",
                "count": len(all_entries),
                "source": "tools/leantrail/external_index.py",
            },
        }
        out_path.write_text(
            json.dumps(payload, indent=2, ensure_ascii=True) + "\n",
            encoding="utf-8",
        )
    else:
        out_path.write_text(
            json.dumps(all_entries, indent=2, ensure_ascii=True) + "\n",
            encoding="utf-8",
        )

    print(f"Saved to: {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
