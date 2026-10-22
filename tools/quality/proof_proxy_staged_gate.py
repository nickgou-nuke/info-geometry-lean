#!/usr/bin/env python3
"""Pre-commit gate for staged Lean headers and OpenGauss proof-integrity traps."""

from __future__ import annotations

import os
import re
import hashlib
import subprocess
import sys
import tempfile
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

TOP_ANY_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\n]+\]\s*)?(axiom|theorem|lemma|def|abbrev|structure|class)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b"
)
PROP_STRUCTURE_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\n]+\]\s*)*(?:private\s+|protected\s+)?structure\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)\b([^\n]*)\n((?:[ \t]*\n|[ \t]+[^\s\n][^\n]*\n)*)"
)
PROP_RESULT_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\n]+\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|example)\b"
    r"[^\n]*?:\s*([A-Za-z_][A-Za-z0-9_'.]*)\b(?:[^\n]*?\b(where)\b|\s*:=)"
)
FIELD_ASSIGN_RE = re.compile(r"(?m)^\s+([A-Za-z_][A-Za-z0-9_']*)\s*:=\s*([^\n]+)")
DEBT_BURIAL_COMMENT_RE = re.compile(
    r"\b(DEBT|OPEN CLOSURE DEBT|missing proof|not a proof|removed|no Lean declaration|owner-side proof)\b",
    re.IGNORECASE,
)
REQUIRED_LEAN_COPYRIGHT_HEADER = (
    "/-\n"
    "Copyright (c) 2026 InfoGeometry Authors. All rights reserved.\n"
    "Released under Apache 2.0 license as described in the file LICENSE.\n"
    "Authors: InfoGeometry Engine Contributors\n"
    "-/\n"
)
EXECUTED_GATE_SOURCES = (
    "tools/quality/proof_proxy_staged_gate.py",
    "tools/infra/opengauss_screener.py",
)


class ActiveIndexCache:
    """Memoize imported-file reads for one stable staged-entry snapshot.

    Git may refresh stat-cache data in `.git/index` without changing any staged
    path, mode, stage, or blob.  Those physical index updates do not alter the
    source snapshot being certified, so stability is measured from Git's
    canonical stage-entry listing rather than index-file metadata.
    """

    def __init__(self, repo_root: Path):
        self.repo_root = repo_root
        self._index_signature = self._read_index_signature()
        self._tracked: dict[str, bool] = {}
        self._matches: dict[str, bool] = {}
        self._blobs: dict[str, tuple[int, bytes, str]] = {}
        self._imports: dict[str, list[str]] = {}

    def _read_index_signature(self) -> str | None:
        configured = os.environ.get("GIT_INDEX_FILE")
        if configured:
            index_path = Path(configured)
            if not index_path.is_absolute():
                index_path = self.repo_root / index_path
        else:
            path_result = subprocess.run(
                ["git", "rev-parse", "--git-path", "index"],
                cwd=self.repo_root,
                capture_output=True,
                text=True,
                check=False,
            )
            if path_result.returncode != 0:
                return None
            index_path = Path(path_result.stdout.strip())
            if not index_path.is_absolute():
                index_path = self.repo_root / index_path
        if not index_path.is_file():
            return None
        result = subprocess.run(
            ["git", "ls-files", "--stage", "-z"],
            cwd=self.repo_root,
            capture_output=True,
            check=False,
        )
        if result.returncode != 0:
            return None
        return hashlib.sha256(result.stdout).hexdigest()

    def still_current(self) -> bool:
        """Fail closed if index-backed reads crossed an active-index update."""
        return self._index_signature is not None and self._index_signature == self._read_index_signature()

    def tracked(self, relative_path: str) -> bool:
        if relative_path not in self._tracked:
            result = subprocess.run(
                ["git", "ls-files", "--error-unmatch", "--", relative_path],
                cwd=self.repo_root,
                capture_output=True,
                text=True,
                check=False,
            )
            self._tracked[relative_path] = result.returncode == 0
        return self._tracked[relative_path]

    def matches_worktree(self, relative_path: str) -> bool:
        if relative_path not in self._matches:
            result = subprocess.run(
                ["git", "diff", "--quiet", "--", relative_path],
                cwd=self.repo_root,
                capture_output=True,
                check=False,
            )
            self._matches[relative_path] = result.returncode == 0
        return self._matches[relative_path]

    def blob(self, relative_path: str) -> tuple[int, bytes, str]:
        if relative_path not in self._blobs:
            result = subprocess.run(
                ["git", "show", f":{relative_path}"],
                cwd=self.repo_root,
                capture_output=True,
                check=False,
            )
            detail = result.stderr.decode("utf-8", errors="replace").strip()
            self._blobs[relative_path] = (result.returncode, result.stdout, detail)
        return self._blobs[relative_path]

    def imports(self, source: str) -> list[str]:
        if source not in self._imports:
            try:
                from tools.infra.opengauss_screener import _strip_lean_comments_and_strings
            except ImportError:
                return []
            import_pattern = re.compile(r"^\s*import\s+([A-Za-z0-9_. ]+)\s*$", re.MULTILINE)
            clean = _strip_lean_comments_and_strings(source)
            self._imports[source] = [
                module for line in import_pattern.findall(clean) for module in line.split()
            ]
        # Callers consume their pending worklists with ``pop``. Return a copy
        # so one traversal cannot empty the memoized imports for another.
        return list(self._imports[source])


def git(args: list[str]) -> str:
    return subprocess.check_output(["git", *args], text=True)


def _main_index_env() -> dict[str, str]:
    """Environment whose git commands read the repository's main index.

    `git commit --only <paths>` runs hooks with `GIT_INDEX_FILE` pointing at a
    temporary index built from `HEAD` plus the named paths. Comparing checker
    sources against that temporary index would report every staged (but not yet
    committed) checker edit as unstaged. The requirement enforced here is that
    the executed checker equals what the user has staged, i.e. the main index.
    """
    env = dict(os.environ)
    env.pop("GIT_INDEX_FILE", None)
    return env


def checker_index_mismatches(repo_root: Path | None = None) -> list[str]:
    """Return gate source paths whose worktree contents differ from the index.

    The hook executes these files from the worktree while reading Lean payloads
    from stage-0 index blobs. Refuse that mixed snapshot if checker edits have
    not been staged (or unstaged) consistently. The comparison uses the main
    index, so partial commits (`git commit --only`) are judged by the same rule.
    """
    env = _main_index_env()
    result = subprocess.run(
        ["git", "diff", "--quiet", "--", *EXECUTED_GATE_SOURCES],
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=False,
        env=env,
    )
    if result.returncode == 0:
        return []
    if result.returncode == 1:
        changed = subprocess.run(
            ["git", "diff", "--name-only", "--", *EXECUTED_GATE_SOURCES],
            cwd=repo_root,
            capture_output=True,
            text=True,
            check=True,
            env=env,
        ).stdout
        return [line for line in changed.splitlines() if line]
    detail = result.stderr.strip() or f"git diff exited {result.returncode}"
    return [f"gate-source-index-comparison-failed: {detail}"]


def imported_source_index_mismatches(
    source: str, repo_root: Path = _REPO_ROOT,
    index_cache: ActiveIndexCache | None = None,
) -> list[str]:
    """Require repo-local imports read by the screener to match the active index.

    The screener's T16/T17 import checks resolve Lean files from the worktree.
    This guard keeps those reads consistent with the staged declaration being
    screened, including `git commit --only`'s temporary commit index.
    """
    try:
        from tools.infra.opengauss_screener import _strip_lean_comments_and_strings
    except ImportError:
        return ["cannot load canonical QMS comment stripper for import consistency check"]

    def imports_of(text: str) -> list[str]:
        if index_cache is not None:
            return index_cache.imports(text)
        clean = _strip_lean_comments_and_strings(text)
        import_pattern = re.compile(r"^\s*import\s+([A-Za-z0-9_. ]+)\s*$", re.MULTILINE)
        return [module for line in import_pattern.findall(clean) for module in line.split()]

    pending = imports_of(source)
    seen: set[Path] = set()
    mismatches: set[str] = set()
    while pending:
        module = pending.pop()
        relative = Path(*module.split("."))
        roots = (repo_root / "lean", repo_root / "proofs")
        if module.startswith("proofs."):
            relative = Path(*module.removeprefix("proofs.").split("."))
            roots = (repo_root / "proofs",)
        candidates = [root / relative.with_suffix(".lean") for root in roots]
        candidate = None
        for path in candidates:
            if path.is_file():
                candidate = path
                break
            relative_path = path.relative_to(repo_root).as_posix()
            if (index_cache.tracked(relative_path) if index_cache else subprocess.run(
                ["git", "ls-files", "--error-unmatch", "--", relative_path],
                cwd=repo_root, capture_output=True, text=True, check=False,
            ).returncode == 0):
                mismatches.add(
                    f"{relative_path} (present in active index but missing from worktree)"
                )
        if candidate is None:
            continue
        if candidate in seen:
            continue
        seen.add(candidate)
        relative_path = candidate.relative_to(repo_root).as_posix()
        if candidate.is_symlink():
            mismatches.add(f"{relative_path} (repo-local Lean imports may not be symlinks)")
            continue
        is_tracked = index_cache.tracked(relative_path) if index_cache else subprocess.run(
            ["git", "ls-files", "--error-unmatch", "--", relative_path],
            cwd=repo_root, capture_output=True, text=True, check=False,
        ).returncode == 0
        if not is_tracked:
            mismatches.add(f"{relative_path} (not present in active index)")
            continue
        matches_worktree = index_cache.matches_worktree(relative_path) if index_cache else subprocess.run(
            ["git", "diff", "--quiet", "--", relative_path],
            cwd=repo_root, capture_output=True, check=False,
        ).returncode == 0
        if not matches_worktree:
            mismatches.add(f"{relative_path} (worktree differs from active index)")
            continue
        try:
            pending.extend(imports_of(candidate.read_text(encoding="utf-8")))
        except OSError as exc:
            mismatches.add(f"{relative_path} (cannot read imported source: {exc})")
    return sorted(mismatches)


def materialize_indexed_imports(
    source: str, repo_root: Path, snapshot_root: Path,
    index_cache: ActiveIndexCache | None = None,
) -> list[str]:
    """Materialize the transitive repo-local import closure from the active index."""
    try:
        from tools.infra.opengauss_screener import _strip_lean_comments_and_strings
    except ImportError:
        return ["cannot load canonical QMS comment stripper for indexed import snapshot"]

    def imports_of(text: str) -> list[str]:
        if index_cache is not None:
            return index_cache.imports(text)
        clean = _strip_lean_comments_and_strings(text)
        import_pattern = re.compile(r"^\s*import\s+([A-Za-z0-9_. ]+)\s*$", re.MULTILINE)
        return [module for line in import_pattern.findall(clean) for module in line.split()]

    pending = imports_of(source)
    seen: set[str] = set()
    errors: list[str] = []
    while pending:
        module = pending.pop()
        relative = Path(*module.split("."))
        roots = (Path("lean"), Path("proofs"))
        if module.startswith("proofs."):
            relative = Path(*module.removeprefix("proofs.").split("."))
            roots = (Path("proofs"),)
        candidates = [root / relative.with_suffix(".lean") for root in roots]
        indexed_path = None
        for candidate in candidates:
            relative_path = candidate.as_posix()
            tracked = index_cache.tracked(relative_path) if index_cache else subprocess.run(
                ["git", "ls-files", "--error-unmatch", "--", relative_path],
                cwd=repo_root,
                capture_output=True,
                text=True,
                check=False,
            ).returncode == 0
            if tracked:
                indexed_path = relative_path
                break
        if indexed_path is None or indexed_path in seen:
            continue
        seen.add(indexed_path)
        if index_cache is not None:
            blob_returncode, blob_stdout, detail = index_cache.blob(indexed_path)
        else:
            blob = subprocess.run(
                ["git", "show", f":{indexed_path}"],
                cwd=repo_root,
                capture_output=True,
                check=False,
            )
            blob_returncode, blob_stdout = blob.returncode, blob.stdout
            detail = blob.stderr.decode("utf-8", errors="replace").strip()
        if blob_returncode != 0:
            errors.append(f"{indexed_path} (cannot read active-index blob: {detail})")
            continue
        destination = snapshot_root / indexed_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        try:
            if not destination.exists():
                destination.write_bytes(blob_stdout)
        except OSError as exc:
            errors.append(f"{indexed_path} (cannot materialize active-index blob: {exc})")
            continue
        pending.extend(imports_of(blob_stdout.decode("utf-8", errors="replace")))
    return errors


def aggregate_prop_constructors(source: str) -> list[tuple[str, str]]:
    """Find theorem/def constructors that merely bundle a Prop structure's fields.

    Predicate structures are allowed. This catches the aggregate theorem wrapper
    structurally, independent of names chosen for its type, theorem, or fields,
    across `where`, `{ ... }`, `⟨...⟩`, and `.mk` constructor styles.
    """
    try:
        from tools.infra.opengauss_screener import _strip_lean_comments_and_strings
        source = _strip_lean_comments_and_strings(source)
    except ImportError:
        pass
    found: list[tuple[str, str]] = []
    for structure in PROP_STRUCTURE_RE.finditer(source):
        type_name, header, body = structure.groups()
        if not re.search(r":\s*Prop\s+where\s*$", header):
            continue
        fields = [
            item.group(1)
            for item in re.finditer(r"(?m)^\s+([A-Za-z_][A-Za-z0-9_']*)\s*:", body)
        ]
        field_set = set(fields)
        if len(field_set) < 2:
            continue
        for constructor in PROP_RESULT_RE.finditer(source):
            if constructor.group(1) != type_name:
                continue
            is_where = constructor.group(2) == "where"
            tail = source[constructor.end():]
            next_decl = re.search(r"(?m)^\S", tail)
            if next_decl:
                tail = tail[:next_decl.start()]
            if is_where:
                assignments = FIELD_ASSIGN_RE.findall(tail)
                selected = [(name, value.strip()) for name, value in assignments if name in field_set]
                if field_set <= {name for name, _ in selected} and all(
                    re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*(?:\s+[^\n]+)?", value)
                    for _, value in selected
                ):
                    found.append((type_name, constructor.group(0).strip()))
            else:
                rhs = tail.strip()
                brace_assignments = re.findall(
                    r"([A-Za-z_][A-Za-z0-9_']*)\s*:=\s*([^,}\n]+)", rhs
                )
                selected = [(name, value.strip()) for name, value in brace_assignments if name in field_set]
                if field_set <= {name for name, _ in selected}:
                    found.append((type_name, constructor.group(0).strip()))
                    continue
                anon = re.search(r"⟨([^⟩]+)⟩", rhs)
                if anon and len([p for p in anon.group(1).split(",") if p.strip()]) >= len(field_set):
                    found.append((type_name, constructor.group(0).strip()))
                    continue
                if re.search(rf"\b{re.escape(type_name)}\.mk\b", rhs):
                    found.append((type_name, constructor.group(0).strip()))
    return found


def check_text(
    lean_path: str, source: str, repo_root: Path = _REPO_ROOT,
    index_cache: ActiveIndexCache | None = None,
    snapshot_root: Path | None = None,
) -> list[str]:
    """Check staged Lean source with the canonical OpenGauss source screener."""
    failures: list[str] = []
    if not source.startswith(REQUIRED_LEAN_COPYRIGHT_HEADER):
        failures.append(
            f"{lean_path}: missing or malformed required InfoGeometry copyright and license header"
        )
    for mismatch in imported_source_index_mismatches(source, repo_root, index_cache):
        failures.append(
            f"{lean_path}: imported Lean source is not a consistent active-index snapshot: {mismatch}"
        )
    try:
        from tools.infra.opengauss_screener import screen_lean_content
        def screen_with_snapshot(root: Path) -> None:
            for mismatch in materialize_indexed_imports(source, repo_root, root, index_cache):
                failures.append(
                    f"{lean_path}: cannot build active-index import snapshot: {mismatch}"
                )
            for violation in screen_lean_content(
                source, filename=lean_path, import_root=root
            ):
                # The pre-commit gate enforces the screener's blocking findings.
                # Warnings remain advisory, matching the screener's severity model.
                if violation.severity == "ERROR":
                    failures.append(
                        f"{lean_path}:{violation.line_number}: OpenGauss {violation.trap_id} "
                        f"{violation.trap_name}: {violation.message} ({violation.matched_text})"
                    )
        if snapshot_root is not None:
            screen_with_snapshot(snapshot_root)
        else:
            with tempfile.TemporaryDirectory(prefix="opengauss-index-imports-") as temp_dir:
                screen_with_snapshot(Path(temp_dir))
    except ImportError:
        failures.append(
            f"{lean_path}: cannot load the canonical QMS source checker; refusing to certify this staged Lean file"
        )
    for type_name, constructor in aggregate_prop_constructors(source):
        failures.append(
            f"{lean_path}: `{constructor}` constructs Prop structure `{type_name}` by bundling field proofs; audit the owner theorems directly"
        )
    return failures


def main() -> int:
    repo_root = Path(git(["rev-parse", "--show-toplevel"]).strip())
    index_cache = ActiveIndexCache(repo_root)
    out = git(["diff", "--cached", "--unified=0", "--", "*.lean"])
    failures: list[str] = []
    path = ""
    line_no: int | None = None
    removed_decl_files: set[str] = set()
    debt_comment_files: set[str] = set()
    for line in out.splitlines():
        if line.startswith("+++ b/"):
            path = line[6:]
            continue
        if line.startswith("@@"):
            m = re.search(r"\+(\d+)(?:,(\d+))?", line)
            line_no = int(m.group(1)) if m else None
            continue
        if line.startswith("-") and not line.startswith("---"):
            if TOP_ANY_DECL_RE.match(line[1:].strip()):
                removed_decl_files.add(path)
            continue
        if not line.startswith("+") or line.startswith("+++"):
            if line_no is not None:
                line_no += 1
            continue
        added = line[1:]
        loc = f"{path}:{line_no}" if line_no is not None else path
        stripped = added.strip()
        if stripped.startswith(("--", "/-", "*")):
            if DEBT_BURIAL_COMMENT_RE.search(stripped):
                debt_comment_files.add(path)
            if line_no is not None:
                line_no += 1
            continue
        if "`" in stripped or '"' in stripped:
            if line_no is not None:
                line_no += 1
            continue
        if re.search(r"^\s*(?:axiom|postulate)\s+(?:«[^»\n]+»|[^\W\d][\w'.]*)\s*:|^\s*(?:admit|sorry|sorryAx)\b", stripped):
            failures.append(f"{loc}: staged forbidden placeholder `{stripped}`")
        if line_no is not None:
            line_no += 1
    staged_lean_paths = set(
        path
        for path in subprocess.check_output(
            ["git", "diff", "--cached", "--name-only", "-z", "--diff-filter=ACMRT", "--", "*.lean"]
        ).split(b"\0")
        if path
    )
    if staged_lean_paths:
        mismatches = checker_index_mismatches(repo_root)
        if mismatches:
            failures.append(
                "executed QMS gate source differs from staged index; stage or discard checker edits before committing: "
                + ", ".join(mismatches)
            )
    staged_entries = subprocess.check_output(["git", "ls-files", "-s", "-z", "--", "*.lean"])
    blob_by_path: dict[bytes, str] = {}
    for entry in staged_entries.split(b"\0"):
        if not entry:
            continue
        metadata, raw_path = entry.split(b"\t", 1)
        fields = metadata.decode("ascii").split()
        if len(fields) == 3 and fields[2] == "0":
            blob_by_path[raw_path] = fields[1]
    missing_stage_blobs = staged_lean_paths - blob_by_path.keys()
    for raw_path in sorted(missing_stage_blobs):
        failures.append(
            f"{raw_path.decode('utf-8', errors='replace')}: staged Lean path has no stage-0 index blob to validate"
        )
    paths_and_blobs = [
        (path, blob_by_path[path]) for path in sorted(staged_lean_paths) if path in blob_by_path
    ]
    blob_data = subprocess.run(
        ["git", "cat-file", "--batch"],
        input=("\n".join(blob for _, blob in paths_and_blobs) + "\n").encode(),
        capture_output=True,
        check=True,
    ).stdout
    cursor = 0
    with tempfile.TemporaryDirectory(prefix="opengauss-index-imports-") as temp_dir:
        snapshot_root = Path(temp_dir)
        for raw_path, _blob in paths_and_blobs:
            header_end = blob_data.index(b"\n", cursor)
            header = blob_data[cursor:header_end].split()
            size = int(header[2])
            start = header_end + 1
            source = blob_data[start:start + size].decode("utf-8", errors="replace")
            cursor = start + size + 1
            lean_path = raw_path.decode("utf-8", errors="replace")
            failures.extend(check_text(
                lean_path, source, repo_root,
                index_cache=index_cache, snapshot_root=snapshot_root,
            ))
    for buried in sorted(removed_decl_files & debt_comment_files):
        failures.append(
            f"{buried}: staged deletion of Lean declarations with natural-language debt comments; keep open debt compiler-visible instead of burying it in prose"
        )

    if not index_cache.still_current():
        failures.append(
            "active Git index changed during staged proof-proxy scan; refusing mixed-snapshot certification"
        )

    if failures:
        print("proof_proxy_staged_gate: FAIL", file=sys.stderr)
        for failure in failures:
            print(f"  - {failure}", file=sys.stderr)
        return 1
    print("proof_proxy_staged_gate: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
