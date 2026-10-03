#!/usr/bin/env python3
"""Audit whether Python docstrings describe the code that actually exists.

For every first-party Python module this performs *mechanically decidable*
checks of the claims a docstring makes, and records each mismatch with evidence.
Nothing here judges style; it only answers one question per claim:

    does the thing the docstring names actually exist and is it wired up?

Claim classes checked
---------------------
path   A repo-relative path mentioned in a docstring (``tools/x.py``,
       ``lean/InfoGeometry/Foo.lean``, ``reports/x.json``, ...).
flag   A command-line flag mentioned in a docstring (``--stream``) that the
       module never registers with any argument parser.
symbol A backticked identifier mentioned in a docstring (``refresh(...)``,
       ``DeclNode``) that is not defined or referenced anywhere in the module.
cmd    A shell command in a docstring whose script/module path does not exist.

Scope
-----
First-party only.  Vendored trees (``.lake``, ``external_refs``,
``lean/.kilo`` worktrees, ``.venv*``, ``node_modules``), archives
(``artifacts``, ``scratch``, ``proofs``, ``archive``) and build outputs are
excluded by default.  Those trees contain full duplicates of the live source
and would otherwise double-count every finding; see
``docs/ASTAQLHASH-HOWTO.md``.

Usage
-----
    python3 tools/quality/python_docstring_claim_audit.py
    python3 tools/quality/python_docstring_claim_audit.py --json-out reports/x.json
    python3 tools/quality/python_docstring_claim_audit.py --only tools/infra
    python3 tools/quality/python_docstring_claim_audit.py --quiet
"""

from __future__ import annotations

import argparse
import ast
import json
import os
import re
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass, field, asdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

#: Directory names never descended into.  Mirrors the HOWTO's full-graph
#: invariant: these hold duplicates of live source, so auditing them is
#: meaningless and their findings are pure noise.
EXCLUDED_DIRS = frozenset({
    ".lake", ".git", "__pycache__", ".kilo", "node_modules", "site-packages",
    "external_refs", "artifacts", "scratch", "proofs", "archive", "aihub",
    "backend", ".venv", ".mypy_cache", ".pytest_cache", ".ruff_cache",
})
EXCLUDED_DIR_PREFIXES = (".venv",)
#: Top-level trees that are not repo-owned Python.
EXCLUDED_TOP = frozenset({"lean", "external_refs", "artifacts", "scratch",
                          "proofs", "archive", "aihub", "backend", "tmp"})
#: Vendored upstream forks living under an otherwise first-party prefix.
#: ``src/hermes-agent`` is a fork of nousresearch/hermes-agent that this
#: repository consumes; auditing its docstrings measures upstream, not us.
EXCLUDED_PATH_PREFIXES = ("src/hermes-agent",)

#: ``path``/``flag``/``cmd`` are decidable: a missing file or an unregistered
#: flag is a defect.  ``symbol`` is advisory -- a backticked word may legitimately
#: name an external API, a protocol field, or prose, so those findings are
#: reported separately and never counted as stale docstrings on their own.
ADVISORY_KINDS = frozenset({"symbol"})

PATH_CLAIM = re.compile(
    r"(?<![\w./-])((?:tools|lean|docs|src|scripts|configs|reports|artifacts|"
    r"formalizations|proofs|examples)/[A-Za-z0-9_][A-Za-z0-9_./-]*"
    r"\.(?:py|lean|json|md|ya?ml|toml|sh|txt|cfg|ini|ts|js))"
)
FLAG_CLAIM = re.compile(r"(?<![\w-])(--[a-z0-9][a-z0-9-]*)")
BACKTICKED = re.compile(r"`([^`\n]{1,80})`")
SYMBOL_CLAIM = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(?:\(\))?$")
CMD_CLAIM = re.compile(
    r"\b(?:python3?|lake|bash|sh)\s+([A-Za-z0-9_][A-Za-z0-9_./-]*"
    r"\.(?:py|lean))"
)
#: Flag-like tokens that are prose, not flags.
FLAG_STOPWORDS = frozenset({"--and", "--or", "--not", "--if", "--help", "--version"})


@dataclass
class Finding:
    """One docstring claim that the code does not support."""
    file: str
    line: int
    scope: str          # module | ClassName | func_name
    kind: str           # path | flag | symbol | cmd
    claim: str
    detail: str


@dataclass
class FileReport:
    file: str
    docstrings: int = 0
    claims: int = 0
    findings: list[Finding] = field(default_factory=list)
    parse_error: str | None = None


def iter_first_party(only: str | None) -> list[Path]:
    """Every repo-owned ``.py`` file, excluding vendored/duplicate trees."""
    roots = [only] if only else None
    out: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(REPO_ROOT):
        rel_dir = Path(dirpath).relative_to(REPO_ROOT)
        rel_str = rel_dir.as_posix()
        if any(rel_str == px or rel_str.startswith(px + "/")
               for px in EXCLUDED_PATH_PREFIXES):
            continue
        if roots and not any(rel_str == r or rel_str.startswith(r + "/")
                             or str(rel_dir).startswith(r) for r in roots):
            continue
        dirnames[:] = [
            d for d in dirnames
            if d not in EXCLUDED_DIRS and not d.startswith(EXCLUDED_DIR_PREFIXES)
        ]
        if rel_dir.parts and rel_dir.parts[0] in EXCLUDED_TOP:
            continue
        for name in sorted(filenames):
            if name.endswith(".py"):
                out.append(Path(dirpath) / name)
    return out


def module_flags(tree: ast.AST, source: str) -> set[str]:
    """Flags the module actually registers, from string literals and add_argument."""
    found: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            if node.value.startswith("--"):
                found.add(node.value)
        if isinstance(node, ast.Call):
            fname = getattr(node.func, "attr", getattr(node.func, "id", ""))
            if fname == "add_argument":
                for arg in node.args:
                    if isinstance(arg, ast.Constant) and isinstance(arg.value, str) \
                            and arg.value.startswith("--"):
                        found.add(arg.value)
    return found


def defined_symbols(tree: ast.AST) -> set[str]:
    """Module-level and nested definition names, plus every bare identifier used."""
    defined: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            defined.add(node.name)
        elif isinstance(node, ast.Assign):
            for tgt in node.targets:
                for sub in ast.walk(tgt):
                    if isinstance(sub, ast.Name):
                        defined.add(sub.id)
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            defined.add(node.target.id)
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            for alias in node.names:
                defined.add((alias.asname or alias.name).split(".")[0])
        elif isinstance(node, (ast.For, ast.comprehension)):
            tgt = getattr(node, "target", None)
            if isinstance(tgt, ast.Name):
                defined.add(tgt.id)
    return defined


def used_symbols(tree: ast.AST) -> set[str]:
    used: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Name):
            used.add(node.id)
        elif isinstance(node, ast.Attribute):
            used.add(node.attr)
    return used


def path_exists(claim: str, module_dir: Path) -> bool:
    """A path claim is satisfied if it resolves relative to the repo root or the
    module's own directory.  Placeholders (``...``, ``<x>``) are not claims."""
    if any(tok in claim for tok in ("...", "<", ">", "*", "{", "}")):
        return True
    if (REPO_ROOT / claim).exists():
        return True
    try:
        return (module_dir / claim).exists()
    except (OSError, ValueError):
        return False


def audit_file(path: Path) -> FileReport:
    rel = str(path.relative_to(REPO_ROOT))
    rep = FileReport(file=rel)
    try:
        source = path.read_text(encoding="utf-8", errors="replace")
        tree = ast.parse(source)
    except (OSError, SyntaxError, ValueError) as exc:
        rep.parse_error = f"{type(exc).__name__}: {exc}"
        return rep

    flags = module_flags(tree, source)
    defined = defined_symbols(tree)
    used = used_symbols(tree)
    module_dir = path.parent

    docs: list[tuple[int, str, str]] = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef,
                             ast.AsyncFunctionDef)):
            doc = ast.get_docstring(node, clean=False)
            if not doc:
                continue
            scope = getattr(node, "name", "<module>")
            # `ast.Module` carries no position; attribute it to line 1.
            docs.append((getattr(node, "lineno", 1), scope, doc))

    for lineno, scope, doc in docs:
        rep.docstrings += 1
        line_of = lineno

        for m in PATH_CLAIM.finditer(doc):
            rep.claims += 1
            claim = m.group(1).rstrip(".,;:)")
            if not path_exists(claim, module_dir):
                rep.findings.append(Finding(rel, line_of, scope, "path", claim,
                                            "path named in docstring does not exist"))

        for m in FLAG_CLAIM.finditer(doc):
            rep.claims += 1
            flag = m.group(1)
            if flag in FLAG_STOPWORDS or flag in flags:
                continue
            rep.findings.append(Finding(rel, line_of, scope, "flag", flag,
                                        "flag named in docstring is never registered"))

        for m in CMD_CLAIM.finditer(doc):
            rep.claims += 1
            claim = m.group(1).rstrip(".,;:`")
            if not path_exists(claim, module_dir):
                rep.findings.append(Finding(rel, line_of, scope, "cmd", claim,
                                            "command in docstring targets a missing file"))

        for m in BACKTICKED.finditer(doc):
            token = m.group(1).strip()
            core = token[:-2] if token.endswith("()") else token
            if not SYMBOL_CLAIM.match(token):
                continue
            rep.claims += 1
            if core in defined or core in used:
                continue
            rep.findings.append(Finding(rel, line_of, scope, "symbol", token,
                                        "backticked symbol is neither defined nor used"))

    return rep


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--json-out", type=Path, default=None,
                    help="write the full machine-readable report here")
    ap.add_argument("--only", default=None,
                    help="restrict to a path prefix, e.g. tools/infra")
    ap.add_argument("--quiet", action="store_true",
                    help="print only the summary line")
    ap.add_argument("--kinds", default=None,
                    help="comma-separated claim kinds to report, e.g. path,flag,cmd")
    args = ap.parse_args(argv)

    keep = set(args.kinds.split(",")) if args.kinds else None
    files = iter_first_party(args.only)
    reports = [audit_file(f) for f in files]

    by_kind: Counter[str] = Counter()
    by_file: dict[str, list[Finding]] = defaultdict(list)
    total_docs = total_claims = 0
    parse_errors = []

    for rep in reports:
        total_docs += rep.docstrings
        total_claims += rep.claims
        if rep.parse_error:
            parse_errors.append({"file": rep.file, "error": rep.parse_error})
            continue
        for f in rep.findings:
            if keep and f.kind not in keep:
                continue
            by_kind[f.kind] += 1
            by_file[rep.file].append(f)
    hard = sum(v for k, v in by_kind.items() if k not in ADVISORY_KINDS)
    advisory = sum(v for k, v in by_kind.items() if k in ADVISORY_KINDS)

    payload = {
        "scanned_files": len(reports),
        "docstrings": total_docs,
        "claims_checked": total_claims,
        "findings_by_kind": dict(by_kind),
        "hard_findings": hard,
        "advisory_findings": advisory,
        "files_with_findings": len(by_file),
        "parse_errors": parse_errors,
        "findings": [asdict(f) for fs in by_file.values() for f in fs],
    }

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")

    if not args.quiet:
        print(f"scanned {len(reports)} first-party .py files")
        print(f"  docstrings parsed : {total_docs}")
        print(f"  claims checked    : {total_claims}")
        print(f"  findings          : {sum(by_kind.values())} "
              f"in {len(by_file)} files  {dict(by_kind)}")
        print(f"    decidable (path/flag/cmd) : {hard}")
        print(f"    advisory (symbol)          : {advisory}")
        if parse_errors:
            print(f"  parse errors      : {len(parse_errors)}")
        worst = sorted(by_file.items(), key=lambda kv: -len(kv[1]))[:15]
        if worst:
            print("\ntop files by finding count:")
            for name, fs in worst:
                print(f"  {len(fs):4d}  {name}")
    print(f"SUMMARY files={len(reports)} docs={total_docs} claims={total_claims} "
          f"findings={sum(by_kind.values())} hard={hard} advisory={advisory} "
          f"kinds={dict(by_kind)} parse_errors={len(parse_errors)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
