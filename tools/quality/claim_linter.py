#!/usr/bin/env python3
"""Fail-closed claim linter for manuscript prose.

Repository law (AGENTS.md, *The Colimit Continuum Mandate*; see also
docs/REPO_DEEP_SEARCH_PROTOCOL.md):

    Do NOT hallucinate analytical continuations. Do NOT use physical rhetoric
    to justify missing proofs.

A manuscript is where that failure mode actually lands: a physics statement
with no kernel-checked owner reads as certified even though nothing backs it.
This linter makes the absence loud instead of silent.

Every named law in a document must carry exactly one provenance tag:

    [repo-owned: Module#decl]   kernel-checked; `Module` must resolve to a
                                 repo-owned .lean file and `decl` must actually
                                 be declared in it
    [partial: <what is missing>]  partially formalised; the gap is stated
    [unformalized]              prose only; no Lean content is claimed

An untagged law is a hard failure. A dangling `repo-owned` reference is a hard
failure. There is no warn mode: the linter fails closed, because a claim-gate
that can be talked out of failing is not a gate.

Exit codes:
    0  clean
    1  untagged laws, dangling references, or malformed tags
    2  usage / IO error
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Dict, Iterable, List, Set, Tuple

_REPO_ROOT = Path(__file__).resolve().parents[2]

# A "law" is a numbered or titled mathematical assertion. Deliberately narrow:
# prose, derivations and displayed equations that merely restate a tagged law
# are not themselves laws, or every paper would fail.
LAW_HEAD = re.compile(
    r"^\s*(?:>+\s*)?(?:#{1,6}\s+)?"
    r"\*\*\s*(Theorem|Lemma|Proposition|Definition|Corollary|Conjecture)\b"
    r"|^\s*(?:>+\s*)?(?:#{1,6}\s+)?"
    r"(Theorem|Lemma|Proposition|Definition|Corollary|Conjecture)\s+[0-9IVX]"
    r"|^\|\s*\*\*\s*(Theorem|Lemma|Proposition|Definition|Corollary)\b",
    re.IGNORECASE,
)

TAG_OWNED = re.compile(r"\[repo-owned:\s*([^\]]+?)\s*\]")
TAG_PARTIAL = re.compile(r"\[partial:[^\]]*\]")
TAG_UNFORMALIZED = re.compile(r"\[unformalized\]")

def _parse_owners(body: str) -> List[Tuple[str, str]]:
    """Parse a `[repo-owned: …]` body into (module, decl) pairs.

    A law may need more than one owner: a two-step chain that crosses modules is
    still one law. Keep ONE tag, but let it list several owners separated by
    ';', so "exactly one provenance tag" stays literally true and auditable.
    """
    owners: List[Tuple[str, str]] = []
    for part in body.split(";"):
        part = part.strip().strip("`")
        if not part:
            continue
        if "#" in part:
            module, decl = part.split("#", 1)
            owners.append((module.strip(), decl.strip().strip("` ")))
        else:
            owners.append((part, ""))
    return owners

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|instance)\s+"
    r"([^\s(){}\[\],:]+)",
    re.MULTILINE,
)


def _norm_module(token: str) -> str:
    """Normalise a module reference to a repo-relative path stem.

    Accepts dotted Lean module names, .lean paths, and bare file names.
    """
    t = token.strip().strip("`").replace("\\", "/")
    if t.endswith(".lean"):
        t = t[: -len(".lean")]
    if t.startswith("lean/"):
        return t
    # Everything else is relative to the source root, whether written dotted
    # (InfoGeometry.Canonical.X) or slashed (InfoGeometry/Canonical/X).
    return "lean/" + t.replace(".", "/")


def build_index(repo_root: Path) -> Dict[str, Set[str]]:
    """Map repo-relative module stem -> set of declared top-level names."""
    index: Dict[str, Set[str]] = {}
    lean = repo_root / "lean"
    if not lean.is_dir():
        return index
    for path in lean.rglob("*.lean"):
        s = str(path)
        if "/.kilo/" in s or "/archive/" in s or "/external_refs/" in s:
            continue
        rel = path.relative_to(repo_root).as_posix()[: -len(".lean")]
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        names = {m.group(1) for m in DECL.finditer(text)}
        index[rel] = names
    return index


def check_document(doc: Path, index: Dict[str, Set[str]], repo_root: Path) -> List[Dict]:
    """Return one finding per unresolved law.

    The linter is a *detector*, not a judge. It reports mechanical facts --
    "this law carries no provenance tag", "this owner does not resolve" -- and
    refuses to decide whether the underlying claim is true. Adjudication is an
    independent audit step; see docs/CLAIM_LINT_AUDIT_PROTOCOL.md.
    """
    findings: List[Dict] = []
    docid = doc.as_posix()
    try:
        text = doc.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        return [{"id": f"{docid}:1:IO", "kind": "io", "doc": docid, "line": 1,
                 "message": f"cannot read ({exc})", "excerpt": ""}]

    lines = text.splitlines()
    # A law's tag must lie inside ITS OWN block. Bound the window at the next
    # law heading rather than a fixed line count, otherwise two adjacent short
    # laws borrow each other's tags and the screen reports phantom ambiguity.
    for i, line in enumerate(lines):
        if not LAW_HEAD.match(line):
            continue
        lineno = i + 1
        excerpt = line.strip()[:120]
        stop = len(lines)
        for j in range(i + 1, len(lines)):
            if LAW_HEAD.match(lines[j]):
                stop = j
                break
        window = "\n".join(lines[i:stop])

        owned_raw = TAG_OWNED.findall(window)
        n_partial = len(TAG_PARTIAL.findall(window))
        n_unform = len(TAG_UNFORMALIZED.findall(window))

        def add(kind: str, message: str) -> None:
            findings.append({
                "id": f"{docid}:{lineno}:{kind}",
                "kind": kind, "doc": docid, "line": lineno,
                "message": message, "excerpt": excerpt,
            })

        total = len(owned_raw) + n_partial + n_unform
        if total == 0:
            add("untagged",
                "no [repo-owned: …], [partial: …] or [unformalized] tag within "
                "the following block")
            continue
        if total > 1:
            add("ambiguous",
                f"{total} provenance tags on one law; exactly one kind is "
                "required (one repo-owned tag may list several owners)")
            continue

        for owner_body in owned_raw:
            for mod, name in _parse_owners(owner_body):
                rel = _norm_module(mod)
                if rel not in index:
                    add("dangling_module",
                        f"module '{mod}' is not a repo-owned Lean file under lean/")
                    continue
                if not name:
                    add("malformed",
                        f"[repo-owned: {mod}] has no '#decl' component")
                    continue
                names = index[rel]
                bare = name.split(".")[-1]
                if name not in names and bare not in names:
                    close = sorted(n for n in names if n.lower() == bare.lower())
                    hint = f" (did you mean: {', '.join(close)}?)" if close else ""
                    add("dangling_decl",
                        f"'{name}' is not declared in {rel}{hint}")
    return findings


def main(argv: Iterable[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("documents", nargs="+", help="markdown files or directories")
    ap.add_argument("--repo-root", default=str(_REPO_ROOT))
    ap.add_argument("--json", action="store_true",
                    help="emit findings as JSON for the audit step")
    args = ap.parse_args(list(argv) if argv is not None else None)

    repo_root = Path(args.repo_root).resolve()
    index = build_index(repo_root)
    if not index:
        print("claim_linter: no repo-owned Lean modules under lean/", file=sys.stderr)
        return 2

    docs: List[Path] = []
    for d in args.documents:
        p = Path(d)
        docs.extend(sorted(p.rglob("*.md")) if p.is_dir() else [p])

    findings: List[Dict] = []
    for doc in docs:
        if not doc.is_file():
            findings.append({"id": f"{doc}:1:io", "kind": "io", "doc": str(doc),
                             "line": 1, "message": "no such file", "excerpt": ""})
            continue
        findings.extend(check_document(doc, index, repo_root))

    if args.json:
        print(json.dumps({"repo_root": str(repo_root),
                          "modules_indexed": len(index),
                          "documents": len(docs),
                          "findings": findings}, indent=2))
        return 1 if findings else 0

    if findings:
        by_kind: Dict[str, int] = {}
        for f in findings:
            by_kind[f["kind"]] = by_kind.get(f["kind"], 0) + 1
        print(f"claim_linter: {len(findings)} finding(s) across "
              f"{len({f['doc'] for f in findings})} document(s)", file=sys.stderr)
        for kind, n in sorted(by_kind.items()):
            print(f"  {kind}: {n}", file=sys.stderr)
        print("\nThese are MECHANICAL findings only. They establish that a law "
              "lacks an owner\nor names one that does not resolve. They say "
              "nothing about whether the\nnamed owner actually proves the stated "
              "claim -- that is the independent\naudit step "
              "(docs/CLAIM_LINT_AUDIT_PROTOCOL.md). Do not treat a clean\nscreen "
              "as certification.\n", file=sys.stderr)
        for f in findings:
            print(f"  - {f['id']}\n      {f['message']}\n      > {f['excerpt']}",
                  file=sys.stderr)
        return 1

    print(f"claim_linter: screen clean ({len(docs)} document(s)). "
          "This means every law NAMES an owner -- not that the owner proves it.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
