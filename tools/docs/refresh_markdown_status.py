#!/usr/bin/env python3
from __future__ import annotations

import os
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
AUDIT_DATE = "2026-05-02"

EXCLUDED_PREFIXES = (
    ".git/",
    ".agents/",
    ".gemini/",
    ".github/",
    ".lake/",
    "artifacts/",
    "docs/black_books/",
    "docs/black_books_refactor/",
    "external_refs/",
    "skills/",
)


CANONICAL_CURRENT = {
    "PAULI_MANDATE.md",
    "README.md",
    "docs/README.md",
    "docs/CODEBASE_STATUS.md",
    "docs/GenerativeDiscoveryArchitecture.md",
    "docs/RepositoryMemoryMap.md",
    "docs/ModuleMap.md",
    "docs/OperationalIntent.md",
    "docs/GeneratedArtifactsPolicy.md",
    "docs/MarkdownCorpusGovernance.md",
}

MAINTAINED_LOCAL = {
    ".hermes.md",
    "CODEX_TROUBLESHOOTING.md",
    "FORMALIZATION_PROTOCOL.md",
    "GEMINI.md",
    "RELEASE_NOTES.md",
    "THEORY_CANOPY.md",
    "UNIVERSAL_VOLUME_STACK.md",
    "docs/OperatorQuickstart.md",
    "docs/DAGTroubleshooting.md",
    "docs/LOCAL_TOOLCHAIN_ARCHITECTURE.md",
    "docs/LeanTrail.md",
    "docs/Theory.md",
    "docs/ToolingMethodology.md",
    "Installation.md",
    "LLM_DEBT_PROTOCOL.md",
    "LLM_FRONTIER_PROTOCOL.md",
    "NEWCOMER_PATH.md",
    "open_problem.md",
    "SELF_OPTIMIZATION_PROTOCOL.md",
    "tools/README.md",
    "tools/docs/README.md",
    "tools/frontier/README.md",
    "tools/infra/README.md",
    "leantrail/README.md",
    "archive/README.md",
    "handover/README.md",
    "handover/injections/README.md",
    "reports/README.md",
}


@dataclass(frozen=True)
class StatusSpec:
    label: str
    detail: str


def repo_markdown_files() -> list[Path]:
    out: list[Path] = []
    for path in ROOT.rglob("*.md"):
        rel = path.relative_to(ROOT).as_posix()
        if any(rel.startswith(prefix) for prefix in EXCLUDED_PREFIXES):
            continue
        if path.name == "SKILL.md":
            continue
        if should_manage(rel):
            out.append(path)
    return sorted(out)


def all_candidate_markdown_files() -> list[Path]:
    out: list[Path] = []
    for path in ROOT.rglob("*.md"):
        rel = path.relative_to(ROOT).as_posix()
        if any(rel.startswith(prefix) for prefix in EXCLUDED_PREFIXES):
            continue
        if path.name == "SKILL.md":
            continue
        out.append(path)
    return sorted(out)


def should_manage(rel: str) -> bool:
    top_level = "/" not in rel
    if top_level:
        return True
    if rel == "docs/alexandria/ALEXANDRIA_SKILL.md":
        return False
    if rel == "blueprint/README.md":
        return True
    return (
        rel.startswith("docs/")
        or rel.startswith("reports/")
        or rel.startswith("archive/")
        or rel.startswith("handover/")
        or rel.startswith("leantrail/")
        or rel == "tools/README.md"
        or rel == "tools/docs/README.md"
        or rel == "tools/infra/README.md"
        or rel == "tools/frontier/README.md"
        or rel == "tools/frontier/generative_loop_spec.md"
        or rel == "tools/quality/closure_debt_auditor.md"
    )


def classify(rel: str) -> StatusSpec:
    if rel in CANONICAL_CURRENT:
        return StatusSpec(
            "current authority",
            "Maintained against the live code surface.",
        )
    if rel in MAINTAINED_LOCAL:
        return StatusSpec(
            "maintained local guide",
            "Current for this subsystem, but subordinate to repo-wide authority docs and code.",
        )
    if rel.startswith("reports/"):
        return StatusSpec(
            "generated/historical report",
            "Treat this as a snapshot. Regenerate before relying on it.",
        )
    if rel.startswith("archive/"):
        return StatusSpec(
            "archival reference",
            "Kept for provenance and archaeology, not as current policy.",
        )
    if rel.startswith("handover/"):
        return StatusSpec(
            "historical handover",
            "Workflow history and packet memory, not current repository authority.",
        )
    if rel.startswith(".agents/workflows/"):
        return StatusSpec(
            "workflow-local reference",
            "Useful for local workflow context, but not part of the canonical repo status surface.",
        )
    if rel.startswith("docs/"):
        return StatusSpec(
            "reference memory",
            "Re-audit against current code before using for policy, design claims, or status.",
        )
    if rel.startswith("external_refs/") or rel.startswith("arxiv-test-output/"):
        return StatusSpec(
            "external/reference material",
            "Stored as reference input, not as a statement of current repository behavior.",
        )
    return StatusSpec(
        "reference memory",
        "Not part of the maintained authority surface unless explicitly promoted.",
    )


def relative_link(from_rel: str, target_rel: str) -> str:
    from_dir = (ROOT / from_rel).parent
    return os.path.relpath(ROOT / target_rel, from_dir).replace(os.sep, "/")


def make_status_block(rel: str, spec: StatusSpec) -> list[str]:
    repo_readme = relative_link(rel, "README.md")
    docs_readme = relative_link(rel, "docs/README.md")
    codebase_status = relative_link(rel, "docs/CODEBASE_STATUS.md")
    return [
        f"> Status: `{spec.label}`",
        f"> Audited: {AUDIT_DATE}",
        f"> Note: {spec.detail}",
        f"> See: [README.md]({repo_readme}), [docs/README.md]({docs_readme}), [docs/CODEBASE_STATUS.md]({codebase_status})",
        "",
    ]


def strip_existing_status(lines: list[str], start: int) -> tuple[list[str], int]:
    i = start
    if i < len(lines) and lines[i].startswith("> Status:"):
        while i < len(lines) and lines[i].startswith(">"):
            i += 1
        while i < len(lines) and lines[i] == "":
            i += 1
    return lines, i


def strip_inserted_status_block(path: Path) -> bool:
    lines = path.read_text(encoding="utf-8").splitlines()
    insert_at = 0
    if lines and lines[0].startswith("#"):
        insert_at = 1
        while insert_at < len(lines) and lines[insert_at] == "":
            insert_at += 1
    if insert_at >= len(lines) or not lines[insert_at].startswith("> Status:"):
        return False
    if insert_at + 1 >= len(lines) or lines[insert_at + 1] != f"> Audited: {AUDIT_DATE}":
        return False
    _, content_start = strip_existing_status(lines, insert_at)
    new_lines = lines[:insert_at]
    if new_lines and (content_start < len(lines)):
        if new_lines[-1] != "" and lines[content_start] != "":
            new_lines.append("")
    new_lines.extend(lines[content_start:])
    new_text = "\n".join(new_lines).rstrip() + "\n"
    old_text = path.read_text(encoding="utf-8")
    if new_text == old_text:
        return False
    path.write_text(new_text, encoding="utf-8")
    return True


def rewrite_file(path: Path) -> bool:
    rel = path.relative_to(ROOT).as_posix()
    spec = classify(rel)
    lines = path.read_text(encoding="utf-8").splitlines()

    insert_at = 0
    if lines and lines[0].startswith("#"):
        insert_at = 1
        while insert_at < len(lines) and lines[insert_at] == "":
            insert_at += 1

    _, content_start = strip_existing_status(lines, insert_at)
    new_lines = lines[:insert_at]
    if insert_at == 1 and new_lines and len(lines) > 1 and lines[1] != "":
        new_lines.append("")
    new_lines.extend(make_status_block(rel, spec))
    new_lines.extend(lines[content_start:])
    new_text = "\n".join(new_lines).rstrip() + "\n"
    old_text = path.read_text(encoding="utf-8")
    if new_text == old_text:
        return False
    path.write_text(new_text, encoding="utf-8")
    return True


def main() -> int:
    changed = 0
    managed = {path.relative_to(ROOT).as_posix() for path in repo_markdown_files()}
    for path in all_candidate_markdown_files():
        rel = path.relative_to(ROOT).as_posix()
        if rel in managed:
            continue
        if strip_inserted_status_block(path):
            changed += 1
    for path in repo_markdown_files():
        if rewrite_file(path):
            changed += 1
    print(f"updated markdown status blocks: {changed}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
