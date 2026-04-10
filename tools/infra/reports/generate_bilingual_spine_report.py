#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
    from tools.infra.reports.common import generated_timestamp, normalize_user_path, write_text
    from tools.pathing import lean_root, repo_root
else:
    from tools.infra.reports.common import generated_timestamp, normalize_user_path, write_text
    from tools.pathing import lean_root, repo_root


SCHEMA_VERSION = 1
DEFAULT_SPINE_MODULE = "InfoGeometry.Canonical.RedLine"
DEFAULT_OUT = "reports/dag/bilingual-spine-report.md"
DEFAULT_JSON_OUT = "reports/dag/bilingual-spine-report.json"
DEFAULT_IMPORT_PREFIX = "InfoGeometry."

IMPORT_RE = re.compile(r"^\s*import\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
DECL_RE = re.compile(
    r"^\s*(?:(?:protected|noncomputable|private|unsafe|partial)\s+)*"
    r"(?:def|theorem|lemma|class|structure|inductive|abbrev|opaque|axiom|instance)\s+"
    r"(?P<name>[A-Za-z0-9_'.]+)"
)
LANG_TAG_RE = re.compile(r"\b(?P<tag>[A-Z]{2}):")

CONTRACT_MARKERS: dict[str, re.Pattern[str]] = {
    "redline_anchor": re.compile(
        r"\b(redline|repo-native|projective root|owner surface|canonical bridge surface)\b", re.IGNORECASE
    ),
    "mathlib_anchor": re.compile(r"\bmathlib\b", re.IGNORECASE),
    "comparison_anchor": re.compile(r"\b(comparison|coincidence|isomorphism|transport)\b", re.IGNORECASE),
    "upstairs_anchor": re.compile(
        r"\b(upstairs|does not descend|non-descend|not descend|projective space is itself linear)\b",
        re.IGNORECASE,
    ),
    "references_anchor": re.compile(r"\b(references?|bibliography|citations?)\b", re.IGNORECASE),
}


@dataclass(frozen=True)
class ModuleAudit:
    module: str
    path: str
    import_count: int
    info_import_count: int
    mathlib_import_count: int
    info_imports: list[str]
    mathlib_imports: list[str]
    declaration_count: int
    declaration_docstring_missing_count: int
    declaration_docstring_missing_sample: list[str]
    has_module_docstring: bool
    module_docstring_language_tags: list[str]
    module_docstring_has_bilingual_tags: bool
    contract_markers: dict[str, bool]

    def has_contract(self) -> bool:
        return self.has_module_docstring and all(self.contract_markers.values())


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate a bilingual RedLine spine report: import-closure modules, docstring coverage, "
            "and bridge-contract marker presence."
        )
    )
    parser.add_argument(
        "--spine-module",
        default=DEFAULT_SPINE_MODULE,
        help="Root module used to build the import closure (default: InfoGeometry.Canonical.RedLine).",
    )
    parser.add_argument(
        "--import-prefix",
        default=DEFAULT_IMPORT_PREFIX,
        help="Only follow imports with this prefix when building closure (default: InfoGeometry.).",
    )
    parser.add_argument(
        "--transitive",
        action="store_true",
        help="Use full transitive import closure. Default is RedLine + direct imports only.",
    )
    parser.add_argument(
        "--out",
        default=DEFAULT_OUT,
        help="Markdown report output path.",
    )
    parser.add_argument(
        "--json-out",
        default=DEFAULT_JSON_OUT,
        help="JSON report output path.",
    )
    parser.add_argument(
        "--missing-sample-size",
        type=int,
        default=8,
        help="Max declaration names sampled per-module for missing docstrings.",
    )
    parser.add_argument(
        "--enforce",
        action="store_true",
        help="Return non-zero when module contract markers are missing.",
    )
    parser.add_argument(
        "--stub-out-dir",
        help=(
            "Optional directory for per-module bilingual docstring stubs. "
            "When set, stubs are emitted for modules missing the full contract."
        ),
    )
    return parser.parse_args()


def module_to_path(module: str, lean_dir: Path) -> Path:
    return (lean_dir / Path(*module.split("."))).with_suffix(".lean")


def parse_imports(text: str) -> list[str]:
    out: list[str] = []
    for line in text.splitlines():
        m = IMPORT_RE.match(line)
        if m:
            out.append(m.group("name"))
    return out


def extract_module_docstring(text: str) -> str | None:
    start = text.find("/-!")
    if start == -1:
        return None
    end = text.find("-/", start + 3)
    if end == -1:
        return None
    return text[start : end + 2]


def declaration_docstring_gaps(text: str, sample_size: int) -> tuple[int, int, list[str]]:
    lines = text.splitlines()
    in_docstring = False
    docstring_just_ended = False
    declaration_count = 0
    missing: list[str] = []

    for line in lines:
        stripped = line.strip()
        if stripped.startswith("/--"):
            in_docstring = True
        if in_docstring and "-/" in line:
            in_docstring = False
            docstring_just_ended = True
            continue
        if docstring_just_ended and not stripped:
            continue
        m = DECL_RE.match(line.lstrip())
        if m:
            declaration_count += 1
            name = m.group("name")
            if not docstring_just_ended:
                missing.append(name)
            docstring_just_ended = False
            continue
        if stripped and not stripped.startswith("--") and not stripped.startswith("@[") and not stripped.startswith("attribute"):
            docstring_just_ended = False

    return declaration_count, len(missing), missing[:sample_size]


def build_import_closure(
    root_module: str,
    *,
    import_prefix: str,
    lean_dir: Path,
    transitive: bool,
) -> list[str]:
    if not transitive:
        root_path = module_to_path(root_module, lean_dir)
        if not root_path.exists():
            return []
        root_text = root_path.read_text(encoding="utf-8", errors="ignore")
        direct = []
        seen_direct: set[str] = set()
        for imported in parse_imports(root_text):
            if import_prefix and not imported.startswith(import_prefix):
                continue
            if imported in seen_direct:
                continue
            seen_direct.add(imported)
            direct.append(imported)
        return [root_module, *direct]

    seen: set[str] = set()
    ordered: list[str] = []
    pending: list[str] = [root_module]

    while pending:
        module = pending.pop(0)
        if module in seen:
            continue
        seen.add(module)
        path = module_to_path(module, lean_dir)
        if not path.exists():
            continue
        ordered.append(module)
        imports = parse_imports(path.read_text(encoding="utf-8", errors="ignore"))
        for imported in imports:
            if import_prefix and not imported.startswith(import_prefix):
                continue
            if imported not in seen:
                pending.append(imported)

    return ordered


def audit_module(module: str, *, lean_dir: Path, root: Path, sample_size: int) -> ModuleAudit:
    path = module_to_path(module, lean_dir)
    text = path.read_text(encoding="utf-8", errors="ignore")
    imports = parse_imports(text)
    module_doc = extract_module_docstring(text)
    language_tags: list[str] = []
    marker_status = {name: False for name in CONTRACT_MARKERS}
    if module_doc is not None:
        language_tags = sorted({m.group("tag") for m in LANG_TAG_RE.finditer(module_doc)})
        for name, pattern in CONTRACT_MARKERS.items():
            marker_status[name] = bool(pattern.search(module_doc))
    declaration_count, missing_count, missing_sample = declaration_docstring_gaps(text, sample_size)
    rel_path = str(path.relative_to(root))
    return ModuleAudit(
        module=module,
        path=rel_path,
        import_count=len(imports),
        info_import_count=sum(1 for imp in imports if imp.startswith("InfoGeometry.")),
        mathlib_import_count=sum(1 for imp in imports if imp.startswith("Mathlib.")),
        info_imports=sorted({imp for imp in imports if imp.startswith("InfoGeometry.")}),
        mathlib_imports=sorted({imp for imp in imports if imp.startswith("Mathlib.")}),
        declaration_count=declaration_count,
        declaration_docstring_missing_count=missing_count,
        declaration_docstring_missing_sample=missing_sample,
        has_module_docstring=module_doc is not None,
        module_docstring_language_tags=language_tags,
        module_docstring_has_bilingual_tags=("EN" in language_tags and len(language_tags) >= 2),
        contract_markers=marker_status,
    )


def build_markdown_report(
    *,
    root_module: str,
    audits: list[ModuleAudit],
    root: Path,
) -> str:
    total_modules = len(audits)
    contract_ready = sum(1 for row in audits if row.has_contract())
    missing_module_doc = sum(1 for row in audits if not row.has_module_docstring)
    missing_decl_doc = sum(row.declaration_docstring_missing_count for row in audits)
    missing_contract_modules = [row for row in audits if not row.has_contract()]
    heavy_decl_gaps = sorted(
        [row for row in audits if row.declaration_docstring_missing_count > 0],
        key=lambda row: row.declaration_docstring_missing_count,
        reverse=True,
    )

    lines: list[str] = [
        "# Bilingual RedLine Spine Report",
        "",
        f"Generated: {generated_timestamp()}",
        f"Repository: {root}",
        f"Spine root: `{root_module}`",
        "",
        "## Summary",
        "",
        f"- modules in RedLine import-closure: **{total_modules}**",
        f"- modules with full bilingual contract markers: **{contract_ready}**",
        f"- modules missing module docstring: **{missing_module_doc}**",
        f"- total declaration docstring gaps: **{missing_decl_doc}**",
        "",
        "## Contract Marker Legend",
        "",
        "- `redline_anchor`: repo-native/RedLine owner framing is explicit",
        "- `mathlib_anchor`: mathlib presentation/assembler role is explicit",
        "- `comparison_anchor`: translation/comparison theorem surface is explicit",
        "- `upstairs_anchor`: upstairs/non-descending note is explicit",
        "- `references_anchor`: references/citation anchor is explicit",
        "",
    ]

    if missing_contract_modules:
        lines.extend(
            [
                "## Modules Missing Full Contract",
                "",
                "| Module | Path | Missing Markers | Lang Tags |",
                "|---|---|---|---|",
            ]
        )
        for row in missing_contract_modules:
            missing = [name for name, present in row.contract_markers.items() if not present]
            missing_text = ", ".join(missing) if missing else "module_docstring_missing"
            langs = ",".join(row.module_docstring_language_tags) if row.module_docstring_language_tags else "-"
            lines.append(f"| `{row.module}` | `{row.path}` | `{missing_text}` | `{langs}` |")
        lines.append("")

    if heavy_decl_gaps:
        lines.extend(
            [
                "## Declaration Docstring Gaps (Top Modules)",
                "",
                "| Module | Missing | Sample |",
                "|---|---:|---|",
            ]
        )
        for row in heavy_decl_gaps[:15]:
            sample = ", ".join(row.declaration_docstring_missing_sample) if row.declaration_docstring_missing_sample else "-"
            lines.append(f"| `{row.module}` | {row.declaration_docstring_missing_count} | `{sample}` |")
        lines.append("")

    lines.extend(
        [
            "## Suggested Module Header Template",
            "",
            "```lean",
            "/-!",
            "# <Module Title>",
            "",
            "EN: <short English intent>",
            "BG: <short Bulgarian intent>",
            "",
            "Redline: <repo-native owner statement>",
            "Mathlib: <mathlib-native statement/assembler role>",
            "Comparison: <named theorem linking the two presentations>",
            "Upstairs: <what remains ambient / does not descend>",
            "",
            "References:",
            "- <mathlib file / paper / note>",
            "-/",
            "```",
            "",
        ]
    )
    return "\n".join(lines)


def build_json_payload(*, root_module: str, audits: list[ModuleAudit]) -> dict[str, Any]:
    return {
        "schemaVersion": SCHEMA_VERSION,
        "spineModule": root_module,
        "moduleCount": len(audits),
        "contractReadyCount": sum(1 for row in audits if row.has_contract()),
        "moduleDocstringMissingCount": sum(1 for row in audits if not row.has_module_docstring),
        "declarationDocstringMissingTotal": sum(row.declaration_docstring_missing_count for row in audits),
        "modules": [
            {
                "module": row.module,
                "path": row.path,
                "importCount": row.import_count,
                "infoImportCount": row.info_import_count,
                "mathlibImportCount": row.mathlib_import_count,
                "infoImports": row.info_imports,
                "mathlibImports": row.mathlib_imports,
                "declarationCount": row.declaration_count,
                "declarationDocstringMissingCount": row.declaration_docstring_missing_count,
                "declarationDocstringMissingSample": row.declaration_docstring_missing_sample,
                "hasModuleDocstring": row.has_module_docstring,
                "moduleDocstringLanguageTags": row.module_docstring_language_tags,
                "moduleDocstringHasBilingualTags": row.module_docstring_has_bilingual_tags,
                "contractMarkers": row.contract_markers,
                "contractReady": row.has_contract(),
            }
            for row in audits
        ],
    }


def sanitize_module_filename(module: str) -> str:
    return module.replace(".", "__") + ".md"


def build_stub_text(row: ModuleAudit) -> str:
    missing_markers = [name for name, ok in row.contract_markers.items() if not ok]
    references = row.mathlib_imports + row.info_imports[:8]
    ref_lines = "\n".join(f"- `{ref}`" for ref in references) if references else "- <add references>"
    return "\n".join(
        [
            f"# Bilingual Docstring Stub: `{row.module}`",
            "",
            f"Path: `{row.path}`",
            f"Missing markers: `{', '.join(missing_markers) if missing_markers else '-'}`",
            "",
            "```lean",
            "/-!",
            "# <Module Title>",
            "",
            "EN: <short English intent>",
            "BG: <short Bulgarian intent>",
            "",
            "Redline: <repo-native owner statement>",
            "Mathlib: <mathlib-native statement/assembler role>",
            "Comparison: <named theorem linking the two presentations>",
            "Upstairs: <what remains ambient / does not descend>",
            "",
            "References:",
            "- <mathlib file / paper / note>",
            "-/",
            "```",
            "",
            "## Suggested references from current imports",
            "",
            ref_lines,
            "",
        ]
    )


def write_stub_bundle(out_dir: Path, audits: list[ModuleAudit]) -> int:
    out_dir.mkdir(parents=True, exist_ok=True)
    written = 0
    for row in audits:
        if row.has_contract():
            continue
        target = out_dir / sanitize_module_filename(row.module)
        write_text(target, build_stub_text(row))
        written += 1
    return written


def main() -> int:
    args = parse_args()
    root = repo_root()
    lean_dir = lean_root()
    out_path = normalize_user_path(args.out, root / DEFAULT_OUT)
    json_out_path = normalize_user_path(args.json_out, root / DEFAULT_JSON_OUT)

    modules = build_import_closure(
        args.spine_module,
        import_prefix=args.import_prefix,
        lean_dir=lean_dir,
        transitive=args.transitive,
    )
    if not modules:
        raise SystemExit(f"no modules found for spine root {args.spine_module!r}")

    audits = [audit_module(module, lean_dir=lean_dir, root=root, sample_size=max(args.missing_sample_size, 1)) for module in modules]
    markdown = build_markdown_report(root_module=args.spine_module, audits=audits, root=root)
    payload = build_json_payload(root_module=args.spine_module, audits=audits)

    write_text(out_path, markdown)
    write_text(json_out_path, json.dumps(payload, indent=2) + "\n")

    if args.stub_out_dir:
        stub_out_dir = normalize_user_path(args.stub_out_dir, root / "reports/dag/bilingual-docstring-stubs")
        written = write_stub_bundle(stub_out_dir, audits)
        print(f"[bilingual-spine] wrote {written} stubs under {stub_out_dir}")

    contract_missing = sum(1 for row in audits if not row.has_contract())
    print(f"[bilingual-spine] wrote {out_path}")
    print(f"[bilingual-spine] wrote {json_out_path}")
    print(
        "[bilingual-spine] summary: "
        f"modules={len(audits)} "
        f"contract_ready={payload['contractReadyCount']} "
        f"module_doc_missing={payload['moduleDocstringMissingCount']} "
        f"decl_doc_missing_total={payload['declarationDocstringMissingTotal']}"
    )
    if args.enforce and contract_missing > 0:
        print(f"[bilingual-spine] enforce: failing due to {contract_missing} modules missing full contract markers")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
