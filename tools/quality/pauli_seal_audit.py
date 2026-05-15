#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import repo_root
else:
    from tools.pathing import repo_root


ROOT = repo_root()
DEFAULT_FUNCTORIAL_REPORT = "reports/dag/functorial-invariance-audit.json"

DECL_FULL_RE = re.compile(
    r"^\s*(?:(noncomputable)\s+)?(def|abbrev|theorem|lemma|structure|class|instance)\s+([A-Za-z0-9_'.]+)\b"
)
DECL_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma|structure|class|instance)\s+([A-Za-z0-9_'.]+)\b"
)
STRUCT_RE = re.compile(r"^\s*structure\s+([A-Za-z0-9_'.]+)\b")
FIELD_RE = re.compile(r"^\s+([A-Za-z0-9_']+)\s*:\s*(.+?)\s*$")
PHYS_TOKEN_RE = re.compile(
    r"(einstein|penrose|unification|hamiltonian|dirac|majorana|kramers|bekenstein|connes|yangmills|gauge|modular)",
    re.IGNORECASE,
)
INTERFACE_DECL_RE = re.compile(r"(intertwiner|presentation|interface|readiness|unification)", re.IGNORECASE)
TRANSPORT_DECL_RE = re.compile(r"(preserv|invar|isometr|unitar|transport)", re.IGNORECASE)
RFL_RE = re.compile(r"(:=\s*rfl\b)|(\bby\s+rfl\b)|(\bexact\s+rfl\b)")
ID_WITNESS_RE = re.compile(r"\bfun\s+([A-Za-z_][A-Za-z0-9_']*)\s*=>\s*\1\b")
SWAP_WITNESS_RE = re.compile(
    r"\bfun\s+([A-Za-z_][A-Za-z0-9_']*)\s*=>\s*\(\s*\1\.2\s*,\s*\1\.1\s*\)"
)
PROD_SWAP_RE = re.compile(r"\bProd\.swap\b|\.swap\b")
AXIOM_HOLE_RE = re.compile(r"\b(sorry|admit)\b|^\s*axiom\b", re.M)
DEPENDENCY_PACKAGE_RE = re.compile(
    r"(dependencies|assumptions|requirements|obligations|hypotheses|package)$",
    re.IGNORECASE,
)
RESIDUAL_NAME_RE = re.compile(r"residual", re.IGNORECASE)
VANISH_NAME_RE = re.compile(r"(vanish|vanishing|zero|null|eq_zero|is_zero|isZero)", re.IGNORECASE)
PARAM_KEYWORDS = (
    "temperature",
    "inverseTemperature",
    "beta",
    "mass",
    "coupling",
    "chemicalPotential",
    "entropyScale",
    "kappa",
    "lambda",
)
PARAM_NAME_RE = re.compile(
    r"(temperature|inversetemperature|beta|mass|coupling|chemicalpotential|entropyscale|kappa|lambda)",
    re.IGNORECASE,
)
EXISTS_NAME_RE = re.compile(r"(exists|existence|admissible|kms)", re.IGNORECASE)
CLASSICAL_CHOICE_RE = re.compile(r"\bClassical\.choice\b|\bclassical\.choice\b")
PRIVATE_UNIQUENESS_RE = re.compile(
    r"^\s*private\s+(?:theorem|lemma)\s+([A-Za-z0-9_'.]*?(?:unique|uniqueness)[A-Za-z0-9_'.]*)\b",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class Finding:
    directive: str
    file: str
    line: int
    detail: str


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def strip_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_line = False
    in_string = False
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if in_line:
            if ch == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if block_depth > 0:
            if ch == "\n":
                out.append("\n")
                i += 1
                continue
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend("  ")
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend("  ")
                i += 2
                continue
            out.append(" ")
            i += 1
            continue
        if in_string:
            out.append(" " if ch != "\n" else "\n")
            if ch == '"' and (i == 0 or text[i - 1] != "\\"):
                in_string = False
            i += 1
            continue
        if ch == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue
        if ch == "-" and nxt == "-":
            in_line = True
            out.extend("  ")
            i += 2
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            out.extend("  ")
            i += 2
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def count_density(text: str) -> tuple[int, int]:
    comment_lines = 0
    signal_lines = 0
    block_depth = 0
    for raw in text.splitlines():
        line = raw.rstrip("\n")
        stripped = line.strip()
        if block_depth > 0:
            comment_lines += 1
            if "/-" in line:
                block_depth += line.count("/-")
            if "-/" in line:
                block_depth -= line.count("-/")
            continue
        if stripped.startswith("/-"):
            comment_lines += 1
            block_depth += line.count("/-") - line.count("-/")
            continue
        if stripped.startswith("--"):
            comment_lines += 1
            continue
        if stripped == "":
            continue
        if (
            ":=" in line
            or stripped.startswith(("def ", "abbrev ", "theorem ", "lemma ", "structure ", "class ", "instance "))
            or stripped == "by"
            or stripped.startswith("by ")
        ):
            signal_lines += 1
    return comment_lines, signal_lines


def line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def declaration_header(lines: list[str], start: int, max_lines: int = 20) -> str:
    parts: list[str] = []
    upper = min(len(lines), start + max_lines)
    for j in range(start, upper):
        l = lines[j]
        if j > start and (DECL_RE.match(l) or STRUCT_RE.match(l) or l.strip().startswith("/--")):
            break
        parts.append(l)
        if ":=" in l:
            break
    return "\n".join(parts)


def has_shared_param_keyword(a: str, b: str) -> bool:
    al = a.lower()
    bl = b.lower()
    return any(k.lower() in al and k.lower() in bl for k in PARAM_KEYWORDS)


def scan_file(path: Path) -> list[Finding]:
    findings: list[Finding] = []
    raw = path.read_text(encoding="utf-8", errors="ignore")
    text = strip_comments(raw)
    lines = text.splitlines()
    rpath = rel(path)
    has_owner_metric = ("kreinInner" in text) or ("Krein" in text)
    is_canonical_or_core = ("/Canonical/" in f"/{rpath}") or ("/Core/" in f"/{rpath}")

    decl_records: list[tuple[int, str, str, bool]] = []
    for idx, line in enumerate(lines):
        m = DECL_FULL_RE.match(line)
        if not m:
            continue
        decl_records.append((idx, m.group(2), m.group(3), m.group(1) is not None))

    # Collect structure surfaces once to drive Directive I and VI checks.
    existential_structs: dict[str, int] = {}
    i = 0
    while i < len(lines):
        m = STRUCT_RE.match(lines[i])
        if not m:
            i += 1
            continue
        struct_name = m.group(1)
        is_prop_struct = ": Prop" in lines[i]
        j = i + 1
        field_types: list[str] = []
        while j < len(lines):
            l = lines[j]
            if DECL_RE.match(l) or STRUCT_RE.match(l) or l.strip().startswith("end "):
                break
            fm = FIELD_RE.match(l)
            if fm:
                field_types.append(fm.group(2))
            j += 1

        # Directive I (wish-list structures): physically-loaded structure with Prop-only fields.
        if PHYS_TOKEN_RE.search(struct_name) and field_types and all("Prop" in t for t in field_types):
            findings.append(
                Finding(
                    directive="I.no_mask_mandate",
                    file=rpath,
                    line=i + 1,
                    detail=f"structure `{struct_name}` is Prop-only wish-list surface",
                )
            )

        # Directive VI: existential hypothesis packages.
        has_existential_fields = any(("∃" in t) or ("Exists" in t) for t in field_types)
        looks_like_dependency_package = bool(DEPENDENCY_PACKAGE_RE.search(struct_name.split(".")[-1]))
        if is_prop_struct and (has_existential_fields or looks_like_dependency_package):
            existential_structs[struct_name] = i + 1
            short_name = struct_name.split(".")[-1]
            existential_structs.setdefault(short_name, i + 1)
            if has_existential_fields:
                detail = f"Prop structure `{struct_name}` carries existential obligations"
            else:
                detail = f"Prop structure `{struct_name}` is a dependency-package hypothesis shell"
            findings.append(
                Finding(
                    directive="VI.anti_existential_hypothesis",
                    file=rpath,
                    line=i + 1,
                    detail=detail,
                )
            )
        i = max(j, i + 1)

    # Directive II: no floating import shells.
    has_decl = bool(decl_records)
    meaningful = [l.strip() for l in lines if l.strip()]
    if not has_decl and meaningful:
        if all(l.startswith("import ") or l.startswith("open ") or l.startswith("namespace ") or l.startswith("end ") for l in meaningful):
            findings.append(
                Finding(
                    directive="II.functorial_connectivity",
                    file=rpath,
                    line=1,
                    detail="floating module with no declaration/value-edge surface",
                )
            )

    # Directive III: axiom/sorry/admit holes.
    for m in AXIOM_HOLE_RE.finditer(text):
        findings.append(
            Finding(
                directive="III.axiom_surface_seal",
                file=rpath,
                line=line_of(text, m.start()),
                detail=f"forbidden hole token: `{m.group(0).strip()}`",
            )
        )
    if "InfoGeometry.Meta.Admission" in text:
        findings.append(
            Finding(
                directive="III.axiom_surface_seal",
                file=rpath,
                line=1,
                detail="canonical file references Admission layer",
            )
        )

    # Directive IV: semantic density ratio.
    comment_lines, signal_lines = count_density(raw)
    if comment_lines > 0 and signal_lines < 2 * comment_lines:
        findings.append(
            Finding(
                directive="IV.semantic_weight_ratio",
                file=rpath,
                line=1,
                detail=f"comment lines={comment_lines}, proof/def lines={signal_lines}, required >= {2 * comment_lines}",
            )
        )

    # Directive I and V: physically loaded names with no grounded bridge, and rfl-unification.
    has_thermo_geometry_ref = ("InfoGeometry.Thermo" in text) or ("InfoGeometry.Geometry" in text)
    theorem_lemma_records = [(idx, name) for idx, kind, name, _ in decl_records if kind in ("theorem", "lemma")]
    for idx, kind, name, is_noncomputable in decl_records:
        line = lines[idx]
        window = "\n".join(lines[idx : min(len(lines), idx + 36)])
        header = declaration_header(lines, idx)

        # Directive VI: existential package consumed as theorem hypothesis.
        if kind in ("theorem", "lemma"):
            for dep_name in sorted(existential_structs):
                dep_re = re.compile(
                    rf"\([A-Za-z0-9_']+\s*:\s*{re.escape(dep_name)}(?:\s|[)\{{])"
                )
                if dep_re.search(header):
                    findings.append(
                        Finding(
                            directive="VI.anti_existential_hypothesis",
                            file=rpath,
                            line=idx + 1,
                            detail=f"declaration `{name}` consumes existential dependency package `{dep_name}`",
                        )
                    )
                    break

        # Directive IX: residual definitions must have a vanishing theorem surface.
        if kind in ("def", "abbrev") and RESIDUAL_NAME_RE.search(name):
            short_name = name.split(".")[-1]
            base_name = RESIDUAL_NAME_RE.sub("", short_name).strip("_")
            has_vanishing_surface = False
            for j, theorem_name in theorem_lemma_records:
                theorem_header = declaration_header(lines, j)
                theorem_short = theorem_name.split(".")[-1]
                mentions_residual = (
                    short_name in theorem_header
                    or (base_name and base_name.lower() in theorem_short.lower())
                    or RESIDUAL_NAME_RE.search(theorem_short) is not None
                )
                has_vanish_marker = (
                    VANISH_NAME_RE.search(theorem_short) is not None
                    or "= 0" in theorem_header
                    or "=0" in theorem_header
                    or "∃" in theorem_header and " = 0" in theorem_header
                )
                if mentions_residual and has_vanish_marker:
                    has_vanishing_surface = True
                    break
            if not has_vanishing_surface:
                findings.append(
                    Finding(
                        directive="IX.anti_residual_redirect",
                        file=rpath,
                        line=idx + 1,
                        detail=(
                            f"residual definition `{name}` has no accompanying vanishing theorem "
                            "(expected zero/vanishing closure surface)"
                        ),
                    )
                )

        # Directive X: noncomputable physical parameters require existence witness.
        if kind in ("def", "abbrev") and is_noncomputable and PARAM_NAME_RE.search(name):
            short_name = name.split(".")[-1]
            body_window = "\n".join(lines[idx : min(len(lines), idx + 120)])
            uses_choice = CLASSICAL_CHOICE_RE.search(body_window) is not None
            has_exists_surface = False
            for j, theorem_name in theorem_lemma_records:
                theorem_header = declaration_header(lines, j)
                theorem_short = theorem_name.split(".")[-1]
                mentions_parameter = short_name in theorem_header or has_shared_param_keyword(short_name, theorem_short)
                if not mentions_parameter:
                    continue
                if "∃" in theorem_header or EXISTS_NAME_RE.search(theorem_short):
                    has_exists_surface = True
                    break
            if not has_exists_surface:
                detail = (
                    f"noncomputable physical parameter `{name}` has no local existence witness theorem"
                )
                if uses_choice:
                    detail += " (uses Classical.choice-style admission)"
                findings.append(
                    Finding(
                        directive="X.parameter_admission",
                        file=rpath,
                        line=idx + 1,
                        detail=detail,
                    )
                )

        # Directive VII: trivial witness used on interface-like declaration surfaces.
        if INTERFACE_DECL_RE.search(name):
            witness_markers: list[str] = []
            if RFL_RE.search(window):
                witness_markers.append("rfl-like closure")
            if ID_WITNESS_RE.search(window):
                witness_markers.append("identity witness `fun x => x`")
            if SWAP_WITNESS_RE.search(window) or PROD_SWAP_RE.search(window):
                witness_markers.append("swap witness")
            if witness_markers:
                findings.append(
                    Finding(
                        directive="VII.interface_witness_fidelity",
                        file=rpath,
                        line=idx + 1,
                        detail=f"interface-like declaration `{name}` appears to use trivial witness ({', '.join(witness_markers)})",
                    )
                )

        # Directive VIII: proxy metric preservation where owner metric is present.
        if TRANSPORT_DECL_RE.search(name) and has_owner_metric:
            uses_inner = " inner " in f" {window} " or "inner" in window
            uses_krein_inner = "kreinInner" in window
            phase_linear_proxy = "IsPhaseLinear" in window
            if uses_inner and not uses_krein_inner:
                detail = (
                    f"declaration `{name}` uses `inner` without local `kreinInner` evidence "
                    "in a file that carries Krein metric surfaces"
                )
                if phase_linear_proxy:
                    detail += " (contains `IsPhaseLinear` proxy marker)"
                findings.append(
                    Finding(
                        directive="VIII.metric_fidelity",
                        file=rpath,
                        line=idx + 1,
                        detail=detail,
                    )
                )

        if PHYS_TOKEN_RE.search(name):
            if not has_thermo_geometry_ref:
                findings.append(
                    Finding(
                        directive="I.no_mask_mandate",
                        file=rpath,
                        line=idx + 1,
                        detail=f"physically-loaded declaration `{name}` lacks explicit Thermo/Geometry reference",
                    )
                )
            # check nearby body for trivial reflexive closure
            if RFL_RE.search(window):
                findings.append(
                    Finding(
                        directive="V.identity_via_reflexivity",
                        file=rpath,
                        line=idx + 1,
                        detail=f"physically-loaded declaration `{name}` closes by `rfl`-like proof",
                    )
                )

    # Directive XI: no private uniqueness theorem in Canonical/Core.
    if is_canonical_or_core:
        for idx, line in enumerate(lines):
            m = PRIVATE_UNIQUENESS_RE.match(line)
            if m:
                findings.append(
                    Finding(
                        directive="XI.public_uniqueness_mandate",
                        file=rpath,
                        line=idx + 1,
                        detail=f"private uniqueness theorem `{m.group(1)}` in Canonical/Core namespace",
                    )
                )

    return findings


def load_json(path: Path) -> dict[str, Any] | None:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None
    return raw if isinstance(raw, dict) else None


def main() -> int:
    parser = argparse.ArgumentParser(description="Pauli Seal audit (mandatory anti-vacuity directives)")
    parser.add_argument(
        "--root",
        default="lean/InfoGeometry/Canonical",
        help="Root directory to audit (default: lean/InfoGeometry/Canonical)",
    )
    parser.add_argument(
        "--json-out",
        default="reports/pauli-seal-audit.json",
        help="JSON report output path",
    )
    parser.add_argument(
        "--functorial-report",
        default=DEFAULT_FUNCTORIAL_REPORT,
        help="Path to functorial invariance audit JSON report",
    )
    parser.add_argument(
        "--skip-functorial-gate",
        action="store_true",
        help="Skip mandatory reconciliation against functorial invariance report",
    )
    args = parser.parse_args()

    target_root = ROOT / args.root
    if not target_root.exists():
        print(f"[pauli-seal] target root not found: {target_root}", file=sys.stderr)
        return 2

    findings: list[Finding] = []
    files = [p for p in sorted(target_root.rglob("*.lean")) if p.is_file()]
    skipped_missing: list[str] = []
    for p in files:
        try:
            findings.extend(scan_file(p))
        except FileNotFoundError:
            skipped_missing.append(relpath(p))

    functorial_status: dict[str, Any] = {"enabled": not args.skip_functorial_gate}
    if not args.skip_functorial_gate:
        report_path = (ROOT / args.functorial_report).resolve()
        report_rel = str(report_path.relative_to(ROOT)) if str(report_path).startswith(str(ROOT)) else str(report_path)
        functorial_status["report"] = report_rel
        if not report_path.exists():
            findings.append(
                Finding(
                    directive="II.functorial_connectivity",
                    file=report_rel,
                    line=1,
                    detail="missing functorial invariance report; run functorial_invariance_audit.py first",
                )
            )
            functorial_status["state"] = "missing"
        else:
            payload = load_json(report_path)
            if payload is None:
                findings.append(
                    Finding(
                        directive="II.functorial_connectivity",
                        file=report_rel,
                        line=1,
                        detail="invalid functorial invariance report JSON",
                    )
                )
                functorial_status["state"] = "invalid"
            else:
                counts = payload.get("counts", {})
                status = str(payload.get("status", ""))
                functorial_status.update(
                    {
                        "state": "loaded",
                        "status": status,
                        "root_with_canopy_total": counts.get("root_with_canopy_total"),
                        "isomorphism_corridor_total": counts.get("isomorphism_corridor_total"),
                        "simplex_projective_corridor_total": counts.get("simplex_projective_corridor_total"),
                    }
                )
                if status != "PASS":
                    findings.append(
                        Finding(
                            directive="II.functorial_connectivity",
                            file=report_rel,
                            line=1,
                            detail=f"functorial invariance report status is `{status}` (expected PASS)",
                        )
                    )
                root_with_canopy_total = int(counts.get("root_with_canopy_total", 0) or 0)
                isomorphism_corridor_total = int(counts.get("isomorphism_corridor_total", 0) or 0)
                simplex_projective_corridor_total = int(
                    counts.get("simplex_projective_corridor_total", 0) or 0
                )
                if root_with_canopy_total <= 0:
                    findings.append(
                        Finding(
                            directive="II.functorial_connectivity",
                            file=report_rel,
                            line=1,
                            detail="core-to-canopy functorial paths missing",
                        )
                    )
                if isomorphism_corridor_total <= 0:
                    findings.append(
                        Finding(
                            directive="II.functorial_connectivity",
                            file=report_rel,
                            line=1,
                            detail="isomorphism corridors missing (equiv/iso/isomorph/simplex/projective)",
                        )
                    )
                if simplex_projective_corridor_total <= 0:
                    findings.append(
                        Finding(
                            directive="II.functorial_connectivity",
                            file=report_rel,
                            line=1,
                            detail="simplex/projective corridor evidence missing",
                        )
                    )

    out_path = ROOT / args.json_out
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(
        json.dumps(
            {
                "schema": "ig.pauli-seal.v3",
                "mandate": "PAULI_MANDATE I-XI",
                "root": args.root,
                "fileCount": len(files),
                "findingCount": len(findings),
                "functorialInvariance": functorial_status,
                "skippedMissingFiles": skipped_missing,
                "findings": [asdict(f) for f in findings],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )

    print(f"[pauli-seal] files scanned: {len(files)}")
    if skipped_missing:
        print(f"[pauli-seal] skipped missing files: {len(skipped_missing)}")
    print(f"[pauli-seal] findings: {len(findings)}")
    by_directive: dict[str, int] = {}
    for f in findings:
        by_directive[f.directive] = by_directive.get(f.directive, 0) + 1
    for key in sorted(by_directive):
        print(f"[pauli-seal] {key}: {by_directive[key]}")
    if not args.skip_functorial_gate:
        print(f"[pauli-seal] functorial gate: {functorial_status.get('state', 'unknown')}")
        if "status" in functorial_status:
            print(f"[pauli-seal] functorial status: {functorial_status['status']}")
        if "root_with_canopy_total" in functorial_status:
            print(
                "[pauli-seal] functorial roots_with_canopy: "
                f"{functorial_status.get('root_with_canopy_total')}"
            )
        if "isomorphism_corridor_total" in functorial_status:
            print(
                "[pauli-seal] functorial isomorphism corridors: "
                f"{functorial_status.get('isomorphism_corridor_total')}"
            )
        if "simplex_projective_corridor_total" in functorial_status:
            print(
                "[pauli-seal] functorial simplex/projective corridors: "
                f"{functorial_status.get('simplex_projective_corridor_total')}"
            )
    try:
        report_label = out_path.relative_to(ROOT).as_posix()
    except ValueError:
        report_label = str(out_path)
    print(f"[pauli-seal] report: {report_label}")

    if findings:
        print("[pauli-seal] FAILED: mandatory directives violated.")
        return 1
    print("[pauli-seal] PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
