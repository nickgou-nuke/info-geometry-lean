#!/usr/bin/env python3
"""Comment-aware declaration/placeholder scan; not a Lean compiler."""
from __future__ import annotations
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "lean" / "InfoGeometry" / "Nuclear"
OWNERS = ["DetectorTransportKernel", "DetectorVolumeResponse", "DetectorBeerLambert", "DetectorDiskIntegral"]
BRIDGE = ["DetectorResponseIntegral"]


def strip_comments(text: str) -> str:
    out: list[str] = []
    depth = 0
    quoted = False
    i = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1; i += 2
            elif text.startswith("-/", i):
                depth -= 1; i += 2
            else:
                out.append("\n" if text[i] == "\n" else " "); i += 1
        elif quoted:
            if text[i] == "\\":
                i += 2
            elif text[i] == '"':
                quoted = False; out.append(" "); i += 1
            else:
                out.append("\n" if text[i] == "\n" else " "); i += 1
        elif text.startswith("/-", i):
            depth = 1; i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            quoted = True; out.append(" "); i += 1
        else:
            out.append(text[i]); i += 1
    if depth or quoted:
        raise ValueError("Unterminated comment or string")
    return "".join(out)


def declarations(stem: str) -> list[dict[str, object]]:
    code = strip_comments((SOURCE / f"{stem}.lean").read_text())
    banned = re.findall(r"\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b", code)
    if banned:
        raise ValueError(f"{stem}: prohibited declaration or proof token: {banned}")
    namespace = re.search(r"^namespace\s+(\S+)", code, re.M)
    if namespace is None:
        raise ValueError(f"{stem}: missing namespace")
    pat = r"^\s*(?:@\[[^\n]*?\]\s*)?(private\s+)?(?:theorem|lemma)\s+([\w']+)"
    return [{"module": stem, "name": namespace[1] + "." + m[2], "private": bool(m[1])}
            for m in re.finditer(pat, code, re.M)]


def main() -> None:
    core = [d for stem in OWNERS for d in declarations(stem)]
    bridge = [d for stem in BRIDGE for d in declarations(stem)]
    for name, imported, rows in [
        ("DetectorResponseAudit", "DetectorResponseCore", core),
        ("DetectorResponseBridgeAudit", "DetectorResponseIntegral", bridge),
    ]:
        (SOURCE / f"{name}.lean").write_text(
            f"import InfoGeometry.Nuclear.{imported}\n\n" +
            "-- Request transitive kernel dependency reports for every public theorem.\n" +
            "".join(f"#print axioms {row['name']}\n" for row in rows if not row["private"]))
    report = {
        "status": "passed_source_scan_only",
        "kernel_verified": False,
        "public_core_declarations": sum(not d["private"] for d in core),
        "private_core_declarations": sum(bool(d["private"]) for d in core),
        "public_bridge_declarations": len(bridge),
        "declarations": core + bridge,
        "custom_axiom_declarations": 0,
        "proof_placeholders": 0,
        "limitation": "This scan does not check parsing, elaboration, tactic execution, or kernel validity.",
    }
    (ROOT / "validation" / "source_audit.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "declarations"}, indent=2))


if __name__ == "__main__":
    main()
