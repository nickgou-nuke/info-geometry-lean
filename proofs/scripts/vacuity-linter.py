#!/usr/bin/env python3
"""Lean 4 vacuity linter.

The linter is intentionally conservative. It classifies Lean source using a
mix of text patterns and optional compiled-graph metadata when available.

Core target criterion:
  AST well-formed + real deps + real proof body

Classifications:
  - non_vacuous
  - bookkeeping_vacuous
  - deferred_interface_pass_through
  - suspiciously_vacuous
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path
from typing import Any, Iterable, List, Tuple

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_GRAPH = REPO_ROOT / "proofs" / "proof_graph.json"

VACUITY_PATTERNS = [
    (1.0, "def_zero", r"def\s+\w+[^=]*?:\s*(?:Prop|ℕ|ℤ|ℚ|ℝ|ℂ|Q)\s*:=\s*0", "Vacuous raw zero scalar definition"),
    (0.9, "trivial_proof", r"theorem\s+\w+.*:.*:=.*\bby\s+trivial\b", "Theorem proven with `by trivial`"),
    (0.8, "trivial_bang", r"theorem\s+\w+.*:.*:=.*\bby\s+trivial!", "Theorem proven with `by trivial!`"),
    (0.7, "admit_proof", r"theorem\s+\w+.*:.*:=.*\bby\s+admit\b", "Theorem proven with `by admit`"),
    (0.7, "sorry_proof", r"theorem\s+\w+.*:.*:=.*\bby\s+sorry\b", "Theorem proven with `by sorry`"),
    (0.6, "true_pattern", r"theorem\s+\w+.*:\s*True\b.*:=", "Theorem states `True`"),
    (0.5, "exact_trivial", r"by\s+exact\s+(True\.trivial|trivial|rfl)\b", "Uses `exact trivial`/`exact rfl`"),
    (0.7, "exact_constructor_trivial", r"exact\s+⟨[^⟩]*(?:True\.trivial|trivial)[^⟩]*⟩", "Constructed proof tuple contains `trivial`"),
    (0.8, "constructor_trivial", r"constructor\s*(?:<;>|;|\n\s*)\s*(?:first\s*\|\s*)?(?:trivial|exact\s+trivial)\b", "`constructor` immediately discharges mathematical content with `trivial`"),
    (0.5, "rfl_vacuous", r"theorem\s+\w+.*:.*:=.*\bby\s+rfl\b", "Theorem proven with `by rfl`"),
    (0.4, "calc_circle", r"calc\s+\n(\s+\w+\s+:=.*\n)+", "`calc` block"),
    (0.3, "empty_where", r"theorem\s+\w+\s+.*:=\s*$", "Theorem with empty body"),
    (0.3, "simp_vacuous", r"by\s+simp(\s*)$", "`by simp` without arguments"),
    (0.2, "auto_prover", r"by\s+(nlinarith|omega|arith|aesop|polyrith)\b", "Automatic prover used"),
    (0.4, "empty_body", r"theorem\s+\w+.*:=\s*--", "Theorem body is just a comment"),
]

TRIVIAL_PATTERN_NAMES = {
    "def_zero",
    "trivial_proof",
    "trivial_bang",
    "admit_proof",
    "sorry_proof",
    "true_pattern",
    "exact_trivial",
    "exact_constructor_trivial",
    "constructor_trivial",
    "rfl_vacuous",
    "empty_where",
    "empty_body",
}

OBFUSCATION_TOKENS = (
    "DeferredInterface",
    "DeferredInterfaceBacked",
    "Witness",
    "witness",
    "Certificate",
    "certificate",
    "Sample",
    "sample",
    "Bound",
    "bound",
    "OwnerDebt",
    "Bookkeeping",
    "Assumption",
    "Assumed",
    "Claim",
    "Debt",
)

ANTI_CONFAB_VOCABULARY = (
    "theorem-honest",
    "theorem_honest",
    "theorem honest",
    "zero-sorry",
    "zero_sorry",
    "zero sorry",
    "zero-sorries",
    "zero_sorries",
    "zero sorries",
    "zero-axiom",
    "zero_axiom",
    "zero axiom",
    "zero-axioms",
    "zero_axioms",
    "zero axioms",
    "oops",
    "opaque",
)

PREMISE_FIELD_TOKENS = (
    "analytic",
    "physical",
    "computed",
    "constructed",
    "realized",
    "deferred_interface",
    "discharged",
    "proved",
    "claim",
    "assumption",
    "witness",
    "certificate",
    "sample",
    "bound",
    "debt",
    "theorem_honest",
    "zero_sorry",
    "zero_sorries",
    "zero_axiom",
    "zero_axioms",
    "oops",
    "opaque",
)

DEFERRED_INTERFACE_HINTS = OBFUSCATION_TOKENS


def suspicious_identifier(name: str) -> bool:
    lowered = name.lower().replace("boundary", "")
    return any(tok.lower() in lowered for tok in OBFUSCATION_TOKENS + ANTI_CONFAB_VOCABULARY)


def load_graph(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    raw = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, list):
        return []
    return [r for r in raw if isinstance(r, dict) and isinstance(r.get("name"), str)]


def module_from_path(path: str | None) -> str | None:
    if not path:
        return None
    stem = Path(path).stem
    return stem or None


def graph_module_records(graph: list[dict[str, Any]], module: str | None) -> list[dict[str, Any]]:
    if not module:
        return []
    prefix = module + "."
    return [r for r in graph if str(r.get("name", "")).startswith(prefix)]


def strip_lean_comments_and_strings(code: str) -> str:
    out: list[str] = []
    i = 0
    n = len(code)
    block_depth = 0
    in_string = False
    while i < n:
        ch = code[i]
        nxt = code[i + 1] if i + 1 < n else ""
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                i += 2
                continue
            i += 1
            continue
        if in_string:
            if ch == "\\" and i + 1 < n:
                i += 2
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue
        if ch == '"':
            in_string = True
            i += 1
            continue
        if ch == "-" and nxt == "-":
            while i < n and code[i] != "\n":
                i += 1
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            i += 2
            continue
        out.append(ch)
        i += 1
    return "".join(out)


def simple_balance_ok(code: str) -> bool:
    pairs = {"(": ")", "[": "]", "{": "}"}
    closing = {v: k for k, v in pairs.items()}
    stack: list[str] = []
    cleaned = strip_lean_comments_and_strings(code)
    for ch in cleaned:
        if ch in pairs:
            stack.append(ch)
        elif ch in closing:
            if not stack or stack[-1] != closing[ch]:
                return False
            stack.pop()
    return not stack


def infer_decl_shell_ok(code: str) -> bool:
    cleaned = strip_lean_comments_and_strings(code)
    if re.search(r"\b(theorem|lemma|def|structure)\b", cleaned) is None:
        return False
    names = {name for _, name, _, _ in detect_vacuity(code)}
    if names & {"empty_where", "empty_body"}:
        return False
    return True


def detect_vacuity(code: str) -> List[Tuple[float, str, str, str]]:
    findings = []
    for score, name, pattern, reason in VACUITY_PATTERNS:
        matches = re.findall(pattern, code, re.MULTILINE)
        if matches:
            findings.append((score, name, matches[0] if isinstance(matches[0], str) else str(matches[0]), reason))
    return findings


def compute_vacuity_score(code: str) -> float:
    findings = detect_vacuity(code)
    if not findings:
        return 0.0
    max_score = max(s for s, _, _, _ in findings)
    count_bonus = min(0.3, len(findings) * 0.05)
    return min(1.0, max_score + count_bonus)


def compute_honesty_score(code: str) -> float:
    return 1.0 - compute_vacuity_score(code)


def source_has_deferred_interface_shape(code: str) -> bool:
    cleaned = strip_lean_comments_and_strings(code)
    tokens = OBFUSCATION_TOKENS + ANTI_CONFAB_VOCABULARY
    return bool(re.search(r"\b(" + "|".join(map(re.escape, tokens)) + r")\b", cleaned, re.IGNORECASE))


def anti_obfuscation_findings(code: str) -> list[dict[str, Any]]:
    """Detect premise-laundering patterns.

    Policy: `sorry` is an honest hole.  Structures/theorems named with
    deferred-interface/witness/certificate/sample/bound/debt language that merely carry
    `Prop` fields are obfuscated holes and should be
    replaced by explicit premises or an honest `sorry` theorem.
    """
    cleaned = strip_lean_comments_and_strings(code)
    findings: list[dict[str, Any]] = []
    vocab_pattern = r"\b(" + "|".join(map(re.escape, ANTI_CONFAB_VOCABULARY)) + r")\b"
    for m in re.finditer(vocab_pattern, cleaned, re.IGNORECASE):
        findings.append({
            "severity": 1.0,
            "name": "explicit_anti_confab_vocabulary",
            "match": m.group(0),
            "reason": "Source uses anti-confabulation vocabulary (`theorem-honest`, `zero-sorry`, `zero-axiom`, `zero sorries`, `zero axioms`, `oops`, or `opaque`); verify this is an explicit contract, not proof laundering.",
        })

    for m in re.finditer(r"\b(structure|class)\s+([A-Za-z_][\w'.]*)\b", cleaned):
        if not suspicious_identifier(m.group(2)):
            continue
        findings.append({
            "severity": 1.0,
            "name": "obfuscating_structure_name",
            "match": m.group(0),
            "reason": "Structure/class name advertises deferred-interface/witness/certificate/sample/bound/debt prose instead of an explicit theorem premise or `sorry`.",
        })

    for m in re.finditer(r"\b(structure|class)\s+([A-Za-z_][\w'.]*)[\s\S]*?\bwhere\b([\s\S]*?)(?=\n\s*(?:theorem|lemma|def|structure|class|inductive|namespace|end)\b|\Z)", cleaned):
        struct_name = m.group(2)
        body = m.group(3)
        for fm in re.finditer(r"^\s*([A-Za-z_][\w'.]*)\s*:\s*Prop\b", body, re.MULTILINE):
            field = fm.group(1)
            hay = (struct_name + " " + field).lower()
            if any(tok.lower() in hay for tok in OBFUSCATION_TOKENS + PREMISE_FIELD_TOKENS):
                findings.append({
                    "severity": 1.0,
                    "name": "prop_field_premise_laundering",
                    "match": f"{struct_name}.{field} : Prop",
                    "reason": "Prop field in a prose/suspicious structure hides an unproved claim. Use an explicit theorem premise or an honest `sorry` target.",
                })

    for m in re.finditer(r"\b(theorem|lemma)\s+([A-Za-z_][\w'.]*)\b", cleaned):
        if not suspicious_identifier(m.group(2)):
            continue
        findings.append({
            "severity": 0.8,
            "name": "obfuscating_theorem_name",
            "match": m.group(0),
            "reason": "Theorem/lemma name contains deferred-interface/witness/certificate/sample/bound/debt/bookkeeping language; verify it is not just premise forwarding.",
        })

    local_hypothesis_name = r"h(?:[0-9A-Z_'][A-Za-z0-9_']*|_[A-Za-z0-9_']*)?"
    local_hypothesis_end = r"(?![A-Za-z0-9_'])"
    pass_patterns = [
        ("exact_hypothesis", r"\bexact\s+" + local_hypothesis_name + local_hypothesis_end, re.MULTILINE),
        ("assumption_tactic", r"\bby\s+assumption\b|\bassumption\b", re.IGNORECASE | re.MULTILINE),
        ("conjunction_of_hypotheses", r"\bexact\s+⟨[^⟩]*(?:" + local_hypothesis_name + local_hypothesis_end + r")[^⟩]*⟩", re.MULTILINE),
        ("field_forwarding", r"\bexact\s+[A-Za-z0-9_'.]+\.(?:" + "|".join(PREMISE_FIELD_TOKENS) + r")[A-Za-z0-9_']*\b", re.IGNORECASE | re.MULTILINE),
    ]
    for name, pat, flags in pass_patterns:
        for m in re.finditer(pat, cleaned, flags):
            findings.append({
                "severity": 0.9,
                "name": name,
                "match": m.group(0)[:160],
                "reason": "Proof appears to forward a supplied premise/hypothesis rather than prove new content.",
            })

    if re.search(r"\bsorry\b", cleaned):
        findings.append({
            "severity": -1.0,
            "name": "honest_sorry_hole",
            "match": "sorry",
            "reason": "Honest visible proof hole; preferable to deferred-interface/witness/certificate/sample/bound obfuscation.",
        })

    return findings


def proof_looks_pass_through(code: str) -> bool:
    pass_through_patterns = [
        r"\bexact\s+⟨?\s*h\b",
        r"\bexact\s+.*\bh\b",
        r"\bintro\s+\w+\s*=>\s*\w+\b",
        r"\bfun\s+\w+\s*=>\s*\w+\b",
        r"\bby\s*\n\s*exact\s+⟨",
        r"\bby\s*\n\s*constructor\b",
    ]
    return any(re.search(p, code, re.MULTILINE) for p in pass_through_patterns)


def proof_looks_nontrivial(code: str) -> bool:
    if detect_vacuity(code):
        return False
    real_proof_markers = [
        r"\bhave\b",
        r"\bcalc\b",
        r"\brw\b",
        r"\bsimp\s*\[",
        r"\bapply\b",
        r"\binduction\b",
        r"\bcases\b",
        r"\bnlinarith\b",
        r"\bomega\b",
        r"\baesop\b",
        r"\bnorm_num\b",
        r"\bfunext\b",
        r"\bext\b",
    ]
    return any(re.search(p, code, re.MULTILINE) for p in real_proof_markers)


def real_dependency_signal(graph_records: list[dict[str, Any]]) -> dict[str, Any]:
    theorem_count = sum(1 for r in graph_records if r.get("kind") == "theorem")
    zero_dep_theorems = [r for r in graph_records if r.get("kind") == "theorem" and not r.get("deps", [])]
    positive_dep = [r for r in graph_records if len(r.get("deps", [])) > 0]
    max_dep = max((len(r.get("deps", [])) for r in graph_records), default=0)
    return {
        "graph_available": bool(graph_records),
        "decl_count": len(graph_records),
        "theorem_count": theorem_count,
        "zero_dep_theorem_count": len(zero_dep_theorems),
        "positive_dep_count": len(positive_dep),
        "max_dep_count": max_dep,
        "has_real_deps": bool(positive_dep),
        "has_zero_dep_theorems": bool(zero_dep_theorems),
        "zero_dep_theorems": [r.get("name") for r in zero_dep_theorems[:20]],
    }


def classify(code: str, graph_metrics: dict[str, Any]) -> str:
    ast_ok = infer_decl_shell_ok(code)
    deps_ok = graph_metrics.get("has_real_deps", False)
    proof_ok = proof_looks_nontrivial(code)
    if not ast_ok:
        return "suspiciously_vacuous"
    if proof_looks_pass_through(code) and not deps_ok:
        return "deferred_interface_pass_through"
    if ast_ok and deps_ok and proof_ok:
        return "non_vacuous"
    if ast_ok and deps_ok and not proof_ok:
        return "bookkeeping_vacuous" if not detect_vacuity(code) else "suspiciously_vacuous"
    if ast_ok and not deps_ok and source_has_deferred_interface_shape(code):
        return "deferred_interface_pass_through"
    return "suspiciously_vacuous"


def analyze(code: str, graph_records: list[dict[str, Any]] | None = None) -> dict[str, Any]:
    findings = detect_vacuity(code)
    graph_metrics = real_dependency_signal(graph_records or [])
    ast_ok = infer_decl_shell_ok(code)
    deps_ok = graph_metrics.get("has_real_deps", False)
    proof_ok = proof_looks_nontrivial(code)
    anti_findings = anti_obfuscation_findings(code)
    class0 = classify(code, graph_metrics)
    if any(f["name"] == "honest_sorry_hole" for f in anti_findings):
        class0 = "sorry_target"
    elif any(f["severity"] >= 1.0 for f in anti_findings):
        class0 = "premise_obfuscation"
    elif any(f["severity"] >= 0.8 for f in anti_findings):
        class0 = "premise_forwarding_or_suspicious_name"
    suggested_context = None
    if class0 in ("suspiciously_vacuous", "sorry_target", "premise_obfuscation") or compute_vacuity_score(code) > 0:
        import urllib.request, json
        # Extract the target definition or theorem name to query the DAG
        m = re.search(r'\b(def|theorem|lemma)\s+([A-Za-z_][\w\'.]*)', code)
        if m:
            target_name = m.group(2)
            try:
                # Query ArangoDB directly to extend help (collaboration rather than just adversary)
                req = urllib.request.Request(
                    "http://localhost:8529/_db/agent_brain/_api/cursor",
                    data=json.dumps({"query": f"FOR doc IN lean_theorems FILTER doc._key == '{target_name}' OR LOWER(doc.ast_content) LIKE LOWER('%{target_name}%') RETURN doc"}).encode('utf-8'),
                    headers={'Content-Type': 'application/json'},
                    method='POST'
                )
                with urllib.request.urlopen(req, timeout=2) as response:
                    res = json.loads(response.read().decode())
                    if res.get('result'):
                        suggested_context = f"COLLABORATIVE GUARDRAIL: Found mathematical context in DAG for {target_name}: {res['result'][0].get('ast_content', 'No AST')}"
            except Exception:
                pass

    result = {
        "ast_well_formed": ast_ok,
        "real_deps": deps_ok,
        "real_proof_body": proof_ok,
        "classification": class0,
        "honesty_score": compute_honesty_score(code),
        "vacuity_score": compute_vacuity_score(code),
        "line_count": len(code.splitlines()),
        "findings": [
            {"severity": s, "name": n, "match": m, "reason": r}
            for s, n, m, r in findings
        ],
        "anti_obfuscation_findings": anti_findings,
        "graph_metrics": graph_metrics,
        "deferred_interface_pass_through_hint": source_has_deferred_interface_shape(code) and proof_looks_pass_through(code),
        "suggested_mathematical_context": suggested_context,
    }
    return result


def print_report(report: dict[str, Any], filepath: str = "<stdin>") -> None:
    print(f"📊 Vacuity Report: {filepath}")
    print("=" * 60)
    print(f"  classification: {report['classification']}")
    print(f"  ast_well_formed: {report['ast_well_formed']}")
    print(f"  real_deps:       {report['real_deps']}")
    print(f"  real_proof_body: {report['real_proof_body']}")
    print(f"  Honesty score:   {report['honesty_score']:.2f}")
    print(f"  Vacuity score:   {report['vacuity_score']:.2f}")
    gm = report.get("graph_metrics", {})
    if gm.get("graph_available"):
        print(
            f"  graph decls:     {gm.get('decl_count', 0)}  "
            f"theorems: {gm.get('theorem_count', 0)}  "
            f"zero-dep theorems: {gm.get('zero_dep_theorem_count', 0)}"
        )
    print(f"  Lines:           {report.get('line_count', 0)}")
    print()
    anti = report.get("anti_obfuscation_findings", [])
    if anti:
        print(f"  🚫 Detected {len(anti)} anti-obfuscation findings:")
        print()
        for finding in sorted(anti, key=lambda x: -x["severity"]):
            severity = "🔴" if finding["severity"] >= 0.9 else "🟡" if finding["severity"] >= 0 else "🟢"
            print(f"  {severity} [{finding['severity']:.1f}] {finding['name']}")
            print(f"       {finding['reason']}")
            print(f"       Match: \"{finding['match'][:120]}\"")
            print()

    findings = report.get("findings", [])
    if findings:
        print(f"  ⚠️  Detected {len(findings)} potential vacuity patterns:")
        print()
        for finding in sorted(findings, key=lambda x: -x["severity"]):
            severity = "🔴" if finding["severity"] >= 0.7 else "🟡" if finding["severity"] >= 0.4 else "🟢"
            print(f"  {severity} [{finding['severity']:.1f}] {finding['name']}")
            print(f"       {finding['reason']}")
            print(f"       Match: \"{finding['match'][:80]}\"")
            print()
    else:
        print("  ✅ No vacuity patterns detected.")
        print()
        
    context = report.get("suggested_mathematical_context")
    if context:
        print("  " + "=" * 60)
        print("  " + context)
        print("  " + "=" * 60)
        print()


def main() -> None:
    parser = argparse.ArgumentParser(description="Lean 4 Vacuity Linter")
    parser.add_argument("file", nargs="?", help="Lean file to check")
    parser.add_argument("--stdin", action="store_true", help="Read from stdin")
    parser.add_argument("--score", action="store_true", help="Return numeric score only")
    parser.add_argument("--json", action="store_true", help="Output JSON")
    parser.add_argument("--graph-json", type=Path, default=DEFAULT_GRAPH, help="Compiled proof graph JSON")
    parser.add_argument("--module", help="Override module name for graph lookup")
    parser.add_argument("--scan-root", type=Path, help="Scan all .lean files under a directory and emit aggregate JSON")
    parser.add_argument("--out", type=Path, help="Output path for --scan-root JSON")
    args = parser.parse_args()

    if args.scan_root:
        graph = load_graph(args.graph_json) if args.graph_json and args.graph_json.exists() else []
        reports = []
        for path in sorted(args.scan_root.rglob("*.lean")):
            if "/.lake/" in str(path) or "/_deprecated/" in str(path):
                continue
            code_i = path.read_text(encoding="utf-8")
            module_i = module_from_path(str(path))
            report_i = analyze(code_i, graph_module_records(graph, module_i))
            anti_count = len([f for f in report_i.get("anti_obfuscation_findings", []) if f.get("severity", 0) >= 0.8])
            reports.append({
                "file": str(path),
                "module": module_i,
                "classification": report_i["classification"],
                "anti_obfuscation_count": anti_count,
                "vacuity_score": report_i["vacuity_score"],
                "honesty_score": report_i["honesty_score"],
                "anti_obfuscation_findings": report_i.get("anti_obfuscation_findings", []),
                "findings": report_i.get("findings", []),
                "graph_metrics": report_i.get("graph_metrics", {}),
            })
        summary = {
            "files_scanned": len(reports),
            "classification_counts": {},
            "anti_obfuscation_files": sum(1 for r in reports if r["anti_obfuscation_count"] > 0),
            "anti_obfuscation_findings": sum(r["anti_obfuscation_count"] for r in reports),
            "top_files": sorted(reports, key=lambda r: (-r["anti_obfuscation_count"], -r["vacuity_score"], r["file"]))[:50],
        }
        for r in reports:
            summary["classification_counts"][r["classification"]] = summary["classification_counts"].get(r["classification"], 0) + 1
        payload = {"summary": summary, "files": reports}
        text = json.dumps(payload, indent=2, ensure_ascii=False)
        if args.out:
            args.out.parent.mkdir(parents=True, exist_ok=True)
            args.out.write_text(text + "\n", encoding="utf-8")
        print(text if args.json else json.dumps(summary, indent=2, ensure_ascii=False))
        return

    code = ""
    if args.file:
        code = Path(args.file).read_text(encoding="utf-8")
    elif args.stdin or not sys.stdin.isatty():
        code = sys.stdin.read()
    else:
        parser.print_help()
        sys.exit(1)

    graph_records = []
    if args.graph_json and args.graph_json.exists():
        graph_records = load_graph(args.graph_json)
        module = args.module or module_from_path(args.file)
        graph_records = graph_module_records(graph_records, module)

    report = analyze(code, graph_records)

    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    elif args.score:
        print(f"{report['honesty_score']:.3f}")
    else:
        print_report(report, args.file or "<stdin>")


if __name__ == "__main__":
    main()
