#!/usr/bin/env python3
"""Statement Fidelity Gate: syntactic contract screening beyond compilation.

Inspired by EMNLP 2025 and Beyond Compilation research in formal reasoning.
A Lean 4 theorem can compile with exit code 0 by omitting essential hypotheses,
weakening assumptions, packaging the conclusion into a hypothesis (Trap T6),
or substituting non-commutative matrix/operator algebras with trivial scalar
surrogates (Trap T16).

This lightweight source parser screens Lean declarations against target specifications. It
is not a Lean AST or semantic-equivalence checker. It checks:
1. Exact presence of all required mathematical premises (preventing dropped hypotheses).
2. Grounded, uncollapsed carrier types (e.g. Matrix (Fin 2) (Fin 2) ℝ vs scalar ℝ).
3. Absence of triviality / T6 packaging (conclusion assumed in hypotheses).
4. Absence of vacuous conclusions (True, 0 = 0, reflexivity tautologies).
5. A heuristic contract-match score ∈ [0.0, 1.0]; it does not establish
   semantic equivalence, which requires independent mathematical review.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Sequence

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    try:
        from tools.pathing import lean_root, repo_root
    except ImportError:
        def repo_root() -> Path:
            return Path(__file__).resolve().parents[2]
        def lean_root() -> Path:
            return repo_root() / "lean"
else:
    from tools.pathing import lean_root, repo_root


# -----------------------------------------------------------------------------
# Data Models
# -----------------------------------------------------------------------------

@dataclass
class FidelityDefect:
    defect_type: str  # DROPPED_HYPOTHESIS, CARRIER_DEMOTION_T16, T6_HYPOTHESIS_PACKAGING, VACUOUS_CONCLUSION, RELATION_MISMATCH, WEAKENED_HYPOTHESIS
    severity: str     # FATAL, ERROR, WARNING
    message: str
    penalty: float
    context: str = ""

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class ParsedBinder:
    raw: str
    kind: str          # "explicit", "implicit", "instance", "strict_implicit"
    names: list[str]
    type_expr: str
    is_arrow_premise: bool = False

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class CarrierInfo:
    primary_carrier: str
    all_carriers: list[str]
    is_matrix: bool
    is_non_commutative: bool
    is_scalar_proxy: bool
    proxy_name: str = ""
    dimension: int | None = None

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class ParsedDeclaration:
    name: str
    kind: str          # "theorem", "lemma", "def"
    binders: list[ParsedBinder]
    universe_params: list[str]
    conclusion: str
    raw_signature: str
    line_number: int = 1
    in_scope_variables: list[ParsedBinder] = field(default_factory=list)
    bundled_structures: dict[str, dict[str, str]] = field(default_factory=dict)

    def all_hypotheses_strings(self) -> list[str]:
        items: list[str] = []
        for b in self.binders:
            items.append(f"{', '.join(b.names)} : {b.type_expr}")
        for v in self.in_scope_variables:
            items.append(f"[scope] {', '.join(v.names)} : {v.type_expr}")
        for sname, fields in self.bundled_structures.items():
            for fname, ftype in fields.items():
                items.append(f"[{sname}.{fname}] : {ftype}")
        return items

    def to_dict(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "kind": self.kind,
            "universe_params": self.universe_params,
            "binders": [b.to_dict() for b in self.binders],
            "in_scope_variables": [v.to_dict() for v in self.in_scope_variables],
            "bundled_structures": self.bundled_structures,
            "conclusion": self.conclusion,
            "raw_signature": self.raw_signature,
            "line_number": self.line_number,
        }


@dataclass
class FidelityReport:
    theorem_name: str
    fidelity_score: float
    passed: bool
    defects: list[FidelityDefect]
    carrier_detected: list[str]
    hypotheses_detected: list[str]
    conclusion_detected: str
    details: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        return {
            "theorem_name": self.theorem_name,
            "fidelity_score": self.fidelity_score,
            "passed": self.passed,
            "defects": [d.to_dict() for d in self.defects],
            "carrier_detected": self.carrier_detected,
            "hypotheses_detected": self.hypotheses_detected,
            "conclusion_detected": self.conclusion_detected,
            "details": self.details,
        }

    def summary(self) -> str:
        status = "[PASS]" if self.passed else "[FAIL]"
        lines = [
            f"{status} Theorem '{self.theorem_name}' - Score: {self.fidelity_score:.4f}",
            f"  Carriers: {', '.join(self.carrier_detected) if self.carrier_detected else 'None detected'}",
            f"  Hypotheses ({len(self.hypotheses_detected)}):",
        ]
        for h in self.hypotheses_detected[:6]:
            lines.append(f"    - {h}")
        if len(self.hypotheses_detected) > 6:
            lines.append(f"    ... (+{len(self.hypotheses_detected) - 6} more)")
        lines.append(f"  Conclusion: {' '.join(self.conclusion_detected.split())}")
        if self.defects:
            lines.append("  Defects:")
            for d in self.defects:
                lines.append(f"    - [{d.severity}] {d.defect_type}: {d.message} (penalty: -{d.penalty:.2f})")
        return "\n".join(lines)


# -----------------------------------------------------------------------------
# Parsing Utilities
# -----------------------------------------------------------------------------

def strip_lean_comments(text: str) -> str:
    """Strip Lean 4 line and nested block comments while preserving line count."""
    res: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        if text[i:i+2] == "/-":
            depth = 1
            i += 2
            while i < n and depth > 0:
                if text[i:i+2] == "/-":
                    depth += 1
                    i += 2
                elif text[i:i+2] == "-/":
                    depth -= 1
                    i += 2
                else:
                    if text[i] == "\n":
                        res.append("\n")
                    i += 1
            res.append(" ")
        elif text[i:i+2] == "--":
            i += 2
            while i < n and text[i] != "\n":
                i += 1
            res.append("\n")
            if i < n and text[i] == "\n":
                i += 1
        else:
            res.append(text[i])
            i += 1
    return "".join(res)


def parse_lean_structures(text: str) -> dict[str, dict[str, str]]:
    """Parse structure declarations and their typed fields from Lean source."""
    structures: dict[str, dict[str, str]] = {}
    lines = text.splitlines()
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        m = re.match(r"^\s*structure\s+([A-Za-z0-9_.\x27]+)(.*?)\bwhere\b", line)
        if m:
            s_name = m.group(1).strip()
            fields: dict[str, str] = {}
            i += 1
            while i < n:
                s_line = lines[i]
                stripped = s_line.strip()
                if not stripped or stripped.startswith(("--", "/-", "/--")):
                    i += 1
                    continue
                # If an unindented top-level declaration keyword appears, structure ends
                if (
                    re.match(
                        r"^(structure|class|def|theorem|lemma|section|namespace|end|noncomputable|open|variable)\b",
                        stripped,
                    )
                    and not s_line.startswith((" ", "\t"))
                ):
                    break
                # Match field: name : type
                fm = re.match(r"^\s+([A-Za-z0-9_.\x27]+)\s*:\s*(.*)$", s_line)
                if fm:
                    fname = fm.group(1).strip()
                    ftype = fm.group(2).strip()
                    fields[fname] = ftype
                i += 1
            structures[s_name] = fields
        else:
            i += 1
    return structures


def parse_binder_tokens(binders_str: str) -> list[ParsedBinder]:
    """Parse a sequence of Lean 4 binders into structured ParsedBinder objects."""
    binders: list[ParsedBinder] = []
    i = 0
    n = len(binders_str)
    delim_pairs = {
        "(": (")", "explicit"),
        "{": ("}", "implicit"),
        "[": ("]", "instance"),
        "⦃": ("⦄", "strict_implicit"),
    }

    while i < n:
        c = binders_str[i]
        if c in delim_pairs:
            close_char, kind = delim_pairs[c]
            depth = 1
            start = i
            i += 1
            while i < n and depth > 0:
                if binders_str[i] == c:
                    depth += 1
                elif binders_str[i] == close_char:
                    depth -= 1
                i += 1
            raw_binder = binders_str[start:i].strip()
            inner = raw_binder[1:-1].strip()

            names: list[str] = []
            type_expr = ""
            if ":" in inner:
                names_part, type_part = inner.split(":", 1)
                names = [nm.strip() for nm in names_part.split() if nm.strip()]
                type_expr = type_part.strip()
            else:
                # Typeclass instance without explicit name: e.g. [Ring A]
                names = ["_inst"]
                type_expr = inner

            binders.append(
                ParsedBinder(
                    raw=raw_binder,
                    kind=kind,
                    names=names,
                    type_expr=type_expr,
                    is_arrow_premise=False,
                )
            )
        else:
            i += 1

    return binders


def _scoped_variables_at(source_prefix: str) -> list[ParsedBinder]:
    """Collect only variable binders still in scope at the end of a source prefix."""
    scopes: list[tuple[str, str, list[ParsedBinder]]] = [("root", "", [])]
    for line in source_prefix.splitlines():
        clean = line.strip()
        namespace = re.match(r"^namespace\s+([A-Za-z0-9_.]+)", clean)
        section = re.match(r"^section(?:\s+([A-Za-z0-9_]+))?$", clean)
        ending = re.match(r"^end(?:\s+([A-Za-z0-9_.]+))?$", clean)
        variable = re.match(r"^variable\s+(.+)$", clean)

        if namespace:
            scopes.append(("namespace", namespace.group(1), []))
        elif section:
            scopes.append(("section", section.group(1) or "", []))
        elif ending and len(scopes) > 1:
            target = ending.group(1)
            if target:
                while len(scopes) > 1:
                    _, scope_name, _ = scopes.pop()
                    if scope_name == target:
                        break
            else:
                scopes.pop()
        elif variable:
            scopes[-1][2].extend(parse_binder_tokens(variable.group(1)))

    return [binder for _, _, binders in scopes for binder in binders]


def split_arrow_premises(expr: str) -> tuple[list[str], str]:
    """Split depth-0 arrow implications into premise strings and target conclusion."""
    premises: list[str] = []
    depth = 0
    current: list[str] = []
    i = 0
    n = len(expr)

    while i < n:
        c = expr[i]
        if c in "({[⦃⟨":
            depth += 1
            current.append(c)
            i += 1
        elif c in ")}]⦄⟩":
            depth -= 1
            current.append(c)
            i += 1
        elif depth == 0 and (expr[i:i+1] == "→" or expr[i:i+2] == "->"):
            prem = "".join(current).strip()
            if prem:
                premises.append(prem)
            current = []
            i += 1 if expr[i] == "→" else 2
        else:
            current.append(c)
            i += 1

    conclusion = "".join(current).strip()
    return premises, conclusion


def parse_declaration_from_text(
    chunk: str,
    line_number: int = 1,
    in_scope_variables: list[ParsedBinder] | None = None,
    structures: dict[str, dict[str, str]] | None = None,
) -> ParsedDeclaration | None:
    """Parse a single Lean 4 declaration chunk into a ParsedDeclaration."""
    m = re.match(
        r"^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(?:protected\s+|private\s+)?(theorem|lemma|def)\s+([^\s:{(]+)",
        chunk,
    )
    if not m:
        return None

    kind = m.group(1)
    name = m.group(2)
    rest = chunk[m.end():].strip()

    # Universe parameters if any: e.g. .{u, v}
    universe_params: list[str] = []
    u_match = re.match(r"^\.([A-Za-z0-9_.\x27{} ]+)", rest)
    if u_match:
        universe_params.append(u_match.group(1))
        rest = rest[u_match.end():].strip()

    # Scan for depth-0 colon separating binders from return type
    depth = 0
    colon_idx = -1
    for idx, c in enumerate(rest):
        if c in "({[⦃⟨":
            depth += 1
        elif c in ")}]⦄⟩":
            depth -= 1
        elif c == ":" and depth == 0:
            colon_idx = idx
            break

    if colon_idx == -1:
        # No colon found (e.g. definition without type annotation)
        return ParsedDeclaration(
            name=name,
            kind=kind,
            binders=[],
            universe_params=universe_params,
            conclusion="",
            raw_signature=chunk[:120],
            line_number=line_number,
            in_scope_variables=in_scope_variables or [],
            bundled_structures=structures or {},
        )

    binders_part = rest[:colon_idx].strip()
    after_colon = rest[colon_idx+1:].strip()

    # Find the end of return type before proof assignment (:= or where)
    # Notice: 'let x := ...' in the type has := at depth 0, so track 'let'
    depth = 0
    in_let = False
    decl_end_idx = -1
    i = 0
    n = len(after_colon)

    while i < n:
        c = after_colon[i]
        if c in "({[⦃⟨":
            depth += 1
            i += 1
        elif c in ")}]⦄⟩":
            depth -= 1
            i += 1
        elif depth == 0:
            if after_colon[i:i+3] == "let" and (i+3 == n or not after_colon[i+3].isalnum()):
                in_let = True
                i += 3
            elif after_colon[i:i+2] == ":=":
                if in_let:
                    in_let = False
                    i += 2
                else:
                    decl_end_idx = i
                    break
            elif after_colon[i:i+5] == "where" and (i+5 == n or not after_colon[i+5].isalnum()):
                decl_end_idx = i
                break
            else:
                i += 1
        else:
            i += 1

    conclusion_raw = (
        after_colon[:decl_end_idx].strip() if decl_end_idx != -1 else after_colon.strip()
    )

    # Parse explicit binders
    parsed_binders = parse_binder_tokens(binders_part)

    # Parse arrow premises from conclusion if any
    arrow_prems, main_conclusion = split_arrow_premises(conclusion_raw)
    for idx, prem in enumerate(arrow_prems, start=1):
        parsed_binders.append(
            ParsedBinder(
                raw=prem,
                kind="explicit",
                names=[f"_premise_{idx}"],
                type_expr=prem,
                is_arrow_premise=True,
            )
        )

    # Resolve bundled structures for any binder types
    bundled: dict[str, dict[str, str]] = {}
    if structures:
        for b in parsed_binders:
            b_type_clean = b.type_expr.split("(")[0].strip()
            if b_type_clean in structures:
                bundled[b_type_clean] = structures[b_type_clean]
        if in_scope_variables:
            for v in in_scope_variables:
                v_type_clean = v.type_expr.split("(")[0].strip()
                if v_type_clean in structures:
                    bundled[v_type_clean] = structures[v_type_clean]

    return ParsedDeclaration(
        name=name,
        kind=kind,
        binders=parsed_binders,
        universe_params=universe_params,
        conclusion=main_conclusion,
        raw_signature=f"{kind} {name} {binders_part} : {conclusion_raw}",
        line_number=line_number,
        in_scope_variables=in_scope_variables or [],
        bundled_structures=bundled,
    )


def parse_lean_declarations(
    text_or_path: str | Path,
) -> tuple[list[ParsedDeclaration], dict[str, dict[str, str]]]:
    """Parse all declarations and structures from Lean text or file path."""
    if isinstance(text_or_path, Path) or (isinstance(text_or_path, str) and "\n" not in text_or_path and Path(text_or_path).is_file()):
        raw_content = Path(text_or_path).read_text(encoding="utf-8")
    else:
        raw_content = str(text_or_path)

    # Parse structures first
    structures = parse_lean_structures(raw_content)

    clean_text = strip_lean_comments(raw_content)
    lines = clean_text.splitlines()

    # Track in-scope variable binders across sections/namespaces
    in_scope_vars: list[ParsedBinder] = []
    scope_stack: list[list[ParsedBinder]] = []

    declarations: list[ParsedDeclaration] = []

    # Find declaration headers
    decl_re = re.compile(
        r"(?:^|\n)\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(?:protected\s+|private\s+)?(theorem|lemma|def)\s+([^\s:{(]+)"
    )

    matches = list(decl_re.finditer(clean_text))
    for idx, m in enumerate(matches):
        start = m.start()
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(clean_text)
        chunk = clean_text[start:end].strip()

        # Calculate 1-based line number
        # `m.start()` points at the newline consumed by (?:^|\n), so it is
        # one line early for ordinary declarations. Use the declaration keyword.
        line_no = clean_text[:m.start(1)].count("\n") + 1

        # Keep only variable declarations still in scope (closed sections and
        # namespaces must not leak assumptions into later declarations).
        current_vars = _scoped_variables_at(clean_text[:start])

        parsed = parse_declaration_from_text(
            chunk,
            line_number=line_no,
            in_scope_variables=current_vars,
            structures=structures,
        )
        if parsed:
            parsed.name = _qualified_declaration_name(
                clean_text, line_no, parsed.name
            )
            declarations.append(parsed)

    return declarations, structures


def _qualified_declaration_name(source: str, line_number: int, local_name: str) -> str:
    """Qualify a parsed declaration using the namespace stack at its source line.

    This mirrors the source-scope convention used by Gate 5's theorem inventory.
    It remains a source parser, not Lean elaborator AST evidence.
    """
    stack: list[tuple[str, str]] = []
    lines = source.splitlines()
    for line in lines[: max(0, line_number - 1)]:
        clean = strip_lean_comments(line).split("--")[0].strip()
        namespace = re.match(r"^namespace\s+([A-Za-z0-9_.]+)", clean)
        if namespace:
            stack.append(("namespace", namespace.group(1)))
            continue
        section = re.match(r"^section(?:\s+([A-Za-z0-9_.]+))?$", clean)
        if section:
            stack.append(("section", section.group(1) or ""))
            continue
        end = re.match(r"^end(?:\s+([A-Za-z0-9_.]+))?$", clean)
        if end and stack:
            named_end = end.group(1)
            if named_end:
                while stack:
                    _, popped = stack.pop()
                    if popped == named_end:
                        break
            else:
                stack.pop()
    namespaces = [name for kind, name in stack if kind == "namespace"]
    return ".".join([*namespaces, local_name]) if namespaces else local_name


def parse_from_ast_json(ast_data: dict[str, Any] | str) -> list[ParsedDeclaration]:
    """Parse declarations from an AST JSON export or dict representation."""
    if isinstance(ast_data, str):
        try:
            data = json.loads(ast_data)
        except json.JSONDecodeError:
            return []
    else:
        data = ast_data

    decls: list[ParsedDeclaration] = []
    raw_list = data.get("declarations", [data] if "name" in data else [])

    for item in raw_list:
        if not isinstance(item, dict):
            continue
        name = item.get("name", "<unnamed>")
        kind = item.get("kind", "theorem")
        raw_binders = item.get("binders", [])
        binders: list[ParsedBinder] = []
        for b in raw_binders:
            if isinstance(b, dict):
                binders.append(
                    ParsedBinder(
                        raw=b.get("raw", f"({b.get('name', '_')} : {b.get('type', '')})"),
                        kind=b.get("kind", "explicit"),
                        names=[b.get("name", "_")],
                        type_expr=b.get("type", ""),
                    )
                )
            elif isinstance(b, str):
                binders.extend(parse_binder_tokens(b))

        conclusion = item.get("conclusion", item.get("type", ""))
        decls.append(
            ParsedDeclaration(
                name=name,
                kind=kind,
                binders=binders,
                universe_params=item.get("universe_params", []),
                conclusion=conclusion,
                raw_signature=item.get("raw_signature", f"{kind} {name} : {conclusion}"),
                line_number=item.get("line_number", 1),
                bundled_structures=item.get("bundled_structures", {}),
            )
        )
    return decls


# -----------------------------------------------------------------------------
# Carrier Analysis & Defect Checking
# -----------------------------------------------------------------------------

SCALAR_TYPES = {"ℝ", "Float", "Nat", "Int", "Rat", "Real", "Bool", "Unit"}
PROXY_NAME_PATTERNS = re.compile(
    r"(Proxy|Surrogate|Dummy|Toy|BlockSuperTrace|TraceProxy|ScalarProxy|ScalarCarrier)",
    re.IGNORECASE,
)


def is_prop_type(t: str) -> bool:
    """Determine whether a type expression is a proposition (hypothesis) rather than a carrier."""
    prop_chars = {"=", "≠", "≤", "≥", "<", ">", "∀", "∃", "∧", "∨", "¬", "↔", "Prop"}
    return any(c in t for c in prop_chars)


def get_related_structures(
    decl: ParsedDeclaration,
    structures: dict[str, dict[str, str]] | None,
) -> dict[str, dict[str, str]]:
    """Filter structures to only those bundled or referenced by the declaration."""
    related: dict[str, dict[str, str]] = {}
    if decl.bundled_structures:
        related.update(decl.bundled_structures)

    if not structures:
        return related

    # Only binder types provide hypotheses. A name in the theorem conclusion,
    # declaration name, or an unrelated structure elsewhere in the file does
    # not make that structure a premise of this theorem.
    pending_types = [b.type_expr for b in [*decl.binders, *decl.in_scope_variables]]
    while pending_types:
        type_expr = pending_types.pop()
        for sname, fields in structures.items():
            if sname in related:
                continue
            if re.search(rf"(?<![\w'.]){re.escape(sname)}(?![\w'])", type_expr):
                related[sname] = fields
                pending_types.extend(fields.values())

    return related


def detect_carrier_types(
    decl: ParsedDeclaration,
    structures: dict[str, dict[str, str]] | None = None,
    definitions: dict[str, str] | None = None,
) -> CarrierInfo:
    """Analyze carrier types used in parameters, return type, bundled structures, and referenced defs."""
    all_carriers: set[str] = set()
    is_matrix = False
    is_non_comm = False
    is_scalar_proxy = False
    proxy_name = ""
    dim: int | None = None

    # Check explicit binder types
    for b in decl.binders:
        t = b.type_expr.strip()
        if not is_prop_type(t):
            all_carriers.add(t)
        if PROXY_NAME_PATTERNS.search(t):
            is_scalar_proxy = True
            proxy_name = t

    # Check bundled structure fields (only non-prop fields are carriers)
    structs = get_related_structures(decl, structures)
    for sname, fields in structs.items():
        all_carriers.add(sname)
        if PROXY_NAME_PATTERNS.search(sname):
            is_scalar_proxy = True
            proxy_name = sname
        for fname, ftype in fields.items():
            if not is_prop_type(ftype):
                all_carriers.add(ftype)

    # Check referenced definitions (e.g. nullPlus, matJ, matPerm12, blockEmbed)
    if definitions:
        global_inst = re.search(r"\(\s*R\s*:=\s*([^\s)]+)\s*\)", decl.conclusion) or re.search(r"\(\s*R\s*:=\s*([^\s)]+)\s*\)", decl.raw_signature)
        global_arg = global_inst.group(1) if global_inst else None

        for dname, dtype in definitions.items():
            if re.search(rf"\b{re.escape(dname)}\b", decl.conclusion) or re.search(rf"\b{re.escape(dname)}\b", decl.raw_signature):
                if not is_prop_type(dtype):
                    all_carriers.add(dtype)
                    # Check for definition-specific instantiation or global instantiation
                    inst_match = re.search(rf"\b{re.escape(dname)}\s*\(\s*R\s*:=\s*([^\s)]+)\s*\)", decl.conclusion)
                    inst_arg = inst_match.group(1) if inst_match else global_arg
                    if inst_arg and "R" in dtype:
                        inst_type = re.sub(r"\bR\b", inst_arg, dtype)
                        all_carriers.add(inst_type)

    # Check conclusion annotations and terms
    conc = decl.conclusion
    conc_clean = conc.strip()
    if structures and conc_clean in structures:
        all_carriers.add(conc_clean)
        if PROXY_NAME_PATTERNS.search(conc_clean):
            is_scalar_proxy = True
            proxy_name = conc_clean

    # Find Matrix (Fin n) (Fin n) R
    mat_matches = re.findall(r"Matrix\s*\(\s*Fin\s+(\d+)\s*\)\s*\(\s*Fin\s+(\d+)\s*\)\s*([^\s),]+)", conc)
    for m in mat_matches:
        is_matrix = True
        dim_row, dim_col, scalar_ring = int(m[0]), int(m[1]), m[2]
        dim = max(dim_row, dim_col)
        all_carriers.add(f"Matrix (Fin {dim_row}) (Fin {dim_col}) {scalar_ring}")
        if dim >= 2:
            is_non_comm = True

    # Check carriers in all collected carrier strings
    for c in list(all_carriers):
        mat_m = re.search(r"Matrix\s*\(\s*Fin\s+(\d+)\s*\)\s*\(\s*Fin\s+(\d+)\s*\)\s*([^\s),]+)", c)
        if mat_m:
            is_matrix = True
            dim = int(mat_m.group(1))
            if dim >= 2:
                is_non_comm = True

    # Check non-commutative witnesses
    if "≠" in conc or "[n_-" in conc or "nullPlus" in conc or "matJ" in conc:
        is_non_comm = True

    # Determine primary carrier
    matrix_carriers = [c for c in all_carriers if "Matrix" in c]
    if matrix_carriers:
        primary = matrix_carriers[0]
    elif any(c in SCALAR_TYPES for c in all_carriers):
        primary = [c for c in all_carriers if c in SCALAR_TYPES][0]
    elif all_carriers:
        primary = sorted(all_carriers, key=len, reverse=True)[0]
    else:
        primary = "Unknown"

    return CarrierInfo(
        primary_carrier=primary,
        all_carriers=sorted(all_carriers),
        is_matrix=is_matrix,
        is_non_commutative=is_non_comm,
        is_scalar_proxy=is_scalar_proxy,
        proxy_name=proxy_name,
        dimension=dim,
    )


def normalize_lean_expr(expr: str) -> str:
    """Normalize Lean expressions for simple textual contract comparisons."""
    s = re.sub(r"\s+", " ", expr).strip()
    s = re.sub(r"^\((.*)\)$", r"\1", s).strip()
    return s


def detect_t6_packaging(
    decl: ParsedDeclaration,
    structures: dict[str, dict[str, str]] | None = None,
) -> list[FidelityDefect]:
    """Detect Trap T6: Theorem packaging hypothesis that is identical to conclusion."""
    defects: list[FidelityDefect] = []
    norm_conc = normalize_lean_expr(decl.conclusion)

    # Check explicit binders
    for b in decl.binders:
        norm_type = normalize_lean_expr(b.type_expr)
        if norm_type == norm_conc:
            defects.append(
                FidelityDefect(
                    defect_type="T6_HYPOTHESIS_PACKAGING",
                    severity="FATAL",
                    message=f"Hypothesis '{b.raw}' is definitionally identical to the conclusion '{decl.conclusion}'.",
                    penalty=1.0,
                    context=b.raw,
                )
            )

    # Check bundled structure fields
    structs = get_related_structures(decl, structures)
    for sname, fields in structs.items():
        for fname, ftype in fields.items():
            norm_field = normalize_lean_expr(ftype)
            if norm_field == norm_conc:
                defects.append(
                    FidelityDefect(
                        defect_type="T6_HYPOTHESIS_PACKAGING",
                        severity="FATAL",
                        message=f"Bundled field '{sname}.{fname}' ({ftype}) is identical to the conclusion.",
                        penalty=1.0,
                        context=f"{sname}.{fname}",
                    )
                )

    return defects


def detect_vacuous_conclusion(decl: ParsedDeclaration) -> list[FidelityDefect]:
    """Detect vacuous tautologies in conclusions (True, 0 = 0, reflexivity)."""
    defects: list[FidelityDefect] = []
    c_clean = normalize_lean_expr(decl.conclusion)

    vacuous_patterns = [
        (r"^True$", "Conclusion is vacuous 'True'."),
        (r"^0\s*=\s*0$", "Conclusion is trivial literal identity '0 = 0'."),
        (r"^1\s*=\s*1$", "Conclusion is trivial literal identity '1 = 1'."),
        (r"^(\w+)\s*=\s*\1$", "Conclusion is trivial reflexivity identity on free identifier."),
        (r"^True\s*∧\s*True$", "Conclusion is conjunction of vacuous True."),
        (r"^(?:trivial|rfl)$", "Conclusion is vacuous proof token rather than mathematical proposition."),
    ]

    for pat, msg in vacuous_patterns:
        if re.match(pat, c_clean):
            defects.append(
                FidelityDefect(
                    defect_type="VACUOUS_CONCLUSION",
                    severity="FATAL",
                    message=msg,
                    penalty=1.0,
                    context=c_clean,
                )
            )
            break

    return defects


def check_carrier_fidelity(
    carrier_info: CarrierInfo,
    carrier_spec: dict[str, Any] | None,
) -> list[FidelityDefect]:
    """Check carrier against target requirements (Trap T16 scalar surrogate prevention)."""
    defects: list[FidelityDefect] = []
    if not carrier_spec:
        return defects

    # Check forbidden carriers
    forbidden = carrier_spec.get("forbidden_carriers", [])
    for forb in forbidden:
        for c in carrier_info.all_carriers:
            # If forbidden carrier is a scalar type (e.g. ℝ), check exact equality so Matrix ... ℝ is not banned!
            if forb in SCALAR_TYPES:
                if c.strip() == forb:
                    defects.append(
                        FidelityDefect(
                            defect_type="CARRIER_DEMOTION_T16",
                            severity="ERROR",
                            message=f"Carrier uses bare forbidden scalar type '{c}'.",
                            penalty=0.50,
                            context=c,
                        )
                    )
            else:
                if forb.lower() in c.lower() or c == forb:
                    defects.append(
                        FidelityDefect(
                            defect_type="CARRIER_DEMOTION_T16",
                            severity="ERROR",
                            message=f"Carrier uses forbidden scalar proxy or toy carrier '{c}' (forbidden: {forb}).",
                            penalty=0.50,
                            context=c,
                        )
                    )

    if carrier_info.is_scalar_proxy:
        defects.append(
            FidelityDefect(
                defect_type="CARRIER_DEMOTION_T16",
                severity="ERROR",
                message=f"Detected scalar surrogate proxy record '{carrier_info.proxy_name}'.",
                penalty=0.50,
                context=carrier_info.proxy_name,
            )
        )

    # Check expected carrier
    expected = carrier_spec.get("expected_carrier")
    if expected:
        norm_expected = normalize_lean_expr(expected)
        matched = any(
            norm_expected in normalize_lean_expr(c) or normalize_lean_expr(c) in norm_expected
            for c in carrier_info.all_carriers
        )
        if not matched:
            defects.append(
                FidelityDefect(
                    defect_type="CARRIER_DEMOTION_T16",
                    severity="ERROR",
                    message=f"Expected carrier '{expected}' not found in declaration carriers {carrier_info.all_carriers}.",
                    penalty=0.50,
                    context=f"expected: {expected}",
                )
            )

    # Check non-commutativity
    if carrier_spec.get("non_commutative", False):
        if not carrier_info.is_non_commutative and not carrier_info.is_matrix:
            defects.append(
                FidelityDefect(
                    defect_type="CARRIER_DEMOTION_T16",
                    severity="ERROR",
                    message="Specification requires non-commutative carrier algebra, but commutative/scalar carrier was detected.",
                    penalty=0.50,
                    context="non_commutative requirement",
                )
            )

    return defects


def check_hypotheses_fidelity(
    decl: ParsedDeclaration,
    structures: dict[str, dict[str, str]] | None,
    required_hypotheses: list[dict[str, Any] | str] | None,
) -> tuple[list[FidelityDefect], list[str]]:
    """Verify presence of all required hypotheses (preventing dropped hypotheses)."""
    defects: list[FidelityDefect] = []
    detected_hyps: list[str] = decl.all_hypotheses_strings()

    if not required_hypotheses:
        return defects, detected_hyps

    # Combine all searchable hypothesis text
    searchable_pool: list[str] = []
    for b in decl.binders:
        searchable_pool.append(f"{' '.join(b.names)} : {b.type_expr}")
    for v in decl.in_scope_variables:
        searchable_pool.append(f"{' '.join(v.names)} : {v.type_expr}")
    structs = get_related_structures(decl, structures)
    for sname, fields in structs.items():
        for fname, ftype in fields.items():
            searchable_pool.append(f"{sname}.{fname} : {ftype}")

    full_search_text = "\n".join(searchable_pool)

    penalty_per_dropped = max(0.25, round(1.0 / max(1, len(required_hypotheses)), 2))

    for req in required_hypotheses:
        if isinstance(req, str):
            h_name = req
            h_pattern = req
            desc = req
        else:
            h_name = req.get("name", "hypothesis")
            h_pattern = req.get("pattern", h_name)
            desc = req.get("description", h_name)

        # Check if matched in pool
        matched = False
        try:
            if re.search(h_pattern, full_search_text, re.IGNORECASE):
                matched = True
        except re.error:
            if h_pattern in full_search_text:
                matched = True

        if not matched:
            defects.append(
                FidelityDefect(
                    defect_type="DROPPED_HYPOTHESIS",
                    severity="ERROR",
                    message=f"Missing required hypothesis '{h_name}' ({desc}). Expected pattern: '{h_pattern}'.",
                    penalty=penalty_per_dropped,
                    context=h_name,
                )
            )

    return defects, detected_hyps


def check_target_relation(
    decl: ParsedDeclaration,
    target_rel_spec: dict[str, Any] | str | None,
) -> list[FidelityDefect]:
    """Verify conclusion satisfies target relation specification."""
    defects: list[FidelityDefect] = []
    if not target_rel_spec:
        return defects

    conc = decl.conclusion
    norm_conc = normalize_lean_expr(conc)

    if isinstance(target_rel_spec, str):
        target_pattern = target_rel_spec
        rel_symbol = None
    else:
        target_pattern = (
            target_rel_spec.get("pattern", "")
            or target_rel_spec.get("target_conclusion", "")
            or target_rel_spec.get("conclusion", "")
        )
        rel_symbol = target_rel_spec.get("relation_symbol")

    # Check relation symbol if specified
    if rel_symbol:
        if rel_symbol not in conc and rel_symbol not in norm_conc:
            defects.append(
                FidelityDefect(
                    defect_type="RELATION_MISMATCH",
                    severity="ERROR",
                    message=f"Conclusion missing required relation symbol '{rel_symbol}'.",
                    penalty=0.40,
                    context=conc,
                )
            )

    # Check pattern matching
    if target_pattern:
        norm_pattern = normalize_lean_expr(target_pattern)
        matched = (target_pattern in conc) or (norm_pattern in norm_conc)
        if not matched:
            try:
                matched = bool(re.search(target_pattern, conc) or re.search(target_pattern, norm_conc))
            except re.error:
                pass
        if not matched:
            defects.append(
                FidelityDefect(
                    defect_type="RELATION_MISMATCH",
                    severity="ERROR",
                    message=f"Conclusion does not match target relation pattern '{target_pattern}'.",
                    penalty=0.40,
                    context=conc,
                )
            )

    return defects


# -----------------------------------------------------------------------------
# Core Evaluation API
# -----------------------------------------------------------------------------

TARGET_NAME_FIELDS = ("theorem_name", "target_symbol", "target_declaration", "decl")


def _target_names(spec: dict[str, Any]) -> tuple[list[tuple[str, str]], list[str]]:
    """Collect declared target aliases, rejecting malformed selectors."""
    supplied: list[tuple[str, str]] = []
    errors: list[str] = []
    for field_name in TARGET_NAME_FIELDS:
        if field_name not in spec:
            continue
        value = spec[field_name]
        if not isinstance(value, str) or not value.strip():
            errors.append(f"{field_name} must be a non-empty declaration-name string")
            continue
        supplied.append((field_name, value.strip()))
    return supplied, errors


def _resolve_declaration_selector(
    declarations: list[ParsedDeclaration], selector: str
) -> tuple[ParsedDeclaration | None, str | None]:
    """Resolve exact or unique short names to one parsed declaration identity."""
    exact = [d for d in declarations if d.name == selector]
    if len(exact) == 1:
        return exact[0], None
    if len(exact) > 1:
        return None, f"selector {selector!r} matches duplicate exact declarations"
    if "." not in selector:
        short = [d for d in declarations if d.name.rsplit(".", 1)[-1] == selector]
        if len(short) == 1:
            return short[0], None
        if len(short) > 1:
            return None, f"unqualified selector {selector!r} is ambiguous across {[d.name for d in short]}"
    return None, f"selector {selector!r} does not resolve to a parsed declaration"


def _select_target_declaration(
    declarations: list[ParsedDeclaration], spec: dict[str, Any], target_decl: str | None = None
) -> tuple[ParsedDeclaration | None, str | None, str | None]:
    """Resolve every provided alias and require one canonical declaration identity."""
    supplied, errors = _target_names(spec)
    if errors:
        return None, "TARGET_DECLARATION_AMBIGUOUS", "; ".join(errors)
    if target_decl is not None:
        if not isinstance(target_decl, str) or not target_decl.strip():
            return None, "TARGET_DECLARATION_REQUIRED", "Explicit target selector must be a non-empty declaration name."
        supplied.append(("target_decl", target_decl.strip()))
    if not supplied:
        if spec.get("allow_first_declaration") is True:
            return declarations[0], None, None
        return (
            None,
            "TARGET_DECLARATION_REQUIRED",
            "No target identifier supplied. Set one of theorem_name, target_symbol, "
            "target_declaration, or decl; first-declaration selection requires "
            "allow_first_declaration=true.",
        )

    resolved: list[tuple[str, ParsedDeclaration]] = []
    for field, selector in supplied:
        declaration, error = _resolve_declaration_selector(declarations, selector)
        if error or declaration is None:
            code = "TARGET_DECLARATION_AMBIGUOUS" if "ambiguous" in (error or "") or "duplicate" in (error or "") else "TARGET_DECLARATION_NOT_FOUND"
            return None, code, f"{field}: {error}"
        resolved.append((field, declaration))
    identities = {declaration.name for _, declaration in resolved}
    if len(identities) != 1:
        detail = ", ".join(f"{field}={declaration.name!r}" for field, declaration in resolved)
        return None, "TARGET_DECLARATION_AMBIGUOUS", f"Conflicting target selectors resolve to different declarations: {detail}."
    return resolved[0][1], None, None

def evaluate_statement_fidelity(
    decl_ast_or_text: str | dict[str, Any],
    spec: dict[str, Any],
) -> FidelityReport:
    """Evaluate syntactic contract fidelity beyond compilation against a specification.

    Args:
        decl_ast_or_text: Lean 4 theorem code string, AST JSON string, or AST dict.
        spec: Target specification dict containing required_hypotheses,
              carrier_requirements, and target_relation.

    Returns a heuristic syntactic FidelityReport. The score is not a probability,
    proof of semantic equivalence, or substitute for independent review.
    """
    # 1. Parse declaration
    structures: dict[str, dict[str, str]] = {}
    declarations: list[ParsedDeclaration] = []

    target_names, target_field_errors = _target_names(spec)
    target_name = (
        target_names[0][1]
        if len(target_names) == 1
        else "<invalid-target>" if target_names or target_field_errors else "<unknown>"
    )

    if isinstance(decl_ast_or_text, dict):
        declarations = parse_from_ast_json(decl_ast_or_text)
    elif isinstance(decl_ast_or_text, str) and decl_ast_or_text.strip().startswith("{"):
        declarations = parse_from_ast_json(decl_ast_or_text)
    else:
        declarations, structures = parse_lean_declarations(str(decl_ast_or_text))

    if not declarations:
        return FidelityReport(
            theorem_name=target_name or "<unknown>",
            fidelity_score=0.0,
            passed=False,
            defects=[
                FidelityDefect(
                    defect_type="PARSE_FAILURE",
                    severity="FATAL",
                    message="Failed to parse any Lean 4 declaration from input.",
                    penalty=1.0,
                )
            ],
            carrier_detected=[],
            hypotheses_detected=[],
            conclusion_detected="",
        )

    # Select target declaration
    selected_decl, selection_error, selection_message = _select_target_declaration(
        declarations, spec
    )
    if selected_decl is None:
        return FidelityReport(
            theorem_name=target_name,
            fidelity_score=0.0,
            passed=False,
            defects=[
                FidelityDefect(
                    defect_type=selection_error or "TARGET_DECLARATION_NOT_FOUND",
                    severity="FATAL",
                    message=selection_message or "Target declaration selection failed.",
                    penalty=1.0,
                    context=target_name,
                )
            ],
            carrier_detected=[],
            hypotheses_detected=[],
            conclusion_detected="",
        )

    # If spec has structure definitions, merge them
    if "structures" in spec and isinstance(spec["structures"], dict):
        structures.update(spec["structures"])

    # Extract in-scope definitions (e.g. nullPlus, matJ, matPerm12)
    definitions: dict[str, str] = {d.name: d.conclusion for d in declarations if d.kind == "def"}
    if "definitions" in spec and isinstance(spec["definitions"], dict):
        definitions.update(spec["definitions"])

    # 2. Extract carriers
    carrier_info = detect_carrier_types(selected_decl, structures, definitions=definitions)

    # 3. Check defects
    all_defects: list[FidelityDefect] = []

    # T6 Packaging check
    t6_defects = detect_t6_packaging(selected_decl, structures)
    all_defects.extend(t6_defects)

    # Vacuity check
    vac_defects = detect_vacuous_conclusion(selected_decl)
    all_defects.extend(vac_defects)

    # Carrier fidelity check
    carrier_spec = spec.get("carrier_requirements")
    if not carrier_spec and "carrier" in spec:
        carrier_value = spec["carrier"]
        if isinstance(carrier_value, str):
            carrier_spec = {"expected_carrier": carrier_value}
        elif isinstance(carrier_value, dict):
            carrier_spec = carrier_value
    carrier_defects = check_carrier_fidelity(carrier_info, carrier_spec)
    all_defects.extend(carrier_defects)

    # Hypotheses check
    req_hyps = spec.get("required_hypotheses")
    if req_hyps is None:
        req_hyps = spec.get("hypotheses", [])
    hyp_defects, detected_hyps = check_hypotheses_fidelity(
        selected_decl, structures, req_hyps
    )
    all_defects.extend(hyp_defects)

    # Target relation check
    rel_spec = spec.get("target_relation")
    if rel_spec is None:
        rel_spec = spec.get("target_conclusion")
    rel_defects = check_target_relation(selected_decl, rel_spec)
    all_defects.extend(rel_defects)

    # 4. Calculate normalized Fidelity Score ∈ [0.0, 1.0]
    has_fatal = any(d.severity == "FATAL" for d in all_defects)
    if has_fatal:
        fidelity_score = 0.0
    else:
        total_penalties = sum(d.penalty for d in all_defects)
        fidelity_score = max(0.0, min(1.0, round(1.0 - total_penalties, 4)))

    has_errors = any(d.severity in ("FATAL", "ERROR") for d in all_defects)
    passed = (fidelity_score >= 0.95) and not has_errors

    return FidelityReport(
        theorem_name=selected_decl.name,
        fidelity_score=fidelity_score,
        passed=passed,
        defects=all_defects,
        carrier_detected=carrier_info.all_carriers,
        hypotheses_detected=detected_hyps,
        conclusion_detected=selected_decl.conclusion,
        details={
            "carrier_info": carrier_info.to_dict(),
            "kind": selected_decl.kind,
            "raw_signature": selected_decl.raw_signature,
            "line_number": selected_decl.line_number,
        },
    )


def evaluate_file_fidelity(
    lean_path: str | Path,
    spec_path_or_dict: str | Path | dict[str, Any],
    target_decl: str | None = None,
) -> dict[str, FidelityReport]:
    """Evaluate fidelity for theorems in a Lean file against a target spec (single or multi-theorem)."""
    # Load spec
    if isinstance(spec_path_or_dict, (str, Path)):
        spec_data = json.loads(Path(spec_path_or_dict).read_text(encoding="utf-8"))
    else:
        spec_data = spec_path_or_dict

    lean_content = Path(lean_path).read_text(encoding="utf-8")
    return evaluate_source_fidelity(lean_content, spec_data, target_decl)


def evaluate_source_fidelity(
    lean_content: str,
    spec_data: dict[str, Any],
    target_decl: str | None = None,
) -> dict[str, FidelityReport]:
    """Screen a caller-supplied immutable source snapshot against a spec.

    This remains source-syntax screening. The caller can bind the exact text to
    external kernel evidence by hashing it once before passing it here.
    """
    declarations, structures = parse_lean_declarations(lean_content)

    if target_decl is not None and (not isinstance(target_decl, str) or not target_decl.strip()):
        return {"<invalid-target>": FidelityReport(
            theorem_name="<invalid-target>", fidelity_score=0.0, passed=False,
            defects=[FidelityDefect(
                defect_type="TARGET_DECLARATION_REQUIRED", severity="FATAL",
                message="Explicit target selector must be a non-empty declaration name.",
                penalty=1.0, context=str(target_decl),
            )], carrier_detected=[], hypotheses_detected=[], conclusion_detected="",
        )}

    requested_declaration: ParsedDeclaration | None = None
    if target_decl is not None:
        requested_declaration, selector_error = _resolve_declaration_selector(
            declarations, target_decl.strip()
        )
        if selector_error or requested_declaration is None:
            defect_type = (
                "TARGET_DECLARATION_AMBIGUOUS"
                if "ambiguous" in (selector_error or "") or "duplicate" in (selector_error or "")
                else "TARGET_DECLARATION_NOT_FOUND"
            )
            return {target_decl: FidelityReport(
                theorem_name=target_decl, fidelity_score=0.0, passed=False,
                defects=[FidelityDefect(
                    defect_type=defect_type, severity="FATAL",
                    message=selector_error or "Explicit target selector did not resolve.",
                    penalty=1.0, context=target_decl,
                )], carrier_detected=[], hypotheses_detected=[], conclusion_detected="",
            )}

    results: dict[str, FidelityReport] = {}

    # Multi-theorem spec
    if "theorems" in spec_data and isinstance(spec_data["theorems"], dict):
        suite = spec_data["theorems"]
        selected_members: list[tuple[str, dict[str, Any]]] = []
        for th_name, th_spec in suite.items():
            th_spec_copy = dict(th_spec)
            # A suite key is an asserted target too; preserve aliases to expose conflicts.
            aliases = [th_spec_copy.get(k) for k in TARGET_NAME_FIELDS if th_spec_copy.get(k)]
            if not aliases:
                th_spec_copy["theorem_name"] = th_name
            elif th_name not in aliases:
                th_spec_copy["target_declaration"] = th_name
            th_spec_copy["structures"] = structures
            if requested_declaration is not None:
                member, member_error, _ = _select_target_declaration(declarations, th_spec_copy)
                if member is not None and member_error is None and member.name == requested_declaration.name:
                    selected_members.append((th_name, th_spec_copy))
                continue
            selected_members.append((th_name, th_spec_copy))

        if requested_declaration is not None and len(selected_members) > 1:
            return {target_decl: FidelityReport(
                theorem_name=requested_declaration.name, fidelity_score=0.0, passed=False,
                defects=[FidelityDefect(
                    defect_type="TARGET_DECLARATION_AMBIGUOUS", severity="FATAL",
                    message=f"Multiple suite entries select {requested_declaration.name!r}.",
                    penalty=1.0, context=requested_declaration.name,
                )], carrier_detected=[], hypotheses_detected=[], conclusion_detected="",
            )}
        for th_name, th_spec_copy in selected_members:
            report = evaluate_statement_fidelity(lean_content, th_spec_copy)
            results[th_name] = report
    else:
        # Single theorem spec
        spec_copy = dict(spec_data)
        if target_decl is not None:
            # Add the CLI selector as another alias; canonical resolution below
            # accepts short/qualified equivalence and rejects actual conflicts.
            spec_copy["target_declaration"] = target_decl
        spec_copy["structures"] = structures
        # Pass CLI selectors directly so an explicit empty string cannot vanish
        # through truthiness checks in this API path.
        report = evaluate_statement_fidelity(lean_content, spec_copy)
        key = target_decl or report.theorem_name
        results[key] = report

    # A requested suite member that does not exist must not become an empty,
    # successful result set in the CLI/API.
    if target_decl and not results:
        results[target_decl] = FidelityReport(
            theorem_name=target_decl,
            fidelity_score=0.0,
            passed=False,
            defects=[FidelityDefect(
                defect_type="TARGET_DECLARATION_NOT_FOUND",
                severity="FATAL",
                message=f"Requested target {target_decl!r} is not a member of the specification suite.",
                penalty=1.0,
                context=target_decl,
            )],
            carrier_detected=[],
            hypotheses_detected=[],
            conclusion_detected="",
        )

    return results


# -----------------------------------------------------------------------------
# CLI Interface
# -----------------------------------------------------------------------------

def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Run syntactic contract checks on Lean declarations beyond compilation."
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    eval_parser = subparsers.add_parser("evaluate", help="Evaluate fidelity of a Lean file against spec.")
    eval_parser.add_argument("--lean", required=True, help="Path to Lean 4 source file.")
    eval_parser.add_argument("--spec", required=True, help="Path to target specification JSON file.")
    eval_parser.add_argument("--decl", default=None, help="Optional specific theorem name to evaluate.")
    eval_parser.add_argument("--json", action="store_true", help="Output results in JSON format.")
    eval_parser.add_argument("--min-score", type=float, default=0.95, help="Minimum fidelity score threshold (default: 0.95).")

    args = parser.parse_args(argv)

    if args.command == "evaluate":
        lean_path = Path(args.lean)
        spec_path = Path(args.spec)

        if not lean_path.is_file():
            print(f"[ERROR] Lean file not found: {lean_path}", file=sys.stderr)
            return 1
        if not spec_path.is_file():
            print(f"[ERROR] Spec file not found: {spec_path}", file=sys.stderr)
            return 1

        reports = evaluate_file_fidelity(lean_path, spec_path, target_decl=args.decl)

        all_passed = bool(reports)
        for th_name, rep in reports.items():
            if rep.fidelity_score < args.min_score or not rep.passed:
                all_passed = False

        if args.json:
            out_data = {
                "file": str(lean_path),
                "spec": str(spec_path),
                "all_passed": all_passed,
                "reports": {k: v.to_dict() for k, v in reports.items()},
            }
            print(json.dumps(out_data, indent=2))
        else:
            print("=" * 72)
            print("OpenGauss Statement Fidelity Gate - Syntactic Contract Screening Report")
            print("=" * 72)
            print(f"Target File: {lean_path}")
            print(f"Spec File:   {spec_path}")
            print("-" * 72)
            for th_name, rep in reports.items():
                print(rep.summary())
                print("-" * 72)
            if all_passed:
                print(f"[RESULT] ALL THEOREMS PASSED FIDELITY GATE (Threshold: {args.min_score:.2f})")
            else:
                print(f"[RESULT] FIDELITY VIOLATIONS DETECTED (Threshold: {args.min_score:.2f})")

        return 0 if all_passed else 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
