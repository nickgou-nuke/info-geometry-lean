#!/usr/bin/env python3
"""OpenGauss / TeamAntigravity Automated Screener & Protocol Validator.

Implements automated screening against the 15-Trap Catalog (TRAP_CATALOG.md)
and validates top-down assume-and-recurse proof invariants for Lean 4 modules.
"""

from __future__ import annotations

import argparse
import datetime
import functools
import hashlib
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


@dataclass
class TrapViolation:
    trap_id: str
    trap_name: str
    line_number: int
    matched_text: str
    message: str
    severity: str = "ERROR"  # ERROR or WARNING


# Regular expression patterns for static screening of T1-T15 traps
_TRAP_PATTERNS = [
    (
        "T1",
        "Raw Chart/Coordinate Extraction off Basepoint",
        re.compile(r"\b(coordChange|extChartAt)\b.*?\b(achart\s+\w+)\b"),
        "Raw coordinate change with moving chart index detected. Enforce intrinsic section or bundle pairing.",
        "ERROR",
    ),
    (
        "T3",
        "Global Flatness / Locally Constant Chart",
        re.compile(r"\bHasLocallyConstantChartAt\b"),
        "HasLocallyConstantChartAt hypothesis detected. Strictly prohibited on non-trivial manifolds.",
        "ERROR",
    ),
    (
        "T4",
        "Vacuous Binders & Degenerate Conditions",
        re.compile(r"[({]\s*\w+\s*:\s*(0\s*=\s*0|True|x\s*=\s*x|inner\s+0\s+\w+\s*=\s*0)\s*[)}]|\b(?:def|abbrev)\s+\w+\s*:\s*Prop\s*:=\s*True\b"),
        "Vacuous binder detected in hypotheses. Remove or state genuine mathematical constraint.",
        "ERROR",
    ),
    (
        "T6",
        "Hypothesis Packaging",
        re.compile(r"\btheorem\b|\blemma\b"),  # handled via custom structural parser
        "Hypothesis packaging detected: hypothesis type is definitionally identical to the conclusion.",
        "ERROR",
    ),
    (
        "T9",
        "Two-Sided Derivative on Cutoff Interval",
        re.compile(r"\bHasDerivAt\b.*?\b(Icc|Ico|Ioc|Ici)\b"),
        "Two-sided derivative asserted on boundary/interval. Use HasDerivWithinAt.",
        "WARNING",
    ),
    (
        "T10",
        "Boundary Smoothness on Closed Intervals",
        re.compile(r"\bContDiffOn\s+ℝ\s+\w+\s+(?:⊤|∞|\d+)[^\n]*(?:Icc|Ici)|\bContDiff\s+ℝ\s+(?:⊤|∞|\d+)\s+\w+[^\n]*(?:Icc|Ici)"),
        "Top-order smoothness is asserted on a closed interval. Check boundary regularity; use interior smoothness with explicit within-set boundary regularity.",
        "WARNING",
    ),
    (
        "T13",
        "Krein / Positive-Definite Signature Clash",
        re.compile(
            r"(?:\bKreinSpace\b[^\n]*(?:kreinInner|KreinInner)[^\n]*"
            r"(?:PositiveDefinite|IsPositiveDefinite)|"
            r"(?:PositiveDefinite|IsPositiveDefinite)[^\n]*(?:kreinInner|KreinInner))"
        ),
        "Positive definiteness is asserted for the Krein form itself; distinguish it from the auxiliary Hilbert majorant.",
        "ERROR",
    ),
    (
        "T15",
        "Definitional Unfolding Loop Risk",
        re.compile(r"\b(dsimp|unfold)\s+\[(?:[^\]]*\b(TensorTower|Colimit|Quotient)\b[^\]]*)\]"),
        "Unbounded definitional unfolding on deep colimit/quotient structures. Use opaque barriers or lemma rewrites.",
        "WARNING",
    ),
    (
        "T16",
        "Semantic Surrogate / Scalar Toy Proxy",
        re.compile(r"\bstructure\s+(?:BlockSuperTrace|\w*TraceProxy|\w*ScalarProxy|\w*DummyCarrier)\b"),
        "Scalar surrogate record detected in place of genuine operator/matrix algebra. Use native Matrix, End, or module carriers.",
        "ERROR",
    ),
]



def check_hypothesis_packaging(lines: list[str]) -> list[TrapViolation]:
    """Detect Trap T6: A hypothesis whose type is identical to the theorem's conclusion."""
    violations: list[TrapViolation] = []
    source = "\n".join(lines)
    starts = list(re.finditer(r"^\s*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+([\w'.]+)", source, re.MULTILINE))
    for index, start in enumerate(starts):
        end = starts[index + 1].start() if index + 1 < len(starts) else len(source)
        declaration = source[start.start():end]
        parsed = _top_level_result_type(declaration)
        if parsed is None:
            continue
        binders_text, conclusion = parsed
        assignment = _top_level_assignment_index(declaration)
        if assignment is None:
            continue
        proof = declaration[assignment + 2:].strip()
        cleaned_proof = re.sub(r"(?:\n\s*end(?:\s+[\w.]+)?\s*)+\Z", "", proof).strip()
        closing_ident: str | None = None
        implicit_closing_tactic: str | None = None
        for pattern in (
            r"(?:(?:by\s+)?(?:exact|apply|refine)\s+)?(?:\(\s*)?(?:id\s+)?([\w'.]+)(?:\s*\))?",
            r"by\s+simpa\b[^\n]*?\busing\s+([\w'.]+)",
            r"by\s+simp(?:\s+only)?\s*\[[^\]]*(?<![\w'])([\w'.]+)(?![\w'])[^\]]*\]",
        ):
            m = re.fullmatch(pattern, cleaned_proof, re.DOTALL)
            if m is not None:
                closing_ident = m.group(1)
                break
        if closing_ident is None:
            implicit_match = re.fullmatch(
                r"by\s+(assumption|tauto|trivial|rwa(?:\s*\[[^\]]*\])?(?:\s+at\s+\*)?)",
                cleaned_proof,
                re.DOTALL,
            )
            if implicit_match is not None:
                implicit_closing_tactic = implicit_match.group(1)
        if closing_ident is None and implicit_closing_tactic is None:
            continue
        # Read all explicit binder groups with balanced delimiters, including
        # implicit and instance binders. Their types may themselves be nested.
        binders: list[tuple[str, str]] = []
        pos = 0
        while pos < len(binders_text):
            if binders_text[pos] not in "({[⦃":
                pos += 1
                continue
            atom = _balanced_lean_atom(binders_text, pos)
            if atom is None:
                break
            group, next_pos = atom
            colon = _top_level_result_type(group[1:-1])
            if colon is not None:
                names, binder_type = colon
                binders.extend((name, binder_type) for name in re.findall(r"[\w']+", names))
            pos = next_pos
        norm_conclusion = re.sub(r"\s+", " ", conclusion).strip()
        for b_name, b_type in binders:
            norm_b_type = re.sub(r"\s+", " ", b_type).strip()
            if norm_b_type != norm_conclusion:
                continue
            if closing_ident == b_name or implicit_closing_tactic is not None:
                line_number = source.count("\n", 0, start.start()) + 1
                returned_repr = closing_ident if closing_ident is not None else implicit_closing_tactic
                violations.append(TrapViolation(
                    trap_id="T6",
                    trap_name="Hypothesis Packaging",
                    line_number=line_number,
                    matched_text=declaration.strip()[:100],
                    message=f"Theorem '{start.group(1)}' assumes hypothesis '{b_name} : {b_type}' and returns '{returned_repr}' as proof.",
                    severity="ERROR",
                ))
    return violations


def check_unused_hypothesis_binders(source: str) -> list[TrapViolation]:
    """Flag named hypothesis binders unused by a theorem's result and proof."""
    violations: list[TrapViolation] = []
    starts = list(re.finditer(
        r"^\s*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+([\w'.]+)",
        source,
        re.MULTILINE,
    ))
    for index, start in enumerate(starts):
        end = starts[index + 1].start() if index + 1 < len(starts) else len(source)
        declaration = source[start.start():end]
        parsed = _top_level_result_type(declaration)
        if parsed is None:
            continue
        binders_text, conclusion = parsed
        assignment = _top_level_assignment_index(declaration)
        proof = declaration[assignment + 2:] if assignment is not None else ""
        pos = 0
        parsed_binders: list[tuple[str, str]] = []
        while pos < len(binders_text):
            if binders_text[pos] not in "({[⦃":
                pos += 1
                continue
            atom = _balanced_lean_atom(binders_text, pos)
            if atom is None:
                break
            group, next_pos = atom
            parsed_binder = _top_level_result_type(group[1:-1])
            if parsed_binder is not None:
                names, binder_type = parsed_binder
                for name in re.findall(r"[\w']+", names):
                    parsed_binders.append((name, binder_type))
            pos = next_pos

        # Lean's `subst x` consumes an equality hypothesis with `x` as a bare
        # side. The source screen cannot determine which local equality the
        # tactic selects after the proof has changed its local context. Grant
        # an implicit-use exemption only when `subst` is the first proof
        # tactic, the declaration binder is the unique direct-equality
        # candidate, and the target occurs as a bare side of that equality.
        subst_consumed: set[str] = set()
        for subst_match in re.finditer(
            r"\bsubst\s+([A-Za-z_][A-Za-z0-9_']*)", proof
        ):
            target = subst_match.group(1)
            proof_prefix = proof[:subst_match.start()]
            # Strip the theorem proof's leading `by`. A preceding completed
            # `have` is harmless when its declared type does not mention the
            # substitution target: its proof runs in a nested tactic block and
            # cannot change the outer local context. Any other outer tactic
            # may introduce or alter equalities, so the text-only screen must
            # not guess which hypothesis `subst` consumes.
            proof_prefix = re.sub(r"^\s*by\b", "", proof_prefix, count=1).strip()
            prefix_is_safe = True
            prefix_lines = proof_prefix.splitlines()
            line_index = 0
            while line_index < len(prefix_lines):
                raw_line = prefix_lines[line_index]
                prefix_line = raw_line.strip()
                if not prefix_line:
                    line_index += 1
                    continue
                harmless_have = re.fullmatch(
                    r"have\s+[A-Za-z_][A-Za-z0-9_']*\s*:\s*(.*?)\s*:=\s*(.*)",
                    prefix_line,
                )
                if (
                    harmless_have is None
                    or re.search(rf"\b{re.escape(target)}\b", harmless_have.group(1))
                ):
                    prefix_is_safe = False
                    break
                # If the nested proof starts on the next line, consume only
                # its more-indented lines. A same-indent outer tactic remains
                # visible to the loop and therefore rejects the exemption.
                if harmless_have.group(2).strip() == "by":
                    have_indent = len(raw_line) - len(raw_line.lstrip())
                    line_index += 1
                    while line_index < len(prefix_lines):
                        nested_line = prefix_lines[line_index]
                        if nested_line.strip() and len(nested_line) - len(nested_line.lstrip()) <= have_indent:
                            break
                        line_index += 1
                    continue
                line_index += 1
            if not prefix_is_safe:
                continue
            candidates = [
                name
                for name, binder_type in parsed_binders
                if (
                    (equality_sides := _top_level_equality_sides(binder_type))
                    is not None
                    and (
                        _bare_identifier(equality_sides[0]) == target
                        or _bare_identifier(equality_sides[1]) == target
                    )
                )
            ]
            if len(candidates) == 1:
                subst_consumed.add(candidates[0])

        for name, binder_type in parsed_binders:
            if binder_type.lstrip().startswith("∀") and _is_reflexive_equality_type(binder_type):
                line_number = source.count("\n", 0, start.start()) + 1
                violations.append(TrapViolation(
                    trap_id="T4",
                    trap_name="Vacuous Binders & Degenerate Conditions",
                    line_number=line_number,
                    matched_text=f"({name} : {binder_type})"[:100],
                    message=(
                        f"Degenerate reflexive hypothesis: theorem '{start.group(1)}' "
                        f"assumes '{name} : {binder_type}', which is reflexive for every quantified input."
                    ),
                    severity="ERROR",
                ))
                continue
            is_underscore_hyp = name.startswith("_h")
            is_regular_hyp = name.startswith("h") and name not in {"have", "has", "hypothesis"}
            if not (is_underscore_hyp or is_regular_hyp):
                continue
            escaped_name = re.escape(name)
            ident_pattern = rf"(?<![\w']){escaped_name}(?![\w'])"
            noop_patterns = (
                rf"\b(?:let|have)\s+_\s*(?::[^:=\n]+)?\s*:=\s*{escaped_name}(?![\w'])",
                rf"\b(?:let|have)\s+{escaped_name}\s*(?::[^:=\n]+)?\s*:=\s*{escaped_name}(?![\w'])",
                rf"\bclear\s+(?:[A-Za-z_][A-Za-z0-9_']*\s+)*{escaped_name}(?![\w'])",
            )
            had_noop_discard = any(re.search(pat, proof) for pat in noop_patterns)
            sanitized_proof = proof
            for pat in noop_patterns:
                sanitized_proof = re.sub(pat, "", sanitized_proof)
            used_text = conclusion + " " + sanitized_proof
            if name not in subst_consumed and not re.search(ident_pattern, used_text):
                line_number = source.count("\n", 0, start.start()) + 1
                is_evasion = is_underscore_hyp or had_noop_discard
                violations.append(TrapViolation(
                    trap_id="T4",
                    trap_name="Vacuous Binders & Degenerate Conditions",
                    line_number=line_number,
                    matched_text=f"({name} : {binder_type})"[:100],
                    message=(
                        f"Vacuous binder: Theorem '{start.group(1)}' has an unused hypothesis binder "
                        f"'{name} : {binder_type}'"
                        + (" (silenced via underscore prefix or no-op discard)." if is_evasion else ".")
                    ),
                    severity="ERROR" if is_evasion else "WARNING",
                ))
    return violations


def check_scalar_surrogates(lines: list[str]) -> list[TrapViolation]:
    """Detect Trap T16: Scalar surrogate records posing as operator or matrix algebras."""
    violations: list[TrapViolation] = []
    in_struct = False
    struct_name = ""
    struct_line = 0
    scalar_trace_fields: list[str] = []

    for idx, line in enumerate(lines, start=1):
        stripped = line.strip()
        if stripped.startswith("--") or stripped.startswith("/-"):
            continue
        m = re.match(r"^structure\s+(\w+)", stripped)
        if m:
            in_struct = True
            struct_name = m.group(1)
            struct_line = idx
            scalar_trace_fields = []
            if re.search(r"BlockSuperTrace|ScalarProxy|TraceProxy|DummyCarrier", struct_name):
                violations.append(
                    TrapViolation(
                        trap_id="T16",
                        trap_name="Semantic Surrogate / Scalar Toy Proxy",
                        line_number=idx,
                        matched_text=stripped[:80],
                        message=f"Structure '{struct_name}' is an explicit scalar surrogate proxy. Must use native Matrix or operator carriers.",
                        severity="ERROR",
                    )
                )
            continue
        if in_struct:
            if (stripped.startswith("def ") or stripped.startswith("theorem ") or
                stripped.startswith("lemma ") or stripped.startswith("end ") or
                stripped.startswith("namespace ") or stripped.startswith("open ")):
                in_struct = False
                continue
            field_m = re.match(r"^(tr_[A-Za-z0-9]+|det[A-Za-z0-9]+|schur[A-Za-z0-9_]+)\s*:\s*([A-Za-z0-9_]+)", stripped)
            if field_m:
                scalar_trace_fields.append(field_m.group(1))
                if len(scalar_trace_fields) >= 2:
                    violations.append(
                        TrapViolation(
                            trap_id="T16",
                            trap_name="Semantic Surrogate / Scalar Toy Proxy",
                            line_number=struct_line,
                            matched_text=f"structure {struct_name} (fields: {', '.join(scalar_trace_fields)})",
                            message=f"Structure '{struct_name}' bundles scalar trace/determinant values as a toy proxy. Ground in native Matrix or End.",
                            severity="ERROR",
                        )
                    )
                    in_struct = False
    return violations


def check_homomorphism_rejection(lines: list[str]) -> list[TrapViolation]:
    """Detect Trap T16 Homomorphism Rejection:

    Flags attempts to collapse non-commutative operator/matrix algebras into
    scalar fields via unauthorized linear/trace mappings before commutators or
    Lie brackets are evaluated (e.g. commutator (tr A) (tr B), ⁅tr A, tr B⁆, or
    tr(A) * tr(B) - tr(B) * tr(A)).
    """
    violations: list[TrapViolation] = []

    # Pattern 1: commutator or Lie bracket directly wrapping scalar/trace projections
    pat_bracket_scalar = re.compile(
        r"(?:\bcommutator\s*\(?\s*|⁅\s*)(?:(?:Matrix\.)?trace|tr\b|det\b|[A-Za-z0-9_]*\.(?:omega|trace|tr|det)\b)"
    )
    # Pattern 2: scalar product difference of linear/trace mappings mimicking a commutator
    pat_trace_product_diff = re.compile(
        r"(?:\b(?:Matrix\.)?trace|tr|det|[A-Za-z0-9_]*\.omega)\s*(?:\([^)]*\)|[a-zA-Z0-9_]+)\s*\*\s*"
        r"(?:\b(?:Matrix\.)?trace|tr|det|[A-Za-z0-9_]*\.omega)\s*(?:\([^)]*\)|[a-zA-Z0-9_]+)\s*-\s*"
        r"(?:\b(?:Matrix\.)?trace|tr|det|[A-Za-z0-9_]*\.omega)"
    )

    for idx, line in enumerate(lines, start=1):
        clean = line.split("--")[0].strip()
        if not clean or clean.startswith("/-"):
            continue

        if pat_bracket_scalar.search(clean):
            violations.append(
                TrapViolation(
                    trap_id="T16",
                    trap_name="Homomorphism Rejection / Pre-Commutator Scalar Collapse",
                    line_number=idx,
                    matched_text=clean[:80],
                    message=(
                        "Non-commutative algebra is collapsed into a scalar field via unauthorized "
                        "linear/trace projection before commutator/bracket evaluation. "
                        "Evaluate commutators natively within the operator algebra before applying state/trace functionals."
                    ),
                    severity="ERROR",
                )
            )
        elif pat_trace_product_diff.search(clean):
            violations.append(
                TrapViolation(
                    trap_id="T16",
                    trap_name="Homomorphism Rejection / Pre-Commutator Scalar Collapse",
                    line_number=idx,
                    matched_text=clean[:80],
                    message=(
                        "Scalar product difference of trace/state projections detected in place of genuine algebra commutator. "
                        "Commutators in non-commutative algebras must not be replaced by commutative scalar products."
                    ),
                    severity="ERROR",
                )
            )

    return violations


def check_noncommutative_witness_requirement(
    content: str,
    lines: list[str],
    filename: str = "<unknown>",
    import_root: Path | None = None,
) -> list[TrapViolation]:
    """Detect Trap T16 Non-Commutativity Witness Requirement:

    For files declaring non-commutative algebras or matrices (e.g. Matrix (Fin 2) (Fin 2) R,
    Clifford algebras, or Cockle split-quaternions), verify they explicitly contain or import
    non-commutativity witnesses (e.g. [E01, E10] ≠ 0, matI * matJ ≠ matJ * matI,
    or anticommutator {i, j} = 0).
    """
    violations: list[TrapViolation] = []

    pat_noncomm_decl = re.compile(
        r"\bMatrix\s*\(\s*Fin\s+([2-9]|\d{2,}|n)\s*\)\s*\(\s*Fin\s+([2-9]|\d{2,}|n)\s*\)"
        r"|\bMatrix\s*\(\s*Fin\s+\d+\s*×\s*Fin\s+\d+\s*\)"
        r"|\b(?:CliffordAlgebra|QuaternionAlgebra)\b"
    )

    decl_found = False
    decl_line = 0
    decl_text = ""

    for idx, line in enumerate(lines, start=1):
        clean = line.split("--")[0].strip()
        if not clean or clean.startswith("/-"):
            continue
        m = pat_noncomm_decl.search(clean)
        if m:
            decl_found = True
            decl_line = idx
            decl_text = clean[:80]
            break

    if not decl_found:
        return violations

    # A square matrix type is also used for Gram/Cartan coefficient tables.
    # Only a product whose operands are typed as matrices activates matrix T16;
    # an unrelated scalar product elsewhere in the file must not do so.
    matrix_carriers = _required_matrix_carriers(content)
    has_other_operator_product = _has_typed_noncommutative_product(content)
    if not matrix_carriers and not has_other_operator_product:
        return violations
    # A file can contain operator products over several carriers. Require a
    # matching witness for each carrier; one real-matrix witness cannot certify
    # a separate complex- or finite-field matrix algebra.
    if matrix_carriers:
        carrier_coverage = all(
            _has_closed_noncommutativity_witness(content, required_carriers={carrier})
            or _has_resolved_import_witness(
                content,
                filename,
                required_carriers={carrier},
                import_root=import_root,
            )
            for carrier in matrix_carriers
        )
    else:
        carrier_coverage = (
            _has_closed_noncommutativity_witness(content)
            or _has_resolved_import_witness(
                content, filename, import_root=import_root
            )
        )

    if not carrier_coverage:
        violations.append(
            TrapViolation(
                trap_id="T16",
                trap_name="Semantic Surrogate / Missing Non-Commutativity Witness",
                line_number=decl_line,
                matched_text=decl_text,
                message=(
                    "File declares non-commutative algebra or matrix structures (e.g. Matrix (Fin n) or CliffordAlgebra) "
                    "but lacks an explicit non-commutativity witness (e.g. matI * matJ ≠ matJ * matI, [A, B] ≠ 0, "
                    "or anticommutator {i, j} = 0) or an imported witness module."
                ),
                severity="ERROR",
            )
        )

    return violations


_NONCOMMUTATIVITY_PATTERNS = (
    r"(?:\b\w+\s*\*\s*\w+\s*(?:≠|!=)\s*\w+\s*\*\s*\w+\b|"
    r"⁅\s*\w+\s*,\s*\w+\s*⁆\s*(?:≠|!=)\s*0|"
    r"\[\s*\w+\s*,\s*\w+\s*\]\s*(?:≠|!=)\s*0|"
    r"\b\w+\s*\*\s*\w+\s*-\s*\w+\s*\*\s*\w+\s*(?:≠|!=)\s*0|"
    r"¬\s*Commute\b|!Commute\b|"
    r"\b\w+\s*\*\s*\w+\s*\+\s*\w+\s*\*\s*\w+\s*=\s*(?:0|1|2|-1)\b|"
    r"\b\w+\s*\*\s*\w+\s*-\s*\w+\s*\*\s*\w+\s*=\s*(?:[2-9]|-|\w+\s*•|\w+)\b)"
)


def _top_level_assignment_index(header: str) -> int | None:
    """Find the proof/value assignment delimiter outside nested syntax."""
    depth = 0
    for i in range(len(header) - 1):
        char = header[i]
        if char in "([{⦃":
            depth += 1
        elif char in ")]}⦄" :
            depth = max(0, depth - 1)
        elif depth == 0 and header.startswith(":=", i):
            if re.search(
                r"\blet\s+(?:\([^)]*\)|[A-Za-z_][A-Za-z0-9_']*)(?:\s+\([^)]*\))*(?:\s*:\s*[^:=]*)?\s*$",
                header[:i],
            ):
                continue
            return i
    return None


def _top_level_result_type(header: str) -> tuple[str, str] | None:
    """Return `(bindersAndName, resultType)` for a Lean declaration header."""
    assignment = _top_level_assignment_index(header)
    if assignment is not None:
        header = header[:assignment]
    depth = 0
    for i, char in enumerate(header):
        if char in "([{⦃":
            depth += 1
        elif char in ")]}⦄" :
            depth = max(0, depth - 1)
        elif depth == 0 and char == ":":
            return header[:i], header[i + 1 :].strip()
    return None


def _top_level_equality_sides(expression: str) -> tuple[str, str] | None:
    """Return the two sides of a bare equality outside nested Lean syntax."""
    expression = expression.strip()
    # Parenthesized binder types are common, but only peel a pair that encloses
    # the complete expression. Nested equalities must remain nested.
    while expression.startswith("("):
        atom = _balanced_lean_atom(expression, 0)
        if atom is None or atom[1] != len(expression):
            break
        expression = atom[0][1:-1].strip()

    depth = 0
    equality_positions: list[int] = []
    for index, char in enumerate(expression):
        if char in "([{⦃":
            depth += 1
        elif char in ")] }⦄".replace(" ", ""):
            depth = max(0, depth - 1)
        elif char == "=" and depth == 0:
            before = expression[index - 1] if index else ""
            after = expression[index + 1] if index + 1 < len(expression) else ""
            if before not in ":=<>!" and after not in "=>":
                equality_positions.append(index)
    if len(equality_positions) == 1:
        position = equality_positions[0]
        return expression[:position].strip(), expression[position + 1 :].strip()
    # `Eq x y` is the explicit proposition form corresponding to `x = y`.
    # Read two balanced atoms; callers only credit bare identifiers after
    # normalization, so applications cannot be mistaken for a direct side.
    if expression.startswith("Eq") and (len(expression) == 2 or expression[2].isspace()):
        left = _balanced_lean_atom(expression, 2)
        if left is not None:
            right = _balanced_lean_atom(expression, left[1])
            if right is not None and not expression[right[1] :].strip():
                return left[0], right[0]
    return None


def _is_reflexive_equality_type(expression: str) -> bool:
    """Detect a hypothesis type reducing textually to `∀ ..., t = t`.

    This catches reflexive evidence hidden behind quantified binders, such as
    `(h : ∀ x, f x = f x)`, which an unused-binder scan misses when the proof
    explicitly consumes `h`.
    """
    expression = expression.strip()
    while expression.startswith("("):
        atom = _balanced_lean_atom(expression, 0)
        if atom is None or atom[1] != len(expression):
            break
        expression = atom[0][1:-1].strip()

    while expression.startswith("∀"):
        depth = 0
        comma = None
        for index, char in enumerate(expression[1:], start=1):
            if char in "([{⦃":
                depth += 1
            elif char in ")] }⦄".replace(" ", ""):
                depth = max(0, depth - 1)
            elif char == "," and depth == 0:
                comma = index
                break
        if comma is None:
            return False
        expression = expression[comma + 1 :].strip()

    sides = _top_level_equality_sides(expression)
    if sides is None:
        return False
    def token_signature(term: str) -> tuple[str, ...]:
        # Ignore redundant parentheses around the whole term, but preserve
        # token boundaries: deleting whitespace would conflate `f x` with
        # the distinct identifier `fx`.
        term = term.strip()
        while term.startswith("("):
            atom = _balanced_lean_atom(term, 0)
            if atom is None or atom[1] != len(term):
                break
            term = atom[0][1:-1].strip()
        return tuple(re.findall(r"[^\W\d]\w*(?:['′]\w*)?|\d+|[^\s]", term))

    return token_signature(sides[0]) == token_signature(sides[1])


def _bare_identifier(expression: str) -> str | None:
    """Recognize an identifier optionally wrapped in redundant parentheses."""
    expression = expression.strip()
    while expression.startswith("("):
        atom = _balanced_lean_atom(expression, 0)
        if atom is None or atom[1] != len(expression):
            break
        expression = atom[0][1:-1].strip()
    return expression if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", expression) else None


def _prior_variable_binders(source: str, *, already_clean: bool = False) -> list[tuple[str, str]]:
    """Return `(name, type)` pairs from preceding Lean `variable` commands."""
    clean = source if already_clean else _strip_lean_comments_and_strings(source)
    binders: list[tuple[str, str]] = []
    active_declarations = _ambient_variable_declarations(clean, len(clean))
    for block in active_declarations:
        position = 0
        while position < len(block):
            opener = re.search(r"[([{⦃]", block[position:])
            if opener is None:
                break
            start = position + opener.start()
            atom = _balanced_lean_atom(block, start)
            if atom is None:
                position = start + 1
                continue
            group, next_position = atom
            parsed = _top_level_result_type(group[1:-1])
            if parsed is not None:
                names, binder_type = parsed
                binders.extend(
                    (name, binder_type)
                    for name in re.findall(r"[A-Za-z_][A-Za-z0-9_']*", names)
                )
            position = next_position
    return binders


def _has_prior_variable_binder(source: str, target: str) -> bool:
    """Detect an ambient `variable` binder that shadows a scalar projection name."""
    return any(name == target for name, _ in _prior_variable_binders(source))


@functools.lru_cache(maxsize=256)
def _strip_lean_comments_and_strings(source: str) -> str:
    """Blank comments and strings while preserving line breaks and offsets."""
    chars = list(source)
    i = 0
    depth = 0
    in_string = False
    while i < len(chars):
        if in_string:
            if chars[i] == "\\":
                if i + 1 < len(chars) and chars[i + 1] != "\n":
                    chars[i] = chars[i + 1] = " "
                    i += 2
                    continue
            elif chars[i] == '"':
                in_string = False
            if chars[i] != "\n":
                chars[i] = " "
            i += 1
            continue
        if depth:
            if source.startswith("/-", i):
                depth += 1
                chars[i] = chars[i + 1] = " "
                i += 2
                continue
            if source.startswith("-/", i):
                depth -= 1
                chars[i] = chars[i + 1] = " "
                i += 2
                continue
            if chars[i] != "\n":
                chars[i] = " "
            i += 1
            continue
        if source.startswith("/-", i):
            depth = 1
            chars[i] = chars[i + 1] = " "
            i += 2
        elif source.startswith("--", i):
            while i < len(chars) and chars[i] != "\n":
                chars[i] = " "
                i += 1
        elif source.startswith("'\"'", i):
            chars[i] = chars[i + 1] = chars[i + 2] = " "
            i += 3
        elif source.startswith("'\\\"'", i):
            chars[i] = chars[i + 1] = chars[i + 2] = chars[i + 3] = " "
            i += 4
        elif chars[i] == '"':
            in_string = True
            chars[i] = " "
            i += 1
        else:
            i += 1
    return "".join(chars)


def check_authored_axioms_and_holes(source: str) -> list[TrapViolation]:
    """Reject repo-authored axioms and proof holes in Lean source.

    This is a source gate. The allowed foundational axiom footprint of a
    checked theorem is audited separately with Lean's `#print axioms` output.
    """
    clean = _strip_lean_comments_and_strings(source)
    violations: list[TrapViolation] = []
    lean_name = r"(?:«[^»\n]+»|[^\W\d][\w'.]*)"
    axiom_decl = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped)\s+)*(?:axiom|postulate)\s+"
        rf"({lean_name})",
        re.MULTILINE,
    )
    for match in axiom_decl.finditer(clean):
        line = clean.count("\n", 0, match.start()) + 1
        violations.append(TrapViolation(
            "QMS_AXIOM", "Repository-authored axiom", line, match.group(0).strip(),
            "Repository source must prove results with Lean/Mathlib theorems; do not declare axioms.",
            "ERROR",
        ))
    # `sorryAx` and `admitAx` are kernel-level axiom names. An audit companion has to be able
    # to *mention* them (e.g. `grep`ing a `.trace` for `sorryAx`), so a backtick-quoted
    # occurrence is permitted; any other occurrence fails this source gate. Note the escape
    # below is deliberately narrower than this comment might suggest: it only exempts the
    # *words* `sorry`/`admit` when they appear as the tail of a dotted Lean path (e.g.
    # `Lean.sorry`), so `Lean.sorryAx` unquoted is still rejected. That is fail-closed and
    # intentional \u2014 a real `sorryAx` proof term can never reach a build through this path.
    for match in re.finditer(
        r"(?<![\w'])(?:[A-Za-z_][\w']*\.)*(sorry|admit|sorryAx|admitAx)\b|«(sorry|admit|sorryAx|admitAx)»",
        clean,
    ):
        token = match.group(1) or match.group(2)
        if token in {"sorryAx", "admitAx"} and clean[max(0, match.start() - 2):match.start()] == "``":
            continue
        if token in {"sorry", "admit"} and match.group(2) is None and "." in match.group(0):
            continue
        line = clean.count("\n", 0, match.start()) + 1
        violations.append(TrapViolation(
            "QMS_HOLE", "Unproved theorem placeholder", line, match.group(0),
            "Remove proof holes and provide a kernel-checked proof.", "ERROR",
        ))
    return violations


def _witness_has_only_typeclass_binders(
    binders_and_name: str,
    *,
    target_type_name: str | None = None,
    source: str = "",
) -> bool:
    """Allow type parameters and ordinary laws, but no assumed witness data."""
    prefix = re.sub(
        r"^\s*(?:(?:private|protected|noncomputable)\s+)*(?:def|abbrev|theorem|lemma|instance)\s+\S+",
        "",
        binders_and_name,
    )
    for binder in re.findall(r"\[([^\[\]]*)\]", prefix):
        if re.search(r"\b(?:IsEmpty|Subsingleton|False)\b", binder):
            return False
        expanded_binder = _expand_local_type_alias(source, binder) if source else binder
        if re.search(r"\b(?:Nonempty|Inhabited)\b", expanded_binder) and (
            target_type_name is None
            or re.search(rf"\b{re.escape(target_type_name)}\b", expanded_binder)
        ):
            return False
        if target_type_name is not None:
            binder_rhs = binder.split(":", 1)[1] if ":" in binder else binder
            class_name = re.match(r"\s*([A-Za-z_][A-Za-z0-9_'.]*)", binder_rhs)
            if class_name and _typeclass_binder_supplies_target(
                source, class_name.group(1), target_type_name
            ):
                return False
    if any(token in prefix for token in ("≠", "!=", "False", "Commute")):
        return False
    # Type parameters such as `{R : Type*}` are harmless; term assumptions
    # could supply the witness or make its conclusion follow by elimination.
    binder_pattern = r"[({⦃]([^(){}⦃⦄]*)[)}⦄]"
    local_type_params: set[str] = set()
    for binder in re.findall(binder_pattern, prefix):
        if ":" not in binder:
            return False
        names_part, binder_type_raw = binder.split(":", 1)
        binder_type = binder_type_raw.strip()
        if re.fullmatch(r"(?:Type|Sort)(?:\s+\w+)?\s*\*?", binder_type):
            local_type_params.update(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", names_part))
            continue
        if binder_type in {"ℕ", "Nat"}:
            local_type_params.update(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", names_part))
            continue
        if target_type_name is not None and binder_type in local_type_params:
            continue
        return False
    remaining = re.sub(r"\[[^\[\]]*\]", "", prefix)
    remaining = re.sub(binder_pattern, "", remaining)
    return not re.search(r"[({⦃]", remaining)


def _typeclass_binder_supplies_target(source: str, class_name: str, target: str) -> bool:
    """Reject a typeclass assumption whose local class provides the target."""
    # A class declaration imported from another module is opaque to this
    # source-only screen.  Permit only the standard algebraic infrastructure
    # classes that cannot package an arbitrary inhabitant; unknown classes
    # fail closed until an elaborated environment check is available.
    safe_external = {
        "Add", "AddCommMonoid", "AddCommGroup", "AddGroup", "AddMonoid",
        "AddSemigroup", "AddZeroClass", "AddCommSemigroup", "Mul",
        "MulZeroClass", "Semigroup", "Monoid", "CommMonoid", "Group",
        "CommGroup", "Semiring", "CommSemiring", "Ring", "CommRing",
        "DivisionRing", "Field", "Nontrivial", "Zero", "One", "OfNat",
        "Neg", "Sub", "Pow", "SMul", "Module", "Finite",
        "DecidableEq", "Decidable", "BEq", "Hashable", "LawfulBEq", "LinearOrder",
        "PartialOrder", "Preorder", "LE", "LT", "LT.lt", "LE.le",
        "Inhabited",
    }
    clean_source = _strip_lean_comments_and_strings(source)
    text = clean_source
    aliases_of_target = {
        alias for alias, _params, rhs in re.findall(
            r"^\s*(?:(?:private|protected|noncomputable)\s+)*(?:abbrev|def)\s+([A-Za-z_][\w']*)\s*((?:\((?:[^()\n]|\([^()\n]*\))*\)\s*)*)(?:\s*:\s*[^=\n]+)?\s*:=\s*([^\n]+)",
            text,
            re.MULTILINE,
        ) if re.search(rf"\b{re.escape(target)}\b", rhs)
    }
    alias_rhs = {
        alias: rhs for alias, _params, rhs in re.findall(
            r"^\s*(?:(?:private|protected|noncomputable)\s+)*(?:abbrev|def)\s+([A-Za-z_][\w']*)\s*((?:\((?:[^()\n]|\([^()\n]*\))*\)\s*)*)(?:\s*:\s*[^=\n]+)?\s*:=\s*([^\n]+)",
            text,
            re.MULTILINE,
        )
    }
    changed = True
    while changed:
        changed = False
        for alias, rhs in alias_rhs.items():
            if alias not in aliases_of_target and any(
                re.search(rf"\b{re.escape(child)}\b", rhs) for child in aliases_of_target
            ):
                aliases_of_target.add(alias)
                changed = True

    def provides(name: str, seen: set[str]) -> bool:
        if name in seen:
            return False
        seen.add(name)
        declaration = re.search(
            rf"^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*class\s+{re.escape(name)}\b",
            text,
            re.MULTILINE,
        )
        if declaration is None:
            return name.split(".")[-1] not in safe_external
        following = re.search(
            r"^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*(?:class|structure|def|abbrev|theorem|lemma|instance|inductive|namespace|section|end)\b",
            text[declaration.end():],
            re.MULTILINE,
        )
        body_end = declaration.end() + following.start() if following else len(text)
        declaration_text = text[declaration.start():body_end]
        where = re.search(r"\bwhere\b", declaration_text)
        header = declaration_text[:where.start()] if where else declaration_text.splitlines()[0]
        body = declaration_text[where.end():] if where else declaration_text[len(declaration.group(0)):]
        if (re.search(rf"\b{re.escape(target)}\b", body)
                or any(re.search(rf"\b{re.escape(alias)}\b", body) for alias in aliases_of_target)):
            return True
        parents = re.findall(r"\bextends\s+([A-Za-z_][A-Za-z0-9_'.]*)", header)
        return any(provides(parent, seen) for parent in parents)

    return provides(class_name, set())


def _typeclass_binder_supplies_noncommutativity(
    source: str,
    class_name: str,
    required_carriers: set[tuple[str, str, str]] | None = None,
) -> bool:
    """Reject a local class that packages the very T16 witness being audited."""
    clean = _strip_lean_comments_and_strings(source)
    match = re.search(
        rf"^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*class\s+{re.escape(class_name)}\b",
        clean,
        re.MULTILINE,
    )
    if match is None:
        return False
    following = re.search(
        r"^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*(?:class|structure|def|abbrev|theorem|lemma|instance|inductive|namespace|section|end)\b",
        clean[match.end():],
        re.MULTILINE,
    )
    body = clean[match.end():match.end() + following.start()] if following else clean[match.end():]
    if not re.search(_NONCOMMUTATIVITY_PATTERNS, body):
        return False
    carriers = _matrix_carrier_signatures(_expand_local_type_alias(clean, body))
    return not required_carriers or not carriers or bool(carriers & required_carriers)


def _balanced_lean_atom(text: str, start: int) -> tuple[str, int] | None:
    """Read a parenthesized Lean atom or an identifier/application atom."""
    while start < len(text) and text[start].isspace():
        start += 1
    if start >= len(text):
        return None
    if text[start] in "([{⦃":
        pairs = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
        stack = [pairs[text[start]]]
        i = start + 1
        while i < len(text) and stack:
            char = text[i]
            if char in pairs:
                stack.append(pairs[char])
            elif char in ")] }⦄".replace(" ", "") and char == stack[-1]:
                stack.pop()
            i += 1
        return (text[start:i], i) if not stack else None
    match = re.match(r"[\w'][\w'.']*|\d+", text[start:], re.UNICODE)
    if not match:
        return None
    end = start + match.end()
    # Lean type constructors such as Polynomial (ZMod 2) and ZMod 3 are
    # applications. Include their balanced argument atoms in the signature.
    while end < len(text):
        whitespace = end
        while whitespace < len(text) and text[whitespace].isspace():
            whitespace += 1
        if whitespace >= len(text) or text[whitespace] in ",)]}⦄;:=→×∧∨":
            break
        arg = _balanced_lean_atom(text, whitespace)
        if arg is None:
            break
        atom, next_end = arg
        if not (atom.startswith(("(", "[", "{", "⦃")) or atom.isdigit()):
            break
        end = next_end
    return text[start:end].strip(), end


def _matrix_carrier_signatures(text: str) -> set[tuple[str, str, str]]:
    signatures: set[tuple[str, str, str]] = set()
    for occurrence in re.finditer(r"\bMatrix\b", text):
        pos = occurrence.end()
        args: list[str] = []
        for _ in range(3):
            atom = _balanced_lean_atom(text, pos)
            if atom is None:
                break
            value, pos = atom
            args.append(value)
        if len(args) != 3:
            continue
        dimensions = []
        for arg in args[:2]:
            match = re.fullmatch(r"\(\s*Fin\s+(\d+)\s*\)", arg)
            if not match:
                break
            dimensions.append(match.group(1))
        if len(dimensions) != 2:
            continue
        scalar = args[2].strip()
        if scalar.startswith("(") and scalar.endswith(")"):
            scalar = scalar[1:-1].strip()
        scalar = re.sub(r"\s+", " ", scalar)
        signatures.add((dimensions[0], dimensions[1], scalar))
    return signatures


def _matrix_carrier_at(text: str, start: int = 0) -> tuple[str, str, str] | None:
    occurrence = re.search(r"\bMatrix\b", text[start:])
    if occurrence is None:
        return None
    pos = start + occurrence.end()
    args: list[str] = []
    for _ in range(3):
        atom = _balanced_lean_atom(text, pos)
        if atom is None:
            return None
        value, pos = atom
        args.append(value)
    dimensions: list[str] = []
    for arg in args[:2]:
        match = re.fullmatch(r"\(\s*Fin\s+(\d+)\s*\)", arg)
        if match is None:
            return None
        dimensions.append(match.group(1))
    scalar = args[2].strip()
    if scalar.startswith("(") and scalar.endswith(")"):
        scalar = scalar[1:-1].strip()
    return dimensions[0], dimensions[1], re.sub(r"\s+", " ", scalar)


def _matrix_carrier_signature(text: str) -> tuple[str, str, str] | None:
    signatures = _matrix_carrier_signatures(text)
    return next(iter(signatures)) if len(signatures) == 1 else None


def _known_nontrivial_scalar_type(scalar: str, source: str = "") -> bool:
    """Recognize common coefficient types with standard nontrivial instances."""
    scalar = re.sub(r"\s+", " ", _expand_local_type_alias(source, scalar) if source else scalar.strip())
    if scalar in {"ℝ", "Real", "ℂ", "Complex", "ℚ", "Rat", "Int", "ℤ", "Nat", "ℕ"}:
        return True
    zmod = re.fullmatch(r"ZMod\s+(\d+)", scalar)
    if zmod:
        return int(zmod.group(1)) > 1
    polynomial = re.fullmatch(r"Polynomial\s+\((.*)\)", scalar)
    return bool(polynomial and _known_nontrivial_scalar_type(polynomial.group(1), source))


@functools.lru_cache(maxsize=128)
def _parsed_local_type_aliases(source: str) -> dict[str, tuple[list[str], str]]:
    """Extract parameterized and unparameterized local type aliases once per source."""
    aliases: dict[str, tuple[list[str], str]] = {}
    for name, params, rhs in re.findall(
        r"^\s*(?:(?:private|protected|noncomputable)\s+)*(?:abbrev|def)\s+([\w']+)\s*((?:\((?:[^()\n]|\([^()\n]*\))*\)\s*)*)(?:\s*:\s*[^=\n]+)?\s*:=\s*([^\n]+)",
        _strip_lean_comments_and_strings(source),
        re.MULTILINE,
    ):
        param_names = re.findall(r"\(\s*([\w']+)\s*:", params)
        aliases[name] = (param_names, rhs.strip())
    return aliases


def _expand_local_type_alias(source: str, type_text: str) -> str:
    """Expand simple local type aliases, including parameterized aliases."""
    aliases = _parsed_local_type_aliases(source)
    expanded = re.sub(r"\s+", " ", type_text.strip())
    for _ in range(min(len(aliases) + 1, 8)):
        updated = expanded
        for name, (params, rhs) in aliases.items():
            if name not in updated:
                continue
            pattern = rf"\b{re.escape(name)}\b"
            match = re.search(pattern + r"((?:\s+\([^()]*\)|\s+[\w'.]+)*)", updated)
            if not match:
                continue
            args = re.findall(r"\(([^()]*)\)|([\w'.]+)", match.group(1))
            arguments = [a or b for a, b in args]
            if params and len(arguments) < len(params):
                continue
            replacement = rhs
            for parameter, argument in zip(params, arguments):
                replacement = re.sub(rf"\b{re.escape(parameter)}\b", argument, replacement)
            updated = updated[:match.start()] + replacement + updated[match.end():]
        if updated == expanded:
            break
        expanded = re.sub(r"\s+", " ", updated).strip()
    return expanded


def _operator_product_roots(text: str) -> list[tuple[str, str]]:
    """Extract operand roots for simple applications and projections around `*`."""
    roots: list[tuple[str, str]] = []
    operand = r"(?:\([^()]*\)|[A-Za-z_][A-Za-z0-9_'.]*(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)?)"
    for match in re.finditer(rf"({operand})\s*\*\s*({operand})", text):
        left = re.match(r"\(?\s*([A-Za-z_][A-Za-z0-9_']*)", match.group(1))
        right = re.match(r"\(?\s*([A-Za-z_][A-Za-z0-9_']*)", match.group(2))
        if left and right:
            roots.append((left.group(1), right.group(1)))
    return roots


def _matrix_operator_carriers(source: str) -> set[tuple[str, str, str]]:
    """Find carriers used by matrix-product declarations, excluding witness lemmas."""
    clean = _strip_lean_comments_and_strings(source)
    starts = list(re.finditer(
        r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*(?:def|theorem|lemma|instance)\b",
        clean,
        re.MULTILINE,
    ))
    result: set[tuple[str, str, str]] = set()
    for idx, match in enumerate(starts):
        end = starts[idx + 1].start() if idx + 1 < len(starts) else len(clean)
        declaration = clean[match.start():end]
        products = _operator_product_roots(declaration)
        if not products and not re.search(r"\bMatrix\.(?:mul|mul_apply|mulVec)\b", declaration):
            continue
        parsed = _top_level_result_type(declaration)
        # Definitions such as `def mul (A B : Matrix ...) := A * B` have no
        # explicit result type, so use the declaration syntax for binder lookup.
        binders = " ".join([
            parsed[0] if parsed else declaration,
            *_ambient_variable_declarations(clean, match.start()),
        ])
        variable_carriers = _witness_carrier_map(source, binders)
        products = _operator_product_roots(declaration)
        used = set()
        for left, right in products:
            left_carrier = variable_carriers.get(left.split(".", 1)[0])
            right_carrier = variable_carriers.get(right.split(".", 1)[0])
            if left_carrier is not None and left_carrier == right_carrier:
                used.add(left_carrier)
        if used:
            result.update(carrier for carrier in used if carrier[0] == carrier[1])
        elif re.search(r"\bMatrix\.(?:mul|mul_apply|mulVec)\b", declaration):
            # Fully qualified multiplication can be recognized even when the
            # operands are not named in local binders. In that ambiguous case,
            # use only matrix carriers occurring in this declaration.
            result.update(
                carrier for carrier in _matrix_carrier_signatures(declaration)
                if carrier[0] == carrier[1]
            )
    return result


def _ambient_variable_declarations(source: str, before_offset: int) -> list[str]:
    """Collect active section variable declarations preceding an offset."""
    scopes: list[list[str]] = [[]]
    for line in source[:before_offset].splitlines():
        stripped = line.strip()
        if re.match(r"^(?:section|namespace)\b", stripped):
            scopes.append([])
        elif re.match(r"^end(?:\s|$)", stripped):
            if len(scopes) > 1:
                scopes.pop()
        elif re.match(r"^variables?\b", stripped):
            scopes[-1].append(stripped)
    return [declaration for scope in scopes for declaration in scope]


def _required_matrix_carriers(source: str) -> set[tuple[str, str, str]]:
    """Return carriers used as operators; ambiguous files fail closed.

    A unique matrix carrier can be inferred when the product parser has no
    declaration-local match. If multiple carriers occur and the operator
    declaration cannot be tied to one, returning the empty set prevents a
    witness for an unrelated carrier from satisfying the gate.
    """
    return _matrix_operator_carriers(source)


def _has_typed_noncommutative_product(source: str) -> bool:
    """Check declarations for products of two locally typed operators."""
    clean = _strip_lean_comments_and_strings(source)
    starts = list(re.finditer(
        r"^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*"
        r"(?:def|theorem|lemma|instance)\b",
        clean,
        re.MULTILINE,
    ))
    operator_type = re.compile(
        r"\b(?:Module\.)?(?:End|CliffordAlgebra|QuaternionAlgebra|LinearMap)\b"
    )
    for index, declaration_start in enumerate(starts):
        end = starts[index + 1].start() if index + 1 < len(starts) else len(clean)
        declaration = clean[declaration_start.start():end]
        ambient = "\n".join(
            _ambient_variable_declarations(clean, declaration_start.start())
        )

        def typed_names(text: str) -> tuple[set[str], set[str]]:
            operator_names: set[str] = set()
            bound_names: set[str] = set()
            position = 0
            while position < len(text):
                opener = re.search(r"[([{⦃]", text[position:])
                if opener is None:
                    break
                start = position + opener.start()
                atom = _balanced_lean_atom(text, start)
                if atom is None:
                    position = start + 1
                    continue
                parsed = _top_level_result_type(atom[0][1:-1])
                if parsed is not None:
                    names = set(re.findall(
                        r"[A-Za-z_][A-Za-z0-9_']*", parsed[0]
                    ))
                    bound_names.update(names)
                    if operator_type.search(parsed[1]):
                        operator_names.update(names)
                position = atom[1]

            # Support `variable A B : Module.End ...` declarations.
            for match in re.finditer(
                r"(?m)^\s*variables?\s+((?:[A-Za-z_][A-Za-z0-9_']*\s+)*"
                r"[A-Za-z_][A-Za-z0-9_']*)\s*:\s*([^\n]+)",
                text,
            ):
                names = set(match.group(1).split())
                bound_names.update(names)
                if operator_type.search(match.group(2)):
                    operator_names.update(names)
            return operator_names, bound_names

        ambient_operators, _ = typed_names(ambient)
        local_operators, local_binders = typed_names(declaration)
        # A declaration-local binder shadows an ambient section variable even
        # if the local binder has a scalar type.
        operator_names = (ambient_operators - local_binders) | local_operators

        if any(
            left in operator_names and right in operator_names
            for left, right in _operator_product_roots(declaration)
        ):
            return True
    return False


@functools.lru_cache(maxsize=128)
def _source_def_carrier_map(source: str) -> dict[str, tuple[str, str, str]]:
    """Map file-level `def`/`abbrev` constants to their matrix carrier once per source."""
    carriers: dict[str, tuple[str, str, str]] = {}
    declaration_start = re.compile(r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*(?:def|abbrev)\s+(\w+)")
    source_lines = source.splitlines()
    for idx, line in enumerate(source_lines):
        match = declaration_start.match(line)
        if not match:
            continue
        header = [line]
        for following in source_lines[idx + 1 : idx + 5]:
            if ":=" in " ".join(header):
                break
            header.append(following)
        signature = _matrix_carrier_signature(
            _expand_local_type_alias(source, " ".join(header).split(":=", 1)[0])
        )
        if signature:
            carriers[match.group(1)] = signature
    return carriers


def _witness_carrier_map(source: str, binders: str) -> dict[str, tuple[str, str, str]]:
    """Map explicit matrix variables/constants to their syntactic carrier."""
    carriers: dict[str, tuple[str, str, str]] = {}
    binder_pattern = re.compile(r"\(([^():]+)\s*:\s*")
    for match in binder_pattern.finditer(binders):
        group_start = match.start()
        while group_start > 0 and binders[group_start] != "(":
            group_start -= 1
        group = _balanced_lean_atom(binders, group_start)
        group_text = group[0] if group else binders[match.end():]
        signature = _matrix_carrier_at(_expand_local_type_alias(source, group_text))
        if signature:
            for name in match.group(1).strip().split():
                carriers[name] = signature

    unparenthesized_variable = re.compile(
        r"^\s*variables?\s+((?:[\w'][\w'.]*\s+)*[\w'][\w'.]*)\s*:\s*(.+)$",
        re.MULTILINE,
    )
    for match in unparenthesized_variable.finditer(binders):
        signature = _matrix_carrier_at(
            _expand_local_type_alias(source, match.group(2))
        )
        if signature:
            for name in match.group(1).split():
                carriers[name] = signature

    carriers.update(_source_def_carrier_map(source))
    return carriers


def _strip_inline_type_ascriptions(expr: str) -> str:
    """Replace a parenthesized `(x : T)` atom by `x`.

    Walk balanced Lean atoms instead of using a flat type regex: matrix types
    contain nested applications such as `Matrix (Fin 2) (Fin 2) R`. Only a
    simple identifier followed by a type-ascription colon is stripped, so a
    named argument `(x := value)` remains untouched.
    """
    pieces: list[str] = []
    position = 0
    while position < len(expr):
        if expr[position] == "(":
            atom = _balanced_lean_atom(expr, position)
            if atom is not None:
                parenthesized, end = atom
                inner = parenthesized[1:-1]
                match = re.match(
                    r"\s*([A-Za-z_][A-Za-z0-9_']*)\s*:(?![=])(?=\s*\S)",
                    inner,
                )
                if match is not None:
                    pieces.append(match.group(1))
                    position = end
                    continue
        pieces.append(expr[position])
        position += 1
    return "".join(pieces)


def _witness_matches_matrix_carriers(source: str, binders: str, result: str,
                                     required_carriers: set[tuple[str, str, str]]) -> bool:
    """Require the two product operands in the witness to belong to this carrier."""
    inline_specializations = {
        k.strip(): v.strip()
        for k, v in re.findall(r"\(\s*([A-Za-z_]\w*)\s*:=\s*([^()]+)\)", result)
    }
    normalized_result = _strip_inline_type_ascriptions(
        re.sub(r"\s*\([^()]*:=\s*[^()]*\)", "", result)
    )
    carrier_map = _witness_carrier_map(source, binders)

    def compatible(actual: tuple[str, str, str] | None) -> bool:
        if actual is None:
            return False
        specialized_scalar = inline_specializations.get(actual[2], actual[2])
        for target in required_carriers:
            if actual[:2] != target[:2]:
                continue
            if actual[2] == target[2] or specialized_scalar == target[2]:
                return True
            if (
                specialized_scalar != actual[2]
                and _known_nontrivial_scalar_type(specialized_scalar, source)
                and re.fullmatch(r"[A-Za-z_]\w*", target[2])
                and re.search(rf"\[(?:CommRing|Ring|Semiring)\s+{re.escape(target[2])}\]", binders)
            ):
                return True
            # A witness polymorphic over arbitrary nontrivial rings can be
            # specialized to the concrete coefficient ring at the use site.
            scalar_parameter = actual[2]
            if (re.fullmatch(r"[A-Za-z_]\w*", scalar_parameter)
                    and re.search(rf"\[(?:CommRing|Ring|Semiring)\s+{re.escape(scalar_parameter)}\]", binders)
                    and re.search(rf"\[Nontrivial\s+{re.escape(scalar_parameter)}\]", binders)
                    and _known_nontrivial_scalar_type(target[2], source)):
                return True
        return False

    pair = re.search(
        r"\b(\w+)\s*\*\s*(\w+)\s*(?:≠|!=)\s*(\w+)\s*\*\s*(\w+)\b",
        normalized_result,
    )
    if pair:
        left_a, left_b, right_a, right_b = pair.groups()
        if (left_a, left_b) != (right_b, right_a):
            return False
        return compatible(carrier_map.get(left_a)) and compatible(carrier_map.get(left_b))

    anticomm = re.search(
        r"\b(\w+)\s*\*\s*(\w+)\s*\+\s*(\w+)\s*\*\s*(\w+)\s*=\s*0\b",
        normalized_result,
    )
    if anticomm:
        left_a, left_b, right_a, right_b = anticomm.groups()
        if (left_a, left_b) == (right_b, right_a) and left_a != left_b:
            if compatible(carrier_map.get(left_a)) and compatible(carrier_map.get(left_b)):
                return True
            # Recognize algebra-to-matrix representation homomorphisms `f (p * q) = f p * f q`
            # where `f` targets the required matrix carrier.
            for fn_name, fn_carrier in carrier_map.items():
                if compatible(fn_carrier) and re.search(
                    rf"\b{re.escape(fn_name)}\s*\(\s*\w+\s*\*\s*\w+\s*\)\s*=\s*"
                    rf"{re.escape(fn_name)}\s+\w+\s*\*\s*{re.escape(fn_name)}\s+\w+\b",
                    source,
                ):
                    return True
    return False



def _unsafe_local_declaration_names(source: str) -> set[str]:
    """Find local axiom, opaque, or hole-backed names and their local aliases."""
    source = _strip_lean_comments_and_strings(source)
    lean_name = r"(?:«[^»\n]+»|[^\W\d][\w']*)"
    declaration = re.compile(
        r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
        rf"(axiom|opaque|def|abbrev|theorem|lemma|instance)\s+({lean_name})(?![\w'])",
        re.MULTILINE,
    )
    matches = list(declaration.finditer(source))
    unsafe: set[str] = set()
    local_bodies: dict[str, str] = {}
    for index, match in enumerate(matches):
        kind, name = match.groups()
        end = matches[index + 1].start() if index + 1 < len(matches) else len(source)
        fragment = source[match.start():end]
        if kind in {"axiom", "opaque"} or re.search(r"\b(?:sorry|admit)\b", fragment):
            unsafe.add(name)
        if kind in {"def", "abbrev", "theorem", "lemma", "instance"}:
            assignment = _top_level_assignment_index(fragment)
            if assignment is not None:
                local_bodies[name] = fragment[assignment + 2:]
    changed = True
    while changed:
        changed = False
        for name, body in local_bodies.items():
            if name not in unsafe and any(
                re.search(rf"(?<![\w']){re.escape(dependency)}(?![\w'])", body)
                for dependency in unsafe
            ):
                unsafe.add(name)
                changed = True
    return unsafe


def _unsafe_qualified_declaration_names(source: str) -> set[str]:
    """Return qualified names of imported declarations tainted by axioms/holes."""
    clean = _strip_lean_comments_and_strings(source)
    lean_name = r"(?:«[^»\n]+»|[^\W\d][\w']*)"
    declarations: list[tuple[str, str, str, str]] = []
    namespaces: list[str] = []
    namespace_at_line: dict[int, str] = {}
    for line_number, line in enumerate(clean.splitlines(), start=1):
        stripped = line.strip()
        namespace = re.match(r"namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)", stripped)
        if namespace:
            namespaces.append(namespace.group(1))
        namespace_at_line[line_number] = ".".join(namespaces)
        if re.match(r"end(?:\s|$)", stripped) and namespaces:
            namespaces.pop()
    decl_start = re.compile(
        rf"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(axiom|opaque|def|abbrev|theorem|lemma|instance)\s+({lean_name})(?![\w'])",
        re.MULTILINE,
    )
    matches = list(decl_start.finditer(clean))
    for index, match in enumerate(matches):
        line_number = clean.count("\n", 0, match.start()) + 1
        end = matches[index + 1].start() if index + 1 < len(matches) else len(clean)
        fragment = clean[match.start():end]
        kind, name = match.groups()
        ns = namespace_at_line.get(line_number, "")
        qualified = f"{ns}.{name}" if ns else name
        declarations.append((kind, name, qualified, fragment))
    unsafe = {
        qualified for kind, _name, qualified, fragment in declarations
        if kind in {"axiom", "opaque"} or re.search(r"\b(?:sorry|admit)\b", fragment)
    }
    changed = True
    while changed:
        changed = False
        for _kind, _name, qualified, fragment in declarations:
            if qualified in unsafe:
                continue
            namespace = qualified.rsplit(".", 1)[0] if "." in qualified else ""
            if any(
                re.search(
                    rf"(?<![\w']){re.escape(dep.rsplit('.', 1)[-1])}(?![\w'])",
                    fragment,
                )
                and (dep.rsplit(".", 1)[0] if "." in dep else "") == namespace
                for dep in unsafe
            ):
                unsafe.add(qualified)
                changed = True
    return unsafe


def _unsafe_inhabited_instance_targets(source: str) -> set[str]:
    """Find target types whose local Inhabited instance forwards to holes/axioms."""
    clean = _strip_lean_comments_and_strings(source)
    unsafe_names = _unsafe_local_declaration_names(clean)
    starts = list(re.finditer(
        r"^\s*(?:(?:private|protected|local|scoped|noncomputable|unsafe)\s+)*instance(?:\s+[A-Za-z_][A-Za-z0-9_']*)?\b",
        clean,
        re.MULTILINE,
    ))
    targets: set[str] = set()
    for index, match in enumerate(starts):
        end = starts[index + 1].start() if index + 1 < len(starts) else len(clean)
        following = re.search(
            r"^\s*(?:(?:private|protected|local|scoped|noncomputable|unsafe|partial)\s+)*(?:def|abbrev|theorem|lemma|instance|structure|class|inductive|axiom|opaque|namespace|section|end)\b",
            clean[match.end():end],
            re.MULTILINE,
        )
        declaration = clean[match.start():match.end() + following.start()] if following else clean[match.start():end]
        parsed = _top_level_result_type(declaration)
        assignment = _top_level_assignment_index(declaration)
        if parsed is None or assignment is None:
            continue
        _binders, result = parsed
        inhabited = re.match(r"Inhabited\s+([A-Za-z_][A-Za-z0-9_'.]*)\b", result)
        if inhabited is None:
            continue
        body = declaration[assignment + 2:]
        identifiers = set(re.findall(r"(?:«[^»\n]+»|[^\W\d][\w']*)", body))
        if re.search(r"\b(?:sorry|admit)\b", body) or identifiers & unsafe_names:
            normalized_target = _expand_local_type_alias(clean, inhabited.group(1))
            targets.add(normalized_target.split(".")[-1])
    return targets


def _has_closed_noncommutativity_witness(
    source: str,
    *,
    exported_only: bool = False,
    required_carriers: set[tuple[str, str, str]] | None = None,
) -> bool:
    """Recognize a closed theorem whose result states a witness, not an assumption."""
    source = _strip_lean_comments_and_strings(source)
    unsafe_names = _unsafe_local_declaration_names(source)
    starts = list(re.finditer(
        r"^\s*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)",
        source,
        re.MULTILINE,
    ))
    for idx, match in enumerate(starts):
        end = starts[idx + 1].start() if idx + 1 < len(starts) else len(source)
        declaration = source[match.start() : end]
        if exported_only and re.match(r"\s*private\s+", declaration):
            continue
        if ":=" not in declaration or re.search(r"\b(?:sorry|admit|axiom)\b", declaration):
            continue
        parsed = _top_level_result_type(declaration)
        if parsed is None:
            continue
        binders, result = parsed
        normalized_result = _strip_inline_type_ascriptions(
            re.sub(r"\s*\([^()]*:=\s*[^()]*\)", "", result)
        )
        assignment = _top_level_assignment_index(declaration)
        proof_body = declaration[assignment + 2:] if assignment is not None else ""
        if set(re.findall(r"(?:«[^»\n]+»|[^\W\d][\w']*)", proof_body)) & unsafe_names:
            continue
        class_binders = re.findall(r"\[([^\[\]]*)\]", binders)
        class_names = [
            found.group(1)
            for binder in class_binders
            if (
                found := re.match(
                    r"\s*([A-Za-z_][A-Za-z0-9_'.]*)",
                    binder.split(":", 1)[1] if ":" in binder else binder,
                )
            )
        ]
        effective_proof_body = re.sub(
            r"\blet\s+_\s*:=\s*[^;\n]+(?=;|$)", "", proof_body
        )
        if any(
            _typeclass_binder_supplies_noncommutativity(
                source, class_name, required_carriers
            )
            and (
                re.search(rf"\b{re.escape(class_name)}\s*\.", effective_proof_body)
                or re.search(rf"\bopen\s+[^\n]*\b{re.escape(class_name)}\b", source)
            )
            for class_name in class_names
        ):
            continue
        ambient_binders = _ambient_variable_declarations(source, match.start())
        if not _witness_has_only_typeclass_binders(
            " ".join([binders, *ambient_binders]), source=source
        ):
            continue
        if re.search(_NONCOMMUTATIVITY_PATTERNS, normalized_result):
            if required_carriers is not None and not _witness_matches_matrix_carriers(
                source, " ".join([binders, *ambient_binders]), result, required_carriers
            ):
                continue
            return True
    return False


def _has_resolved_import_witness(
    source: str,
    filename: str,
    *,
    required_carriers: set[tuple[str, str, str]] | None = None,
    import_root: Path | None = None,
) -> bool:
    """Inspect direct repo-local imports for a carrier-matched witness.

    A witness relied on by an owner should be in its explicit imports. Walking
    the transitive repository graph here made a local review expand into a
    repository-wide source scan, so this check deliberately follows direct
    imports only; imported modules are independently screened in their own
    review/build lane.
    """
    if filename == "<unknown>":
        return False
    repo_root = import_root or Path(__file__).resolve().parents[2]
    source = _strip_lean_comments_and_strings(source)
    subject_carriers = required_carriers or _required_matrix_carriers(source)
    imported_modules = [
        module
        for imported_line in re.findall(
            r"^\s*import\s+([A-Za-z0-9_. ]+)\s*$", source, re.MULTILINE
        )
        for module in imported_line.split()
    ]
    for module in imported_modules:
        relative = Path(*module.split("."))
        roots = (repo_root / "lean", repo_root / "proofs")
        if module.startswith("proofs."):
            relative = Path(*module.removeprefix("proofs.").split("."))
            roots = (repo_root / "proofs",)
        candidate = next(
            (root / relative.with_suffix(".lean") for root in roots
             if (root / relative.with_suffix(".lean")).is_file()),
            None,
        )
        if candidate is None:
            continue
        try:
            imported_source = _strip_lean_comments_and_strings(
                candidate.read_text(encoding="utf-8")
            )
        except OSError:
            continue
        if any(
            _has_closed_noncommutativity_witness(
                imported_source,
                exported_only=True,
                required_carriers={carrier},
            )
            for carrier in subject_carriers
        ):
            return True
    return False


def _repo_import_source_closure(source: str, repo_root: Path) -> str:
    """Read repo-local imports transitively for lexical axiom/hole tainting."""
    pending = [
        module
        for imported_line in re.findall(
            r"^\s*import\s+([A-Za-z0-9_. ]+)\s*$",
            _strip_lean_comments_and_strings(source),
            re.MULTILINE,
        )
        for module in imported_line.split()
    ]
    seen: set[Path] = set()
    fragments: list[str] = []
    while pending:
        module = pending.pop()
        relative = Path(*module.split("."))
        roots = (repo_root / "lean", repo_root / "proofs")
        if module.startswith("proofs."):
            relative = Path(*module.removeprefix("proofs.").split("."))
            roots = (repo_root / "proofs",)
        candidate = next(
            (root / relative.with_suffix(".lean") for root in roots
             if (root / relative.with_suffix(".lean")).is_file()),
            None,
        )
        if candidate is None or candidate in seen:
            continue
        seen.add(candidate)
        try:
            imported = _strip_lean_comments_and_strings(candidate.read_text(encoding="utf-8"))
        except OSError:
            continue
        fragments.append(imported)
        pending.extend(
            module
            for imported_line in re.findall(
                r"^\s*import\s+([A-Za-z0-9_. ]+)\s*$", imported, re.MULTILINE
            )
            for module in imported_line.split()
        )
    return "\n".join(fragments)


def check_tactic_misuse_on_operators(lines: list[str]) -> list[TrapViolation]:
    """Detect Trap T16 Tactic Misuse on Operators:

    Flag direct application of scalar/commutative tactics (`ring`, `linarith`, `nlinarith`)
    directly on non-commutative operator carriers (e.g. `by ring` closing a goal whose target
    is an unprojected `Matrix` or `End` product `A * B`).
    """
    violations: list[TrapViolation] = []

    pat_have_misuse = re.compile(
        r"\bhave\s+\w+\s*:\s*(?:[^:]*?\b(?:Matrix|End|CliffordAlgebra)\b.*?|.*?(\b\w+\s*\*\s*\w+\s*=\s*\w+\s*\*\s*\w+\b).*?):=(?:\s*by)?\s*\b(ring|linarith|nlinarith)\b"
    )

    alias_source = _strip_lean_comments_and_strings("\n".join(lines))
    clean_lines = alias_source.splitlines()
    aliases = set(re.findall(
        r"\b(?:abbrev|def)\s+([A-Za-z_][A-Za-z0-9_']*)[^\n]*:=\s*[^\n]*\bMatrix\b",
        alias_source,
    ))
    all_alias_defs = re.findall(
        r"\b(?:abbrev|def)\s+([A-Za-z_][A-Za-z0-9_']*)[^\n]*:=\s*([^\n]*)",
        alias_source,
    )
    # Propagate direct aliases (`abbrev Op₂ := Op`) to a fixed point once per file.
    changed = True
    while changed:
        changed = False
        for alias, rhs in all_alias_defs:
            if alias not in aliases and any(re.search(rf"\b{re.escape(old)}\b", rhs) for old in aliases):
                aliases.add(alias)
                changed = True

    i = 0
    n = len( lines )
    while i < n:
        raw_line = lines[i]
        line_clean = raw_line.split("--")[0].strip()

        if not line_clean or line_clean.startswith("/-"):
            i += 1
            continue

        # Check inline 'have' statements
        m_have = pat_have_misuse.search(line_clean)
        if m_have:
            tactic_name = m_have.group(2) if m_have.group(2) else "ring"
            violations.append(
                TrapViolation(
                    trap_id="T16",
                    trap_name="Tactic Misuse on Operators",
                    line_number=i + 1,
                    matched_text=line_clean[:80],
                    message=f"Direct application of scalar tactic '{tactic_name}' on unprojected operator statement.",
                    severity="ERROR",
                )
            )

        declaration_start = re.match(
            r"(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:theorem|lemma|def|abbrev|example|instance)\b",
            line_clean,
        )
        if declaration_start:
            decl_start_idx = i + 1
            decl_lines = [line_clean]
            j = i + 1
            # Collect declaration header until ':='
            while j < n and _top_level_assignment_index(" ".join(decl_lines)) is None:
                next_l = lines[j].split("--")[0].strip()
                if (re.match(r"(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:theorem|lemma|def|abbrev|example|instance|structure|class)\b", next_l) or
                    next_l.startswith("end ") or next_l.startswith("namespace ")):
                    break
                if next_l:
                    decl_lines.append(next_l)
                j += 1

            full_header = " ".join(decl_lines)

            # Check if declaration involves operator carriers
            alias_used = any(re.search(rf"\b{re.escape(alias)}\b", full_header) for alias in aliases)
            prior_variables = _prior_variable_binders("\n".join(clean_lines[:i]), already_clean=True)
            prior_variable_names = {name for name, _ in prior_variables}
            ambient_operator_names = {
                name
                for name, binder_type in prior_variables
                if re.search(r"\b(?:Matrix|End|CliffordAlgebra|LinearMap)\b", binder_type)
            }
            ambient_operator_used = any(
                re.search(rf"\b{re.escape(name)}\b", full_header)
                for name in ambient_operator_names
            )
            has_operator = alias_used or ambient_operator_used or bool(
                re.search(
                    r"\b(?:Matrix\s*\(\s*Fin|\bMatrix\b|\bEnd\b|\bCliffordAlgebra\b|\bLinearMap\b)\b",
                    full_header,
                )
            )

            # Check if target conclusion is projected to a scalar
            assignment_index = _top_level_assignment_index(full_header)
            if assignment_index is None:
                header_before_assign = full_header
                after_assign = ""
            else:
                header_before_assign = full_header[:assignment_index]
                after_assign = full_header[assignment_index + 2 :].strip()

            # Extract the result type after the first top-level colon. Colons
            # inside binder types (for example `(C : Matrix ...)`) are not the
            # declaration's result type.
            result_colon = None
            depth = 0
            for colon_idx, char in enumerate(header_before_assign):
                if char in "([{⦃":
                    depth += 1
                elif char in ")]}⦄" :
                    depth = max(0, depth - 1)
                elif depth == 0 and char == ":" and not header_before_assign.startswith(":=", colon_idx):
                    result_colon = colon_idx
                    break
            conclusion = (
                header_before_assign[result_colon + 1 :].strip()
                if result_colon is not None else ""
            )

            matrix_entry_projection = bool(
                re.search(
                    r"\)\s*[A-Za-z_][A-Za-z0-9_']*\s+[A-Za-z_][A-Za-z0-9_']*\s*(?:=|≠|≤|≥|<|>)",
                    conclusion,
                )
            )
            scalar_projection_shadowed = any(
                re.search(rf"[({{⦃]\s*{name}\s*:", header_before_assign)
                or name in prior_variable_names
                for name in ("innerProduct", "dotProduct")
            )
            scalar_projection = bool(
                re.search(
                    r"\b(?:innerProduct|dotProduct)\s+(?:[\w']+|\()",
                    conclusion,
                )
                and not scalar_projection_shadowed
            )
            # Check if conclusion is projected
            is_projected = bool(
                re.search(
                    r"\b(?:Matrix\.det|Matrix\.trace|Matrix\.diag|trace|det)\b|"
                    r"\b[A-Za-z0-9_]+\s+(?:[ij]|\d+)\s+(?:[ij]|\d+)\b|"
                    r"\)\s*[A-Za-z_][A-Za-z0-9_']*\s+[A-Za-z_][A-Za-z0-9_']*\s*(?:=|≠|≤|≥|<|>)|"
                    r"^\s*(?:ℝ|Real|ℂ|Complex|ℕ|ℤ|Bool|[A-Z][A-Za-z0-9_]*)\s*$",
                    conclusion,
                )
            )
            is_projected = is_projected or scalar_projection

            # A scalar projection in one conjunct does not project a mixed
            # target whose result still contains an operator product.
            if (
                re.search(
                    r"\b[A-Za-z_][A-Za-z0-9_']*\s*\*\s*[A-Za-z_][A-Za-z0-9_']*\s*"
                    r"(?:=|≠|!=)\s*(?:[A-Za-z_][A-Za-z0-9_']*\s*\*\s*[A-Za-z_][A-Za-z0-9_']*|"
                    r"[A-Za-z_][A-Za-z0-9_']*)\b",
                    conclusion,
                )
                and not matrix_entry_projection
            ):
                is_projected = False

            is_unprojected_operator = has_operator and not is_projected

            if is_unprojected_operator:
                proof_items: list[tuple[int, str]] = []
                rest = re.sub(r"^by(?:\s+|$)", "", after_assign).strip()
                if rest:
                    proof_items.append((decl_start_idx, rest))

                proof_j = j
                while proof_j < n:
                    p_line = lines[proof_j].split("--")[0].strip()
                    if (re.match(r"(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:theorem|lemma|def|abbrev|example|instance|structure|class)\b", p_line) or
                        p_line.startswith("class ") or p_line.startswith("instance ") or
                        p_line.startswith("end ") or p_line.startswith("namespace ") or
                        p_line.startswith("section ") or p_line.startswith("open ")):
                        break
                    if p_line:
                        proof_items.append((proof_j + 1, p_line))
                    proof_j += 1

                has_ext = False
                scalar_helper_indents: list[int] = []
                for line_num, p_text in proof_items:
                    raw_item = lines[line_num - 1]
                    item_indent = len(raw_item) - len(raw_item.lstrip())
                    while scalar_helper_indents and item_indent <= scalar_helper_indents[-1]:
                        scalar_helper_indents.pop()
                    scalar_helper = re.match(
                        r"have\s+\w+\s*:\s*(.*?)\s*:=\s*by\b", p_text
                    )
                    if scalar_helper:
                        helper_type = scalar_helper.group(1)
                        direct_operator_eq = re.search(
                            r"\b\w+\s*\*\s*\w+\s*=\s*\w+\s*\*\s*\w+\b",
                            helper_type,
                        )
                        if (
                            not direct_operator_eq
                            and (
                                not re.search(r"\b(?:Matrix|End|CliffordAlgebra)\b", helper_type)
                                or re.search(
                                    r"\b(?:innerProduct|dotProduct)\s+(?:[\w']+|\()",
                                    helper_type,
                                ) and not scalar_projection_shadowed
                            )
                        ):
                            scalar_helper_indents.append(item_indent)
                    if re.search(r"\b(?:ext|Matrix\.ext|funext)\b", p_text):
                        has_ext = True
                    m_tactic = re.search(r"\b(ring|linarith|nlinarith)\b", p_text)
                    if (
                        m_tactic
                        and not has_ext
                        and not scalar_helper_indents
                    ):
                        violations.append(
                            TrapViolation(
                                trap_id="T16",
                                trap_name="Tactic Misuse on Operators",
                                line_number=line_num,
                                matched_text=p_text[:80],
                                message=f"Direct application of scalar tactic '{m_tactic.group(1)}' on unprojected operator carrier.",
                                severity="ERROR",
                            )
                        )
                i = proof_j
                continue
            i = j
        else:
            i += 1

    return violations


def check_model_witnessing(
    lines: list[str], filename: str = "<unknown>", import_root: Path | None = None
) -> list[TrapViolation]:
    """Gate 2.5: Mandatory Model Witnessing & Non-Triviality Check (Trap T17).

    Enforces that every newly declared algebraic/geometric class or structure
    possesses at least one constructive instance, model witness, or non-degeneracy
    proof in the module (e.g. instance, non_trivial, non-zero dimension).
    """
    violations: list[TrapViolation] = []
    declared_structures: list[tuple[int, str]] = []

    for idx, line in enumerate(lines, start=1):
        line_clean = line.strip()
        if line_clean.startswith("--") or line_clean.startswith("/-"):
            continue
        declaration_line = re.sub(r"^(?:@\[[^\]]*\]\s*)+", "", line_clean)
        m_struct = re.match(
            r"^(?:(?:private|protected|noncomputable|unsafe)\s+)*(?:class|structure)\s+([A-Za-z0-9_]+)",
            declaration_line,
        )
        if m_struct:
            struct_name = m_struct.group(1)
            # Skip standard meta/internal wrappers
            if not struct_name.endswith("Audit") and not struct_name.startswith("_") and struct_name not in ("TrapViolation",):
                declared_structures.append((idx, struct_name))

    if not declared_structures:
        return violations

    # Lean declarations commonly wrap their result types over several lines.
    # Inspect declaration headers (up to `:=`/`where`) instead of requiring a
    # witness type to occur on the declaration's first physical line.
    declaration_headers: list[tuple[int, str]] = []
    decl_start = re.compile(r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*(?:def|abbrev|theorem|lemma|instance)\b")
    decl_boundary = re.compile(r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*(?:def|abbrev|theorem|lemma|instance|structure|class|inductive|namespace|section|end)\b")
    i = 0
    while i < len(lines):
        line = lines[i]
        if not decl_start.match(line) or line.lstrip().startswith(("--", "/-")):
            i += 1
            continue
        declaration_line = i + 1
        header = [line]
        i += 1
        while i < len(lines):
            current = lines[i]
            if decl_boundary.match(current) or current.lstrip().startswith(("--", "/-")):
                break
            header.append(current)
            if _top_level_assignment_index(" ".join(header)) is not None or re.match(r"^\s*where\b", current):
                break
            i += 1
        declaration_headers.append((declaration_line, " ".join(header)))

    def result_type(header: str) -> str | None:
        """Extract a declaration result type while ignoring binder colons."""
        depth = 0
        result_colon: int | None = None
        i = 0
        while i < len(header):
            char = header[i]
            if char in "([{⦃":
                depth += 1
            elif char in ")]}⦄":
                depth = max(0, depth - 1)
            elif depth == 0 and char == ":" and not header.startswith(":=", i):
                result_colon = i
                break
            i += 1
        if result_colon is None:
            return None

        start = result_colon + 1
        depth = 0
        i = start
        while i < len(header):
            char = header[i]
            if char in "([{⦃":
                depth += 1
            elif char in ")]}⦄":
                depth = max(0, depth - 1)
            elif depth == 0 and header.startswith(":=", i):
                return header[start:i]
            elif depth == 0 and re.match(r"where\b", header[i:]):
                return header[start:i]
            i += 1
        return header[start:]

    def directly_inhabits_structure(declared_type: str | None, struct_name: str) -> bool:
        if declared_type is None:
            return False
        # A function or implication whose domain merely mentions the structure
        # is not an inhabitant. Accept a direct value, or the standard logical
        # wrappers that explicitly assert existence.
        result = declared_type.strip()
        wrapper = re.match(r"^(?:Nonempty|Inhabited)\s+", result)
        if wrapper:
            result = result[wrapper.end():].strip()
            if result.startswith("(") and result.endswith(")"):
                depth = 0
                outer_application = True
                for index, char in enumerate(result):
                    if char == "(":
                        depth += 1
                    elif char == ")":
                        depth -= 1
                    if depth == 0 and index < len(result) - 1:
                        outer_application = False
                        break
                if outer_application:
                    result = result[1:-1].strip()
        if not re.match(rf"^{re.escape(struct_name)}(?:\s|$|\(|\{{)", result):
            return False
        # Structure applications may have several explicit arguments, but a
        # product/implication beginning with the structure is not itself a
        # direct inhabitant. Operators nested inside an argument are harmless.
        depth = 0
        for token in re.finditer(r"→|×|∧|∨|↔|=", result):
            depth = sum(
                1 if char in "([{⟨" else -1 if char in ")]}⟩" else 0
                for char in result[:token.start()]
            )
            if depth == 0:
                return False
        return True

    source_text = "\n".join(lines)

    def ambient_variable_names(line_idx: int) -> set[str]:
        # Track section/namespace scopes with a stack: an `end Inner` must not
        # erase variables still active in the enclosing section.
        scopes: list[set[str]] = [set()]
        for prior in lines[: line_idx - 1]:
            stripped = prior.strip()
            if re.match(r"^(?:section|namespace)\b", stripped):
                scopes.append(set())
            elif re.match(r"^end(?:\s|$)", stripped):
                if len(scopes) > 1:
                    scopes.pop()
            elif re.match(r"^variables?\b", stripped):
                declaration = re.sub(r"^variables?\s+", "", stripped)
                binders = re.findall(r"[({⦃]([^(){}⦃⦄]+)[)}⦄]", declaration)
                for binder in binders:
                    name_part, separator, type_part = binder.partition(":")
                    if separator and re.fullmatch(r"\s*(?:Type|Sort)(?:\s+\w+)?\s*\*?\s*", type_part):
                        continue
                    scopes[-1].update(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", name_part))
                unparenthesized = re.match(
                    r"((?:[A-Za-z_][A-Za-z0-9_']*\s+)*[A-Za-z_][A-Za-z0-9_']*)\s*:",
                    declaration,
                )
                if unparenthesized:
                    type_text = declaration[unparenthesized.end():].strip()
                    if not re.fullmatch(r"(?:Type|Sort)(?:\s+\w+)?\s*\*?", type_text):
                        scopes[-1].update(unparenthesized.group(1).split())
        names: set[str] = set()
        for scope in scopes:
            names.update(scope)
        return names

    def declaration_has_hole(start_line: int) -> bool:
        start = start_line - 1
        base_indent = len(lines[start]) - len(lines[start].lstrip())
        for offset in range(start, len(lines)):
            current = lines[offset]
            indent = len(current) - len(current.lstrip())
            if offset > start and decl_boundary.match(current.lstrip()) and indent <= base_indent:
                break
            if re.search(r"\b(?:sorry|admit)\b", current):
                return True
        return False

    def declaration_body(start_line: int) -> str:
        start = start_line - 1
        base_indent = len(lines[start]) - len(lines[start].lstrip())
        boundary = re.compile(
            r"^(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+)*(?:def|abbrev|theorem|lemma|instance|structure|class|inductive|axiom|opaque|namespace|section|end)\b"
        )
        collected: list[str] = []
        for offset in range(start, len(lines)):
            current = lines[offset]
            indent = len(current) - len(current.lstrip())
            if offset > start and boundary.match(current.lstrip()) and indent <= base_indent:
                break
            collected.append(current)
        text = "\n".join(collected)
        assignment = _top_level_assignment_index(text)
        return text[assignment + 2:] if assignment is not None else ""

    # A syntactically closed model may still forward to a local axiom or a
    # hole-bearing helper. Propagate this taint through local declaration
    # bodies before treating any declaration as a T17 witness.
    imported_source = _repo_import_source_closure(
        source_text, import_root or Path(__file__).resolve().parents[2]
    )
    # Local and repo-resolved imported declarations share one taint closure so
    # a model that forwards through an imported axiom/sorry cannot satisfy T17.
    local_unsafe_names = _unsafe_local_declaration_names(source_text)
    imported_unsafe_names = _unsafe_local_declaration_names(imported_source)
    imported_qualified_unsafe_names = _unsafe_qualified_declaration_names(imported_source)
    local_declared_names = set(re.findall(
        r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:def|abbrev|theorem|lemma|instance|axiom|opaque)\s+([A-Za-z_][A-Za-z0-9_']*)\b",
        source_text,
        re.MULTILINE,
    ))
    # A same-spelled declaration in another namespace is not a dependency.
    imported_unsafe_names.difference_update(local_declared_names)
    unsafe_names = local_unsafe_names | imported_unsafe_names
    def references_unsafe(body: str, names: set[str] = unsafe_names) -> bool:
        identifiers = set(re.findall(r"(?:«[^»\n]+»|[^\W\d][\w']*)", body))
        if identifiers & names:
            return True
        return any(
            re.search(rf"\b{re.escape(qualified)}\b", body)
            for qualified in imported_qualified_unsafe_names
        )

    unsafe_default_targets = _unsafe_inhabited_instance_targets(
        source_text + "\n" + imported_source
    )
    local_bodies: dict[str, str] = {}
    for start_line, header in declaration_headers:
        name_match = re.match(
            r"\s*(?:(?:private|protected|noncomputable)\s+)*(?:def|abbrev|theorem|lemma|instance)\s+([A-Za-z_][A-Za-z0-9_']*)",
            header,
        )
        if name_match:
            name = name_match.group(1)
            local_bodies[name] = declaration_body(start_line)
            if declaration_has_hole(start_line):
                unsafe_names.add(name)
    changed = True
    while changed:
        changed = False
        for name, body in local_bodies.items():
            if name not in unsafe_names and references_unsafe(body):
                unsafe_names.add(name)
                changed = True

    for line_idx, struct_name in declared_structures:
        has_typed_witness = False
        for start_line, header in declaration_headers:
            parsed_binders = _top_level_result_type(header)
            conclusion = result_type(header)
            if parsed_binders is None or conclusion is None:
                continue
            binders, _ = parsed_binders
            if (
                directly_inhabits_structure(conclusion, struct_name)
                and _witness_has_only_typeclass_binders(
                    binders,
                    target_type_name=struct_name,
                    source=source_text,
                )
                and not declaration_has_hole(start_line)
                and not (
                    re.match(r"\s*(?:by\s+)?(?:exact\s+)?default\b", declaration_body(start_line))
                    and struct_name in unsafe_default_targets
                )
                and not references_unsafe(declaration_body(start_line))
                # Section variables are implicit parameters in Lean's elaborated
                # declaration type when referenced or pulled in by tactics/holes.
                # Tactics such as `assumption` and anonymous term holes can use
                # them without spelling their names in source.
                and not (
                    ambient_variable_names(start_line)
                    and re.search(
                        r"\b(?:by|assumption|trivial|solve_by_elim|aesop|tauto|inferInstance)\b|‹|\b_\b",
                        declaration_body(start_line),
                    )
                )
                and not (
                    set(re.findall(r"(?:«[^»\n]+»|[^\W\d][\w']*)", declaration_body(start_line)))
                    & ambient_variable_names(start_line)
                )
            ):
                has_typed_witness = True
                break
        structure_indent = len(lines[line_idx - 1]) - len(lines[line_idx - 1].lstrip())
        deriving_lines = []
        declaration_boundary = re.compile(
            r"^(?:private\s+|protected\s+|noncomputable\s+)*(?:def|theorem|lemma|instance|structure|class|inductive|namespace|section|end)\b"
        )
        for offset in range(line_idx, len(lines)):
            current = lines[offset]
            current_indent = len(current) - len(current.lstrip())
            if offset > line_idx and declaration_boundary.match(current.lstrip()) and current_indent <= structure_indent:
                break
            deriving_lines.append(current)
        deriving_window = "\n".join(deriving_lines)
        has_inhabited_derivation = bool(
            re.search(r"\bderiving\b[\s\S]*?\bInhabited\b", deriving_window)
        )

        if not (has_typed_witness or has_inhabited_derivation):
            violations.append(
                TrapViolation(
                    trap_id="T17",
                    trap_name="Unwitnessed Structure / Model Non-Degeneracy Risk (Gate 2.5)",
                    line_number=line_idx,
                    matched_text=f"structure/class {struct_name}",
                    message=(
                        f"Structure/class '{struct_name}' lacks a recognizable constructive inhabitant or "
                        "`Inhabited` instance in this source. This text screen does not certify semantic non-degeneracy."
                    ),
                    severity="WARNING",
                )
            )

    return violations


def screen_lean_content(
    content: str, filename: str = "<unknown>", *, import_root: Path | None = None
) -> list[TrapViolation]:
    """Run the 17-trap screener on a Lean source string."""
    content = _strip_lean_comments_and_strings(content)
    violations: list[TrapViolation] = []
    lines = content.splitlines()

    # 1. Structural checks
    violations.extend(check_authored_axioms_and_holes(content))
    violations.extend(check_hypothesis_packaging(lines))
    violations.extend(check_scalar_surrogates(lines))
    violations.extend(check_homomorphism_rejection(lines))
    violations.extend(
        check_noncommutative_witness_requirement(
            content, lines, filename, import_root=import_root
        )
    )
    violations.extend(check_tactic_misuse_on_operators(lines))
    violations.extend(check_model_witnessing(lines, filename=filename, import_root=import_root))

    # 2. Regex-based pattern scans for other traps
    for idx, line in enumerate(lines, start=1):
        stripped = line.strip()
        if stripped.startswith("--") or stripped.startswith("/-"):
            continue  # ignore comments


        for trap_id, trap_name, pattern, msg, severity in _TRAP_PATTERNS:
            if trap_id == "T6":
                continue  # handled structurally
            if pattern.search(line):
                violations.append(
                    TrapViolation(
                        trap_id=trap_id,
                        trap_name=trap_name,
                        line_number=idx,
                        matched_text=line.strip()[:80],
                        message=msg,
                        severity=severity,
                    )
                )

    violations.extend(check_unused_hypothesis_binders(content))
    return violations


def screen_lean_file(path: Path) -> list[TrapViolation]:
    """Screen an on-disk Lean file."""
    try:
        content = path.read_text(encoding="utf-8")
        return screen_lean_content(content, filename=str(path))
    except Exception as exc:
        return [
            TrapViolation(
                trap_id="IO_ERROR",
                trap_name="File Read Error",
                line_number=0,
                matched_text=str(path),
                message=f"Could not read file: {exc}",
                severity="ERROR",
            )
        ]


def serialize_quarantine_packet(
    v: TrapViolation,
    lean_file: Path,
    quarantine_dir: Path,
    repo_root: Path,
) -> Path:
    """Serializes a detected trap violation into a structured TypedObstructionPacket JSON."""
    quarantine_dir.mkdir(parents=True, exist_ok=True)
    now_dt = datetime.datetime.now(datetime.timezone.utc)
    timestamp = now_dt.isoformat()
    try:
        rel_file = str(lean_file.relative_to(repo_root))
    except Exception:
        rel_file = str(lean_file)

    seed = f"{rel_file}:{v.trap_id}:{v.line_number}:{v.matched_text}:{timestamp}"
    h = hashlib.sha256(seed.encode("utf-8")).hexdigest()[:8]
    ts_compact = now_dt.strftime("%Y%m%d_%H%M%S")
    packet_id = f"Q_{v.trap_id}_{ts_compact}_{h}"

    data = {
        "packet_id": packet_id,
        "timestamp": timestamp,
        "source_file": rel_file,
        "trap_id": v.trap_id,
        "trap_name": v.trap_name,
        "line_number": v.line_number,
        "severity": v.severity,
        "matched_text": v.matched_text,
        "description": v.message,
        "negative_constraint": f"DO NOT allow {v.trap_id} ({v.trap_name}) at {rel_file}:{v.line_number}: {v.matched_text}",
    }

    out_path = quarantine_dir / f"{packet_id}.json"
    out_path.write_text(json.dumps(data, indent=2), encoding="utf-8")
    return out_path


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="OpenGauss / TeamAntigravity Automated Trap Screener"
    )
    parser.add_argument("paths", nargs="+", help="Lean files or directories to screen.")
    parser.add_argument("--json", action="store_true", help="Emit JSON output.")
    parser.add_argument("--strict", action="store_true", help="Treat warnings as errors.")
    parser.add_argument("--quarantine", action="store_true", help="Automatically persist violations as TypedObstructionPackets to quarantine dir.")
    parser.add_argument("--quarantine-dir", default=None, help="Directory to save obstruction packets (default: artifacts/residue_quarantine).")

    args = parser.parse_args(argv)

    repo_root = Path(__file__).resolve().parent.parent.parent
    quarantine_dir = Path(args.quarantine_dir) if args.quarantine_dir else (repo_root / "artifacts" / "residue_quarantine")

    all_violations: dict[str, list[dict]] = {}
    quarantined_packets: list[str] = []
    has_errors = False

    for target in args.paths:
        p = Path(target)
        if p.is_file():
            targets = [p]
        elif p.is_dir():
            targets = sorted(p.rglob("*.lean"))
        else:
            print(f"Target not found: {target}", file=sys.stderr)
            has_errors = True
            continue

        for lean_file in targets:
            violations = screen_lean_file(lean_file)
            if violations:
                rel = str(lean_file)
                all_violations[rel] = [asdict(v) for v in violations]
                for v in violations:
                    is_err = (v.severity == "ERROR") or (args.strict and v.severity == "WARNING")
                    if is_err:
                        has_errors = True
                    if args.quarantine and is_err:
                        pkt_path = serialize_quarantine_packet(v, lean_file, quarantine_dir, repo_root)
                        quarantined_packets.append(str(pkt_path))

    if args.json:
        out_dict = {
            "violations": all_violations,
            "quarantined_packets": quarantined_packets,
        }
        print(json.dumps(out_dict, indent=2))
    else:
        if not all_violations:
            print("✓ OpenGauss Screener: All screened files passed cleanly (0 traps detected).")
        else:
            for file_path, v_list in all_violations.items():
                print(f"\n[OpenGauss Screening Report] {file_path}:")
                for v in v_list:
                    sev = v["severity"]
                    tid = v["trap_id"]
                    tname = v["trap_name"]
                    line = v["line_number"]
                    msg = v["message"]
                    print(f"  [{sev}] {tid} ({tname}) at line {line}: {msg}")
                    print(f"        Match: \"{v['matched_text']}\"")
            if quarantined_packets:
                print(f"\n[OpenGauss Quarantine] Successfully quarantined {len(quarantined_packets)} obstruction packets in {quarantine_dir}:")
                for qp in quarantined_packets:
                    print(f"  → {qp}")

    return 1 if has_errors else 0


if __name__ == "__main__":
    sys.exit(main())
