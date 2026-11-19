"""Tier 1 module presence, Tier 2 quality gates, R3 architectural checks, and repo invariants."""

from __future__ import annotations

import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

from tests.primary_sources import (
    CANONICAL_ALL_REL,
    FEATURE_SPECS,
    REPO_ROOT,
    REQUIRED_LEAN_COPYRIGHT_HEADER,
    TRIANGLE_BRIDGE_REL,
)
from tests.primary_sources.manifest_checker import CheckOutcome
from tools.infra.opengauss_screener import _strip_lean_comments_and_strings
from tools.quality.proof_proxy_staged_gate import aggregate_prop_constructors

PYTHON_EXE: str = sys.executable

# Historical baseline anchor files that predate the byte-0 2026 Apache header policy.
# Used ONLY when running --include-anchors on untouched repo anchors; new M2-M6 files
# are NEVER exempt from the byte-0 header check.
ANCHOR_HEADER_EXEMPT: frozenset[str] = frozenset(
    {
        "lean/InfoGeometry/KK/ClNNFredholmBridge.lean",
        "lean/InfoGeometry/OperatorAlgebra/SpectralTriple.lean",
        "lean/InfoGeometry/Krein/KreinSpace.lean",
    }
)

_LEAN_IDENT_SEG = r"(?:«[^»\n]+»|[^\W\d][^\s:({\[⦃=.,]*)"
_LEAN_NAME = rf"{_LEAN_IDENT_SEG}(?:\.{_LEAN_IDENT_SEG})*"
_MOD_KW_RX = re.compile(r"^(?:private|protected|noncomputable|unsafe|partial|scoped|local)\b")
_DECL_START_RX = re.compile(
    r"^[ \t]*(?P<kind>def|abbrev|theorem|lemma|structure|class|inductive|instance|opaque|axiom)"
    rf"(?:\s+(?P<name>{_LEAN_NAME})|\s*(?=[:(\[{{⦃]))"
)
_NS_RX = re.compile(rf"^[ \t]*namespace\s+({_LEAN_NAME})\s*$")
_SEC_RX = re.compile(
    rf"^[ \t]*(?:noncomputable\s+|private\s+|protected\s+)?section(?:\s+({_LEAN_NAME}))?\s*$"
)
_END_RX = re.compile(rf"^[ \t]*end(?:\s+({_LEAN_NAME}))?\s*$")
_MUTUAL_RX = re.compile(
    r"^[ \t]*(?:noncomputable\s+|private\s+|protected\s+)?mutual\s*$"
)
_VAR_RX = re.compile(r"^[ \t]*variables?(?:\s|$)")
_OPEN_RX = re.compile(r"^[ \t]*open(?:\s|$)")
_IN_CMD_START_RX = re.compile(
    r"^(?:(?:local|scoped)\s+)?(?:open(?:\s+scoped)?|set_option|attribute|universes?|variables?|include|omit|suppress_compilation)\b"
)
_TOP_CMD_RX = re.compile(
    r"^[ \t]*(?:(?:@\[[^\]]*\]|private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(?:def|abbrev|theorem|lemma|structure|class|inductive|instance|opaque|axiom|example)\b"
    r"|^[ \t]*(?:namespace\b|section\b|end\b|mutual\b|variables?\b|open\b|import\b|include\b|omit\b|set_option\b|attribute\b|universes?\b|#)"
)


@dataclass(frozen=True)
class LeanDecl:
    fqn: str
    short_name: str
    kind: str
    is_private: bool
    start_line: int
    end_line: int
    header_text: str
    block_text: str
    active_variables: tuple[str, ...] = ()
    active_opens: tuple[str, ...] = ()
    effective_header: str = ""


def strip_lean_comments_and_strings(text: str) -> str:
    return _strip_lean_comments_and_strings(text)


def _strip_lean_preserving_interpolations(source: str) -> str:
    """Blank Lean comments and string literals, but preserve `{...}` expressions inside `s!"..."`/`m!"..."`/`f!"..."`."""
    chars = list(source)
    n = len(chars)
    i = 0
    comment_depth = 0
    # Stack of interpolation states: each item is ("str", interp: bool) or ("brace", brace_depth: int)
    interp_stack: list[tuple[str, Any]] = []

    while i < n:
        if comment_depth > 0:
            if source.startswith("/-", i):
                comment_depth += 1
                chars[i] = chars[i + 1] = " "
                i += 2
                continue
            if source.startswith("-/", i):
                comment_depth -= 1
                chars[i] = chars[i + 1] = " "
                i += 2
                continue
            if chars[i] != "\n":
                chars[i] = " "
            i += 1
            continue

        if interp_stack and interp_stack[-1][0] == "str":
            is_interp = bool(interp_stack[-1][1])
            ch = chars[i]
            if ch == "\\":
                if i + 1 < n and chars[i + 1] != "\n":
                    chars[i] = chars[i + 1] = " "
                    i += 2
                    continue
                if chars[i] != "\n":
                    chars[i] = " "
                i += 1
                continue
            if ch == '"':
                chars[i] = " "
                interp_stack.pop()
                i += 1
                continue
            if is_interp and ch == "{":
                chars[i] = " "
                interp_stack.append(("brace", 1))
                i += 1
                continue
            if ch != "\n":
                chars[i] = " "
            i += 1
            continue

        # Code context (either top-level or inside `{...}` of an interpolated string)
        if source.startswith("/-", i):
            comment_depth = 1
            chars[i] = chars[i + 1] = " "
            i += 2
            continue
        if source.startswith("--", i):
            while i < n and chars[i] != "\n":
                chars[i] = " "
                i += 1
            continue
        if chars[i] == "'" and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'")):
            if i + 1 < n and chars[i + 1] == "\\":
                if i + 5 < n and chars[i + 2] == "x" and chars[i + 5] == "'":
                    for k in range(i, i + 6):
                        chars[k] = " "
                    i += 6
                    continue
                if i + 7 < n and chars[i + 2] == "u" and chars[i + 7] == "'":
                    for k in range(i, i + 8):
                        chars[k] = " "
                    i += 8
                    continue
                if i + 3 < n and chars[i + 2] != "\n" and chars[i + 3] == "'":
                    for k in range(i, i + 4):
                        chars[k] = " "
                    i += 4
                    continue
            elif i + 2 < n and chars[i + 1] not in ("\\", "'", "\n") and chars[i + 2] == "'":
                chars[i] = chars[i + 1] = chars[i + 2] = " "
                i += 3
                continue
        if (
            (source.startswith('s!"', i) or source.startswith('m!"', i) or source.startswith('f!"', i))
            and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] == "_"))
        ):
            chars[i] = chars[i + 1] = chars[i + 2] = " "
            interp_stack.append(("str", True))
            i += 3
            continue
        if chars[i] == '"':
            chars[i] = " "
            interp_stack.append(("str", False))
            i += 1
            continue
        if interp_stack and interp_stack[-1][0] == "brace":
            if chars[i] == "{":
                interp_stack[-1] = ("brace", interp_stack[-1][1] + 1)
            elif chars[i] == "}":
                new_d = interp_stack[-1][1] - 1
                if new_d == 0:
                    chars[i] = " "
                    interp_stack.pop()
                    i += 1
                    continue
                interp_stack[-1] = ("brace", new_d)
        i += 1

    return "".join(chars)


def _consume_in_prefixes(lines: list[str], idx: int) -> tuple[list[str], int, str]:
    """Consume single- or multi-line `<cmd> ... in ` prefixes tracking `()[]{}⦃⦄«»` depth."""
    num_lines = len(lines)
    if idx >= num_lines:
        return [], idx, ""
    cur_idx = idx
    cur_rem = lines[cur_idx].lstrip()
    prefixes: list[str] = []

    while _IN_CMD_START_RX.match(cur_rem):
        depth = 0
        in_french = False
        scan_idx = cur_idx
        scan_text = cur_rem
        buf_parts: list[str] = []
        found = False

        while scan_idx < num_lines:
            n = len(scan_text)
            k = 0
            found_at = -1
            while k < n:
                ch = scan_text[k]
                if in_french:
                    if ch == "»":
                        in_french = False
                    k += 1
                    continue
                if ch == "«":
                    in_french = True
                    k += 1
                    continue
                if ch in "([{⦃":
                    depth += 1
                elif ch in ")]}⦄":
                    if depth > 0:
                        depth -= 1
                elif depth == 0 and scan_text.startswith("in", k):
                    prev_ok = k == 0 or not (scan_text[k - 1].isalnum() or scan_text[k - 1] in "_'")
                    nxt = k + 2
                    next_ok = nxt >= n or not (scan_text[nxt].isalnum() or scan_text[nxt] in "_'")
                    if prev_ok and next_ok:
                        found_at = k
                        break
                k += 1

            if found_at != -1:
                head = scan_text[:found_at].strip()
                if head:
                    buf_parts.append(head)
                prefixes.append(" ".join(buf_parts).strip())
                cur_idx = scan_idx
                cur_rem = scan_text[found_at + 2 :].lstrip()
                found = True
                break

            part = scan_text.strip()
            if part:
                buf_parts.append(part)
            scan_idx += 1
            if scan_idx >= num_lines:
                break
            next_line = lines[scan_idx]
            next_stripped = next_line.strip()
            if depth == 0 and not in_french:
                if (
                    not next_stripped
                    or _TOP_CMD_RX.match(next_line)
                    or _MOD_KW_RX.match(next_stripped)
                    or next_stripped.startswith("@[")
                ):
                    break
            scan_text = next_line.lstrip()

        if not found:
            break

    if not prefixes:
        return [], idx, lines[idx].lstrip()
    return prefixes, cur_idx, cur_rem


def _split_in_prefixes(line: str) -> tuple[list[str], str]:
    """Single-line wrapper around `_consume_in_prefixes`."""
    prefixes, _, rem = _consume_in_prefixes([line], 0)
    return prefixes, rem


def _consume_mods_and_attrs(lines: list[str], idx: int, cur_line: str) -> tuple[list[str], int, str]:
    """Consume leading modifier keywords and balanced single/multi-line `@[...]` blocks."""
    mods: list[str] = []
    cur_idx = idx
    rem = cur_line.lstrip()
    num_lines = len(lines)
    while True:
        rem = rem.lstrip()
        if not rem:
            break
        m_kw = _MOD_KW_RX.match(rem)
        if m_kw and (m_kw.end() == len(rem) or rem[m_kw.end()].isspace() or rem[m_kw.end()] == "@"):
            mods.append(m_kw.group(0))
            rem = rem[m_kw.end() :].lstrip()
            continue
        if rem.startswith("@["):
            depth = 0
            pos = 1  # at '['
            scan_line = rem
            scan_idx = cur_idx
            closed = False
            while scan_idx < num_lines:
                n_s = len(scan_line)
                while pos < n_s:
                    ch = scan_line[pos]
                    if ch == "[":
                        depth += 1
                    elif ch == "]":
                        depth -= 1
                        if depth == 0:
                            mods.append("@[...]")
                            rem = scan_line[pos + 1 :].lstrip()
                            cur_idx = scan_idx
                            closed = True
                            break
                    pos += 1
                if closed:
                    break
                scan_idx += 1
                if scan_idx < num_lines:
                    scan_line = lines[scan_idx]
                    pos = 0
            if not closed:
                return mods, num_lines - 1, ""
            continue
        break
    return mods, cur_idx, rem


def _extract_balanced_header(block_text: str) -> str:
    """Extract declaration header up to top-level `:=` or `where` (ignoring `:=` inside binders)."""
    depth = 0
    in_french = False
    n = len(block_text)
    i = 0
    while i < n:
        ch = block_text[i]
        if in_french:
            if ch == "»":
                in_french = False
            i += 1
            continue
        if ch == "«":
            in_french = True
            i += 1
            continue
        if ch in "([{⦃":
            depth += 1
            i += 1
            continue
        if ch in ")]}⦄":
            if depth > 0:
                depth -= 1
            i += 1
            continue
        if depth == 0:
            if block_text.startswith(":=", i):
                return block_text[:i]
            if block_text.startswith("where", i):
                prev_ok = i == 0 or not (block_text[i - 1].isalnum() or block_text[i - 1] == "_")
                after_idx = i + 5
                next_ok = after_idx >= n or not (block_text[after_idx].isalnum() or block_text[after_idx] == "_")
                if prev_ok and next_ok:
                    return block_text[:i]
        i += 1
    return block_text


def parse_lean_declarations(source_text: str, *, already_stripped: bool = False) -> list[LeanDecl]:
    """Strip comments/strings, track namespace/section/end/variable/open stack, and extract declarations."""
    stripped = source_text if already_stripped else strip_lean_comments_and_strings(source_text)
    lines = stripped.splitlines()
    # Stack entries: [kind_tag ("file"|"ns"|"sec"), name, list_of_vars, list_of_opens]
    stack: list[tuple[str, str, list[str], list[str]]] = [("file", "", [], [])]
    raw_entries: list[tuple[int, str, str, str, bool, tuple[str, ...], tuple[str, ...], str | None]] = []
    scope_boundaries: list[int] = []
    pending_private = False
    pending_in_vars: list[str] = []
    pending_in_opens: list[str] = []
    mutual_depth = 0
    idx = 0
    num_lines = len(lines)

    while idx < num_lines:
        line = lines[idx]
        s = line.strip()
        if not s:
            idx += 1
            continue
        m_ns = _NS_RX.match(line)
        if m_ns:
            pending_private = False
            pending_in_vars.clear()
            pending_in_opens.clear()
            scope_boundaries.append(idx)
            for part in m_ns.group(1).split("."):
                stack.append(("ns", part, [], []))
            idx += 1
            continue
        m_sec = _SEC_RX.match(line)
        if m_sec:
            pending_private = False
            pending_in_vars.clear()
            pending_in_opens.clear()
            scope_boundaries.append(idx)
            stack.append(("sec", m_sec.group(1) or "", [], []))
            idx += 1
            continue
        if _MUTUAL_RX.match(line):
            pending_private = False
            pending_in_vars.clear()
            pending_in_opens.clear()
            mutual_depth += 1
            idx += 1
            continue
        m_end = _END_RX.match(line)
        if m_end:
            pending_private = False
            pending_in_vars.clear()
            pending_in_opens.clear()
            scope_boundaries.append(idx)
            target = m_end.group(1)
            if not target:
                if mutual_depth > 0:
                    mutual_depth -= 1
                elif len(stack) > 1:
                    stack.pop()
            else:
                for part in reversed(target.split(".")):
                    for k in range(len(stack) - 1, 0, -1):
                        if stack[k][1] == part:
                            del stack[k:]
                            break
            idx += 1
            continue

        prefixes, in_end_idx, after_in = _consume_in_prefixes(lines, idx)
        line_in_vars: list[str] = []
        line_in_opens: list[str] = []
        if prefixes:
            pending_private = False
            scope_boundaries.append(idx)
            for pref in prefixes:
                if re.match(r"^(?:(?:local|scoped)\s+)?variables?\b", pref):
                    line_in_vars.append(pref)
                elif re.match(r"^(?:(?:local|scoped)\s+)?open\b", pref):
                    line_in_opens.append(pref)
            if not after_in:
                pending_in_vars.extend(line_in_vars)
                pending_in_opens.extend(line_in_opens)
                idx = in_end_idx + 1
                continue
            cur_idx = in_end_idx
            cur_line = after_in
        else:
            cur_idx = idx
            cur_line = line
            if _VAR_RX.match(line):
                pending_private = False
                pending_in_vars.clear()
                pending_in_opens.clear()
                scope_boundaries.append(idx)
                var_lines = [s]
                j = idx + 1
                while j < num_lines:
                    nxt = lines[j]
                    nxt_s = nxt.strip()
                    if not nxt_s or _TOP_CMD_RX.match(nxt):
                        break
                    var_lines.append(nxt_s)
                    j += 1
                stack[-1][2].append(" ".join(var_lines))
                idx = j
                continue

            if _OPEN_RX.match(line):
                pending_private = False
                pending_in_vars.clear()
                pending_in_opens.clear()
                scope_boundaries.append(idx)
                open_lines = [s]
                bdepth = sum(1 for c in s if c in "([{⦃") - sum(1 for c in s if c in ")]}⦄")
                j = idx + 1
                while bdepth > 0 and j < num_lines:
                    nxt_s = lines[j].strip()
                    open_lines.append(nxt_s)
                    bdepth += sum(1 for c in nxt_s if c in "([{⦃") - sum(1 for c in nxt_s if c in ")]}⦄")
                    j += 1
                joined_open = " ".join(open_lines)
                if not re.search(r"\bin\b", joined_open):
                    stack[-1][3].append(joined_open)
                idx = j
                continue

        mods, end_mod_idx, rem = _consume_mods_and_attrs(lines, cur_idx, cur_line)
        if not rem and mods:
            pending_in_vars.extend(line_in_vars)
            pending_in_opens.extend(line_in_opens)
            if "private" in mods:
                pending_private = True
            idx = end_mod_idx + 1
            continue

        m_d = _DECL_START_RX.match(rem)
        if m_d:
            is_priv = ("private" in mods) or pending_private
            pending_private = False
            kind = m_d.group("kind")
            name = m_d.group("name") or f"<anon_{kind}_{end_mod_idx + 1}>"
            if name in ("where", "by", "of", "_"):
                pending_in_vars.clear()
                pending_in_opens.clear()
                idx = end_mod_idx + 1
                continue
            ns = ".".join(p for kind_tag, p, _, _ in stack if kind_tag == "ns" and p)
            if name.startswith("_root_."):
                fqn = name[len("_root_.") :]
            else:
                fqn = f"{ns}.{name}" if ns else name
            active_vars = tuple(v for _, _, vs, _ in stack for v in vs) + tuple(pending_in_vars) + tuple(line_in_vars)
            active_opens = tuple(o for _, _, _, os_ in stack for o in os_) + tuple(pending_in_opens) + tuple(line_in_opens)
            pending_in_vars.clear()
            pending_in_opens.clear()
            first_line_override = rem if (prefixes or end_mod_idx > cur_idx) else None
            raw_entries.append((end_mod_idx, fqn, name, kind, is_priv, active_vars, active_opens, first_line_override))
            idx = end_mod_idx + 1
            continue

        pending_private = False
        pending_in_vars.clear()
        pending_in_opens.clear()
        idx = end_mod_idx + 1

    boundary_set = sorted(set(scope_boundaries + [e[0] for e in raw_entries] + [num_lines]))
    decls: list[LeanDecl] = []
    b_ptr = 0
    for start_idx, fqn, short_name, kind, is_priv, active_vars, active_opens, first_line_override in raw_entries:
        while b_ptr < len(boundary_set) and boundary_set[b_ptr] <= start_idx:
            b_ptr += 1
        end_idx = boundary_set[b_ptr] if b_ptr < len(boundary_set) else num_lines
        block_lines = list(lines[start_idx:end_idx])
        if first_line_override is not None and block_lines:
            block_lines[0] = first_line_override
        block_text = "\n".join(block_lines)
        header_text = _extract_balanced_header(block_text)
        effective_header = (
            ("\n".join(active_vars) + "\n" if active_vars else "") + header_text
        )

        decls.append(
            LeanDecl(
                fqn=fqn,
                short_name=short_name,
                kind=kind,
                is_private=is_priv,
                start_line=start_idx + 1,
                end_line=end_idx,
                header_text=header_text,
                block_text=block_text,
                active_variables=active_vars,
                active_opens=active_opens,
                effective_header=effective_header,
            )
        )
    return decls


def check_feature_lean_presence(feature_id: int, repo_root: Path = REPO_ROOT) -> CheckOutcome:
    """Tier 1 check: verify feature owner .lean file exists and exports substantive defs + theorems."""
    spec = next(f for f in FEATURE_SPECS if f.feature_id == feature_id)
    candidate_rel_paths = [spec.owner_file, *spec.alt_owner_files]
    existing_paths = [rel for rel in candidate_rel_paths if (repo_root / rel).is_file()]
    if not existing_paths:
        return CheckOutcome(
            check_id=f"T1-F{feature_id:02d}",
            tier=1,
            milestone=spec.milestone,
            pillar=spec.pillar,
            status="FAIL",
            summary=f"Missing owner file {spec.owner_file}",
            details={"missing": spec.owner_file, "feature": spec.name},
        )

    per_file_errors: list[str] = []
    for rel in existing_paths:
        raw = (repo_root / rel).read_text(encoding="utf-8", errors="replace")
        stripped = strip_lean_comments_and_strings(raw)
        decls = [d for d in parse_lean_declarations(stripped, already_stripped=True) if not d.is_private]
        defs = [d for d in decls if d.kind in {"def", "structure", "class", "inductive", "abbrev"}]
        thms = [d for d in decls if d.kind in {"theorem", "lemma"}]

        errors: list[str] = []
        if not defs:
            errors.append("no public def/structure/class/inductive/abbrev found")
        if not thms:
            errors.append("no public theorem/lemma found")
        if feature_id == 23:
            decl_corpus = "\n".join(
                ln for ln in stripped.splitlines()
                if not re.match(r"^\s*(?:namespace|section|end)\b", ln)
            )
        else:
            decl_corpus = "\n".join(
                f"{d.short_name}\n{d.effective_header}\n{d.block_text}" for d in decls
            )
        for pat in spec.concept_patterns:
            if not re.search(pat, decl_corpus):
                errors.append(f"missing expected mathematical concept pattern {pat!r}")

        if not errors:
            return CheckOutcome(
                check_id=f"T1-F{feature_id:02d}",
                tier=1,
                milestone=spec.milestone,
                pillar=spec.pillar,
                status="PASS",
                summary=f"{rel}: {len(defs)} def/struct, {len(thms)} theorem/lemma; concepts present",
                details={"file": rel, "defs": len(defs), "thms": len(thms)},
            )
        per_file_errors.append(f"{rel}: " + "; ".join(errors))

    return CheckOutcome(
        check_id=f"T1-F{feature_id:02d}",
        tier=1,
        milestone=spec.milestone,
        pillar=spec.pillar,
        status="FAIL",
        summary="; ".join(per_file_errors),
        details={"errors": per_file_errors},
    )


def check_apache_header_byte0(
    rel_paths: Iterable[str],
    repo_root: Path = REPO_ROOT,
    *,
    allow_anchor_exempt: bool = False,
) -> CheckOutcome:
    """Tier 2 check: enforce exact byte-0 5-line Apache 2.0 2026 header (including LF line endings)."""
    failures: list[str] = []
    exempted: list[str] = []
    expected_bytes = REQUIRED_LEAN_COPYRIGHT_HEADER.encode("utf-8")
    paths = list(dict.fromkeys(rel_paths))
    for rel in paths:
        full = repo_root / rel
        if not full.is_file():
            failures.append(f"{rel}: missing file")
            continue
        raw_bytes = full.read_bytes()
        if not raw_bytes.startswith(expected_bytes):
            if allow_anchor_exempt and rel in ANCHOR_HEADER_EXEMPT:
                exempted.append(rel)
            else:
                failures.append(f"{rel}: missing/malformed byte-0 Apache 2026 header")
    if failures:
        return CheckOutcome(
            check_id="T2-APACHE-HEADER",
            tier=2,
            milestone="ALL",
            pillar="all",
            status="FAIL",
            summary="; ".join(failures[:5]),
            details={"failures": failures, "exempted": exempted},
        )
    return CheckOutcome(
        check_id="T2-APACHE-HEADER",
        tier=2,
        milestone="ALL",
        pillar="all",
        status="PASS",
        summary=f"Byte-0 Apache 2026 header verified on {len(paths) - len(exempted)}/{len(paths)} files",
        details={"exempted": exempted},
    )


def _is_trivial_prop_field(fty: str) -> bool:
    s = fty.strip()
    return bool(
        re.fullmatch(r"(?:(?:∀(?=\s|\(|{|\[|⦃)|forall\b)[^,]*,\s*)*True", s)
        or re.fullmatch(r"(?:(?:∀(?=\s|\(|{|\[|⦃)|forall\b)[^,]*,\s*)*(\w+)\s*=\s*\1", s)
    )


def _split_top_level_commas(text: str) -> list[str]:
    parts: list[str] = []
    depth = 0
    start = 0
    for idx, ch in enumerate(text):
        if ch in "([{⦃⟨":
            depth += 1
        elif ch in ")]}⦄⟩":
            if depth > 0:
                depth -= 1
        elif ch == "," and depth == 0:
            parts.append(text[start:idx].strip())
            start = idx + 1
    tail = text[start:].strip()
    if tail:
        parts.append(tail)
    return parts


def _is_bare_proxy_bundling(cand: LeanDecl, rhs: str, field_names: list[str], type_name: str) -> bool:
    """Return True iff `rhs` merely repackages existing hypothesis identifiers into `type_name`."""
    param_names = _extract_header_param_names(cand.header_text, cand.short_name)
    for vline in cand.active_variables:
        param_names |= _extract_header_param_names(vline, "")
    rhs_s = rhs.strip()
    if re.match(r"^where\b", rhs_s):
        assignments = re.findall(r"(?m)^\s*([A-Za-z_][A-Za-z0-9_']*)\s*:=\s*([^\n]+)", rhs_s)
        selected = [(k, v.strip()) for k, v in assignments if k in set(field_names)]
        if len(selected) >= len(set(field_names)) and all(
            re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", val)
            and val not in {"trivial", "rfl"}
            and (not param_names or val in param_names)
            for _, val in selected
        ):
            return True
        return False

    if not rhs_s.startswith(":="):
        return False
    rhs_body = rhs_s[2:].strip()
    term = re.sub(r"^by\s+(?:exact|refine)\s+", "", rhs_body).strip()
    m_anon = re.fullmatch(r"⟨([^⟩]+)⟩", term)
    if m_anon:
        parts = _split_top_level_commas(m_anon.group(1))
        return len(parts) >= len(set(field_names)) and all(
            re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", p)
            and p not in {"trivial", "rfl"}
            and (not param_names or p in param_names)
            for p in parts
        )
    m_brace = re.fullmatch(r"\{([^{}]+)\}", term)
    if m_brace:
        assigns = re.findall(r"([A-Za-z_][A-Za-z0-9_']*)\s*:=\s*([^,\n}]+)", m_brace.group(1))
        selected = [(k, v.strip()) for k, v in assigns if k in set(field_names)]
        return len(selected) >= len(set(field_names)) and all(
            re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", val)
            and val not in {"trivial", "rfl"}
            and (not param_names or val in param_names)
            for _, val in selected
        )
    m_mk = re.fullmatch(rf"(?:[\w.]+\.)?{re.escape(type_name)}\.mk((?:\s+[A-Za-z_][A-Za-z0-9_']*)+)", term)
    if m_mk:
        args = m_mk.group(1).split()
        return len(args) >= len(set(field_names)) and all(
            arg not in {"trivial", "rfl"} and (not param_names or arg in param_names)
            for arg in args
        )
    return False


def _detect_prop_structure_wrappers(stripped_code: str, decls: list[LeanDecl]) -> list[tuple[str, str]]:
    """Detect 1-field, trivial Is*, class : Prop, and tactic-brace/constructor wrappers."""
    found: list[tuple[str, str]] = []
    for d in decls:
        if d.kind not in {"structure", "class"}:
            continue
        if not re.search(r":\s*Prop\s*$", d.header_text):
            continue
        tail = d.block_text[len(d.header_text) :]
        m_where = re.match(r"^\s*where\b", tail)
        if not m_where:
            continue
        type_name = d.short_name
        body = tail[m_where.end() :]
        field_matches = list(re.finditer(r"(?m)^[ \t]+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*([^\n]+)", body))
        fields = [m.group(1) for m in field_matches]
        if not fields:
            continue
        colon_idx = d.header_text.rfind(":")
        has_params = bool(re.search(r"[({\[⦃]", d.header_text[:colon_idx]))
        is_trivial_1field = len(fields) == 1 and _is_trivial_prop_field(field_matches[0].group(2))
        is_all_trivial = all(_is_trivial_prop_field(m.group(2)) for m in field_matches)
        if is_trivial_1field or is_all_trivial:
            found.append((type_name, f"{d.kind} {type_name} (trivial Prop wrapper)"))
            continue
        is_substantive_is_pred = type_name.startswith("Is") and has_params
        for cand in decls:
            if cand.kind not in {"theorem", "lemma", "def"}:
                continue
            hdr = cand.header_text.strip()
            if not re.search(rf":\s*(?:[\w.]+\.)?{re.escape(type_name)}(?:\s+[^:=]*)?\s*$", hdr):
                continue
            rhs = cand.block_text[len(cand.header_text) :]
            has_brace_ctor = bool(
                re.search(r":=\s*(?:by\s+(?:exact|refine)\s+)?\{", rhs)
                or re.search(r"\b(?:exact|refine)\s+\{", rhs)
            )
            has_ctor = bool(
                re.search(r"\bby\s+constructor\b", rhs)
                or re.search(r"\bconstructor\b", rhs)
                or re.search(rf"\b{re.escape(type_name)}\.mk\b", rhs)
                or re.search(r"⟨[^⟩]+⟩", rhs)
                or has_brace_ctor
                or re.match(r"^\s*where\b", rhs)
            )
            if not has_ctor:
                continue
            if is_substantive_is_pred:
                if _is_bare_proxy_bundling(cand, rhs, fields, type_name):
                    found.append((type_name, f"{cand.kind} {cand.short_name}"))
            else:
                found.append((type_name, f"{cand.kind} {cand.short_name}"))
    return found


def check_forbidden_tokens_and_prop_wrappers(
    rel_paths: Iterable[str],
    repo_root: Path = REPO_ROOT,
) -> CheckOutcome:
    """Tier 2 check: comment-stripped sorry/admit/native_decide/postulate/axiom/opaque/unsafe/partial + Prop wrappers."""
    failures: list[str] = []
    forbidden_inline_rx = re.compile(r"\b(sorry|admit|native_decide|postulate)\b")
    forbidden_top_kw_rx = re.compile(r"^(?:axiom|opaque|unsafe|partial)\b")
    paths = list(dict.fromkeys(rel_paths))
    for rel in paths:
        full = repo_root / rel
        if not full.is_file():
            failures.append(f"{rel}: missing file")
            continue
        raw = full.read_text(encoding="utf-8", errors="replace")
        stripped_interp = _strip_lean_preserving_interpolations(raw)
        stripped = strip_lean_comments_and_strings(raw)
        for lineno, line in enumerate(stripped_interp.splitlines(), start=1):
            m = forbidden_inline_rx.search(line)
            if m:
                failures.append(f"{rel}:{lineno}: forbidden token {m.group(1)!r}")
        stripped_lines = stripped.splitlines()
        l_idx = 0
        while l_idx < len(stripped_lines):
            raw_line = stripped_lines[l_idx]
            if not raw_line.strip():
                l_idx += 1
                continue
            prefixes, in_end_idx, after_in = _consume_in_prefixes(stripped_lines, l_idx)
            if prefixes:
                if not after_in:
                    l_idx = in_end_idx + 1
                    continue
                cur = after_in
                cur_idx = in_end_idx
            else:
                cur = raw_line
                cur_idx = l_idx
            mods, end_mod_idx, rem = _consume_mods_and_attrs(stripped_lines, cur_idx, cur)
            bad_mods = [md for md in mods if md in {"unsafe", "partial"}]
            if bad_mods:
                failures.append(
                    f"{rel}:{end_mod_idx + 1}: forbidden declaration modifier/keyword {bad_mods[0]!r}"
                )
            elif forbidden_top_kw_rx.match(rem):
                kw = forbidden_top_kw_rx.match(rem).group(0)  # type: ignore[union-attr]
                failures.append(f"{rel}:{end_mod_idx + 1}: forbidden declaration modifier/keyword {kw!r}")
            l_idx = end_mod_idx + 1
        seen_prop = set()
        for type_name, decl_hdr in aggregate_prop_constructors(raw):
            seen_prop.add((type_name, decl_hdr))
            failures.append(f"{rel}: aggregate Prop constructor wrapper {type_name} ({decl_hdr})")
        decls = parse_lean_declarations(stripped, already_stripped=True)
        for type_name, decl_hdr in _detect_prop_structure_wrappers(stripped, decls):
            if (type_name, decl_hdr) not in seen_prop:
                failures.append(f"{rel}: Prop structure wrapper {type_name} ({decl_hdr})")

    if failures:
        return CheckOutcome(
            check_id="T2-FORBIDDEN-SCAN",
            tier=2,
            milestone="ALL",
            pillar="all",
            status="FAIL",
            summary="; ".join(failures[:5]),
            details={"failures": failures},
        )
    return CheckOutcome(
        check_id="T2-FORBIDDEN-SCAN",
        tier=2,
        milestone="ALL",
        pillar="all",
        status="PASS",
        summary=f"Zero forbidden tokens, axioms, opaques, unsafe/partial, or Prop wrappers across {len(paths)} file(s)",
        details={},
    )


def _run_tool(cmd: list[str], repo_root: Path, timeout: int = 180) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=repo_root,
        capture_output=True,
        text=True,
        timeout=timeout,
        check=False,
    )


def run_scoped_quality_tools(
    rel_paths: Iterable[str],
    repo_root: Path = REPO_ROOT,
    *,
    strict_placeholder_names: bool = True,
) -> list[CheckOutcome]:
    """Run repo quality gates scoped explicitly to target .lean files (no --quarantine)."""
    targets = [p for p in dict.fromkeys(rel_paths) if (repo_root / p).is_file()]
    if not targets:
        return []
    outcomes: list[CheckOutcome] = []

    # 1. placeholder_audit.py --strict --format json
    abs_targets = [str((repo_root / t).resolve()) for t in targets]
    pa = _run_tool(
        [
            PYTHON_EXE,
            str(REPO_ROOT / "tools/quality/placeholder_audit.py"),
            "--root",
            str(repo_root),
            "--strict",
            "--format",
            "json",
            *abs_targets,
        ],
        repo_root,
    )
    pa_data = json.loads(pa.stdout) if pa.stdout.strip().startswith("{") else {}
    pa_summary = pa_data.get("summary", {})
    hard_cnt = int(pa_summary.get("hard_count", pa_summary.get("provenance", {}).get("hard_failures", -1)))
    naming_hits = [
        f"{f.get('file')}:{f.get('line')}: "
        f"{f.get('finding') or f.get('heuristic_signal') or f.get('rule')} "
        f"({f.get('declaration_name') or f.get('symbol')})"
        for f in pa_data.get("findings", [])
        if strict_placeholder_names
        and (f.get("finding") or f.get("heuristic_signal") or f.get("rule")) == "placeholder-naming"
    ]
    pa_ok = pa.returncode == 0 and hard_cnt == 0 and not naming_hits
    outcomes.append(
        CheckOutcome(
            check_id="T2-PLACEHOLDER-AUDIT",
            tier=2,
            milestone="ALL",
            pillar="all",
            status="PASS" if pa_ok else "FAIL",
            summary=(
                f"placeholder_audit ok (hard={hard_cnt}, findings={pa_summary.get('finding_count', 0)})"
                if pa_ok
                else f"placeholder_audit failed (rc={pa.returncode}, hard={hard_cnt}, naming={naming_hits[:3]})"
            ),
            details=pa_data,
        )
    )

    # 2. axiom_audit.py --fail-on-gaps --format json
    aa = _run_tool(
        [PYTHON_EXE, str(REPO_ROOT / "tools/infra/axiom_audit.py"), "--fail-on-gaps", "--format", "json", *targets],
        repo_root,
    )
    aa_data = json.loads(aa.stdout) if aa.stdout.strip().startswith("{") else {}
    open_gaps = int(aa_data.get("total_open_gaps", -1))
    aa_ok = aa.returncode == 0 and open_gaps == 0
    outcomes.append(
        CheckOutcome(
            check_id="T2-AXIOM-AUDIT-SCAN",
            tier=2,
            milestone="ALL",
            pillar="all",
            status="PASS" if aa_ok else "FAIL",
            summary=(
                f"axiom_audit ok (clean_files={aa_data.get('clean_files', '?')}, gaps=0)"
                if aa_ok
                else f"axiom_audit failed (rc={aa.returncode}, gaps={open_gaps})"
            ),
            details=aa_data,
        )
    )

    # 3. detect_hollow_theorems.py --strict
    dh = _run_tool(
        [PYTHON_EXE, str(REPO_ROOT / "tools/quality/detect_hollow_theorems.py"), "--strict", *targets],
        repo_root,
    )
    dh_ok = dh.returncode == 0
    outcomes.append(
        CheckOutcome(
            check_id="T2-HOLLOW-THEOREMS",
            tier=2,
            milestone="ALL",
            pillar="all",
            status="PASS" if dh_ok else "FAIL",
            summary="detect_hollow_theorems --strict ok" if dh_ok else f"hollow theorems detected: {(dh.stdout or dh.stderr).strip()[:240]}",
            details={"stdout": dh.stdout, "stderr": dh.stderr},
        )
    )

    # 4. semantic_vacuity_gate.py --fail-on error
    sv = _run_tool(
        [PYTHON_EXE, str(REPO_ROOT / "tools/quality/semantic_vacuity_gate.py"), "--fail-on", "error", *targets],
        repo_root,
    )
    sv_ok = sv.returncode == 0
    outcomes.append(
        CheckOutcome(
            check_id="T2-SEMANTIC-VACUITY",
            tier=2,
            milestone="ALL",
            pillar="all",
            status="PASS" if sv_ok else "FAIL",
            summary="semantic_vacuity_gate ok" if sv_ok else f"semantic_vacuity_gate failed: {(sv.stdout or sv.stderr).strip()[:240]}",
            details={"stdout": sv.stdout, "stderr": sv.stderr},
        )
    )

    # 5. opengauss_screener.py --json (NEVER --quarantine)
    og = _run_tool(
        [PYTHON_EXE, str(REPO_ROOT / "tools/infra/opengauss_screener.py"), "--json", *targets],
        repo_root,
    )
    og_data = json.loads(og.stdout) if og.stdout.strip().startswith("{") else {}
    og_errors = [
        f"{fpath}:{item.get('line_number', item.get('line', '?'))}: {item.get('trap_id', '')} {item.get('message', '')}"
        for fpath, items in og_data.get("violations", {}).items()
        for item in items
        if str(item.get("severity", "")).upper() == "ERROR"
    ]
    og_ok = og.returncode == 0 and not og_errors
    outcomes.append(
        CheckOutcome(
            check_id="T2-OPENGAUSS-SCREENER",
            tier=2,
            milestone="ALL",
            pillar="all",
            status="PASS" if og_ok else "FAIL",
            summary=(
                f"opengauss_screener ok ({len(targets)} file(s))"
                if og_ok
                else f"opengauss_screener failed: {og_errors[:3] or og.stderr.strip()[:200]}"
            ),
            details={"errors": og_errors, "raw": og_data},
        )
    )
    return outcomes


def _decl_corpus(decls: list[LeanDecl], *, include_private: bool = False) -> str:
    return "\n".join(
        f"{d.short_name}\n{d.effective_header}\n{d.block_text}"
        for d in decls
        if include_private or not d.is_private
    )


def _strip_outer_parens(expr: str) -> str:
    s = expr.strip()
    while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
        depth = 0
        matched = True
        for idx, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and idx < len(s) - 1:
                    matched = False
                    break
        if matched and depth == 0:
            s = s[1:-1].strip()
        else:
            break
    return s


def _extract_header_param_names(header_text: str, short_name: str) -> set[str]:
    """Extract bound parameter names from declaration header binders."""
    names: set[str] = set()
    start = header_text.find(short_name)
    tail = header_text[start + len(short_name) :] if start != -1 else header_text
    depth = 0
    top_colon = len(tail)
    for idx, ch in enumerate(tail):
        if ch in "([{⦃":
            depth += 1
        elif ch in ")]}⦄":
            if depth > 0:
                depth -= 1
        elif ch == ":" and depth == 0:
            top_colon = idx
            break
    binders_part = tail[:top_colon]
    for m in re.finditer(r"[({⦃]\s*([^:(){}\[\]⦃⦄]+?)\s*:", binders_part):
        for tok in m.group(1).split():
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", tok):
                names.add(tok)
    return names


def _decl_rhs(d: LeanDecl) -> str | None:
    tail = d.block_text[len(d.header_text) :].strip()
    if not tail.startswith(":="):
        return None
    return _strip_outer_parens(tail[2:])


def _strip_parens_and_ascriptions(expr: str) -> str:
    """Iteratively strip outer parentheses and top-level `: Type` ascriptions."""
    s = _strip_outer_parens(expr)
    while True:
        depth = 0
        in_french = False
        top_colon = -1
        has_top_arrow = False
        n = len(s)
        for idx, ch in enumerate(s):
            if in_french:
                if ch == "»":
                    in_french = False
                continue
            if ch == "«":
                in_french = True
                continue
            if ch in "([{⦃":
                depth += 1
            elif ch in ")]}⦄":
                if depth > 0:
                    depth -= 1
            elif depth == 0:
                if s.startswith("=>", idx):
                    has_top_arrow = True
                elif ch == ":" and not s.startswith(":=", idx) and (idx == 0 or s[idx - 1] != ":"):
                    top_colon = idx
        if top_colon != -1 and not has_top_arrow:
            s = _strip_outer_parens(s[:top_colon])
            continue
        break
    return s


def _split_top_level_header_colon(header_text: str, short_name: str) -> tuple[str, str]:
    """Split a declaration header into (hypothesis/binder part, return-type part) at top-level `:`."""
    start = header_text.find(short_name)
    prefix = header_text[: start + len(short_name)] if start != -1 else ""
    tail = header_text[start + len(short_name) :] if start != -1 else header_text
    depth = 0
    in_french = False
    for idx, ch in enumerate(tail):
        if in_french:
            if ch == "»":
                in_french = False
            continue
        if ch == "«":
            in_french = True
            continue
        if ch in "([{⦃":
            depth += 1
        elif ch in ")]}⦄":
            if depth > 0:
                depth -= 1
        elif ch == ":" and depth == 0 and not tail.startswith(":=", idx):
            return prefix + tail[:idx], tail[idx + 1 :]
    return header_text, ""


def _parse_fun_binders_and_body(expr: str) -> tuple[list[str], str] | None:
    """If `expr` starts with `fun ... => body`, return (binder_names, body)."""
    s = _strip_parens_and_ascriptions(expr)
    if not re.match(r"^fun\b", s):
        return None
    depth = 0
    in_french = False
    arrow_idx = -1
    n = len(s)
    i = 3
    while i < n:
        ch = s[i]
        if in_french:
            if ch == "»":
                in_french = False
            i += 1
            continue
        if ch == "«":
            in_french = True
            i += 1
            continue
        if ch in "([{⦃":
            depth += 1
        elif ch in ")]}⦄":
            if depth > 0:
                depth -= 1
        elif depth == 0 and s.startswith("=>", i):
            arrow_idx = i
            break
        i += 1
    if arrow_idx == -1:
        return None
    binder_seg = s[3:arrow_idx].strip()
    body = s[arrow_idx + 2 :].strip()
    names: list[str] = []
    # Scan top-level binders in binder_seg
    j = 0
    bn = len(binder_seg)
    while j < bn:
        while j < bn and binder_seg[j].isspace():
            j += 1
        if j >= bn:
            break
        if binder_seg[j] in "({[⦃":
            open_ch = binder_seg[j]
            close_ch = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}[open_ch]
            bdepth = 0
            start_b = j + 1
            while j < bn:
                if binder_seg[j] == open_ch:
                    bdepth += 1
                elif binder_seg[j] == close_ch:
                    bdepth -= 1
                    if bdepth == 0:
                        inner = binder_seg[start_b:j]
                        j += 1
                        break
                j += 1
            else:
                inner = binder_seg[start_b:]
            head_part = inner.split(":", 1)[0]
            for tok in head_part.split():
                if tok == "_" or re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", tok):
                    names.append(tok)
        else:
            start_tok = j
            while j < bn and not binder_seg[j].isspace() and binder_seg[j] not in "({[⦃":
                j += 1
            tok = binder_seg[start_tok:j]
            if tok == "_" or re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", tok):
                names.append(tok)
    if not names:
        return None
    return names, body


def _is_identity_rhs(d: LeanDecl) -> bool:
    rhs = _decl_rhs(d)
    if rhs is None:
        return False
    rhs_clean = _strip_parens_and_ascriptions(rhs)
    if re.match(
        r"^(?:id\b|LinearMap\.id\b|ContinuousLinearMap\.id\b|LinearIsometryEquiv\.refl\b)",
        rhs_clean,
    ):
        return True
    cur = rhs_clean
    bound_names: list[str] = []
    while True:
        parsed_fun = _parse_fun_binders_and_body(cur)
        if parsed_fun is None:
            break
        bnames, body = parsed_fun
        bound_names.extend(bnames)
        cur = _strip_parens_and_ascriptions(body)
    if bound_names:
        if cur in {b for b in bound_names if b != "_"}:
            return True
        if re.match(
            r"^(?:id\b|LinearMap\.id\b|ContinuousLinearMap\.id\b|LinearIsometryEquiv\.refl\b)",
            cur,
        ):
            return True
    param_names = _extract_header_param_names(d.header_text, d.short_name)
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", rhs_clean) and rhs_clean in param_names:
        return True
    return False


def _unwrap_eta_and_casts(rhs: str) -> str:
    """Unwrap type ascriptions, outer parens, and eta-expansions `fun x => tgt x`."""
    cur = _strip_parens_and_ascriptions(rhs)
    while True:
        parsed = _parse_fun_binders_and_body(cur)
        if parsed is None:
            break
        bnames, body = parsed
        body_clean = _strip_parens_and_ascriptions(body)
        # Peel binders from right to left if body ends with `<head> <bname>`
        peeled = body_clean
        ok = True
        for bname in reversed(bnames):
            if bname == "_":
                ok = False
                break
            m_tail = re.match(rf"^(.+?)\s+{re.escape(bname)}$", peeled, re.DOTALL)
            if not m_tail:
                ok = False
                break
            head_part = _strip_parens_and_ascriptions(m_tail.group(1))
            if re.search(rf"\b{re.escape(bname)}\b", head_part):
                ok = False
                break
            peeled = head_part
        if ok:
            cur = peeled
            continue
        # Also catch `fun (K : KreinSpace H) => tgt` (unused binder)
        if not any(re.search(rf"\b{re.escape(b)}\b", body_clean) for b in bnames if b != "_"):
            cur = body_clean
            continue
        break
    return cur


def _extract_alias_head(d: LeanDecl) -> str | None:
    rhs = _decl_rhs(d)
    if rhs is None:
        return None
    unwrapped = _unwrap_eta_and_casts(rhs)
    m = re.fullmatch(
        r"(?:[A-Za-z0-9_.]+\.)?([A-Za-z_][A-Za-z0-9_']*)(?:\s+(?:[A-Za-z0-9_'.]+|\([^()]+\)|\{[^{}]+\}))*",
        unwrapped,
    )
    if not m:
        return None
    return m.group(1)


def _is_alias_of(d: LeanDecl, targets: set[str]) -> str | None:
    head = _extract_alias_head(d)
    if head and head in targets:
        return head
    return None


def _is_valid_pontryagin_extends(header_text: str) -> bool:
    """Verify PontryaginSpace `extends` clause directly lists `KreinSpace` as a parent type."""
    m_ext = re.search(r"\bextends\b([\s\S]*)$", header_text)
    if not m_ext:
        return False
    seg = m_ext.group(1)
    # Stop at top-level `:` (return universe annotation if any)
    depth = 0
    for idx, ch in enumerate(seg):
        if ch in "([{⦃":
            depth += 1
        elif ch in ")]}⦄":
            if depth > 0:
                depth -= 1
        elif ch == ":" and depth == 0:
            seg = seg[:idx]
            break
    for parent in _split_top_level_commas(seg):
        p = _strip_outer_parens(parent)
        if re.match(r"^(?:[A-Za-z0-9_.]+\.)?KreinSpace(?:\s|$|[({\[⦃])", p):
            return True
    return False


def _find_fin_arrow(
    text: str,
    *,
    header_text: str = "",
    fin_aliases: set[str] | None = None,
) -> str | None:
    """Find hardcoded coordinate `Fin <n> → <scalar>` (distinguishing `Fin k → V` and `Fin m → K × K`)."""
    patterns = [r"\bFin\s+"]
    if fin_aliases:
        patterns.append(r"\b(?:" + "|".join(re.escape(a) for a in sorted(fin_aliases)) + r")\b")
    combined_rx = re.compile("|".join(patterns))
    n = len(text)
    scalar_names = {"ℝ", "Real", "ℂ", "Complex", "ℚ", "Rat", "ℤ", "Int", "ℕ", "Nat"}

    for m in combined_rx.finditer(text):
        i = m.end()
        matched_txt = m.group(0).strip()
        if matched_txt == "Fin":
            if i >= n:
                continue
            if text[i] == "(":
                depth = 0
                while i < n:
                    if text[i] == "(":
                        depth += 1
                    elif text[i] == ")":
                        depth -= 1
                        if depth == 0:
                            i += 1
                            break
                    i += 1
            else:
                while i < n and not text[i].isspace() and not text.startswith("→", i) and not text.startswith("->", i) and text[i] not in "()[]{}⦃⦄":
                    i += 1
        while i < n and text[i].isspace():
            i += 1
        if not (text.startswith("→", i) or text.startswith("->", i)):
            continue
        arrow_len = 1 if text.startswith("→", i) else 2
        j = i + arrow_len
        while j < n and text[j].isspace():
            j += 1
        if j >= n:
            continue
        # Parse codomain expression
        if text[j] == "(":
            depth = 0
            start_c = j
            while j < n:
                if text[j] == "(":
                    depth += 1
                elif text[j] == ")":
                    depth -= 1
                    if depth == 0:
                        j += 1
                        break
                j += 1
            cod_raw = _strip_outer_parens(text[start_c:j])
        else:
            start_c = j
            depth = 0
            while j < n:
                ch = text[j]
                if ch in "([{⦃":
                    depth += 1
                elif ch in ")]}⦄":
                    if depth == 0:
                        break
                    depth -= 1
                elif depth == 0 and (ch in ",;" or text.startswith("→", j) or text.startswith("->", j)):
                    break
                j += 1
            cod_raw = text[start_c:j].strip()

        # Witt hyperbolic sum `Fin m → K × K` / `Prod K K` is coordinate-free
        if "×" in cod_raw or re.match(r"^(?:_root_\.)?Prod\b", cod_raw):
            continue
        cod_head_m = re.match(r"^([A-Za-z_ℝℂℚℤℕ][A-Za-z0-9_'.]*)", cod_raw)
        if not cod_head_m:
            continue
        cod_head = cod_head_m.group(1)
        is_coord_scalar = cod_head in scalar_names
        if not is_coord_scalar:
            scope_hdr = header_text or text
            if re.search(rf"\[(?:CommRing|CommSemiring|Ring|Field|Semiring)\s+{re.escape(cod_head)}\b", scope_hdr):
                is_coord_scalar = True
            elif re.search(rf"\bQuadratic(?:Form|Map)\s+{re.escape(cod_head)}\b", text) or re.search(
                rf"\bQuadratic(?:Form|Map)\s+{re.escape(cod_head)}\b", scope_hdr
            ):
                is_coord_scalar = True
        if is_coord_scalar:
            return text[m.start() : i + arrow_len].strip()
    return None


def check_r3_compliance(
    rel_paths: Iterable[str],
    repo_root: Path = REPO_ROOT,
    *,
    pillar_filter: str = "all",
) -> list[CheckOutcome]:
    """Tier 2 static + AST R3.1-R3.4 architectural compliance checks on present M2-M6 / anchor files."""
    targets = {p: repo_root / p for p in rel_paths if (repo_root / p).is_file()}
    outcomes: list[CheckOutcome] = []

    def _read_stripped(rel: str) -> tuple[str, list[LeanDecl]]:
        raw = targets[rel].read_text(encoding="utf-8", errors="replace")
        stripped = strip_lean_comments_and_strings(raw)
        return stripped, parse_lean_declarations(stripped, already_stripped=True)

    # R3.1: Krein / Pontryagin / Spectral Triple separation
    r31_files = [
        r for r in targets
        if r.endswith(("PontryaginSpace.lean", "KreinSpectralTriplePrimary.lean", "ClNNFredholmBridge.lean", "SpectralTriple.lean", "KreinSpace.lean"))
    ]
    if r31_files and pillar_filter in {"all", "r2_m35"}:
        r31_errors: list[str] = []
        for rel in r31_files:
            stripped, decls = _read_stripped(rel)
            pub_corpus = _decl_corpus(decls, include_private=False)
            if rel.endswith("PontryaginSpace.lean"):
                if "KreinPontryaginCPTBridge" in stripped or re.search(r"\bState\s*:=\s*ℝ\s*×\s*ℝ", stripped):
                    r31_errors.append(f"{rel}: references retired KreinPontryaginCPTBridge or State := ℝ × ℝ stub")
                pont_decls = [
                    d for d in decls
                    if not d.is_private and (d.short_name == "PontryaginSpace" or d.fqn.endswith(".PontryaginSpace"))
                ]
                pont_types = [d for d in pont_decls if d.kind in {"class", "structure"}]
                if not pont_types:
                    r31_errors.append(f"{rel}: missing non-collapsed class/structure PontryaginSpace (abbrev/stub disallowed)")
                elif not any(_is_valid_pontryagin_extends(d.header_text) for d in pont_types):
                    r31_errors.append(f"{rel}: PontryaginSpace must genuinely extend KreinSpace in its own header")
                for d in decls:
                    if d.short_name in {"J", "jCLM", "J_krein", "jKrein", "beta"} or re.search(r"\.(?:J|jCLM)$", d.fqn):
                        if _is_identity_rhs(d):
                            r31_errors.append(f"{rel}:{d.start_line} ({d.short_name}): Wick-collapse detected ({d.short_name} := id)")
            if rel.endswith("KreinSpectralTriplePrimary.lean"):
                for forbidden in (
                    r"\bgradeCLM\s*(?::=|=)\s*\(?\s*jCLM\b",
                    r"\bjCLM\s*(?::=|=)\s*\(?\s*gradeCLM\b",
                    r"\bchi\s*(?::=|=)\s*\(?\s*jCLM\b",
                    r"\bjCLM\s*(?::=|=)\s*\(?\s*chi\b",
                    r"\bJ_real\s*(?::=|=)\s*\(?\s*(?:jCLM|gradeCLM|chi)\b",
                    r"\bjCLM\b[^\n]*:=\s*\(?\s*(?:ContinuousLinearMap\.id|LinearMap\.id|id\b)",
                    r"\bJ_real\b[^\n]*:=\s*\(?\s*(?:ContinuousLinearMap\.id|LinearMap\.id|id\b)",
                ):
                    if re.search(forbidden, stripped):
                        r31_errors.append(f"{rel}: R3.1 collapse pattern {forbidden!r}")
                # Build transitive alias closure + identity set across declarations
                id_decl_names: set[str] = {d.short_name for d in decls if _is_identity_rhs(d)}
                alias_edges: dict[str, set[str]] = {}
                for d in decls:
                    head = _extract_alias_head(d)
                    if head and head != d.short_name:
                        alias_edges.setdefault(d.short_name, set()).add(head)

                def _reachable_targets(start: str) -> set[str]:
                    seen: set[str] = set()
                    stack = list(alias_edges.get(start, ()))
                    while stack:
                        cur_n = stack.pop()
                        if cur_n in seen:
                            continue
                        seen.add(cur_n)
                        stack.extend(alias_edges.get(cur_n, ()))
                    return seen

                for d in decls:
                    if d.short_name in {"jCLM", "gradeCLM", "chi", "J_real"}:
                        if d.short_name in id_decl_names:
                            r31_errors.append(f"{rel}:{d.start_line}: {d.short_name} collapsed to identity")
                        reach = _reachable_targets(d.short_name)
                        id_hit = sorted(reach & id_decl_names)
                        if id_hit:
                            r31_errors.append(f"{rel}:{d.start_line}: {d.short_name} transitively collapsed to identity via {id_hit[0]}")
                        if d.short_name in {"gradeCLM", "chi"} and "jCLM" in reach:
                            r31_errors.append(f"{rel}:{d.start_line}: {d.short_name} collapsed to jCLM")
                        if d.short_name == "jCLM":
                            hit = sorted(reach & {"gradeCLM", "chi"})
                            if hit:
                                r31_errors.append(f"{rel}:{d.start_line}: jCLM collapsed to {hit[0]}")
                        if d.short_name == "J_real":
                            hit = sorted(reach & {"jCLM", "gradeCLM", "chi"})
                            if hit:
                                r31_errors.append(f"{rel}:{d.start_line}: J_real collapsed to {hit[0]}")
                has_krein = bool(re.search(r"\b(?:jCLM|KreinSpace|kreinInner)\b", pub_corpus))
                has_grade = bool(re.search(r"\b(?:gradeCLM|ChiralGrading|chi)\b", pub_corpus))
                has_real = bool(re.search(r"\b(?:J_real|RealStructure|PhaseRealStructure)\b", pub_corpus))
                if not (has_krein and has_grade and has_real):
                    r31_errors.append(f"{rel}: must keep Krein jCLM, grading gradeCLM/chi, and J_real distinct in declarations")
                if "RealStructureMetricCompatible" in stripped and "RealStructureKreinCompatible" not in stripped:
                    r31_errors.append(f"{rel}: Hilbert-only RealStructureMetricCompatible without RealStructureKreinCompatible")
        outcomes.append(
            CheckOutcome(
                check_id="T2-R3.1-KREIN-SEPARATION",
                tier=2,
                milestone="M5",
                pillar="r2_m35",
                status="FAIL" if r31_errors else "PASS",
                summary="; ".join(r31_errors) if r31_errors else f"R3.1 Krein/grade/real separation verified on {len(r31_files)} file(s)",
                details={"files": r31_files, "errors": r31_errors},
            )
        )

    # R3.2: Metric-free SL(V)-covariant Grassmann & basis-free O(Q)/Witt
    r32_files = [
        r for r in targets
        if r.endswith(("GrassmannPrimarySources.lean", "LipschitzWittRieszPrimary.lean", "CoordinateLessCliffordInvariance.lean"))
    ]
    if r32_files and pillar_filter in {"all", "r2_f25", "r3"}:
        r32_errors: list[str] = []
        for rel in r32_files:
            stripped, decls = _read_stripped(rel)
            pub_corpus = _decl_corpus(decls, include_private=False)
            if rel.endswith("GrassmannPrimarySources.lean"):
                def _is_explicit_hodge_comparison_thm(d: LeanDecl) -> bool:
                    if d.kind not in {"theorem", "lemma"}:
                        return False
                    if re.search(r"\b(?:MetricSpace|NormedSpace|NormedAddCommGroup)\b", d.effective_header):
                        return False
                    param_names = _extract_header_param_names(d.header_text, d.short_name)
                    _, ret_part = _split_top_level_header_colon(d.header_text, d.short_name)
                    rhs_part = d.block_text[len(d.header_text) :]
                    non_param_text = f"{d.short_name}\n{ret_part}\n{rhs_part}"
                    has_hodge_name = bool(re.search(r"hodge", d.short_name, re.IGNORECASE))
                    has_hodge_const = bool(
                        re.search(r"ExteriorRegressive\.hodge|\bhodgeStar\b|\bhodgeDual\b", non_param_text, re.IGNORECASE)
                        or (
                            re.search(r"\bhodge\b", non_param_text, re.IGNORECASE)
                            and "hodge" not in param_names
                        )
                    )
                    has_regressive_ref = bool(
                        re.search(r"(?:ExteriorRegressive|grassmannRegressive|regressive)", d.short_name, re.IGNORECASE)
                        or (
                            re.search(r"(?:ExteriorRegressive|grassmannRegressive|\bregressive\b)", non_param_text, re.IGNORECASE)
                            and "regressive" not in param_names
                        )
                    )
                    return has_regressive_ref and (has_hodge_name or has_hodge_const)

                basis_metric_rx = re.compile(
                    r"\b(?:InnerProductSpace|NormedAddCommGroup|NormedSpace|MetricSpace|Module\.Basis)\b"
                    r"|[\[\({⦃]\s*(?:[^:(){}\[\]⦃⦄\n]+:\s*)?(?:Module\.)?Basis\b"
                )
                basis_metric_aliases: set[str] = set()
                for d in decls:
                    if d.kind in {"abbrev", "def"}:
                        rhs_part = d.block_text[len(d.header_text) :]
                        if re.search(
                            r"\b(?:InnerProductSpace|NormedAddCommGroup|NormedSpace|MetricSpace|Module\.Basis|Basis)\b",
                            rhs_part,
                        ):
                            basis_metric_aliases.add(d.short_name)
                changed_bm = True
                while changed_bm:
                    changed_bm = False
                    if basis_metric_aliases:
                        bm_rx = re.compile(r"\b(?:" + "|".join(re.escape(a) for a in sorted(basis_metric_aliases)) + r")\b")
                        for d in decls:
                            rhs_part = d.block_text[len(d.header_text) :]
                            if d.kind in {"abbrev", "def"} and d.short_name not in basis_metric_aliases and bm_rx.search(rhs_part):
                                basis_metric_aliases.add(d.short_name)
                                changed_bm = True

                intrinsic_public = [
                    d for d in decls
                    if not d.is_private
                    and d.kind in {"def", "abbrev", "theorem", "lemma"}
                    and not _is_explicit_hodge_comparison_thm(d)
                ]
                if not intrinsic_public:
                    r32_errors.append(f"{rel}: no intrinsic metric-free definitions/theorems found")
                for d in decls:
                    if d.kind not in {"def", "abbrev", "theorem", "lemma", "structure", "class", "instance"}:
                        continue
                    if _is_explicit_hodge_comparison_thm(d):
                        continue
                    m_met = basis_metric_rx.search(d.effective_header)
                    if m_met:
                        r32_errors.append(
                            f"{rel}:{d.start_line} ({d.short_name}): forbidden metric/basis hypothesis {m_met.group(0)!r} in intrinsic signature/variable"
                        )
                        continue
                    other_bm = sorted(basis_metric_aliases - {d.short_name})
                    if other_bm:
                        m_bm = re.search(r"\b(?:" + "|".join(re.escape(a) for a in other_bm) + r")\b", d.effective_header)
                        if m_bm:
                            r32_errors.append(
                                f"{rel}:{d.start_line} ({d.short_name}): forbidden metric/basis alias {m_bm.group(0)!r} in intrinsic signature/variable"
                            )
                            continue
                    if d.kind in {"abbrev", "def", "structure", "class"}:
                        m_body_met = re.search(
                            r"\b(?:InnerProductSpace|NormedAddCommGroup|NormedSpace|MetricSpace|Module\.Basis)\b"
                            r"|[\[\({⦃]\s*(?:[^:(){}\[\]⦃⦄\n]+:\s*)?(?:Module\.)?Basis\b",
                            d.block_text,
                        )
                        if m_body_met:
                            r32_errors.append(
                                f"{rel}:{d.start_line} ({d.short_name}): forbidden metric/basis token {m_body_met.group(0)!r} in intrinsic definition"
                            )
                            continue
                    m_hodge = re.search(r"\b(?:ExteriorRegressive\.hodge|hodge)\b|\.hodge\b", d.block_text)
                    if m_hodge:
                        r32_errors.append(
                            f"{rel}:{d.start_line} ({d.short_name}): forbidden Hodge token {m_hodge.group(0)!r} in intrinsic declaration"
                        )
                if not re.search(r"\b(?:SL|SpecialLinear|LinearMap\.det)\b", pub_corpus):
                    r32_errors.append(f"{rel}: missing SL(V) / det = 1 covariance in public declarations")
            if rel.endswith("LipschitzWittRieszPrimary.lean"):
                fin_aliases: set[str] = set()
                for d in decls:
                    if d.kind in {"abbrev", "def"}:
                        rhs_part = _decl_rhs(d) or ""
                        if re.fullmatch(r"Fin\s+(?:\([^)]+\)|[^\s()→]+)", rhs_part):
                            fin_aliases.add(d.short_name)
                changed_fin = True
                while changed_fin:
                    changed_fin = False
                    if fin_aliases:
                        fa_rx = re.compile(r"\b(?:" + "|".join(re.escape(a) for a in sorted(fin_aliases)) + r")\b")
                        for d in decls:
                            rhs_part = _decl_rhs(d) or ""
                            if d.kind in {"abbrev", "def"} and d.short_name not in fin_aliases and fa_rx.fullmatch(rhs_part):
                                fin_aliases.add(d.short_name)
                                changed_fin = True

                coord_aliases: set[str] = set()
                for d in decls:
                    if d.kind in {"abbrev", "def", "structure", "class", "inductive"}:
                        body_part = d.block_text[len(d.header_text) :]
                        if re.search(r"\bEuclideanSpace\b|\bMatrix\b", body_part) or _find_fin_arrow(
                            body_part, header_text=d.effective_header, fin_aliases=fin_aliases
                        ):
                            coord_aliases.add(d.short_name)
                changed = True
                while changed:
                    changed = False
                    if coord_aliases:
                        alias_rx = re.compile(r"\b(?:" + "|".join(re.escape(a) for a in sorted(coord_aliases)) + r")\b")
                        for d in decls:
                            body_part = d.block_text[len(d.header_text) :]
                            if (
                                d.kind in {"abbrev", "def", "structure", "class", "inductive"}
                                and d.short_name not in coord_aliases
                                and alias_rx.search(body_part)
                            ):
                                coord_aliases.add(d.short_name)
                                changed = True
                core_univ = [
                    d for d in decls
                    if not d.is_private
                    and d.kind in {"def", "abbrev", "structure", "class", "theorem", "lemma"}
                    and re.search(r"(?:lipschitz|witt|riesz|isometry|cancel|grade)", d.short_name, re.IGNORECASE)
                ]
                if not core_univ:
                    r32_errors.append(f"{rel}: no core universal Lipschitz/Witt/Riesz declarations found")
                for d in decls:
                    if d.is_private or d.kind not in {"def", "abbrev", "structure", "class", "theorem", "lemma"}:
                        continue
                    scan_target = d.block_text if d.kind in {"abbrev", "def", "structure", "class"} else d.effective_header
                    m_coord = re.search(r"\bEuclideanSpace\b|\bMatrix\b", scan_target)
                    fin_hit = _find_fin_arrow(
                        scan_target, header_text=d.effective_header, fin_aliases=fin_aliases
                    )
                    other_aliases = sorted(coord_aliases - {d.short_name})
                    m_al = (
                        re.search(r"\b(?:" + "|".join(re.escape(a) for a in other_aliases) + r")\b", scan_target)
                        if other_aliases
                        else None
                    )
                    if m_coord:
                        r32_errors.append(
                            f"{rel}:{d.start_line} ({d.short_name}): hardcoded coordinate type {m_coord.group(0)!r} in universal signature/variable"
                        )
                    elif fin_hit:
                        r32_errors.append(
                            f"{rel}:{d.start_line} ({d.short_name}): hardcoded coordinate type {fin_hit!r} in universal signature/variable"
                        )
                    elif m_al:
                        r32_errors.append(
                            f"{rel}:{d.start_line} ({d.short_name}): coordinate type alias {m_al.group(0)!r} in universal signature/variable"
                        )
                if not re.search(r"\bQuadraticForm\b", pub_corpus):
                    r32_errors.append(f"{rel}: missing polymorphic QuadraticForm in public declarations")
        outcomes.append(
            CheckOutcome(
                check_id="T2-R3.2-METRIC-BASIS-FREE",
                tier=2,
                milestone="M2/M3",
                pillar=pillar_filter if pillar_filter in {"r2_f25", "r3"} else "r2_f25",
                status="FAIL" if r32_errors else "PASS",
                summary="; ".join(r32_errors) if r32_errors else f"R3.2 metric-free SL & basis-free O(Q)/Witt verified on {len(r32_files)} file(s)",
                details={"files": r32_files, "errors": r32_errors},
            )
        )

    # R3.3: Koszul Z/2-graded Clifford towers & Jordan-Wigner parity soldering
    r33_files = [
        r for r in targets
        if r.endswith(("KahlerHestenesJWABSPrimary.lean", "Cl11GradedTensorMorita.lean"))
    ]
    if r33_files and pillar_filter in {"all", "r3"}:
        r33_errors: list[str] = []

        def _is_scalar_base_change_only(effective_header: str) -> bool:
            """Allow explicit scalar-extension `ℂ ⊗[ℝ] CliffordAlgebra Q` / `K' ⊗[K] CliffordAlgebra Q` only."""
            # Identify scalar variables in header
            scalar_vars = set(
                re.findall(r"\[(?:Field|CommRing|CommSemiring)\s+([A-Za-z_][A-Za-z0-9_']*)\b", effective_header)
            ) | {"ℂ", "Complex", "ℝ", "Real"}

            def _is_scalar_side(side: str) -> bool:
                s = _strip_outer_parens(side)
                return s in scalar_vars

            def _is_clifford_side(side: str) -> bool:
                s = _strip_outer_parens(side)
                return "CliffordAlgebra" in s and "⊗[" not in s and "TensorProduct" not in s

            matches_found = 0
            # Check `lhs ⊗[R] rhs` occurrences
            for m in re.finditer(r"⊗\[[^\]]*\]", effective_header):
                matches_found += 1
                # Scan left from m.start()
                l_idx = m.start() - 1
                while l_idx >= 0 and effective_header[l_idx].isspace():
                    l_idx -= 1
                if l_idx >= 0 and effective_header[l_idx] == ")":
                    depth = 0
                    end_l = l_idx + 1
                    while l_idx >= 0:
                        if effective_header[l_idx] == ")":
                            depth += 1
                        elif effective_header[l_idx] == "(":
                            depth -= 1
                            if depth == 0:
                                break
                        l_idx -= 1
                    lhs = effective_header[max(l_idx, 0) : end_l].strip()
                else:
                    end_l = l_idx + 1
                    while l_idx >= 0 and (effective_header[l_idx].isalnum() or effective_header[l_idx] in "_.'ℂℝ"):
                        l_idx -= 1
                    lhs = effective_header[l_idx + 1 : end_l].strip()
                # Scan right from m.end()
                r_idx = m.end()
                n_h = len(effective_header)
                while r_idx < n_h and effective_header[r_idx].isspace():
                    r_idx += 1
                if r_idx < n_h and effective_header[r_idx] == "(":
                    depth = 0
                    start_r = r_idx
                    while r_idx < n_h:
                        if effective_header[r_idx] == "(":
                            depth += 1
                        elif effective_header[r_idx] == ")":
                            depth -= 1
                            if depth == 0:
                                r_idx += 1
                                break
                        r_idx += 1
                    rhs = effective_header[start_r:r_idx].strip()
                else:
                    start_r = r_idx
                    depth = 0
                    while r_idx < n_h:
                        ch = effective_header[r_idx]
                        if ch in "([{⦃":
                            depth += 1
                        elif ch in ")]}⦄":
                            if depth == 0:
                                break
                            depth -= 1
                        elif depth == 0 and (ch in ",:" or effective_header.startswith("→", r_idx) or effective_header.startswith("≃", r_idx)):
                            break
                        r_idx += 1
                    rhs = effective_header[start_r:r_idx].strip()
                if not ((_is_scalar_side(lhs) and _is_clifford_side(rhs)) or (_is_scalar_side(rhs) and _is_clifford_side(lhs))):
                    return False

            if "TensorProduct" in effective_header and matches_found == 0:
                return False
            return matches_found > 0

        for rel in r33_files:
            stripped, decls = _read_stripped(rel)
            has_koszul = False
            for d in decls:
                if d.is_private:
                    continue
                _, ret_p = _split_top_level_header_colon(d.header_text, d.short_name)
                rhs_p = d.block_text[len(d.header_text) :]
                rhs_no_lets = re.sub(r"(?m)^[ \t]*(?:let|have)\s+[^\n]*$", "", rhs_p)
                koszul_corpus = f"{d.short_name}\n{ret_p}\n{rhs_no_lets}"
                if re.search(
                    r"GradedTensorProduct|CliffordAlgebra\.evenOdd|\bevenOdd\b|ᵍ⊗|\(-1\s*:\s*ℤˣ\)|\bsupercommute\b",
                    koszul_corpus,
                ):
                    has_koszul = True
                    break
                if re.search(r"\b(?:parityString|jwParity|koszulSign)\w*", d.short_name):
                    has_koszul = True
                    break
                if re.search(r"\b(?:parityString|jwParity|koszulSign)\w*", f"{ret_p}\n{rhs_no_lets}"):
                    pnames = _extract_header_param_names(d.header_text, d.short_name)
                    m_ps = re.search(r"\b(?:parityString|jwParity|koszulSign)\w*", f"{ret_p}\n{rhs_no_lets}")
                    if m_ps and m_ps.group(0) not in pnames:
                        has_koszul = True
                        break
            if not has_koszul:
                r33_errors.append(f"{rel}: missing Koszul ℤ/2-graded tensor / evenOdd / parity-sign structure in public declarations")

            ungraded_tp_aliases: set[str] = set()
            alghom_aliases: set[str] = set()
            if rel.endswith("KahlerHestenesJWABSPrimary.lean"):
                for d in decls:
                    if d.kind in {"abbrev", "def"}:
                        rhs_part = d.block_text[len(d.header_text) :]
                        has_tp = bool(re.search(r"\bTensorProduct\b|⊗\[", rhs_part))
                        has_gr = bool(re.search(r"GradedTensorProduct|CliffordAlgebra\.evenOdd|\bevenOdd\b|ᵍ⊗", rhs_part))
                        if has_tp and not has_gr:
                            ungraded_tp_aliases.add(d.short_name)
                        if re.search(r"\bAlgHom\b|→ₐ\[|\bAlgEquiv\b|≃ₐ\[", rhs_part):
                            alghom_aliases.add(d.short_name)
                changed = True
                while changed:
                    changed = False
                    if ungraded_tp_aliases:
                        tp_al_rx = re.compile(r"\b(?:" + "|".join(re.escape(a) for a in sorted(ungraded_tp_aliases)) + r")\b")
                        for d in decls:
                            rhs_part = d.block_text[len(d.header_text) :]
                            if d.kind in {"abbrev", "def"} and d.short_name not in ungraded_tp_aliases and tp_al_rx.search(rhs_part):
                                has_gr = bool(re.search(r"GradedTensorProduct|CliffordAlgebra\.evenOdd|\bevenOdd\b|ᵍ⊗", rhs_part))
                                if not has_gr:
                                    ungraded_tp_aliases.add(d.short_name)
                                    changed = True
                    if alghom_aliases:
                        ah_al_rx = re.compile(r"\b(?:" + "|".join(re.escape(a) for a in sorted(alghom_aliases)) + r")\b")
                        for d in decls:
                            rhs_part = d.block_text[len(d.header_text) :]
                            if d.kind in {"abbrev", "def"} and d.short_name not in alghom_aliases and ah_al_rx.search(rhs_part):
                                alghom_aliases.add(d.short_name)
                                changed = True
            for d in decls:
                if rel.endswith("KahlerHestenesJWABSPrimary.lean"):
                    if d.kind not in {"def", "abbrev", "theorem", "lemma", "structure", "instance"}:
                        continue
                    other_tp_aliases = sorted(ungraded_tp_aliases - {d.short_name})
                    tp_alias_rx = (
                        re.compile(r"\b(?:" + "|".join(re.escape(a) for a in other_tp_aliases) + r")\b")
                        if other_tp_aliases
                        else None
                    )
                    other_ah_aliases = sorted(alghom_aliases - {d.short_name})
                    ah_alias_rx = (
                        re.compile(r"\b(?:" + "|".join(re.escape(a) for a in other_ah_aliases) + r")\b")
                        if other_ah_aliases
                        else None
                    )
                    rhs_no_dead = re.sub(r"(?m)^[ \t]*(?:let|have)\s+[^\n]*$", "", d.block_text[len(d.header_text) :])
                    decl_no_dead = f"{d.effective_header}\n{rhs_no_dead}"

                    sig_has_ungraded_tp = bool(
                        re.search(r"\bTensorProduct\b|⊗\[", d.effective_header)
                        or (tp_alias_rx and tp_alias_rx.search(d.effective_header))
                    )
                    any_has_ungraded_tp = bool(
                        sig_has_ungraded_tp
                        or re.search(r"\bTensorProduct\b|⊗\[", rhs_no_dead)
                        or (tp_alias_rx and tp_alias_rx.search(rhs_no_dead))
                    )
                    has_alghom = bool(
                        re.search(r"\bAlgHom\b|→ₐ\[|\bAlgEquiv\b|≃ₐ\[", decl_no_dead)
                        or (ah_alias_rx and ah_alias_rx.search(decl_no_dead))
                    )
                    if sig_has_ungraded_tp:
                        # Signature-level ungraded TensorProduct cannot be rescued by proof-body `have`/`let`
                        has_graded_or_jw = bool(
                            re.search(
                                r"GradedTensorProduct|CliffordAlgebra\.evenOdd|\bevenOdd\b|ᵍ⊗|\bparityString\w*|\bjwParity\w*|\bcarSoldering\w*",
                                d.effective_header,
                            )
                        )
                        is_scalar_bc = (
                            not (tp_alias_rx and tp_alias_rx.search(d.effective_header))
                            and _is_scalar_base_change_only(d.effective_header)
                        )
                    else:
                        has_graded_or_jw = bool(
                            re.search(
                                r"GradedTensorProduct|CliffordAlgebra\.evenOdd|\bevenOdd\b|ᵍ⊗|\bparityString\w*|\bjwParity\w*|\bcarSoldering\w*",
                                d.effective_header,
                            )
                            or re.search(
                                r"GradedTensorProduct\.(?:lift|of)|CliffordAlgebra\.evenOdd|ᵍ⊗",
                                rhs_no_dead,
                            )
                        )
                        is_scalar_bc = False
                    if any_has_ungraded_tp and has_alghom and not has_graded_or_jw and not is_scalar_bc:
                        r33_errors.append(
                            f"{rel}:{d.start_line} ({d.short_name}): ungraded TensorProduct AlgHom without Z/2-grading or JW parity-string"
                        )
                else:
                    if d.kind in {"def", "abbrev"} and re.search(r"(?:abs|tensor|clifford|jw|jordanWigner)", d.short_name, re.IGNORECASE):
                        if "TensorProduct" in d.header_text and "GradedTensorProduct" not in d.header_text and "evenOdd" not in d.block_text and "parity" not in d.block_text.lower():
                            if "→ₐ[" in d.header_text:
                                r33_errors.append(f"{rel}:{d.start_line} ({d.short_name}): ungraded TensorProduct AlgHom without Z/2-grading")
        outcomes.append(
            CheckOutcome(
                check_id="T2-R3.3-KOSZUL-Z2-GRADING",
                tier=2,
                milestone="M3",
                pillar="r3",
                status="FAIL" if r33_errors else "PASS",
                summary="; ".join(r33_errors) if r33_errors else f"R3.3 Koszul Z/2-grading & JW parity verified on {len(r33_files)} file(s)",
                details={"files": r33_files, "errors": r33_errors},
            )
        )

    # R3.4: Faithfulness-free LieActionLane, Peirce/nilpotent soldering, & diamond hygiene
    r34_files = [
        r for r in targets
        if r.endswith(("PeirceCartanKoszulDVPrimary.lean", "DerivationLieLane.lean"))
    ]
    all_lean_targets = sorted(targets.keys())
    if pillar_filter in {"all", "r1"} and (r34_files or all_lean_targets):
        r34_errors: list[str] = []
        for rel in r34_files:
            stripped, decls = _read_stripped(rel)
            pub_corpus = _decl_corpus(decls, include_private=False)
            if not re.search(r"\bLieActionLane\b|\bIsLeibnizAction\b", pub_corpus):
                r34_errors.append(f"{rel}: missing faithfulness-free LieActionLane / IsLeibnizAction in public declarations")
            if re.search(r"^[ \t]*import\s+Mathlib\.RingTheory\.Derivation(?:\.\S+)?\b", stripped, re.MULTILINE):
                r34_errors.append(f"{rel}: imports commutative Mathlib.RingTheory.Derivation")
            if rel.endswith("PeirceCartanKoszulDVPrimary.lean"):
                for d in decls:
                    decl_all = f"{d.effective_header}\n{d.block_text}"
                    hyp_part, ret_part = _split_top_level_header_colon(d.effective_header, d.short_name)
                    is_comm_kaehler = bool(
                        re.search(r"kaehler|kahler", d.short_name, re.IGNORECASE)
                        and len(re.findall(r"\[(?:CommRing|CommSemiring|Field)\b", d.effective_header)) >= 2
                        and not re.search(
                            r"\[Ring\b|\bLieActionLane\b|\bIsLeibnizAction\b|\bNonAssocDerivation\b",
                            d.effective_header,
                        )
                    )
                    if (
                        re.search(
                            r"\[\s*(?:[\w.]+\.)?Derivation\b|\(\s*[^:()\n]+:\s*(?:[\w.]+\.)?Derivation\b|\{\s*[^:{}\n]+:\s*(?:[\w.]+\.)?Derivation\b",
                            d.effective_header,
                        )
                        and not is_comm_kaehler
                    ):
                        r34_errors.append(f"{rel}:{d.start_line} ({d.short_name}): commutative Derivation hypothesis on noncommutative declaration")

                    # Check .faithful: ALWAYS forbidden as a hypothesis; only allowed if negated in return type of a theorem/lemma
                    if re.search(r"DerivationLieLane\.faithful|\.faithful\b", hyp_part):
                        r34_errors.append(f"{rel}:{d.start_line} ({d.short_name}): declaration requires .faithful hypothesis")
                    elif re.search(r"DerivationLieLane\.faithful|\.faithful\b", decl_all):
                        is_negated_in_ret = (
                            d.kind in {"theorem", "lemma"}
                            and bool(re.search(r"(?:¬|Not)\s*\(?\s*(?:[\w.]+\.)?(?:DerivationLieLane\.)?faithful\b|¬[^\n]*\.faithful\b", ret_part))
                        )
                        if not is_negated_in_ret:
                            r34_errors.append(f"{rel}:{d.start_line} ({d.short_name}): declaration requires .faithful")

                    # Check Function.Injective alongside Lie/derivation tokens
                    has_lie_ctx = bool(
                        re.search(
                            r"\b(?:LieActionLane|IsLeibnizAction|Derivation|chevalley|koszul|dubois|maurer|act)\b",
                            f"{d.short_name}\n{decl_all}",
                            re.IGNORECASE,
                        )
                    )
                    if has_lie_ctx:
                        if re.search(r"\bFunction\.Injective\b", hyp_part):
                            r34_errors.append(f"{rel}:{d.start_line} ({d.short_name}): Lie/derivation declaration requires Function.Injective hypothesis")
                        elif re.search(r"\bFunction\.Injective\b", decl_all):
                            is_negated_inj = (
                                d.kind in {"theorem", "lemma"}
                                and bool(re.search(r"(?:¬|Not)\s*\(?\s*Function\.Injective\b", ret_part))
                            )
                            if not is_negated_inj:
                                r34_errors.append(f"{rel}:{d.start_line} ({d.short_name}): Lie/derivation declaration requires Function.Injective")
                if not re.search(r"(?:peirce|IsIdempotentElem|nilpotent|IsNilpotent|\*\s*e\s*=\s*e)", pub_corpus, re.IGNORECASE):
                    r34_errors.append(f"{rel}: missing Peirce idempotent / nilpotent soldering in declarations")

        for rel in all_lean_targets:
            stripped, _ = _read_stripped(rel)
            s_lines = stripped.splitlines()
            s_num = len(s_lines)
            s_idx = 0
            while s_idx < s_num:
                s_line = s_lines[s_idx]
                if not s_line.strip():
                    s_idx += 1
                    continue
                prefixes, in_end_idx, after_in = _consume_in_prefixes(s_lines, s_idx)
                if prefixes:
                    # Check if a declaration-local `open scoped ... in` was actually applied to `section`/`namespace` (not single decl)
                    if not after_in:
                        nxt_i = in_end_idx + 1
                        while nxt_i < s_num and not s_lines[nxt_i].strip():
                            nxt_i += 1
                        if nxt_i < s_num and re.match(r"^\s*(?:section|namespace)\b", s_lines[nxt_i]):
                            for pref in prefixes:
                                if re.search(r"\b(?:Erlangen20Unification|FiniteTensorProduct)\b", pref):
                                    r34_errors.append(f"{rel}:{s_idx + 1}: `open ... in section/namespace` acts as global diamond")
                        s_idx = in_end_idx + 1
                        continue
                    cur_idx = in_end_idx
                    cur = after_in
                else:
                    cur_idx = s_idx
                    cur = s_line

                if _OPEN_RX.match(cur):
                    open_parts = [cur.strip()]
                    bdepth = sum(1 for c in cur if c in "([{⦃") - sum(1 for c in cur if c in ")]}⦄")
                    j = cur_idx + 1
                    while bdepth > 0 and j < s_num:
                        nxt_s = s_lines[j].strip()
                        open_parts.append(nxt_s)
                        bdepth += sum(1 for c in nxt_s if c in "([{⦃") - sum(1 for c in nxt_s if c in ")]}⦄")
                        j += 1
                    open_cmd = " ".join(open_parts)
                    if re.search(
                        r"^\s*open\s+scoped\b[^\n]*\b(?:Erlangen20Unification|FiniteTensorProduct)\b"
                        r"|^\s*open\s+(?:[A-Za-z_][A-Za-z0-9_]*\s+)*(?:Erlangen20Unification|FiniteTensorProduct)\b"
                        r"|^\s*open\s+[A-Za-z0-9_.]+\s*\([^\n)]*\b(?:Erlangen20Unification|FiniteTensorProduct)\b",
                        open_cmd,
                    ):
                        r34_errors.append(f"{rel}:{cur_idx + 1}: forbidden global `open (scoped) Erlangen20Unification / FiniteTensorProduct` diamond")
                    s_idx = j
                    continue

                if re.match(r"^\s*attribute\s*\[", cur):
                    # Consume balanced `[...]` and trailing target names (including multi-line continuations)
                    b_pos = cur.find("[")
                    adepth = 0
                    scan_i = cur_idx
                    scan_l = cur[b_pos:]
                    attr_chunks: list[str] = []
                    closed_attr = False
                    after_attr = ""
                    while scan_i < s_num:
                        for ch_i, ch in enumerate(scan_l):
                            if ch == "[":
                                adepth += 1
                            elif ch == "]":
                                adepth -= 1
                                if adepth == 0:
                                    attr_chunks.append(scan_l[: ch_i + 1])
                                    after_attr = scan_l[ch_i + 1 :]
                                    closed_attr = True
                                    break
                        if closed_attr:
                            break
                        attr_chunks.append(scan_l)
                        scan_i += 1
                        if scan_i < s_num:
                            scan_l = s_lines[scan_i]
                    attr_hdr = " ".join(attr_chunks)
                    target_parts = [after_attr.strip()]
                    j = scan_i + 1
                    while j < s_num:
                        nxt_l = s_lines[j]
                        nxt_s = nxt_l.strip()
                        if not nxt_s or _TOP_CMD_RX.match(nxt_l) or _MOD_KW_RX.match(nxt_s) or nxt_s.startswith("@["):
                            break
                        target_parts.append(nxt_s)
                        j += 1
                    targets_blob = " ".join(target_parts)
                    if (
                        re.search(r"\binstance\b", attr_hdr)
                        and not re.search(r"\b(?:local|scoped)\b", attr_hdr)
                        and re.search(r"\binstAlgebraClTower\w*\b", targets_blob)
                    ):
                        r34_errors.append(f"{rel}:{cur_idx + 1}: forbidden global `attribute [instance] instAlgebraClTower` diamond")
                    s_idx = j
                    continue

                mods, end_mod_idx, rem = _consume_mods_and_attrs(s_lines, cur_idx, cur)
                if re.match(r"^instance\b", rem) and not any(m in {"local", "scoped"} for m in mods):
                    inst_parts = [rem]
                    j = end_mod_idx + 1
                    while j < s_num and ":=" not in " ".join(inst_parts) and not re.search(r"\bwhere\b", " ".join(inst_parts)):
                        nxt_l = s_lines[j]
                        nxt_s = nxt_l.strip()
                        if not nxt_s or _TOP_CMD_RX.match(nxt_l):
                            break
                        inst_parts.append(nxt_s)
                        j += 1
                    if re.search(r"\binstAlgebraClTower\w*\b", " ".join(inst_parts)):
                        r34_errors.append(f"{rel}:{end_mod_idx + 1}: forbidden global `instance instAlgebraClTower` diamond")
                    s_idx = j
                    continue

                s_idx = end_mod_idx + 1

        outcomes.append(
            CheckOutcome(
                check_id="T2-R3.4-LIE-PEIRCE-DIAMONDS",
                tier=2,
                milestone="M4/ALL",
                pillar="r1",
                status="FAIL" if r34_errors else "PASS",
                summary="; ".join(r34_errors) if r34_errors else f"R3.4 faithfulness-free Lie/Peirce & diamond hygiene verified on {len(all_lean_targets)} file(s)",
                details={"files": all_lean_targets, "errors": r34_errors},
            )
        )

    return outcomes


def check_repo_lean_invariants(
    repo_root: Path = REPO_ROOT,
    *,
    require_m6_in_all: bool = False,
) -> CheckOutcome:
    """Tier 4 repo invariant: tests/test_default_lean_sources.py declared==existing + audit_default_lean_sources."""
    lakefile = repo_root / "lakefile.lean"
    if not lakefile.is_file():
        return CheckOutcome(
            check_id="T4-REPO-LEAN-INVARIANT",
            tier=4,
            milestone="GLOBAL",
            pillar="all",
            status="FAIL",
            summary="Missing lakefile.lean",
            details={},
        )
    config = lakefile.read_text(encoding="utf-8", errors="replace")
    suite_match = re.search(
        r"lean_lib InfoGeometryTestSuite where\n(.*?)(?=^\S|\Z)", config, re.M | re.S
    )
    if suite_match is None:
        return CheckOutcome(
            check_id="T4-REPO-LEAN-INVARIANT",
            tier=4,
            milestone="GLOBAL",
            pillar="all",
            status="FAIL",
            summary="InfoGeometryTestSuite not found in lakefile.lean",
            details={},
        )
    suite_body = suite_match.group(1)
    if ".anonymous" in suite_body:
        return CheckOutcome(
            check_id="T4-REPO-LEAN-INVARIANT",
            tier=4,
            milestone="GLOBAL",
            pillar="all",
            status="FAIL",
            summary="InfoGeometryTestSuite must not use .anonymous",
            details={},
        )
    suite_declared = set(re.findall(r"`([\w.]+)", suite_body))
    opt_in: set[str] = set()
    for lib_name, lib_body in re.findall(
        r"^lean_lib (\w+) where\n(.*?)(?=^\S|\Z)", config, re.M | re.S
    ):
        if lib_name != "InfoGeometryTestSuite" and 'srcDir := "../tests"' in lib_body:
            opt_in.update(re.findall(r"`([\w.]+)", lib_body))
    existing = {
        ".".join(path.relative_to(repo_root / "tests").with_suffix("").parts)
        for path in (repo_root / "tests").rglob("*.lean")
    }
    declared = suite_declared | opt_in
    if declared != existing:
        extra = sorted(existing - declared)
        missing = sorted(declared - existing)
        return CheckOutcome(
            check_id="T4-REPO-LEAN-INVARIANT",
            tier=4,
            milestone="GLOBAL",
            pillar="all",
            status="FAIL",
            summary=f"lakefile.lean tests declared != existing: extra={extra}, missing={missing}",
            details={"extra": extra, "missing": missing},
        )

    # Check M6 wiring into R1R2R3UnifiedTriangleBridge / Canonical/All if required
    wiring_errors: list[str] = []
    if require_m6_in_all:
        all_path = repo_root / CANONICAL_ALL_REL
        tri_path = repo_root / TRIANGLE_BRIDGE_REL
        all_txt = all_path.read_text(encoding="utf-8", errors="replace") if all_path.is_file() else ""
        tri_txt = tri_path.read_text(encoding="utf-8", errors="replace") if tri_path.is_file() else ""
        if "InfoGeometry.Canonical.PrimarySourceFourPillarBridge" not in all_txt:
            wiring_errors.append(f"{CANONICAL_ALL_REL} missing import InfoGeometry.Canonical.PrimarySourceFourPillarBridge")
        if "PrimarySourceFourPillarBridge" not in tri_txt:
            wiring_errors.append(f"{TRIANGLE_BRIDGE_REL} does not reference PrimarySourceFourPillarBridge")

    if wiring_errors:
        return CheckOutcome(
            check_id="T4-REPO-LEAN-INVARIANT",
            tier=4,
            milestone="M6",
            pillar="all",
            status="FAIL",
            summary="; ".join(wiring_errors),
            details={"wiring_errors": wiring_errors},
        )

    return CheckOutcome(
        check_id="T4-REPO-LEAN-INVARIANT",
        tier=4,
        milestone="GLOBAL",
        pillar="all",
        status="PASS",
        summary=f"tests/ declared == existing ({len(existing)} Lean test files); M6 wiring={require_m6_in_all}",
        details={"lean_test_count": len(existing)},
    )
