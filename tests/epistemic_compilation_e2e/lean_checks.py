"""Tier 1 Lean Gate Checks & Static Quality Scanners (T1-LEAN-01 .. T1-LEAN-05)."""

from __future__ import annotations

import json
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from tests.epistemic_compilation_e2e import (
    BASELINE_SMOKE_LEAN_REL,
    CheckOutcome,
    DEFAULT_BUILD_LOCK_PATH,
    REQUIRED_LEAN_COPYRIGHT_HEADER,
)
from tests.epistemic_compilation_e2e.intake_checks import run_subprocess_safe

MODULE_SEGMENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
_LEAN_IDENT_SEG = (
    r"(?:«[^»\n]+»|(?:[^\W\d_]|_)"
    r"(?:[^\s():{\[⦃=,;)\]\}⦄.+*\-/^<>|~@#&%$⟨⟩\"'\\"
    r"≤≥≠×∘∧∨↔→←↦∈∉⊆⊂⊇⊃∪∩∖⊕⊗⋅∙•·≈≡∼≃≅≪≫≺≻⊢⊨⊥⊤∀∃∑∏∫√∂∇¬±∓÷‖∣∥†‡⋆∗□◇△"
    r"⊓⊔≍⨅⨆⋂⋃⊞⊟⊠⋊⋉≲≳≢⧸⁻¹ᵀᴴ"
    r"⊑⊒⊏⊐⨁⨂↪↠⇒⇐⇔⊖⊘⊙≼≽]|')*)"
)
_LEAN_QUAL_IDENT = rf"{_LEAN_IDENT_SEG}(?:\.{_LEAN_IDENT_SEG})*"
_LEAN_IDENT_SEG_RE = re.compile(rf"^{_LEAN_IDENT_SEG}$")
_LEAN_IDENT_TOKEN_RE = re.compile(_LEAN_IDENT_SEG)
_LEAN_QUAL_TOKEN_RE = re.compile(rf"\.{_LEAN_IDENT_SEG}|{_LEAN_QUAL_IDENT}")


def split_lean_qual_ident(ident: str) -> list[str]:
    """Split a dotted Lean identifier on `.` outside `«...»` guillemets."""
    s = str(ident).strip()
    if not s:
        return []
    parts: list[str] = []
    cur: list[str] = []
    in_guil = False
    for ch in s:
        if ch == "«":
            in_guil = True
            cur.append(ch)
        elif ch == "»":
            in_guil = False
            cur.append(ch)
        elif ch == "." and not in_guil:
            seg = "".join(cur)
            if seg:
                parts.append(seg)
            cur.clear()
        else:
            cur.append(ch)
    tail = "".join(cur)
    if tail:
        parts.append(tail)
    return parts


def lean_short_name(ident: str) -> str:
    """Return the trailing segment of a qualified Lean identifier, preserving `«...»` guillemets."""
    parts = split_lean_qual_ident(ident)
    return parts[-1] if parts else str(ident).strip()
DECL_NAME_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\n]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    rf"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+({_LEAN_QUAL_IDENT})"
)
NON_OPAQUE_DECL_NAME_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\n]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    rf"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+({_LEAN_QUAL_IDENT})"
)
NATIVE_DECIDE_RE = re.compile(r"\bnative_decide\b")
FORBIDDEN_KERNEL_BYPASS_RE = re.compile(r"\b(?:Lean\.)?(?:ofReduceBool|trustCompiler)\b")
VACUOUS_DECL_START_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\n]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(theorem|lemma|example|def|abbrev|instance)\b"
)
PROP_STRUCT_HEAD_START_RE = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\n]*\]\s*)*(?:(?:private|protected|scoped|local)\s+)*(?:structure|class)\s+"
    rf"({_LEAN_QUAL_IDENT})(?=\s|$|[:({{\[⦃]|\.\{{)"
)
PROP_CONSTRUCTOR_HEAD_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\n]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|example|instance)\b"
)
NONTRIVIAL_PROP_PROOF_RE = re.compile(
    r"\b(?:induction|cases|by_cases|fin_cases|rcases|obtain|calc|rw|rewrite|"
    r"ring|noncomm_ring|linarith|nlinarith|omega|abel|positivity|norm_num|ext|unfold|"
    r"simp\s+(?:only\s+)?\[|noConfusion|Function\.bijective_id|bot_le)\b"
)
_NON_SIMP_NONTRIVIAL_PROP_PROOF_RE = re.compile(
    r"\b(?:induction|cases|by_cases|fin_cases|rcases|obtain|calc|rw|rewrite|"
    r"ring|noncomm_ring|linarith|nlinarith|omega|abel|positivity|norm_num|ext|unfold|"
    r"noConfusion|Function\.bijective_id|bot_le)\b"
)
def _split_top_level_ws(s: str) -> list[str]:
    """Split `s` on whitespace at bracket/guillemet depth 0."""
    tokens: list[str] = []
    cur: list[str] = []
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    i = 0
    n = len(s)
    while i < n:
        ch = s[i]
        if ch == "«":
            cur.append(ch)
            i += 1
            while i < n and s[i] not in ("»", "\n"):
                cur.append(s[i])
                i += 1
            if i < n and s[i] == "»":
                cur.append("»")
                i += 1
            continue
        if ch in open_ch:
            depth += 1
            cur.append(ch)
        elif ch in close_ch and depth > 0:
            depth -= 1
            cur.append(ch)
        elif depth == 0 and ch.isspace():
            if cur:
                tokens.append("".join(cur))
                cur.clear()
        else:
            cur.append(ch)
        i += 1
    if cur:
        tokens.append("".join(cur))
    return tokens


def _split_struct_literal_fields(
    inner: str,
    *,
    allow_pattern_shorthand: bool = False,
) -> list[tuple[str, str]] | None:
    """Parse `{ f1 := v1, f2 := v2 }` body into `[(field, val), ...]` (optionally allowing `..` & punning) or return `None`."""
    segs: list[str] = []
    cur: list[str] = []
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    i = 0
    n = len(inner)
    while i < n:
        ch = inner[i]
        if ch == "«":
            cur.append(ch)
            i += 1
            while i < n and inner[i] not in ("»", "\n"):
                cur.append(inner[i])
                i += 1
            if i < n and inner[i] == "»":
                cur.append("»")
                i += 1
            continue
        if ch in open_ch:
            depth += 1
            cur.append(ch)
        elif ch in close_ch and depth > 0:
            depth -= 1
            cur.append(ch)
        elif depth == 0 and ch == ",":
            seg = "".join(cur).strip()
            if seg:
                segs.append(seg)
            cur.clear()
        elif depth == 0 and ch == "\n":
            seg = "".join(cur).strip()
            if not seg:
                cur.clear()
            elif re.search(r"(?::=|\b(?:by|exact|refine'?))\s*$", seg):
                cur.append("\n")
            else:
                rest_after_nl = inner[i + 1 :].lstrip()
                if rest_after_nl and (
                    re.match(rf"{_LEAN_IDENT_SEG}\s*:=", rest_after_nl)
                    or (
                        allow_pattern_shorthand
                        and (
                            rest_after_nl.startswith("..")
                            or re.match(rf"{_LEAN_IDENT_SEG}\s*(?:,|\n|$)", rest_after_nl)
                        )
                    )
                ):
                    segs.append(seg)
                    cur.clear()
                else:
                    cur.append("\n")
        else:
            cur.append(ch)
        i += 1
    tail = "".join(cur).strip()
    if tail:
        segs.append(tail)
    if not segs:
        return None
    pairs: list[tuple[str, str]] = []
    for seg in segs:
        if allow_pattern_shorthand and seg == "..":
            continue
        m = re.match(rf"^({_LEAN_IDENT_SEG})\s*:=\s*(.+)$", seg, flags=re.S)
        if m:
            pairs.append((m.group(1), m.group(2).strip()))
            continue
        if (
            allow_pattern_shorthand
            and _LEAN_IDENT_SEG_RE.fullmatch(seg)
            and seg not in _LEAN_TERM_KEYWORDS
            and seg != "_"
        ):
            pairs.append((seg, seg))
            continue
        return None
    return pairs


def _parse_named_ctor_arg(arg: str) -> tuple[str | None, str]:
    """If `arg` is a parenthesized named argument `(field := val)`, return `(field, val)`; otherwise `(None, arg)`."""
    s = arg.strip()
    if not (s.startswith("(") and s.endswith(")")):
        return None, s
    inner = s[1:-1].strip()
    m = re.match(rf"^({_LEAN_IDENT_SEG})\s*:=\s*(.+)$", inner, flags=re.S)
    if not m:
        return None, s
    # Ensure `:=` is at depth 0 inside `inner`
    depth = 0
    i = 0
    n = len(inner)
    while i < n:
        ch = inner[i]
        if ch == "«":
            i += 1
            while i < n and inner[i] not in ("»", "\n"):
                i += 1
            if i < n and inner[i] == "»":
                i += 1
            continue
        if ch in "([{⦃⟨":
            depth += 1
        elif ch in ")]}⦄⟩" and depth > 0:
            depth -= 1
        elif depth == 0 and inner.startswith(":=", i):
            if inner[:i].strip() == m.group(1):
                return m.group(1), inner[i + 2 :].strip()
            return None, s
        i += 1
    return None, s


def _unwrap_named_ctor_arg(arg: str) -> str:
    """If `arg` is a parenthesized named argument `(field := val)`, return `val`; otherwise return `arg`."""
    return _parse_named_ctor_arg(arg)[1]


def _is_named_or_implicit_arg_tok(tok: str) -> bool:
    """Return True iff `tok` is an implicit `{...}` or named `(name := val)` argument token."""
    t = tok.strip()
    if t.startswith("{") and t.endswith("}"):
        return True
    if t.startswith("(") and t.endswith(")"):
        return _unwrap_named_ctor_arg(t) != t
    return False


def _strip_type_ascription(expr: str) -> str:
    """Unwrap outer `(...)`, trailing top-level `: <Type>` ascriptions, `show ... from ...`, and `id`/`@id` wrappers."""
    s = _strip_outer_parens(expr.strip())
    while s:
        changed = False
        s_paren = _strip_outer_parens(s)
        if s_paren != s:
            s = s_paren
            changed = True
        m_show = re.match(r"^show(?=\s|[({\[⦃⟨«])", s)
        if m_show:
            depth = 0
            open_ch = set("([{⦃⟨")
            close_ch = set(")]}⦄⟩")
            idx = m_show.end()
            n = len(s)
            unwrapped_show = False
            while idx < n:
                ch = s[idx]
                if ch == "«":
                    idx += 1
                    while idx < n and s[idx] not in ("»", "\n"):
                        idx += 1
                    if idx < n and s[idx] == "»":
                        idx += 1
                    continue
                if ch in open_ch:
                    depth += 1
                elif ch in close_ch and depth > 0:
                    depth -= 1
                elif depth == 0 and (idx == 0 or not (s[idx - 1].isalnum() or s[idx - 1] in "_'«».")):
                    if re.match(r"^from(?=\s|[({\[⦃⟨«])", s[idx:]):
                        s = _strip_outer_parens(s[idx + 4 :].strip())
                        changed = True
                        unwrapped_show = True
                        break
                    if re.match(r"^by(?=\s|$)", s[idx:]):
                        s = s[idx:].strip()
                        changed = True
                        unwrapped_show = True
                        break
                idx += 1
            if unwrapped_show:
                continue
        if not re.match(r"^(?:fun|λ|forall|∀|let|have|match|if)\b", s):
            depth = 0
            open_ch = set("([{⦃⟨")
            close_ch = set(")]}⦄⟩")
            colon_idx: int | None = None
            idx = 0
            n = len(s)
            while idx < n:
                ch = s[idx]
                if ch == "«":
                    idx += 1
                    while idx < n and s[idx] not in ("»", "\n"):
                        idx += 1
                    if idx < n and s[idx] == "»":
                        idx += 1
                    continue
                if ch in open_ch:
                    depth += 1
                elif ch in close_ch and depth > 0:
                    depth -= 1
                elif depth == 0 and ch == ":" and not s.startswith(":=", idx) and not s.startswith("::", idx):
                    if idx == 0 or s[idx - 1] != ":":
                        colon_idx = idx
                        break
                idx += 1
            if colon_idx is not None and colon_idx > 0:
                lhs = s[:colon_idx].strip()
                if lhs:
                    s = _strip_outer_parens(lhs)
                    changed = True
        toks = _split_top_level_ws(s)
        if len(toks) >= 2 and re.fullmatch(r"@?id(?:\.\{[^}]*\})?", toks[0]):
            is_at_id = toks[0].startswith("@")
            saw_alpha = False
            a_val: str | None = None
            pos_toks: list[str] = []
            id_ok = True
            for t in toks[1:]:
                ts = t.strip()
                if ts.startswith("{") and ts.endswith("}"):
                    continue
                aname, aval = _parse_named_ctor_arg(ts)
                if aname is not None:
                    if aname == "α":
                        saw_alpha = True
                        continue
                    if aname == "a" and a_val is None:
                        a_val = aval
                        continue
                    id_ok = False
                    break
                pos_toks.append(t)
            if id_ok:
                unwrapped_s: str | None = None
                if is_at_id:
                    if a_val is not None:
                        if not pos_toks or (not saw_alpha and len(pos_toks) == 1):
                            unwrapped_s = a_val
                    elif saw_alpha and len(pos_toks) == 1:
                        unwrapped_s = pos_toks[0]
                    elif not saw_alpha and len(pos_toks) == 2:
                        unwrapped_s = pos_toks[1]
                else:
                    if a_val is not None and not pos_toks:
                        unwrapped_s = a_val
                    elif a_val is None and len(pos_toks) == 1:
                        unwrapped_s = pos_toks[0]
                if unwrapped_s is not None:
                    s = _strip_outer_parens(unwrapped_s)
                    changed = True
        if not changed:
            break
    return s


def _ctor_head_field_count(head: str, struct_field_counts: dict[str, int] | None) -> int | None:
    """Resolve expected field count for `head` (`@?T.mk` or `@?(And|Iff|Exists).intro`)."""
    raw = re.sub(r"\.\{[^}]*\}$", "", head.lstrip("@"))
    if raw in ("And.intro", "Iff.intro", "Exists.intro"):
        return 2
    if struct_field_counts and raw.endswith(".mk"):
        type_part = raw[:-3]
        if type_part in struct_field_counts:
            return struct_field_counts[type_part]
        short_type = lean_short_name(type_part)
        if short_type in struct_field_counts:
            return struct_field_counts[short_type]
    return None


def _ctor_param_names_for_head(head: str, struct_param_names: dict[str, set[str]] | None) -> set[str]:
    """Resolve structure parameter names for `head` (`@?T.mk`) so `(param := val)` args are skipped."""
    if not struct_param_names:
        return set()
    raw = re.sub(r"\.\{[^}]*\}$", "", head.lstrip("@"))
    if raw.endswith(".mk"):
        type_part = raw[:-3]
        if type_part in struct_param_names:
            return struct_param_names[type_part]
        short_type = lean_short_name(type_part)
        if short_type in struct_param_names:
            return struct_param_names[short_type]
    return set()


_CTOR_HEAD_RE = re.compile(
    r"(?:@?(?:[A-Za-z_][A-Za-z0-9_'.?!]*)?\.mk(?:\.\{[^}]*\})?|@?(?:And|Iff|Exists)\.intro(?:\.\{[^}]*\})?)"
)


def _unwrap_ctor_app_tokens(expr: str) -> list[str]:
    """Split `expr` into top-level tokens, unwrapping parenthesized/ascribed heads and curried `id`/`@id` wrappers."""
    toks = _split_top_level_ws(expr.strip())
    for _ in range(10):
        if not toks:
            break
        hd = toks[0].strip()
        if re.fullmatch(r"id(?:\.\{[^}]*\})?", hd) and len(toks) >= 2:
            rem = toks[1:]
            unwrapped_id = False
            while rem:
                r0 = rem[0].strip()
                if r0.startswith("{") and r0.endswith("}"):
                    rem = rem[1:]
                    continue
                aname, aval = _parse_named_ctor_arg(r0)
                if aname == "α":
                    rem = rem[1:]
                    continue
                if aname == "a":
                    tail_rem: list[str] = []
                    for rt2 in rem[1:]:
                        rt2s = rt2.strip()
                        if rt2s.startswith("{") and rt2s.endswith("}"):
                            continue
                        a2_name, _ = _parse_named_ctor_arg(rt2s)
                        if a2_name == "α":
                            continue
                        tail_rem.append(rt2)
                    rem = _split_top_level_ws(aval) + tail_rem
                    unwrapped_id = True
                    break
                if aname is not None:
                    rem = []
                    break
                unwrapped_id = True
                break
            if unwrapped_id and rem:
                toks = rem
                continue
        if re.fullmatch(r"@id(?:\.\{[^}]*\})?", hd) and len(toks) >= 2:
            rem_all = toks[1:]
            rem = []
            saw_alpha = False
            for idx_r, rt in enumerate(rem_all):
                rts = rt.strip()
                if rts.startswith("{") and rts.endswith("}"):
                    continue
                aname, aval = _parse_named_ctor_arg(rts)
                if aname is not None:
                    if aname == "α":
                        saw_alpha = True
                        continue
                    if aname == "a":
                        kept_tail: list[str] = []
                        for rt2 in rem_all[idx_r + 1 :]:
                            rt2s = rt2.strip()
                            if rt2s.startswith("{") and rt2s.endswith("}"):
                                continue
                            a2_name, _ = _parse_named_ctor_arg(rt2s)
                            if a2_name == "α":
                                saw_alpha = True
                                continue
                            if not saw_alpha and a2_name is None:
                                saw_alpha = True
                                continue
                            kept_tail.append(rt2)
                        rem = _split_top_level_ws(aval) + kept_tail
                        break
                    rem = []
                    break
                if not saw_alpha:
                    saw_alpha = True
                    continue
                rem = rem_all[idx_r:]
                break
            if rem:
                toks = rem
                continue
        if not (hd.startswith("(") and hd.endswith(")")):
            break
        if _is_named_or_implicit_arg_tok(hd):
            break
        inner = _strip_type_ascription(hd)
        if not inner or inner == hd or _find_top_level_colon(inner) is not None:
            break
        inner_toks = _split_top_level_ws(inner)
        if not inner_toks:
            break
        toks = inner_toks + toks[1:]
    return toks


def _match_ctor_apply_in_line(
    text: str,
    *,
    allow_trivial_field_args: bool = False,
    struct_field_counts: dict[str, int] | None = None,
    struct_param_names: dict[str, set[str]] | None = None,
) -> tuple[int, int, str] | None:
    """Return `(start, end, head)` if `text` contains `apply <ctor_expr>` where `<ctor_expr>` unwraps to a `_CTOR_HEAD_RE` head."""
    for m_app in re.finditer(r"(?<![\w'»])apply\s+", text):
        pos = m_app.end()
        n_t = len(text)
        depth = 0
        while pos < n_t:
            if depth == 0 and text.startswith("<;>", pos):
                break
            ch = text[pos]
            if ch == "«":
                pos += 1
                while pos < n_t and text[pos] not in ("»", "\n"):
                    pos += 1
                if pos < n_t and text[pos] == "»":
                    pos += 1
                continue
            if ch in "([{⦃⟨":
                depth += 1
            elif ch in ")]}⦄⟩":
                if depth == 0:
                    break
                depth -= 1
            elif depth == 0 and ch in (";", "|", "\n"):
                break
            pos += 1
        arg_expr = text[m_app.end() : pos].strip()
        if not arg_expr:
            continue
        toks = _unwrap_ctor_app_tokens(_strip_type_ascription(arg_expr))
        if not toks or not _CTOR_HEAD_RE.fullmatch(toks[0]):
            continue
        raw_head = re.sub(r"\.\{[^}]*\}$", "", toks[0].lstrip("@"))
        type_part = raw_head[:-3] if raw_head.endswith(".mk") else ""
        has_known_params = bool(
            struct_param_names
            and type_part
            and (type_part in struct_param_names or lean_short_name(type_part) in struct_param_names)
        )
        param_names = _ctor_param_names_for_head(toks[0], struct_param_names)
        args_ok = True
        for tok in toks[1:]:
            ts = tok.strip()
            if ts == "_" or (ts.startswith("{") and ts.endswith("}")) or re.fullmatch(r"\d+", ts):
                continue
            arg_name, arg_val = _parse_named_ctor_arg(ts)
            if arg_name is not None:
                if has_known_params:
                    if arg_name in param_names:
                        continue
                elif re.fullmatch(rf"(?:_|\d+|{_LEAN_IDENT_SEG})", arg_val):
                    continue
                if allow_trivial_field_args and _is_trivial_proof_expr(
                    arg_val,
                    _depth=1,
                    struct_field_counts=struct_field_counts,
                    struct_param_names=struct_param_names,
                ):
                    continue
                args_ok = False
                break
            if allow_trivial_field_args and _is_trivial_proof_expr(
                ts,
                _depth=1,
                struct_field_counts=struct_field_counts,
                struct_param_names=struct_param_names,
            ):
                continue
            args_ok = False
            break
        if args_ok:
            return m_app.start(), pos, toks[0]
    return None


def _extract_eq_refl_arg(expr: str) -> str | None:
    """Return the reflected value argument `x` for `Eq.refl x`, `HEq.refl x`, `Eq.refl (α := _) x`, `Eq.refl (a := x)`, `@Eq.refl α x`, etc."""
    toks = _unwrap_ctor_app_tokens(expr)
    if not toks:
        return None
    m_hd = re.fullmatch(r"(@?)(?:Eq|HEq)\.refl(?:\.\{[^}]*\})?", toks[0])
    if not m_hd:
        return None
    is_at = bool(m_hd.group(1))
    saw_named_alpha = False
    named_a: str | None = None
    pos_toks: list[str] = []
    for t in toks[1:]:
        ts = t.strip()
        if ts.startswith("{") and ts.endswith("}"):
            continue
        arg_name, unwrapped = _parse_named_ctor_arg(ts)
        if arg_name is not None:
            if arg_name == "α":
                saw_named_alpha = True
                continue
            if arg_name == "a":
                named_a = unwrapped
                continue
            return None
        pos_toks.append(t)
    if named_a is not None:
        if is_at and not saw_named_alpha:
            return named_a if len(pos_toks) == 1 else None
        return named_a if len(pos_toks) == 0 else None
    if is_at and not saw_named_alpha:
        return pos_toks[1] if len(pos_toks) == 2 else None
    return pos_toks[0] if len(pos_toks) == 1 else None


def _is_eq_refl_expr(expr: str) -> bool:
    """Return True iff `expr` is `Eq.refl x`, `HEq.refl x`, `@Eq.refl α x`, or `@HEq.refl α x`."""
    return _extract_eq_refl_arg(expr) is not None


def _filter_at_ctor_field_args(
    head: str,
    raw_toks: list[str],
    struct_field_counts: dict[str, int] | None,
    struct_param_names: dict[str, set[str]] | None = None,
) -> list[str]:
    """Extract field-proof argument expressions from `@Ctor arg...` (skipping leading index/type/implicit/param args)."""
    param_names = _ctor_param_names_for_head(head, struct_param_names)
    named_vals: list[str] = []
    pos_args: list[str] = []
    for tok in raw_toks:
        t = tok.strip()
        if t.startswith("{") and t.endswith("}"):
            continue
        arg_name, unwrapped = _parse_named_ctor_arg(t)
        if arg_name is not None:
            if arg_name in param_names:
                continue
            named_vals.append(unwrapped)
        else:
            pos_args.append(t)
    expected_fields = _ctor_head_field_count(head, struct_field_counts)
    if expected_fields is not None:
        rem_needed = expected_fields - len(named_vals)
        if rem_needed <= 0:
            return named_vals
        if len(pos_args) >= rem_needed:
            return named_vals + pos_args[-rem_needed:]
        return []
    # Fallback without field count: drop `_` wildcards and leading non-proof index tokens when >=2 trailing trivial args remain
    non_wild = [a for a in pos_args if a != "_"]
    return named_vals + non_wild


def _is_trivial_proof_expr(
    expr: str,
    *,
    _depth: int = 0,
    struct_field_counts: dict[str, int] | None = None,
    struct_param_names: dict[str, set[str]] | None = None,
) -> bool:
    """Return True iff `expr` is a trivial reflexivity/True/constructor proof term (no lemma/hyp refs)."""
    if _depth > 20:
        return False
    s = _strip_type_ascription(_unwrap_named_ctor_arg(expr))
    if not s:
        return False
    if re.fullmatch(r"(?:rfl|trivial|True\.intro|Iff\.rfl)", s):
        return True
    if _is_eq_refl_expr(s):
        return True
    m_by = re.match(r"^by(?=\s|$)(.*)$", s, flags=re.S)
    if m_by:
        return _is_trivial_tactic_seq(
            m_by.group(1).strip(),
            _depth=_depth + 1,
            struct_field_counts=struct_field_counts,
            struct_param_names=struct_param_names,
        )
    if s.startswith("⟨") and s.endswith("⟩"):
        # Verify single balanced outer ⟨...⟩
        b_depth = 0
        balanced_outer = True
        open_ch = set("([{⦃⟨")
        close_ch = set(")]}⦄⟩")
        for idx_c, ch in enumerate(s):
            if ch in open_ch:
                b_depth += 1
            elif ch in close_ch:
                b_depth -= 1
                if b_depth == 0 and idx_c < len(s) - 1:
                    balanced_outer = False
                    break
        if balanced_outer and b_depth == 0:
            args = _split_top_level_commas(s[1:-1])
            return bool(args) and all(
                _is_trivial_proof_expr(
                    a,
                    _depth=_depth + 1,
                    struct_field_counts=struct_field_counts,
                    struct_param_names=struct_param_names,
                )
                for a in args
            )
    if s.startswith("{") and s.endswith("}") and _is_single_balanced_brace_block(s):
        pairs = _split_struct_literal_fields(s[1:-1])
        if pairs:
            return all(
                _is_trivial_proof_expr(
                    val,
                    _depth=_depth + 1,
                    struct_field_counts=struct_field_counts,
                    struct_param_names=struct_param_names,
                )
                for _, val in pairs
            )
    toks = _unwrap_ctor_app_tokens(s)
    if len(toks) >= 2:
        head = toks[0]
        if _CTOR_HEAD_RE.fullmatch(head):
            if head.startswith("@"):
                if _ctor_head_field_count(head, struct_field_counts) is not None:
                    field_args = _filter_at_ctor_field_args(
                        head, toks[1:], struct_field_counts, struct_param_names=struct_param_names
                    )
                    return bool(field_args) and all(
                        _is_trivial_proof_expr(
                            a,
                            _depth=_depth + 1,
                            struct_field_counts=struct_field_counts,
                            struct_param_names=struct_param_names,
                        )
                        for a in field_args
                    )
                param_names = _ctor_param_names_for_head(head, struct_param_names)
                pos_args: list[str] = []
                for a in toks[1:]:
                    a_s = a.strip()
                    if a_s.startswith("{") and a_s.endswith("}"):
                        continue
                    a_name, a_val = _parse_named_ctor_arg(a_s)
                    if a_name is not None and a_name in param_names:
                        continue
                    pos_args.append(a_val)
                non_wild = [a for a in pos_args if a != "_"]
                if not non_wild:
                    return False
                first_triv_idx: int | None = None
                for idx_a, a in enumerate(non_wild):
                    if _is_trivial_proof_expr(
                        a,
                        _depth=_depth + 1,
                        struct_field_counts=struct_field_counts,
                        struct_param_names=struct_param_names,
                    ):
                        first_triv_idx = idx_a
                        break
                if first_triv_idx is None:
                    return False
                if first_triv_idx > 0 and len(non_wild) - first_triv_idx < 2:
                    return False
                return all(
                    _is_trivial_proof_expr(
                        a,
                        _depth=_depth + 1,
                        struct_field_counts=struct_field_counts,
                        struct_param_names=struct_param_names,
                    )
                    for a in non_wild[first_triv_idx:]
                )
            param_names = _ctor_param_names_for_head(head, struct_param_names)
            args: list[str] = []
            for a in toks[1:]:
                a_s = a.strip()
                if a_s.startswith("{") and a_s.endswith("}"):
                    continue
                a_name, a_val = _parse_named_ctor_arg(a_s)
                if a_name is not None and a_name in param_names:
                    continue
                args.append(a_val)
            return bool(args) and all(
                _is_trivial_proof_expr(
                    a,
                    _depth=_depth + 1,
                    struct_field_counts=struct_field_counts,
                    struct_param_names=struct_param_names,
                )
                for a in args
            )
    return False


def _split_top_level_pipes(s: str) -> list[str]:
    """Split `s` on single `|` tactic-arm separators at bracket/guillemet depth 0."""
    arms: list[str] = []
    cur: list[str] = []
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    i = 0
    n = len(s)
    while i < n:
        ch = s[i]
        if ch == "«":
            cur.append(ch)
            i += 1
            while i < n and s[i] not in ("»", "\n"):
                cur.append(s[i])
                i += 1
            if i < n and s[i] == "»":
                cur.append("»")
                i += 1
            continue
        if ch in open_ch:
            depth += 1
            cur.append(ch)
        elif ch in close_ch and depth > 0:
            depth -= 1
            cur.append(ch)
        elif depth == 0 and ch == "|" and not s.startswith(("||", "|>"), i):
            arm = "".join(cur).strip()
            if arm:
                arms.append(arm)
            cur.clear()
        else:
            cur.append(ch)
        i += 1
    tail = "".join(cur).strip()
    if tail:
        arms.append(tail)
    return arms


def _strip_tactic_arm_prefix(tac: str) -> str:
    """Strip leading bullet (`·`/`•`) and `case <tag> =>` / `case' <tag> =>` / `next ... =>` arm prefixes at depth 0."""
    s = re.sub(r"^(?:·|•)\s*", "", tac.strip())
    while s:
        m_arm = re.match(r"^(?:case'?\s+[^\n=>]+?|next(?:\s+[^\n=>]+?)?)\s*=>\s*(.+)$", s, flags=re.S)
        if not m_arm:
            break
        s = re.sub(r"^(?:·|•)\s*", "", m_arm.group(1).strip())
    return s


def _split_unmatched_closing_delims(text: str, openers_before: list[str]) -> str:
    """Truncate `text` before the first unmatched `)`/`}` closing an opener in `openers_before`."""
    if not openers_before:
        return text
    stack = list(openers_before)
    depth_inner = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    pairs = {"(": ")", "{": "}", "[": "]", "⦃": "⦄", "⟨": "⟩"}
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if ch == "«":
            i += 1
            while i < n and text[i] not in ("»", "\n"):
                i += 1
            if i < n and text[i] == "»":
                i += 1
            continue
        if ch in open_ch:
            depth_inner += 1
        elif ch in close_ch:
            if depth_inner > 0:
                depth_inner -= 1
            elif stack and ch == pairs.get(stack[-1]):
                return text[:i].rstrip()
        i += 1
    return text


def _unclosed_openers_before(prefix: str) -> list[str]:
    """Return unclosed `(` / `{` openers in `prefix` before a nested tactic."""
    stack: list[str] = []
    pairs = {")": "(", "}": "{", "]": "[", "⦄": "⦃", "⟩": "⟨"}
    i = 0
    n = len(prefix)
    while i < n:
        ch = prefix[i]
        if ch == "«":
            i += 1
            while i < n and prefix[i] not in ("»", "\n"):
                i += 1
            if i < n and prefix[i] == "»":
                i += 1
            continue
        if ch in ("(", "{", "[", "⦃", "⟨"):
            stack.append(ch)
        elif ch in pairs:
            if stack and stack[-1] == pairs[ch]:
                stack.pop()
        i += 1
    return [op for op in stack if op in ("(", "{")]


def _is_trivial_tactic_seq(
    tac_text: str,
    *,
    _depth: int = 0,
    struct_field_counts: dict[str, int] | None = None,
    struct_param_names: dict[str, set[str]] | None = None,
) -> bool:
    """Return True iff `tac_text` closes its goal(s) using only trivial/constructor tactics."""
    if _depth > 20:
        return False
    s = _strip_tactic_arm_prefix(_strip_outer_parens(tac_text.strip()))
    if not s:
        return False
    if s.startswith("{") and s.endswith("}") and _is_single_balanced_brace_block(s):
        return _is_trivial_tactic_seq(
            s[1:-1],
            _depth=_depth + 1,
            struct_field_counts=struct_field_counts,
            struct_param_names=struct_param_names,
        )
    # Split on top-level `;` and `<;>` and newlines (when not continuing a combinator/pipe arm)
    steps: list[str] = []
    cur: list[str] = []
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    i = 0
    n = len(s)
    while i < n:
        if depth == 0 and s.startswith("<;>", i):
            seg = "".join(cur).strip()
            if seg:
                steps.append(seg)
            cur.clear()
            i += 3
            continue
        ch = s[i]
        if ch == "«":
            cur.append(ch)
            i += 1
            while i < n and s[i] not in ("»", "\n"):
                cur.append(s[i])
                i += 1
            if i < n and s[i] == "»":
                cur.append("»")
                i += 1
            continue
        if ch in open_ch:
            depth += 1
            cur.append(ch)
        elif ch in close_ch and depth > 0:
            depth -= 1
            cur.append(ch)
        elif depth == 0 and ch == ";":
            seg = "".join(cur).strip()
            if seg:
                steps.append(seg)
            cur.clear()
        elif depth == 0 and ch == "\n":
            seg_so_far = "".join(cur).strip()
            rest_l = s[i + 1 :].lstrip()
            nxt_is_pipe = rest_l.startswith("|") and not rest_l.startswith(("||", "|>"))
            if (
                seg_so_far
                and not nxt_is_pipe
                and not re.search(
                    r"(?:\b(?:exact|refine'?|by|all_goals|any_goals|repeat'?|try|focus|first|"
                    r"with_reducible|with_reducible_and_instances|iterate(?:\s+\d+)?)|:=|=>)\s*$",
                    seg_so_far,
                )
            ):
                steps.append(seg_so_far)
                cur.clear()
            else:
                cur.append(" ")
        else:
            cur.append(ch)
        i += 1
    tail_seg = "".join(cur).strip()
    if tail_seg:
        steps.append(tail_seg)
    if not steps:
        return False
    # Handle `constructor` / `apply <Type>.mk` / `refine'? <ctor_with_holes>` followed by trivial subgoal steps/arms
    m_ref0 = re.match(r"^refine'?(?:\s+|(?=[⟨{(]))(.+)$", steps[0], flags=re.S)
    m_app0 = _match_ctor_apply_in_line(
        steps[0],
        allow_trivial_field_args=True,
        struct_field_counts=struct_field_counts,
        struct_param_names=struct_param_names,
    )
    is_ctor_step0 = bool(
        re.fullmatch(r"constructor", steps[0])
        or (m_app0 is not None and m_app0[0] == 0 and m_app0[1] == len(steps[0]))
        or (
            m_ref0
            and _is_trivial_refine_ctor_with_holes(
                m_ref0.group(1),
                struct_field_counts=struct_field_counts,
                struct_param_names=struct_param_names,
            )
        )
    )
    if is_ctor_step0:
        rest_steps = steps[1:]
        if not rest_steps:
            return False
        return all(
            _is_trivial_tactic_seq(
                _strip_tactic_arm_prefix(st),
                _depth=_depth + 1,
                struct_field_counts=struct_field_counts,
                struct_param_names=struct_param_names,
            )
            for st in rest_steps
        )
    for st in steps:
        st_clean = _strip_outer_parens(_strip_tactic_arm_prefix(st))
        if not st_clean:
            continue
        if st_clean.startswith("{") and st_clean.endswith("}") and _is_single_balanced_brace_block(st_clean):
            if not _is_trivial_tactic_seq(
                st_clean[1:-1],
                _depth=_depth + 1,
                struct_field_counts=struct_field_counts,
                struct_param_names=struct_param_names,
            ):
                return False
            continue
        if re.fullmatch(r"(?:rfl|trivial|True\.intro|Iff\.rfl|done|simp|simp\s+only\s*\[\s*\])", st_clean) or _dsimp_targets_goal(st_clean):
            continue
        m_first = re.match(r"^first\s*\|(.*)$", st_clean, flags=re.S)
        if m_first:
            arms = _split_top_level_pipes(m_first.group(1))
            if arms and all(
                _is_trivial_tactic_seq(
                    arm,
                    _depth=_depth + 1,
                    struct_field_counts=struct_field_counts,
                    struct_param_names=struct_param_names,
                )
                for arm in arms
            ):
                continue
            return False
        m_comb = re.match(r"^(?:all_goals|any_goals|repeat'?|try|focus)\s+(.+)$", st_clean, flags=re.S)
        if m_comb:
            if _is_trivial_tactic_seq(
                m_comb.group(1),
                _depth=_depth + 1,
                struct_field_counts=struct_field_counts,
                struct_param_names=struct_param_names,
            ):
                continue
            return False
        m_ex = re.match(r"^(?:exact|refine'?)(?:\s+|(?=[⟨{(]))(.+)$", st_clean, flags=re.S)
        if m_ex and _is_trivial_proof_expr(
            m_ex.group(1),
            _depth=_depth + 1,
            struct_field_counts=struct_field_counts,
            struct_param_names=struct_param_names,
        ):
            continue
        if (";" in st_clean or "<;>" in st_clean or "\n" in st_clean) and st_clean != s:
            if _is_trivial_tactic_seq(
                st_clean,
                _depth=_depth + 1,
                struct_field_counts=struct_field_counts,
                struct_param_names=struct_param_names,
            ):
                continue
        return False
    return True


def _is_trivial_refine_arg(
    arg: str,
    *,
    _depth: int = 0,
    struct_field_counts: dict[str, int] | None = None,
    struct_param_names: dict[str, set[str]] | None = None,
) -> tuple[bool, bool]:
    """Return `(all_ok, saw_hole)` for an arg in a `refine` constructor pattern."""
    if _depth > 20:
        return False, False
    s = _strip_type_ascription(_unwrap_named_ctor_arg(arg))
    if s == "?_" or re.fullmatch(rf"\?{_LEAN_IDENT_SEG}", s):
        return True, True
    if _is_trivial_proof_expr(
        s,
        _depth=_depth + 1,
        struct_field_counts=struct_field_counts,
        struct_param_names=struct_param_names,
    ):
        return True, False
    if s.startswith("⟨") and s.endswith("⟩"):
        args = _split_top_level_commas(s[1:-1])
        if args:
            saw_hole = False
            for sub in args:
                ok, sub_hole = _is_trivial_refine_arg(
                    sub,
                    _depth=_depth + 1,
                    struct_field_counts=struct_field_counts,
                    struct_param_names=struct_param_names,
                )
                if not ok:
                    return False, False
                saw_hole = saw_hole or sub_hole
            return True, saw_hole
    if s.startswith("{") and s.endswith("}") and _is_single_balanced_brace_block(s):
        pairs = _split_struct_literal_fields(s[1:-1])
        if pairs:
            saw_hole = False
            for _, val in pairs:
                ok, sub_hole = _is_trivial_refine_arg(
                    val,
                    _depth=_depth + 1,
                    struct_field_counts=struct_field_counts,
                    struct_param_names=struct_param_names,
                )
                if not ok:
                    return False, False
                saw_hole = saw_hole or sub_hole
            return True, saw_hole
    if _is_trivial_refine_ctor_with_holes(
        s,
        _depth=_depth + 1,
        struct_field_counts=struct_field_counts,
        struct_param_names=struct_param_names,
    ):
        return True, True
    return False, False


def _is_trivial_refine_ctor_with_holes(
    expr: str,
    *,
    _depth: int = 0,
    struct_field_counts: dict[str, int] | None = None,
    struct_param_names: dict[str, set[str]] | None = None,
) -> bool:
    """Return True iff `expr` is a constructor shape containing `?_` / `?name` holes and only trivial non-hole args."""
    if _depth > 20:
        return False
    s = _strip_type_ascription(expr)
    if not s:
        return False
    if s.startswith("⟨") and s.endswith("⟩"):
        b_depth = 0
        balanced_outer = True
        for idx_c, ch in enumerate(s):
            if ch in "([{⦃⟨":
                b_depth += 1
            elif ch in ")]}⦄⟩":
                b_depth -= 1
                if b_depth == 0 and idx_c < len(s) - 1:
                    balanced_outer = False
                    break
        if balanced_outer and b_depth == 0:
            args = _split_top_level_commas(s[1:-1])
            if args:
                saw_hole = False
                for a in args:
                    ok, sub_hole = _is_trivial_refine_arg(
                        a,
                        _depth=_depth + 1,
                        struct_field_counts=struct_field_counts,
                        struct_param_names=struct_param_names,
                    )
                    if not ok:
                        return False
                    saw_hole = saw_hole or sub_hole
                return saw_hole
    if s.startswith("{") and s.endswith("}") and _is_single_balanced_brace_block(s):
        pairs = _split_struct_literal_fields(s[1:-1])
        if pairs:
            saw_hole = False
            for _, val in pairs:
                ok, sub_hole = _is_trivial_refine_arg(
                    val,
                    _depth=_depth + 1,
                    struct_field_counts=struct_field_counts,
                    struct_param_names=struct_param_names,
                )
                if not ok:
                    return False
                saw_hole = saw_hole or sub_hole
            return saw_hole
    toks = _unwrap_ctor_app_tokens(s)
    if len(toks) >= 2:
        head = toks[0]
        if _CTOR_HEAD_RE.fullmatch(head):
            if head.startswith("@") and _ctor_head_field_count(head, struct_field_counts) is not None:
                args = _filter_at_ctor_field_args(
                    head, toks[1:], struct_field_counts, struct_param_names=struct_param_names
                )
            else:
                param_names = _ctor_param_names_for_head(head, struct_param_names)
                args = []
                for a in toks[1:]:
                    a_s = a.strip()
                    if a_s.startswith("{") and a_s.endswith("}"):
                        continue
                    a_name, a_val = _parse_named_ctor_arg(a_s)
                    if a_name is not None and a_name in param_names:
                        continue
                    args.append(a_val)
                if head.startswith("@"):
                    args = [a for a in args if a != "_"]
            if args:
                saw_hole = False
                for a in args:
                    ok, sub_hole = _is_trivial_refine_arg(
                        a,
                        _depth=_depth + 1,
                        struct_field_counts=struct_field_counts,
                        struct_param_names=struct_param_names,
                    )
                    if not ok:
                        return False
                    saw_hole = saw_hole or sub_hole
                return saw_hole
    return False


def _has_trivial_ctor_closure(
    tail_no_have: str,
    *,
    struct_field_counts: dict[str, int] | None = None,
    struct_param_names: dict[str, set[str]] | None = None,
) -> bool:
    """Detect trivial constructor closures (`exact`/`refine`/`constructor`/`apply *.mk`) in `tail_no_have`."""
    if _TRIVIAL_CTOR_CLOSURE_RE.search(tail_no_have):
        return True
    # 1. Check `exact <expr>` / `refine'? <expr>` structurally (brace struct literals, nested ⟨...⟩, parenthesized/ascripted ctors, id ⟨...⟩, show ... from ..., @T.mk, multiline args, by ...)
    for m_ex in re.finditer(r"(?<![\w'»])(?:exact|refine'?)(?=\s|[⟨{(])", tail_no_have):
        stmt_line_start = tail_no_have.rfind("\n", 0, m_ex.start()) + 1
        stmt_line_prefix = tail_no_have[stmt_line_start : m_ex.start()]
        stmt_line_indent = len(stmt_line_prefix[: len(stmt_line_prefix) - len(stmt_line_prefix.lstrip())].replace("\t", "    "))
        m_b_ex = _LEADING_BULLET_RE.match(stmt_line_prefix.lstrip())
        min_cont_indent = stmt_line_indent + (m_b_ex.end() if m_b_ex else 1)
        pos = m_ex.end()
        n = len(tail_no_have)
        while pos < n and tail_no_have[pos] in (" ", "\t"):
            pos += 1
        if pos < n and tail_no_have[pos] == "\n":
            # Allow indented term on next line
            p_nl = pos + 1
            while p_nl < n and tail_no_have[p_nl] in (" ", "\t", "\n"):
                p_nl += 1
            pos = p_nl
        start = pos
        depth = 0
        open_ch = set("([{⦃⟨")
        close_ch = set(")]}⦄⟩")
        while pos < n:
            if depth == 0 and tail_no_have.startswith("<;>", pos):
                break
            ch = tail_no_have[pos]
            if ch == "«":
                pos += 1
                while pos < n and tail_no_have[pos] not in ("»", "\n"):
                    pos += 1
                if pos < n and tail_no_have[pos] == "»":
                    pos += 1
                continue
            if ch in open_ch:
                depth += 1
            elif ch in close_ch:
                if depth == 0:
                    break
                depth -= 1
            elif depth == 0 and ch in (";", "|"):
                break
            elif depth == 0 and ch == "\n":
                # Continue across newline if next non-empty line is an indented argument/expression continuation
                p_la = pos + 1
                while p_la < n:
                    nl_la = tail_no_have.find("\n", p_la)
                    line_la = tail_no_have[p_la:] if nl_la == -1 else tail_no_have[p_la:nl_la]
                    if line_la.strip():
                        nxt_ind = len(line_la[: len(line_la) - len(line_la.lstrip())].replace("\t", "    "))
                        nxt_s = line_la.lstrip()
                        is_arm_or_end = (
                            nxt_s.startswith(("·", "•", "|", ")", "}", "]", "⟩", "⦄"))
                            or bool(re.match(r"^(?:case'?\s+|next(?:\s|$|=>))", nxt_s))
                        )
                        is_cont = (not is_arm_or_end) and (
                            nxt_ind >= min_cont_indent
                            or nxt_s.startswith(("(", "{", "⟨", "⦃", "["))
                        )
                        break
                    if nl_la == -1:
                        is_cont = False
                        break
                    p_la = nl_la + 1
                else:
                    is_cont = False
                if not is_cont:
                    break
            pos += 1
        expr = tail_no_have[start:pos].strip()
        expr_inner = _strip_type_ascription(expr)
        expr_toks = _unwrap_ctor_app_tokens(expr_inner)
        is_ctor_shape = (
            (expr_inner.startswith("⟨") and expr_inner.endswith("⟩"))
            or (expr_inner.startswith("{") and expr_inner.endswith("}") and ":=" in expr_inner)
            or (len(expr_toks) >= 2 and bool(_CTOR_HEAD_RE.fullmatch(expr_toks[0])))
            or bool(re.match(r"^by(?=\s|$)", expr_inner))
        )
        if is_ctor_shape and _is_trivial_proof_expr(
            expr, struct_field_counts=struct_field_counts, struct_param_names=struct_param_names
        ):
            return True

    # 2. Check inline or multiline `constructor` / `apply <Type>.mk` / `refine'? <ctor_with_holes>` subgoals
    lines = tail_no_have.splitlines()
    ctor_tac_re = re.compile(r"(?<![\w'»])constructor(?![\w'»])")
    refine_tac_re = re.compile(r"(?<![\w'»])refine'?(?=\s|[⟨{(])")
    for idx, line in enumerate(lines):
        m_ctor_kw = ctor_tac_re.search(line)
        m_ctor_app = _match_ctor_apply_in_line(
            line,
            allow_trivial_field_args=True,
            struct_field_counts=struct_field_counts,
            struct_param_names=struct_param_names,
        )
        ctor_span: tuple[int, int] | None = None
        if m_ctor_kw is not None and (m_ctor_app is None or m_ctor_kw.start() <= m_ctor_app[0]):
            ctor_span = (m_ctor_kw.start(), m_ctor_kw.end())
        elif m_ctor_app is not None:
            ctor_span = (m_ctor_app[0], m_ctor_app[1])
        after_ctor: str | None = None
        last_stmt_idx = idx
        openers_before: list[str] = []
        if ctor_span is not None:
            prefix_up_to_ctor = "\n".join([*lines[:idx], line[: ctor_span[0]]])
            openers_before = _unclosed_openers_before(prefix_up_to_ctor)
            after_ctor = _split_unmatched_closing_delims(line[ctor_span[1] :].strip(), openers_before)
        else:
            m_ref = refine_tac_re.search(line)
            if m_ref:
                prefix_up_to_ref = "\n".join([*lines[:idx], line[: m_ref.start()]])
                openers_before = _unclosed_openers_before(prefix_up_to_ref)
                ref_line_indent = len(line[: len(line) - len(line.lstrip())].replace("\t", "    "))
                m_b_ref = _LEADING_BULLET_RE.match(line.lstrip())
                min_ref_cont_indent = ref_line_indent + (m_b_ref.end() if m_b_ref else 1)
                ref_col_indent = ref_line_indent + (m_b_ref.end() if m_b_ref else 0)
                # Extract refine expression (joining balanced multiline ⟨...⟩ / {...} / (...) and indented T.mk args)
                joined = line[m_ref.end() :].strip()
                j_end = idx
                bal = 0
                for ch in joined:
                    if ch in "([{⦃⟨":
                        bal += 1
                    elif ch in ")]}⦄⟩" and bal > 0:
                        bal -= 1
                while j_end + 1 < len(lines):
                    if bal <= 0:
                        if joined.endswith((";", "<;>")):
                            break
                        nxt_raw = lines[j_end + 1]
                        nxt_s = nxt_raw.strip()
                        if not nxt_s:
                            j_end += 1
                            continue
                        nxt_ind = len(nxt_raw[: len(nxt_raw) - len(nxt_raw.lstrip())].replace("\t", "    "))
                        is_arm_or_end = (
                            nxt_s.startswith(("·", "•", "|", ")", "}", "]", "⟩", "⦄"))
                            or bool(re.match(r"^(?:case'?\s+|next(?:\s|$|=>))", nxt_s))
                        )
                        if is_arm_or_end:
                            break
                        if joined.endswith(("⟩", "}")) and not nxt_s.startswith((";", "<;>")):
                            j_inner = _strip_outer_parens(joined)
                            if j_inner.startswith(("{", "⟨")):
                                break
                            if not nxt_s.startswith(("(", "{", "⟨", "⦃", "[", "?")) and _is_trivial_refine_ctor_with_holes(
                                joined,
                                struct_field_counts=struct_field_counts,
                                struct_param_names=struct_param_names,
                            ):
                                j_toks = _unwrap_ctor_app_tokens(j_inner)
                                exp_f = _ctor_head_field_count(j_toks[0], struct_field_counts) if j_toks else None
                                if exp_f is None:
                                    break
                                p_names = _ctor_param_names_for_head(j_toks[0], struct_param_names)
                                supplied_cnt = sum(
                                    1
                                    for t_j in j_toks[1:]
                                    if not (t_j.strip().startswith("{") and t_j.strip().endswith("}"))
                                    and _parse_named_ctor_arg(t_j)[0] not in p_names
                                )
                                if supplied_cnt >= exp_f:
                                    break
                        if nxt_ind < min_ref_cont_indent and not nxt_s.startswith(("(", "{", "⟨", "⦃", "[", ";", "<;>")):
                            break
                        if (
                            nxt_ind <= ref_col_indent
                            and not nxt_s.startswith(("(", "{", "⟨", "⦃", "[", "?", ";", "<;>"))
                            and _is_trivial_refine_ctor_with_holes(
                                joined,
                                struct_field_counts=struct_field_counts,
                                struct_param_names=struct_param_names,
                            )
                        ):
                            break
                    j_end += 1
                    nxt_part = lines[j_end].strip()
                    if not nxt_part:
                        continue
                    joined = (joined + "\n" + nxt_part).strip()
                    for ch in nxt_part:
                        if ch in "([{⦃⟨":
                            bal += 1
                        elif ch in ")]}⦄⟩" and bal > 0:
                            bal -= 1
                joined = _split_unmatched_closing_delims(joined, openers_before)
                # Split joined on top-level `;` or `<;>`
                pos_r = 0
                d_r = 0
                split_r: int | None = None
                while pos_r < len(joined):
                    if d_r == 0 and joined.startswith("<;>", pos_r):
                        split_r = pos_r
                        break
                    ch = joined[pos_r]
                    if ch in "([{⦃⟨":
                        d_r += 1
                    elif ch in ")]}⦄⟩" and d_r > 0:
                        d_r -= 1
                    elif d_r == 0 and ch == ";":
                        split_r = pos_r
                        break
                    pos_r += 1
                ref_expr = joined[:split_r].strip() if split_r is not None else joined
                if _is_trivial_refine_ctor_with_holes(
                    ref_expr,
                    struct_field_counts=struct_field_counts,
                    struct_param_names=struct_param_names,
                ):
                    after_ctor = joined[split_r:].strip() if split_r is not None else ""
                    last_stmt_idx = j_end
        if after_ctor is None:
            continue
        if after_ctor:
            if after_ctor.startswith((";", "<;>")):
                after_seq = _split_unmatched_closing_delims(
                    re.sub(r"^(?:<;>|;)\s*", "", after_ctor), openers_before
                )
                if after_seq:
                    if _is_trivial_tactic_seq(
                        after_seq,
                        struct_field_counts=struct_field_counts,
                        struct_param_names=struct_param_names,
                    ):
                        return True
                    continue
                # Empty `after_seq` (`constructor;` or `constructor <;>` at end of line): fall through to multiline subgoal collector
            else:
                continue
        elif m_ctor_app is not None and (m_ctor_kw is None or m_ctor_app[0] <= m_ctor_kw.start()):
            apply_rhs = re.sub(r"^apply\s+", "", line[m_ctor_app[0] : m_ctor_app[1]].strip())
            app_toks = _unwrap_ctor_app_tokens(_strip_type_ascription(apply_rhs))
            if len(app_toks) >= 2 and _CTOR_HEAD_RE.fullmatch(app_toks[0]):
                exp_f = _ctor_head_field_count(app_toks[0], struct_field_counts)
                p_names = _ctor_param_names_for_head(app_toks[0], struct_param_names)
                triv_field_cnt = 0
                for t_a in app_toks[1:]:
                    ts_a = t_a.strip()
                    if ts_a.startswith("{") and ts_a.endswith("}"):
                        continue
                    a_name, a_val = _parse_named_ctor_arg(ts_a)
                    if a_name is not None:
                        if a_name in p_names:
                            continue
                        if _is_trivial_proof_expr(
                            a_val,
                            _depth=1,
                            struct_field_counts=struct_field_counts,
                            struct_param_names=struct_param_names,
                        ):
                            triv_field_cnt += 1
                    elif _is_trivial_proof_expr(
                        ts_a,
                        _depth=1,
                        struct_field_counts=struct_field_counts,
                        struct_param_names=struct_param_names,
                    ):
                        triv_field_cnt += 1
                if exp_f is not None and triv_field_cnt >= exp_f:
                    return True
        # Multiline `constructor` / `apply *.mk` / `refine <ctor_with_holes>`: collect subgoal lines/blocks at >= ctor_eff_indent
        line_indent = len(line[: len(line) - len(line.lstrip())].replace("\t", "    "))
        m_bul = _LEADING_BULLET_RE.match(line.lstrip())
        ctor_eff_indent = line_indent + (m_bul.end() if m_bul else 0)
        sub_lines: list[str] = []
        for j in range(last_stmt_idx + 1, len(lines)):
            nxt = lines[j]
            nxt_s = nxt.strip()
            if not nxt_s:
                continue
            nxt_indent = len(nxt[: len(nxt) - len(nxt.lstrip())].replace("\t", "    "))
            if nxt_indent < ctor_eff_indent:
                break
            sub_lines.append(nxt_s)
        if sub_lines:
            joined_sub = _split_unmatched_closing_delims("\n".join(sub_lines), openers_before)
            if joined_sub and _is_trivial_tactic_seq(
                joined_sub,
                struct_field_counts=struct_field_counts,
                struct_param_names=struct_param_names,
            ):
                return True
    return False


_TRIV_CTOR_ATOM = (
    r"(?:(?:by\s+)?(?:rfl|trivial|True\.intro)(?![\w'»])"
    r"|\(\s*(?:by\s+)?(?:rfl|trivial|True\.intro)\s*\))"
)
_TRIV_CTOR_ELEM = rf"(?:{_TRIV_CTOR_ATOM}|⟨\s*{_TRIV_CTOR_ATOM}(?:\s*,\s*{_TRIV_CTOR_ATOM})*\s*⟩)"
_TRIVIAL_CTOR_CLOSURE_RE = re.compile(
    rf"(?:\b(?:exact|refine)\s+⟨\s*{_TRIV_CTOR_ELEM}(?:\s*,\s*{_TRIV_CTOR_ELEM})*\s*⟩"
    rf"|\b(?:exact|refine)\s+(?:[A-Za-z_][A-Za-z0-9_.]*)?\.mk(?:\s+{_TRIV_CTOR_ELEM})+(?=\s*(?:$|[;\n)\]\}}⦄⟩|]))"
    rf"|\bconstructor\s*(?:;|<;>)\s*(?:exact\s+)?(?:rfl|trivial|True\.intro)(?:\s*;\s*(?:exact\s+)?(?:rfl|trivial|True\.intro))*(?![\w'»]))"
)
STRUCTURAL_PROP_PROOF_RE = re.compile(
    r"\b(?:induction|cases|by_cases|fin_cases|noConfusion|Function\.bijective_id)\b"
)
_DECL_HEAD_NAME_RE = re.compile(
    r"(?m)^([ \t]*(?:@\[[^\n]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|example|instance|structure|class|inductive|axiom|opaque)\s+)"
    rf"({_LEAN_QUAL_IDENT})"
)
_LEAN_TERM_KEYWORDS = frozenset({
    "by", "fun", "let", "have", "match", "if", "do", "show", "suffices", "calc", "exact", "refine", "trivial", "rfl",
})
IMPORT_LINE_RE = re.compile(
    r"^\s*(?:(?:public|private|meta)\s+)*import(?:\s+all)?\s+([A-Za-z0-9_.«» ]+)\s*$",
    re.MULTILINE,
)


@dataclass
class ResolvedTarget:
    path: Path
    rel_path: str
    module: str | None
    exists: bool


def module_to_rel_path(module: str) -> str | None:
    parts = module.split(".")
    if not parts or any(not MODULE_SEGMENT_RE.fullmatch(p) for p in parts):
        return None
    if parts[0] == "InfoGeometry":
        return str(Path("lean", *parts).with_suffix(".lean"))
    return None


def path_to_module(repo_root: Path, path: Path) -> str | None:
    try:
        rel = path.resolve().relative_to((repo_root / "lean").resolve())
    except ValueError:
        return None
    if rel.suffix != ".lean":
        return None
    parts = rel.with_suffix("").parts
    if not parts or any(not MODULE_SEGMENT_RE.fullmatch(p) for p in parts):
        return None
    return ".".join(parts)


def resolve_targets(
    repo_root: Path,
    raw_targets: list[str],
) -> tuple[list[ResolvedTarget], list[str]]:
    """Resolve explicit .lean paths and dotted InfoGeometry.* module names."""
    resolved: list[ResolvedTarget] = []
    errors: list[str] = []
    seen: set[Path] = set()
    for raw in raw_targets:
        if raw.endswith(".lean") or "/" in raw or "\\" in raw:
            p = Path(raw)
            if not p.is_absolute():
                p = repo_root / p
            p_res = p.resolve()
            try:
                rel = str(p_res.relative_to(repo_root.resolve()))
            except ValueError:
                errors.append(f"Target path outside repository: {raw}")
                continue
            mod = path_to_module(repo_root, p_res)
            if p_res not in seen:
                seen.add(p_res)
                resolved.append(ResolvedTarget(path=p_res, rel_path=rel, module=mod, exists=p_res.is_file()))
        else:
            rel_mod = module_to_rel_path(raw)
            if rel_mod is None:
                errors.append(f"Invalid target module or path: {raw}")
                continue
            p_res = (repo_root / rel_mod).resolve()
            if p_res not in seen:
                seen.add(p_res)
                resolved.append(ResolvedTarget(path=p_res, rel_path=rel_mod, module=raw, exists=p_res.is_file()))
    return resolved, errors


def strip_lean_comments_and_strings(source: str) -> str:
    """Strip Lean line/block comments and string literals while preserving line count."""
    out: list[str] = []
    i = 0
    n = len(source)
    block_depth = 0
    in_line_comment = False
    in_string = False
    while i < n:
        ch = source[i]
        nxt = source[i + 1] if i + 1 < n else ""
        if in_line_comment:
            if ch == "\n":
                in_line_comment = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.append("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.append("  ")
                i += 2
            elif ch == "\n":
                out.append("\n")
                i += 1
            else:
                out.append(" ")
                i += 1
            continue
        if in_string:
            if ch == "\\" and i + 1 < n:
                out.append("  " if nxt != "\n" else " \n")
                i += 2
                continue
            if ch == '"':
                in_string = False
                out.append('"')
                i += 1
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        if ch == "-" and nxt == "-":
            in_line_comment = True
            out.append("  ")
            i += 2
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            out.append("  ")
            i += 2
            continue
        if ch == '"':
            in_string = True
            out.append('"')
            i += 1
            continue
        if ch == "'":
            prev_ch = source[i - 1] if i > 0 else ""
            if not (prev_ch.isalnum() or prev_ch in "_'»"):
                m_esc = re.match(r"^'\\(?:x[0-9A-Fa-f]{2}|u[0-9A-Fa-f]{4})'", source[i:])
                if m_esc:
                    span = len(m_esc.group(0))
                    out.append(" " * span)
                    i += span
                    continue
                if i + 3 < n and source[i + 1] == "\\" and source[i + 2] != "\n" and source[i + 3] == "'":
                    out.append("    ")
                    i += 4
                    continue
                if i + 2 < n and source[i + 1] not in ("'", "\\", "\n") and source[i + 2] == "'":
                    out.append("   ")
                    i += 3
                    continue
        out.append(ch)
        i += 1
    return "".join(out)


def extract_lean_imports(source: str) -> list[str]:
    clean = strip_lean_comments_and_strings(source)
    return [
        mod.replace("«", "").replace("»", "")
        for line in IMPORT_LINE_RE.findall(clean)
        for mod in line.split()
    ]


def extract_lean_declarations(source: str) -> set[str]:
    clean = strip_lean_comments_and_strings(source)
    return {m.group(1) for m in DECL_NAME_RE.finditer(clean)}


def extract_non_opaque_lean_declarations(source: str) -> set[str]:
    """Extract implemented Lean declarations, excluding `opaque` and `axiom`."""
    clean = strip_lean_comments_and_strings(source)
    return {m.group(1) for m in NON_OPAQUE_DECL_NAME_RE.finditer(clean)}


def check_lean_copyright_header(path: Path) -> bool:
    return path.read_text(encoding="utf-8").startswith(REQUIRED_LEAN_COPYRIGHT_HEADER)


_DECL_BOUNDARY_RE = re.compile(
    r"(?:@\[|(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+|"
    r"(?:theorem|lemma|example|def|abbrev|structure|class|inductive|instance|axiom|opaque|end|namespace|section|#)\b)"
)
_EQ_ARM_FORBIDDEN_WORD_RE = re.compile(r"^(?:fun|match|let|forall)(?![\w'»])")


def _match_eq_arm_arrow(clean: str, pipe_pos: int, *, is_line_start_pipe: bool) -> bool:
    """Return True iff `clean[pipe_pos] == '|'` opens an equation-style `| pat₁ | pat₂ =>` arm."""
    n = min(len(clean), pipe_pos + 500)
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    j = pipe_pos
    while j < n:
        ch = clean[j]
        if ch in open_ch:
            depth += 1
            j += 1
            continue
        if ch in close_ch:
            if depth > 0:
                depth -= 1
            j += 1
            continue
        if ch == "\n":
            if not is_line_start_pipe:
                return False
            if j + 1 < n and _DECL_BOUNDARY_RE.match(clean[j + 1 :]):
                return False
            j += 1
            continue
        if depth == 0:
            if clean.startswith("=>", j):
                return True
            if clean.startswith((":=", "->"), j) or ch in ("→", "↔", "=", "≠", "∀"):
                return False
            if (j == pipe_pos or not (clean[j - 1].isalnum() or clean[j - 1] in "_'»")) and _EQ_ARM_FORBIDDEN_WORD_RE.match(clean[j:]):
                return False
        j += 1
    return False


def _has_top_level_match_with(s: str) -> bool:
    """Return True iff `s` contains `match ... with` at bracket depth 0."""
    depth = 0
    seen_match = False
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    n = len(s)
    i = 0
    while i < n:
        ch = s[i]
        if ch == "«":
            i += 1
            while i < n and s[i] not in ("»", "\n"):
                i += 1
            if i < n and s[i] == "»":
                i += 1
            continue
        if ch in open_ch:
            depth += 1
        elif ch in close_ch:
            if depth > 0:
                depth -= 1
        elif depth == 0:
            prev_ok = i == 0 or not (s[i - 1].isalnum() or s[i - 1] in "_'«».")
            if prev_ok:
                if not seen_match and re.match(r"match(?![\w'»])", s[i:]):
                    seen_match = True
                    i += 5
                    continue
                if seen_match and re.match(r"with(?![\w'»])", s[i:]):
                    return True
        i += 1
    return False


def _preceded_by_kw(text: str, pos: int, kw: str) -> bool:
    j = pos - 1
    while j >= 0 and text[j].isspace():
        j -= 1
    start = j - len(kw) + 1
    if start < 0 or text[start : j + 1] != kw:
        return False
    return start == 0 or not (text[start - 1].isalnum() or text[start - 1] in "_'«».")


def _find_decl_return_type_and_split(
    clean: str,
    start_pos: int,
    *,
    allow_where: bool = False,
) -> tuple[str | None, int | None, bool]:
    """Scan from after `theorem|lemma|example|def|abbrev` to top-level `:=` (or `where` / equation `| ... =>`)."""
    n = min(len(clean), start_pos + 4000)
    depth = 0
    first_colon: int | None = None
    open_brackets = set("([{⦃")
    close_brackets = set(")]}⦄")
    let_have_stack: list[list[Any]] = []  # [state ("need_assign"|"in_val"|"if_let_assign"), end_indent, in_by_nonbrace]
    i = start_pos
    while i < n:
        ch = clean[i]
        if ch == "«":
            i += 1
            while i < n and clean[i] not in ("»", "\n"):
                i += 1
            if i < n and clean[i] == "»":
                i += 1
            continue
        if ch in open_brackets:
            depth += 1
            i += 1
            continue
        if ch in close_brackets:
            if depth > 0:
                depth -= 1
            i += 1
            continue
        if depth == 0:
            if first_colon is not None and (i == 0 or not (clean[i - 1].isalnum() or clean[i - 1] in "_'«».")):
                m_lh = re.match(r"(let|have)(?![\w'»])", clean[i:])
                if m_lh:
                    ls = clean.rfind("\n", 0, i) + 1
                    kw_col = len(clean[ls:i].replace("\t", "    "))
                    is_if_let = m_lh.group(1) == "let" and _preceded_by_kw(clean, i, "if")
                    let_have_stack.append(["if_let_assign" if is_if_let else "need_assign", kw_col, False])
                    i += len(m_lh.group(1))
                    continue
            if clean.startswith(":=", i):
                if let_have_stack:
                    # Pair with innermost `need_assign` / `if_let_assign` (or top if already assigned)
                    for idx_lh in range(len(let_have_stack) - 1, -1, -1):
                        if let_have_stack[idx_lh][0] in ("need_assign", "if_let_assign"):
                            del let_have_stack[idx_lh + 1 :]
                            break
                    if let_have_stack[-1][0] == "if_let_assign":
                        let_have_stack.pop()
                        i += 2
                        continue
                    let_have_stack[-1][0] = "in_val"
                    nl_pos = clean.find("\n", i + 2)
                    rest_line = clean[i + 2 : (n if nl_pos == -1 else nl_pos)].strip()
                    let_have_stack[-1][2] = bool(re.match(r"^by(?![\w'»])(?!\s*\{)", rest_line))
                    ls = clean.rfind("\n", 0, i) + 1
                    cur_ind = len(clean[ls : ls + len(clean[ls:i]) - len(clean[ls:i].lstrip())].replace("\t", "    "))
                    if not rest_line and nl_pos != -1:
                        p = nl_pos + 1
                        while p < n:
                            nxt_nl = clean.find("\n", p)
                            nxt_line = clean[p:] if nxt_nl == -1 else clean[p:nxt_nl]
                            if nxt_line.strip():
                                nxt_ind = len(nxt_line[: len(nxt_line) - len(nxt_line.lstrip())].replace("\t", "    "))
                                nxt_s = nxt_line.strip()
                                if nxt_ind > cur_ind:
                                    if nxt_s == "by" and nxt_nl != -1:
                                        let_have_stack[-1][2] = True
                                        p2 = nxt_nl + 1
                                        tactic_ind: int | None = None
                                        while p2 < n:
                                            t_nl = clean.find("\n", p2)
                                            t_line = clean[p2:] if t_nl == -1 else clean[p2:t_nl]
                                            if t_line.strip():
                                                tactic_ind = len(
                                                    t_line[: len(t_line) - len(t_line.lstrip())].replace("\t", "    ")
                                                )
                                                break
                                            if t_nl == -1:
                                                break
                                            p2 = t_nl + 1
                                        if tactic_ind is not None and tactic_ind > nxt_ind:
                                            let_have_stack[-1][1] = max(let_have_stack[-1][1], nxt_ind)
                                        else:
                                            let_have_stack[-1][1] = max(let_have_stack[-1][1], nxt_ind - 1)
                                    elif nxt_s.startswith("by "):
                                        let_have_stack[-1][2] = not bool(re.match(r"^by\s*\{", nxt_s))
                                        let_have_stack[-1][1] = max(let_have_stack[-1][1], nxt_ind)
                                    else:
                                        let_have_stack[-1][1] = max(let_have_stack[-1][1], nxt_ind - 1)
                                break
                            if nxt_nl == -1:
                                break
                            p = nxt_nl + 1
                    elif rest_line == "by" and nl_pos != -1:
                        p = nl_pos + 1
                        while p < n:
                            nxt_nl = clean.find("\n", p)
                            nxt_line = clean[p:] if nxt_nl == -1 else clean[p:nxt_nl]
                            if nxt_line.strip():
                                tactic_ind = len(nxt_line[: len(nxt_line) - len(nxt_line.lstrip())].replace("\t", "    "))
                                if tactic_ind > cur_ind:
                                    let_have_stack[-1][1] = max(let_have_stack[-1][1], tactic_ind - 1)
                                break
                            if nxt_nl == -1:
                                break
                            p = nxt_nl + 1
                    i += 2
                    continue
                ret = clean[first_colon + 1 : i].strip() if first_colon is not None else None
                return ret, i + 2, False
            if ch == ";" and let_have_stack and let_have_stack[-1][0] == "in_val" and not let_have_stack[-1][2]:
                let_have_stack.pop()
                i += 1
                continue
            if (
                allow_where
                and (i == 0 or not (clean[i - 1].isalnum() or clean[i - 1] in "_'«»"))
                and re.match(r"where(?![\w'»])", clean[i:])
            ):
                ret = clean[first_colon + 1 : i].strip() if first_colon is not None else None
                return ret, i + 5, True
            if (
                first_colon is not None
                and ch == "|"
                and (i == 0 or clean[i - 1] not in ("<", "|"))
                and not clean.startswith("||", i)
                and not clean.startswith("|>", i)
                and not _has_top_level_match_with(clean[first_colon:i])
            ):
                line_start = clean.rfind("\n", 0, i) + 1
                is_line_start_pipe = not clean[line_start:i].strip()
                if _match_eq_arm_arrow(clean, i, is_line_start_pipe=is_line_start_pipe):
                    ret = clean[first_colon + 1 : i].strip()
                    return ret, i, False
            if ch == ":" and first_colon is None:
                first_colon = i
                i += 1
                continue
            if ch == "\n" and i + 1 < n:
                if _DECL_BOUNDARY_RE.match(clean[i + 1 :]):
                    break
                if let_have_stack and let_have_stack[-1][0] == "in_val":
                    p = i + 1
                    while p < n:
                        nxt_nl = clean.find("\n", p)
                        nxt_line = clean[p:] if nxt_nl == -1 else clean[p:nxt_nl]
                        if nxt_line.strip():
                            nxt_ind = len(nxt_line[: len(nxt_line) - len(nxt_line.lstrip())].replace("\t", "    "))
                            while let_have_stack and let_have_stack[-1][0] == "in_val" and nxt_ind <= let_have_stack[-1][1]:
                                let_have_stack.pop()
                            break
                        if nxt_nl == -1:
                            break
                        p = nxt_nl + 1
        i += 1
    return None, None, False


def _strip_outer_parens(expr: str) -> str:
    s = expr.strip()
    while s.startswith("(") and s.endswith(")"):
        depth = 0
        matched_outer = True
        for idx, ch in enumerate(s):
            if ch in "([{⦃":
                depth += 1
            elif ch in ")]}⦄":
                depth -= 1
                if depth == 0 and idx < len(s) - 1:
                    matched_outer = False
                    break
        if not matched_outer or depth != 0:
            break
        s = s[1:-1].strip()
    return s


_LET_HAVE_CONT_END_RE = re.compile(
    r"(?:\b(?:by|fun|match|if|then|else|where|do)\b|:=|[+\-*/=<>∧∨↔→,(^%])\s*$"
)
_LET_HAVE_CONT_START_RE = re.compile(
    r"^(?:\b(?:else|then|in|where|with)\b|<<<|>>>|\^\^\^|&&&|\|\|\||&&|\|\||==|!=|<=|>=|::|\+\+|\|>|<\||->|:=|[|+\-*/=<>∧∨↔→∘×≤≥≠^%])"
)


def _strip_leading_let_have(s: str) -> str | None:
    """If `s` starts with a `let`/`have` binding, strip its `:= val (; | newline)` prefix and return the body."""
    m_lh = re.match(r"^(?:let|have)(?![\w'»])", s)
    if not m_lh:
        return None
    n = len(s)
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    stack: list[list[Any]] = [["need_assign", False]]
    first_assign_end: int | None = None
    i = m_lh.end()
    while i < n:
        ch = s[i]
        if ch == "«":
            i += 1
            while i < n and s[i] not in ("»", "\n"):
                i += 1
            if i < n and s[i] == "»":
                i += 1
            continue
        if ch in open_ch:
            depth += 1
        elif ch in close_ch and depth > 0:
            depth -= 1
        elif depth == 0:
            if i == 0 or not (s[i - 1].isalnum() or s[i - 1] in "_'«»."):
                m_inner_lh = re.match(r"(let|have)(?![\w'»])", s[i:])
                if m_inner_lh:
                    is_if_let = m_inner_lh.group(1) == "let" and _preceded_by_kw(s, i, "if")
                    stack.append(["if_let_assign" if is_if_let else "need_assign", False])
                    i += len(m_inner_lh.group(1))
                    continue
            if s.startswith(":=", i):
                for idx_s in range(len(stack) - 1, -1, -1):
                    if stack[idx_s][0] in ("need_assign", "if_let_assign"):
                        del stack[idx_s + 1 :]
                        break
                if stack and stack[-1][0] == "if_let_assign":
                    stack.pop()
                    i += 2
                    continue
                in_by_nonbrace = bool(re.match(r"^\s*by(?![\w'»])(?!\s*\{)", s[i + 2 :]))
                stack[-1] = ["in_val", in_by_nonbrace]
                if len(stack) == 1 and first_assign_end is None:
                    first_assign_end = i + 2
                i += 2
                continue
            if ch == ";" and stack and stack[-1][0] == "in_val" and not stack[-1][1]:
                stack.pop()
                if not stack:
                    return s[i + 1 :].strip()
        i += 1
    if first_assign_end is None:
        return None
    # Fallback for newline-separated `let x := val\n  body` without `;`
    nl = s.find("\n", first_assign_end)
    if nl == -1:
        return None
    val_inline = s[first_assign_end:nl].strip()
    b_depth_nl = 0
    for c in s[:nl]:
        if c in open_ch:
            b_depth_nl += 1
        elif c in close_ch and b_depth_nl > 0:
            b_depth_nl -= 1
    first_nxt_s = ""
    first_nxt_ind = 0
    after_first_pos = n
    p_check = nl + 1
    while p_check < n:
        c_nl = s.find("\n", p_check)
        c_raw = s[p_check:] if c_nl == -1 else s[p_check:c_nl]
        c_line = c_raw.strip()
        if c_line:
            first_nxt_s = c_line
            first_nxt_ind = len(c_raw[: len(c_raw) - len(c_raw.lstrip())].replace("\t", "    "))
            after_first_pos = n if c_nl == -1 else (c_nl + 1)
            break
        if c_nl == -1:
            break
        p_check = c_nl + 1
    min_later_ind: int | None = None
    if b_depth_nl == 0 and first_nxt_s and after_first_pos < n:
        later_depth = 0
        for c in s[nl + 1 : after_first_pos]:
            if c in open_ch:
                later_depth += 1
            elif c in close_ch and later_depth > 0:
                later_depth -= 1
        p_lat = after_first_pos
        while p_lat < n:
            l_nl = s.find("\n", p_lat)
            l_raw = s[p_lat:] if l_nl == -1 else s[p_lat:l_nl]
            l_s = l_raw.strip()
            if l_s and later_depth == 0:
                l_ind = len(l_raw[: len(l_raw) - len(l_raw.lstrip())].replace("\t", "    "))
                if min_later_ind is None or l_ind < min_later_ind:
                    min_later_ind = l_ind
                # Stop before smaller-indented continuations of a multi-line `let` body (e.g. `∀ _ : Nat,\n True`)
                if (
                    l_ind < first_nxt_ind
                    and not _LET_HAVE_CONT_START_RE.match(l_s)
                    and (
                        bool(_LET_HAVE_CONT_END_RE.search(l_s))
                        or bool(re.match(r"^(?:∀|∃|forall\b|exists\b|let\b|have\b)", l_s))
                    )
                ):
                    break
            for c in l_raw:
                if c in open_ch:
                    later_depth += 1
                elif c in close_ch and later_depth > 0:
                    later_depth -= 1
            if l_nl == -1:
                break
            p_lat = l_nl + 1
    has_later_smaller_indent = min_later_ind is not None and min_later_ind < first_nxt_ind
    if (
        val_inline
        and not _LET_HAVE_CONT_END_RE.search(val_inline)
        and b_depth_nl == 0
        and not (first_nxt_s and _LET_HAVE_CONT_START_RE.match(first_nxt_s))
        and not has_later_smaller_indent
    ):
        rest = s[nl + 1 :].strip()
        return rest if rest else None
    ends_with_by = bool(re.search(r"\bby$", val_inline))
    starts_with_bare_by = bool(not val_inline and first_nxt_s and re.fullmatch(r"by", first_nxt_s))
    use_min_indent = (not ends_with_by) and (not starts_with_bare_by) and has_later_smaller_indent
    p = nl + 1
    val_indent: int | None = None
    seen_bare_by = False
    prev_complete = True
    b_depth = b_depth_nl
    while p < n:
        nxt_nl = s.find("\n", p)
        line = s[p:] if nxt_nl == -1 else s[p:nxt_nl]
        line_s = line.strip()
        if line_s:
            ind = len(line[: len(line) - len(line.lstrip())].replace("\t", "    "))
            if starts_with_bare_by and not seen_bare_by:
                seen_bare_by = True
            elif val_indent is None:
                val_indent = ind
            elif b_depth == 0:
                if use_min_indent and min_later_ind is not None:
                    if ind <= min_later_ind and prev_complete and not _LET_HAVE_CONT_START_RE.match(line_s):
                        return s[p:].strip()
                else:
                    if ind < val_indent:
                        return s[p:].strip()
                    if (
                        not ends_with_by
                        and not starts_with_bare_by
                        and ind == val_indent
                        and prev_complete
                        and not _LET_HAVE_CONT_START_RE.match(line_s)
                    ):
                        return s[p:].strip()
            prev_complete = not _LET_HAVE_CONT_END_RE.search(line_s)
        for c in line:
            if c in open_ch:
                b_depth += 1
            elif c in close_ch and b_depth > 0:
                b_depth -= 1
        if nxt_nl == -1:
            break
        p = nxt_nl + 1
    return None


def _extract_if_then_else_branches(expr: str) -> tuple[str, str] | None:
    """If `expr` is a top-level `if ... then ... else ...` expression, return `(then_branch, else_branch)`."""
    s = _strip_outer_parens(expr)
    if not re.match(r"^if(?=\s|[({\[⦃«])", s):
        return None
    n = len(s)
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    then_end: int | None = None
    else_start: int | None = None
    else_end: int | None = None
    if_depth = 0
    i = 0
    while i < n:
        ch = s[i]
        if ch == "«":
            i += 1
            while i < n and s[i] not in ("»", "\n"):
                i += 1
            if i < n and s[i] == "»":
                i += 1
            continue
        if ch in open_ch:
            depth += 1
        elif ch in close_ch and depth > 0:
            depth -= 1
        elif depth == 0 and (i == 0 or not (s[i - 1].isalnum() or s[i - 1] in "_'«».")):
            m_kw = re.match(r"(if|then|else)(?![\w'»])", s[i:])
            if m_kw:
                kw = m_kw.group(1)
                if kw == "if":
                    if_depth += 1
                elif kw == "then" and if_depth == 1 and then_end is None:
                    then_end = i + 4
                elif kw == "else":
                    if if_depth == 1 and then_end is not None and else_start is None:
                        else_start = i
                        else_end = i + 4
                        break
                    elif if_depth > 1:
                        if_depth -= 1
                i += len(kw)
                continue
        i += 1
    if then_end is None or else_start is None or else_end is None:
        return None
    t_br = s[then_end:else_start].strip()
    e_br = s[else_end:].strip()
    return (t_br, e_br) if (t_br and e_br) else None


def _strip_leading_forall_and_arrow(expr: str) -> str:
    """Peel outer parens, leading `let`/`have` bindings, `∀ ...,` / `forall ...,` binders, and `... →` / `->` domains."""
    s = expr.strip()
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    while True:
        prev = s
        s = _strip_outer_parens(s)
        peeled_lh = _strip_leading_let_have(s)
        if peeled_lh is not None:
            s = peeled_lh
            continue
        m_forall = re.match(r"^(?:∀|forall(?=\s|[({\[⦃«]))", s)
        if m_forall:
            comma_idx = _forall_comma_map(s, _bracket_depths(s)).get(0)
            if comma_idx is not None:
                s = s[comma_idx + 1 :].strip()
                continue
        depth = 0
        arrow_end: int | None = None
        i = 0
        while i < len(s):
            ch = s[i]
            if ch in open_ch:
                depth += 1
            elif ch in close_ch and depth > 0:
                depth -= 1
            elif depth == 0:
                if ch == "→":
                    arrow_end = i + 1
                    break
                if s.startswith("->", i):
                    arrow_end = i + 2
                    break
            i += 1
        if arrow_end is not None:
            s = s[arrow_end:].strip()
            continue
        if s == prev:
            break
    return _strip_outer_parens(s)


def _is_vacuous_true_type(ret_type: str) -> bool:
    s = ret_type.strip()
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    while True:
        prev = s
        s = _strip_leading_forall_and_arrow(s)
        branches = _extract_if_then_else_branches(s)
        if branches is not None:
            return _is_vacuous_true_type(branches[0]) and _is_vacuous_true_type(branches[1])
        depth = 0
        for idx, ch in enumerate(s):
            if ch in open_ch:
                depth += 1
            elif ch in close_ch and depth > 0:
                depth -= 1
            elif depth == 0 and ch == ":" and not s.startswith(":=", idx):
                if re.fullmatch(r"\s*(?:Prop|Sort\s+0)\s*", s[idx + 1 :]):
                    s = s[:idx].strip()
                    break
        s = _strip_outer_parens(s)
        if s == prev:
            break
    return bool(re.fullmatch(r"True", s))


def _extract_struct_ctor_names(body: str) -> tuple[str, ...]:
    m = re.match(rf"^\s*(?:(?:private|protected)\s+)?({_LEAN_IDENT_SEG})\s*::", body)
    if m:
        ctor = lean_short_name(m.group(1))
        return (ctor,) if ctor else ("mk",)
    return ("mk",)


_FIELD_CONT_END_RE = re.compile(r"(?:->|:=|[:→↔∧∨×,]|\b(?:by|where|with|do|then|else)\b)\s*$")
_STRUCT_FIELD_NONIDENT_KEYWORDS = frozenset({
    "by", "fun", "match", "if", "do", "show", "calc", "where", "deriving", "extends", "with", "then", "else",
})


def _strip_top_level_default_assign(s: str) -> str:
    """Strip trailing top-level `:= ...` default value from a structure field type."""
    depth = 0
    pending_lh = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    i = 0
    n = len(s)
    while i < n:
        ch = s[i]
        if ch == "«":
            i += 1
            while i < n and s[i] not in ("»", "\n"):
                i += 1
            if i < n and s[i] == "»":
                i += 1
            continue
        if ch in open_ch:
            depth += 1
        elif ch in close_ch and depth > 0:
            depth -= 1
        elif depth == 0:
            if i == 0 or not (s[i - 1].isalnum() or s[i - 1] in "_'«»."):
                m_lh = re.match(r"(let|have)(?![\w'»])", s[i:])
                if m_lh and not (m_lh.group(1) == "let" and _preceded_by_kw(s, i, "if")):
                    pending_lh += 1
                    i += len(m_lh.group(1))
                    continue
            if s.startswith(":=", i):
                if pending_lh > 0:
                    pending_lh -= 1
                    i += 2
                    continue
                return s[:i].strip()
        i += 1
    return s.strip()


def _extract_struct_field_types(body: str, is_assign_syntax: bool) -> list[tuple[str, str]]:
    """Extract `[(field_name, field_type_str), ...]` from a `structure`/`class` body."""
    b = re.sub(rf"^\s*(?:(?:private|protected)\s+)?{_LEAN_IDENT_SEG}\s*::", "", body)
    n = len(b)
    fields: list[tuple[str, str]] = []
    at_field_start = True
    field_indent: int | None = None
    open_b = set("([{⦃⟨")
    close_b = set(")]}⦄⟩")
    pairs = {"(": ")", "{": "}", "[": "]"}
    depth = 0
    line_idx = 0
    line_start = 0
    last_nonempty_line = ""
    last_nonempty_indent = 0
    pending_vis_indent: int | None = None
    pending_unparen: tuple[list[str], int] | None = None
    pending_let_semi = 0
    i = 0

    def _flush_pending(end_pos: int) -> None:
        nonlocal pending_unparen, pending_let_semi
        pending_let_semi = 0
        if pending_unparen is not None:
            p_toks, ty_start = pending_unparen
            ty_str = _strip_top_level_default_assign(b[ty_start:end_pos])
            for t in p_toks:
                fields.append((t, ty_str))
            pending_unparen = None

    def _valid_field_toks(raw_lhs: str) -> list[str] | None:
        toks = raw_lhs.strip().split()
        if toks and toks[0] in ("private", "protected"):
            toks = toks[1:]
        if (
            toks
            and all(
                _LEAN_IDENT_SEG_RE.fullmatch(t) and t not in _STRUCT_FIELD_NONIDENT_KEYWORDS and t != "_"
                for t in toks
            )
        ):
            return toks
        return None

    def _record_field_indent(cur_ind: int) -> None:
        nonlocal field_indent
        if not is_assign_syntax or line_idx > 0 or cur_ind >= 2:
            field_indent = cur_ind if field_indent is None else min(field_indent, cur_ind)

    while i < n:
        ch = b[i]
        if ch == "\n":
            raw_cur = b[line_start:i]
            prev_line = raw_cur.strip()
            if prev_line:
                last_nonempty_line = prev_line
                last_nonempty_indent = len(raw_cur[: len(raw_cur) - len(raw_cur.lstrip())].replace("\t", "    "))
            i += 1
            line_idx += 1
            line_start = i
            if depth == 0 and not at_field_start:
                p = i
                while p < n:
                    nxt_nl = b.find("\n", p)
                    nxt_end = n if nxt_nl == -1 else nxt_nl
                    nxt_line = b[p:nxt_end]
                    if nxt_line.strip():
                        nxt_indent = len(nxt_line[: len(nxt_line) - len(nxt_line.lstrip())].replace("\t", "    "))
                        indent_ok = (
                            nxt_indent <= field_indent
                            if field_indent is not None
                            else nxt_indent <= last_nonempty_indent
                        )
                        if indent_ok and not _FIELD_CONT_END_RE.search(last_nonempty_line):
                            _flush_pending(p)
                            at_field_start = True
                        break
                    if nxt_nl == -1:
                        break
                    p = nxt_nl + 1
            continue

        if at_field_start:
            if ch in (" ", "\t"):
                i += 1
                continue
            cur_indent = len(b[line_start:i].replace("\t", "    "))
            m_vis = re.match(r"(?:private|protected)\s+(?=[(\[{])", b[i:])
            if m_vis:
                if pending_vis_indent is None:
                    pending_vis_indent = cur_indent
                i += m_vis.end()
                continue
            eff_indent = pending_vis_indent if pending_vis_indent is not None else cur_indent
            pending_vis_indent = None
            if ch in pairs:
                b_depth = 1
                j = i + 1
                while j < n and b_depth > 0:
                    if b[j] == "«":
                        j += 1
                        while j < n and b[j] not in ("»", "\n"):
                            j += 1
                        if j < n and b[j] == "»":
                            j += 1
                        continue
                    if b[j] in open_b:
                        b_depth += 1
                    elif b[j] in close_b:
                        b_depth -= 1
                    j += 1
                if b_depth == 0:
                    after_j = b[j:].lstrip()
                    if after_j.startswith(("→", "->")):
                        at_field_start = False
                        i = j
                        continue
                    inner = b[i + 1 : j - 1]
                    colon_idx = _find_top_level_colon(inner)
                    if colon_idx is not None:
                        toks = _valid_field_toks(inner[:colon_idx])
                        if toks is not None:
                            _record_field_indent(eff_indent)
                            ty_str = _strip_top_level_default_assign(inner[colon_idx + 1 :])
                            for t in toks:
                                fields.append((t, ty_str))
                            i = j
                            continue
                at_field_start = False
                i = j
                continue

            # Unparenthesized field on current line
            line_end = b.find("\n", i)
            if line_end == -1:
                line_end = n
            scan = i
            scan_depth = 0
            colon_pos: int | None = None
            while scan < line_end:
                sc = b[scan]
                if sc == "«":
                    scan += 1
                    while scan < line_end and b[scan] != "»":
                        scan += 1
                    if scan < line_end and b[scan] == "»":
                        scan += 1
                    continue
                if sc in open_b:
                    scan_depth += 1
                elif sc in close_b and scan_depth > 0:
                    scan_depth -= 1
                elif scan_depth == 0:
                    if b.startswith(":=", scan):
                        break
                    if sc == ":":
                        colon_pos = scan
                        break
                scan += 1
            if colon_pos is not None:
                toks = _valid_field_toks(b[i:colon_pos])
                if toks is not None:
                    _record_field_indent(eff_indent)
                    pending_unparen = (toks, colon_pos + 1)
                    at_field_start = False
                    i = colon_pos + 1
                    continue
            at_field_start = False
            i = line_end
            continue

        # Not at_field_start: track bracket depth & guillemets until next top-level newline
        if ch == "«":
            i += 1
            while i < n and b[i] not in ("»", "\n"):
                i += 1
            if i < n and b[i] == "»":
                i += 1
            continue
        if ch in open_b:
            depth += 1
        elif ch in close_b and depth > 0:
            depth -= 1
        elif depth == 0:
            if i == 0 or not (b[i - 1].isalnum() or b[i - 1] in "_'«»."):
                m_lh = re.match(r"(let|have)(?![\w'»])", b[i:])
                if m_lh and not (m_lh.group(1) == "let" and _preceded_by_kw(b, i, "if")):
                    pending_let_semi += 1
                    i += len(m_lh.group(1))
                    continue
            if ch == ";":
                if pending_let_semi > 0:
                    pending_let_semi -= 1
                else:
                    _flush_pending(i)
                    at_field_start = True
        i += 1
    _flush_pending(n)
    return fields


def _extract_struct_fields(body: str, is_assign_syntax: bool) -> list[str]:
    return [name for name, _ in _extract_struct_field_types(body, is_assign_syntax)]


def _split_top_level_commas(s: str) -> list[str]:
    """Split `s` on `,` outside brackets and `«...»` guillemets."""
    parts: list[str] = []
    cur: list[str] = []
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    i = 0
    n = len(s)
    while i < n:
        ch = s[i]
        if ch == "«":
            cur.append(ch)
            i += 1
            while i < n and s[i] not in ("»", "\n"):
                cur.append(s[i])
                i += 1
            if i < n and s[i] == "»":
                cur.append("»")
                i += 1
            continue
        if ch in open_ch:
            depth += 1
        elif ch in close_ch and depth > 0:
            depth -= 1
        elif depth == 0 and ch == ",":
            seg = "".join(cur).strip()
            if seg:
                parts.append(seg)
            cur.clear()
            i += 1
            continue
        cur.append(ch)
        i += 1
    tail = "".join(cur).strip()
    if tail:
        parts.append(tail)
    return parts


def _extract_extends_parents(extends_tail: str) -> tuple[list[str], list[str]]:
    """Parse `extends [toP :] Parent₁ ..., Parent₂ ...` into `(parent_names, proj_names)`."""
    parents: list[str] = []
    proj_names: list[str] = []
    for chunk in _split_top_level_commas(extends_tail):
        c_strip = chunk.strip()
        if not c_strip:
            continue
        custom_proj: str | None = None
        c_colon = _find_top_level_colon(c_strip)
        if c_colon is not None and not c_strip.startswith(":=", c_colon):
            cand_proj = c_strip[:c_colon].strip()
            if _LEAN_IDENT_SEG_RE.fullmatch(cand_proj):
                custom_proj = cand_proj
                c_strip = c_strip[c_colon + 1 :].strip()
        m_par = re.match(rf"^\s*({_LEAN_QUAL_IDENT})", c_strip)
        if m_par:
            par = m_par.group(1)
            parents.append(par)
            proj_names.append(custom_proj if custom_proj else f"to{lean_short_name(par)}")
    return parents, proj_names


def _parse_prop_structure_header(
    header_no_kw: str,
    known_prop_structs: dict[str, set[str]],
) -> tuple[bool, bool, list[str], list[str]]:
    """Return `(is_prop, is_parameterized, parent_names, parent_proj_names)` for a `structure`/`class` header."""
    h_pre = re.sub(r"^\s*\.\{[^}]*\}", "", header_no_kw).strip()
    m_ext = re.search(r"\bextends\b([\s\S]*)$", h_pre)
    head_before_ext = h_pre[: m_ext.start()] if m_ext else h_pre
    colon_idx = _find_top_level_colon(head_before_ext)
    if colon_idx is not None:
        after_colon = head_before_ext[colon_idx + 1 :]
        if not re.match(r"^\s*(?:Prop|Sort\s+0)(?=\s|$)", after_colon):
            return False, False, [], []
        param_part = head_before_ext[:colon_idx].strip()
        is_param = bool(param_part)
        parents, proj_names = _extract_extends_parents(m_ext.group(1)) if m_ext else ([], [])
        return True, is_param, parents, proj_names

    if not m_ext:
        return False, False, [], []
    param_part = head_before_ext.strip()
    parents, proj_names = _extract_extends_parents(m_ext.group(1))
    if not parents:
        return False, False, [], []
    if all((p in known_prop_structs or lean_short_name(p) in known_prop_structs) for p in parents):
        return True, bool(param_part), parents, proj_names
    return False, False, [], []


_STRUCT_HEADER_STOP_RE = re.compile(
    r"[ \t]*(?:@\[|(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+|"
    r"(?:theorem|lemma|example|def|abbrev|structure|class|inductive|instance|axiom|opaque|end|namespace|section|#)\b)"
)


def _iter_prop_structures(clean: str) -> list[tuple[str, str, str, bool, bool, list[str], list[str]]]:
    """Find single-line and multiline `: Prop` (explicit or inherited via `extends`) structure/class definitions."""
    results: list[tuple[str, str, str, bool, bool, list[str], list[str]]] = []
    known_prop_structs: dict[str, set[str]] = {}
    open_brackets = set("([{⦃")
    close_brackets = set(")]}⦄")
    n = len(clean)
    for st in PROP_STRUCT_HEAD_START_RE.finditer(clean):
        type_name = st.group(1)
        short_name = lean_short_name(type_name)
        i = st.end()
        limit = min(n, i + 4000)
        depth = 0
        saw_explicit_body = False
        while i < limit:
            ch = clean[i]
            if ch in open_brackets:
                depth += 1
                i += 1
                continue
            if ch in close_brackets:
                if depth > 0:
                    depth -= 1
                i += 1
                continue
            if depth == 0:
                if clean.startswith(":=", i):
                    saw_explicit_body = True
                    assign_end = i + 2
                    header = clean[st.end() : assign_end]
                    is_prop, is_param, parents, parent_projs = _parse_prop_structure_header(
                        header[:-2], known_prop_structs
                    )
                    if is_prop:
                        line_end = clean.find("\n", assign_end)
                        if line_end == -1:
                            body = clean[assign_end:]
                        else:
                            pos = line_end + 1
                            while pos < n:
                                nxt_nl = clean.find("\n", pos)
                                line = clean[pos:] if nxt_nl == -1 else clean[pos:nxt_nl]
                                if line.strip() == "" or line[0] in (" ", "\t"):
                                    if nxt_nl == -1:
                                        pos = n
                                        break
                                    pos = nxt_nl + 1
                                else:
                                    break
                            body = clean[assign_end:pos]
                        local_fields = set(_extract_struct_fields(body, True))
                        all_fields = set(local_fields)
                        for par in parents:
                            all_fields.update(known_prop_structs.get(par) or known_prop_structs.get(lean_short_name(par), set()))
                        known_prop_structs[type_name] = all_fields
                        if short_name not in known_prop_structs:
                            known_prop_structs[short_name] = all_fields
                        results.append((type_name, header, body, True, is_param, parents, parent_projs))
                    break
                if (
                    (i == 0 or not (clean[i - 1].isalnum() or clean[i - 1] in "_'«»"))
                    and re.match(r"where(?![\w'»])", clean[i:])
                ):
                    saw_explicit_body = True
                    where_end = i + 5
                    header = clean[st.end() : where_end]
                    is_prop, is_param, parents, parent_projs = _parse_prop_structure_header(
                        header[:-5], known_prop_structs
                    )
                    if is_prop:
                        line_end = clean.find("\n", where_end)
                        if line_end == -1:
                            inline_head = clean[where_end:].strip()
                            body_text = ("  " + inline_head) if inline_head else ""
                        else:
                            inline_head = clean[where_end:line_end].strip()
                            body_start = line_end + 1
                            pos = body_start
                            while pos < n:
                                nxt_nl = clean.find("\n", pos)
                                line = clean[pos:] if nxt_nl == -1 else clean[pos:nxt_nl]
                                if line.strip() == "" or line[0] in (" ", "\t"):
                                    if nxt_nl == -1:
                                        pos = n
                                        break
                                    pos = nxt_nl + 1
                                else:
                                    break
                            body_text = clean[body_start:pos]
                            if inline_head:
                                body_text = f"  {inline_head}\n{body_text}"
                        local_fields = set(_extract_struct_fields(body_text, False))
                        all_fields = set(local_fields)
                        for par in parents:
                            all_fields.update(known_prop_structs.get(par) or known_prop_structs.get(lean_short_name(par), set()))
                        known_prop_structs[type_name] = all_fields
                        if short_name not in known_prop_structs:
                            known_prop_structs[short_name] = all_fields
                        if body_text.strip() or all_fields:
                            results.append((type_name, header, body_text, False, is_param, parents, parent_projs))
                    break
                if ch == "\n" and i + 1 < limit:
                    if _STRUCT_HEADER_STOP_RE.match(clean[i + 1 :]):
                        break
            i += 1
        if not saw_explicit_body:
            header = clean[st.end() : i]
            is_prop, is_param, parents, parent_projs = _parse_prop_structure_header(header, known_prop_structs)
            if is_prop and parents:
                all_fields: set[str] = set()
                for par in parents:
                    all_fields.update(known_prop_structs.get(par) or known_prop_structs.get(lean_short_name(par), set()))
                known_prop_structs[type_name] = all_fields
                if short_name not in known_prop_structs:
                    known_prop_structs[short_name] = all_fields
                if all_fields:
                    results.append((type_name, header, "", False, is_param, parents, parent_projs))
    return results


def scan_native_decide_and_vacuous_true(source: str) -> list[str]:
    clean = strip_lean_comments_and_strings(source)
    findings: list[str] = []
    for idx, line in enumerate(clean.splitlines(), 1):
        if NATIVE_DECIDE_RE.search(line):
            findings.append(f"L{idx}: forbidden `native_decide`")
        if FORBIDDEN_KERNEL_BYPASS_RE.search(line):
            findings.append(f"L{idx}: forbidden `Lean.ofReduceBool`/`Lean.trustCompiler`")
    for m in VACUOUS_DECL_START_RE.finditer(clean):
        ret_type, eq_pos, _ = _find_decl_return_type_and_split(clean, m.end(), allow_where=False)
        if ret_type is not None and eq_pos is not None and _is_vacuous_true_type(ret_type):
            line_no = clean[: m.start()].count("\n") + 1
            findings.append(f"L{line_no}: vacuous `: True` {m.group(1)} wrapper")
    return findings


def _count_anon_ctor_args(rhs: str) -> int:
    """Return the maximum arity among all balanced `⟨...⟩` anonymous constructor literals in `rhs`."""
    best = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    n = len(rhs)
    pos = 0
    while pos < n:
        start = rhs.find("⟨", pos)
        if start == -1:
            break
        depth = 0
        commas = 0
        has_content = False
        matched = False
        for idx in range(start, n):
            ch = rhs[idx]
            if ch in open_ch:
                depth += 1
            elif ch in close_ch:
                depth -= 1
                if depth == 0:
                    count = (commas + 1) if has_content else 0
                    if count > best:
                        best = count
                    pos = idx + 1
                    matched = True
                    break
            elif depth == 1 and ch == ",":
                commas += 1
            elif depth == 1 and not ch.isspace():
                has_content = True
        if not matched:
            pos = start + 1
    return best


_SUBBLOCK_KW_RE = re.compile(r"\b(?:have|let|suffices)\b")
_LEADING_BULLET_RE = re.compile(r"^(?:(?:·|•)\s*|(?:[*+-])\s+)*")
_SUBBLOCK_CONT_END_RE = re.compile(r"(?:\b(?:by|with|do|calc|then|else|where)|:=|[(\[{⦃⟨,|])\s*$")
_TERMINAL_TACTIC_BEFORE_SEMI_RE = re.compile(
    r"^(?:exact|rfl|trivial|assumption|decide|omega|ring|noncomm_ring|linarith|nlinarith|"
    r"norm_num|aesop|tauto|abel|positivity|contradiction|simp_all|simpa)(?![\w'»])"
)
_REFINING_TACTIC_BEFORE_SEMI_RE = re.compile(
    r"^(?:refine|apply|constructor)(?![\w'»])"
)
_COMBINATOR_PREFIX_RE = re.compile(
    r"(?:\||=>|;|<;>|\b(?:focus|try|all_goals|any_goals|repeat'?|iterate(?:\s+\d+)?|"
    r"with_reducible_and_instances|with_reducible|with_unfolding_all|with_unfolding_none|"
    r"fail_if_success|success_if_fail)\b)"
)


_SUBBLOCK_TACTIC_COMBINATOR_RE = re.compile(
    r"(?:by|all_goals|any_goals|try|focus|repeat'?|iterate(?:\s+\d+)?|"
    r"with_reducible_and_instances|with_reducible|with_unfolding_all|with_unfolding_none|"
    r"fail_if_success|success_if_fail|then|else|do)(?![\w'»])"
)
_ANON_HYP_TACTIC_RE = re.compile(
    r"\b(?:assumption|simp_all|aesop|tauto|omega|linarith|nlinarith|contradiction|trivial|simpa)\b"
    r"|\b(?:simp|dsimp)\??\s*(?:only\s*)?\[(?:[^\]\n]*,\s*)?\*(?:\s*,[^\]\n]*)?\]"
    r"|‹"
)


def _match_subblock_stmt(line: str) -> tuple[str, str, int, int, bool, int] | None:
    """Find first tactic-level `(have|let|suffices)` on `line` outside `[...]`/`⦃...⦄`."""
    if not _SUBBLOCK_KW_RE.search(line):
        return None
    n = len(line)
    i = 0
    while i < n and line[i] in (" ", "\t"):
        i += 1
    m_bul = _LEADING_BULLET_RE.match(line[i:])
    bullet_end = i + (m_bul.end() if m_bul else 0)
    cand_starts = {bullet_end}

    other_depth = 0
    other_open = set("[⦃")
    other_close = set("]⦄")
    pos = bullet_end
    while pos < n:
        ch = line[pos]
        if pos in cand_starts:
            p2 = pos
            while p2 < n and line[p2].isspace():
                p2 += 1
            if p2 < n and line[p2] in ("{", "(", "⟨"):
                p3 = p2 + 1
                while p3 < n and line[p3].isspace():
                    p3 += 1
                cand_starts.add(p3)
            m_kw = re.match(r"(have|let|suffices)\b", line[p2:])
            if m_kw and (p2 == 0 or line[p2 - 1] != "."):
                prefix = line[:p2]
                has_nonbullet = bool(line[bullet_end:p2].strip())
                return prefix, m_kw.group(1), p2, p2 + len(m_kw.group(1)), has_nonbullet, bullet_end
        if ch in other_open:
            other_depth += 1
        elif ch in other_close:
            if other_depth > 0:
                other_depth -= 1
        elif other_depth == 0:
            if line.startswith("<;>", pos):
                p2 = pos + 3
                while p2 < n and line[p2].isspace():
                    p2 += 1
                cand_starts.add(p2)
                pos += 3
                continue
            if ch in (";", "{", "(", "⟨", ","):
                p2 = pos + 1
                while p2 < n and line[p2].isspace():
                    p2 += 1
                cand_starts.add(p2)
            elif (
                ch == "|"
                and not line.startswith(("||", "|>"), pos)
                and (pos == 0 or line[pos - 1] not in ("<", "|"))
            ):
                p2 = pos + 1
                while p2 < n and line[p2].isspace():
                    p2 += 1
                cand_starts.add(p2)
            elif line.startswith("=>", pos):
                p2 = pos + 2
                while p2 < n and line[p2].isspace():
                    p2 += 1
                cand_starts.add(p2)
            elif pos == 0 or not (line[pos - 1].isalnum() or line[pos - 1] in "_'»."):
                m_comb = _SUBBLOCK_TACTIC_COMBINATOR_RE.match(line[pos:])
                if m_comb:
                    p2 = pos + m_comb.end()
                    while p2 < n and line[p2].isspace():
                        p2 += 1
                    cand_starts.add(p2)
        pos += 1
    return None


def _find_top_level_semi(s: str, *, initial_depth: int = 0) -> int | None:
    depth = initial_depth
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    i = 0
    n = len(s)
    while i < n:
        if s.startswith("<;>", i):
            i += 3
            continue
        ch = s[i]
        if ch in open_ch:
            depth += 1
        elif ch in close_ch and depth > 0:
            depth -= 1
        elif depth == 0 and ch == ";":
            return i
        i += 1
    return None


def _count_unclosed_wrapper_depth(s: str) -> int:
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    for ch in s:
        if ch in open_ch:
            depth += 1
        elif ch in close_ch and depth > 0:
            depth -= 1
    return depth


def _is_single_balanced_brace_block(s: str) -> bool:
    st = s.strip()
    if not st.startswith("{") or not st.endswith("}"):
        return False
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    for idx, ch in enumerate(st):
        if ch in open_ch:
            depth += 1
        elif ch in close_ch:
            if depth > 0:
                depth -= 1
            if depth == 0:
                return idx == len(st) - 1
    return False


def _strip_trailing_wrappers(s: str, count: int) -> str:
    res = s.rstrip()
    rem = count
    while rem > 0 and res and res[-1] in (")", "}", "⟩"):
        res = res[:-1].rstrip()
        rem -= 1
    return res


def _trim_prefix_open_wrappers(prefix: str, bullet_end: int, count: int) -> tuple[str, bool]:
    nonbullet = prefix[bullet_end:]
    rem = count
    k = len(nonbullet)
    while rem > 0 and k > 0:
        if nonbullet[k - 1].isspace():
            k -= 1
            continue
        if nonbullet[k - 1] in ("(", "{", "⟨"):
            k -= 1
            rem -= 1
            continue
        break
    trimmed_nonbullet = nonbullet[:k].rstrip()
    if trimmed_nonbullet:
        return prefix[:bullet_end] + trimmed_nonbullet, True
    return prefix[:bullet_end], False


def _extract_suffices_hyp_name(header_text: str) -> str:
    h_strip = header_text.lstrip()
    if h_strip.startswith(":"):
        return "this"
    m_hyp = re.match(rf"^({_LEAN_IDENT_SEG})\s*:(?!=)", h_strip)
    if m_hyp and m_hyp.group(1) not in _LEAN_TERM_KEYWORDS:
        return m_hyp.group(1)
    return "this"


def _has_top_level_comma(s: str) -> bool:
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    i = 0
    n = len(s)
    while i < n:
        ch = s[i]
        if ch == "«":
            i += 1
            while i < n and s[i] not in ("»", "\n"):
                i += 1
            if i < n and s[i] == "»":
                i += 1
            continue
        if ch in open_ch:
            depth += 1
        elif ch in close_ch and depth > 0:
            depth -= 1
        elif depth == 0 and ch == ",":
            return True
        i += 1
    return False


def _extract_pattern_bound_names(pat: str) -> list[str]:
    """Extract bound identifier names from a Lean pattern like `⟨(h : Nat), k⟩` or `((h : Nat), k)`."""
    s = pat.strip()
    if not s:
        return []
    if s.startswith("(") and s.endswith(")") and _strip_outer_parens(s) != s:
        inner = _strip_outer_parens(s)
        colon_idx = _find_top_level_colon(inner)
        if colon_idx is not None and not _has_top_level_comma(inner):
            return _extract_pattern_bound_names(inner[:colon_idx])
        return _extract_pattern_bound_names(inner)
    if _has_top_level_comma(s):
        out_names: list[str] = []
        for elem in _split_top_level_commas(s):
            out_names.extend(_extract_pattern_bound_names(elem))
        return out_names
    if s.startswith("⟨") and s.endswith("⟩"):
        b_depth = 0
        balanced = True
        for idx_c, ch in enumerate(s):
            if ch in "([{⦃⟨":
                b_depth += 1
            elif ch in ")]}⦄⟩":
                b_depth -= 1
                if b_depth == 0 and idx_c < len(s) - 1:
                    balanced = False
                    break
        if balanced and b_depth == 0:
            out_names = []
            for elem in _split_top_level_commas(s[1:-1]):
                out_names.extend(_extract_pattern_bound_names(elem))
            return out_names
    if s.startswith("{") and s.endswith("}") and _is_single_balanced_brace_block(s):
        pairs = _split_struct_literal_fields(s[1:-1], allow_pattern_shorthand=True)
        if pairs:
            out_names = []
            for _, field_pat in pairs:
                out_names.extend(_extract_pattern_bound_names(field_pat))
            return out_names
        return []
    m_at = re.match(rf"^({_LEAN_IDENT_SEG})@(.*)$", s, flags=re.S)
    if m_at:
        names = []
        head_id = m_at.group(1)
        if head_id not in _LEAN_TERM_KEYWORDS and head_id != "_":
            names.append(head_id)
        names.extend(_extract_pattern_bound_names(m_at.group(2)))
        return names
    if s.startswith("@"):
        return _extract_pattern_bound_names(s[1:])
    toks = _split_top_level_ws(s)
    if len(toks) == 1:
        tok = toks[0]
        if _LEAN_IDENT_SEG_RE.fullmatch(tok) and tok not in _LEAN_TERM_KEYWORDS and tok != "_":
            return [tok]
        return []
    if len(toks) >= 2:
        # Constructor application pattern like `Prod.mk (h : Nat) k` or `.intro a b`
        out_names = []
        for tok in toks[1:]:
            out_names.extend(_extract_pattern_bound_names(tok))
        return out_names
    return []


_NAT_BOOL_ASCRIPTIONS = frozenset({"Nat", "ℕ", "Bool", "_root_.Nat", "_root_.Bool"})


def _has_non_nat_bool_type_ascription(expr: str) -> bool:
    """Return True iff `expr` contains any `: <Type>` ascription whose `<Type>` is not `Nat`/`ℕ`/`Bool`."""
    n = len(expr)
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    pairs = {"(": ")", "{": "}", "[": "]", "⦃": "⦄", "⟨": "⟩"}
    i = 0
    while i < n:
        ch = expr[i]
        if ch == "«":
            i += 1
            while i < n and expr[i] not in ("»", "\n"):
                i += 1
            if i < n and expr[i] == "»":
                i += 1
            continue
        if ch == '"':
            i += 1
            while i < n:
                if expr[i] == "\\" and i + 1 < n:
                    i += 2
                    continue
                if expr[i] == '"':
                    i += 1
                    break
                i += 1
            continue
        if ch in open_ch:
            depth += 1
        elif ch in close_ch and depth > 0:
            depth -= 1
        elif ch == ":" and not expr.startswith((":=", "::"), i) and (i == 0 or expr[i - 1] != ":"):
            d_colon = depth
            t_depth = d_colon
            k = i + 1
            while k < n:
                tc = expr[k]
                if tc == "«":
                    k += 1
                    while k < n and expr[k] not in ("»", "\n"):
                        k += 1
                    if k < n and expr[k] == "»":
                        k += 1
                    continue
                if tc == '"':
                    k += 1
                    while k < n:
                        if expr[k] == "\\" and k + 1 < n:
                            k += 2
                            continue
                        if expr[k] == '"':
                            k += 1
                            break
                        k += 1
                    continue
                if tc in open_ch:
                    t_depth += 1
                elif tc in close_ch:
                    if t_depth == d_colon:
                        break
                    if t_depth > 0:
                        t_depth -= 1
                elif t_depth == d_colon and tc in (",", ";"):
                    break
                k += 1
            ty_str = _strip_outer_parens(expr[i + 1 : k].strip())
            if ty_str not in _NAT_BOOL_ASCRIPTIONS:
                return True
        i += 1
    return False


_NAT_ONLY_ASCRIPTIONS = frozenset({"Nat", "ℕ", "_root_.Nat"})


def _strip_inner_nat_bool_ascriptions(expr: str, *, allow_bool: bool = False) -> tuple[str, bool]:
    """Strip `: Nat`/`ℕ` (and optionally `: Bool`) ascriptions at any depth; return `('', False)` on other `: <Type>`."""
    allowed = _NAT_BOOL_ASCRIPTIONS if allow_bool else _NAT_ONLY_ASCRIPTIONS
    out: list[str] = []
    n = len(expr)
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    i = 0
    while i < n:
        ch = expr[i]
        if ch == "«":
            start_q = i
            i += 1
            while i < n and expr[i] not in ("»", "\n"):
                i += 1
            if i < n and expr[i] == "»":
                i += 1
            out.append(expr[start_q:i])
            continue
        if ch == '"':
            start_s = i
            i += 1
            while i < n:
                if expr[i] == "\\" and i + 1 < n:
                    i += 2
                    continue
                if expr[i] == '"':
                    i += 1
                    break
                i += 1
            out.append(expr[start_s:i])
            continue
        if ch in open_ch:
            depth += 1
            out.append(ch)
        elif ch in close_ch and depth > 0:
            depth -= 1
            out.append(ch)
        elif ch == ":" and not expr.startswith((":=", "::"), i) and (i == 0 or expr[i - 1] != ":"):
            d_colon = depth
            t_depth = d_colon
            k = i + 1
            while k < n:
                tc = expr[k]
                if tc == "«":
                    k += 1
                    while k < n and expr[k] not in ("»", "\n"):
                        k += 1
                    if k < n and expr[k] == "»":
                        k += 1
                    continue
                if tc == '"':
                    k += 1
                    while k < n:
                        if expr[k] == "\\" and k + 1 < n:
                            k += 2
                            continue
                        if expr[k] == '"':
                            k += 1
                            break
                        k += 1
                    continue
                if tc in open_ch:
                    t_depth += 1
                elif tc in close_ch:
                    if t_depth == d_colon:
                        break
                    if t_depth > 0:
                        t_depth -= 1
                elif t_depth == d_colon and tc in (",", ";"):
                    break
                k += 1
            ty_str = _strip_outer_parens(expr[i + 1 : k].strip())
            if ty_str not in allowed:
                return "", False
            i = k
            continue
        else:
            out.append(ch)
        i += 1
    return "".join(out), True


def _eval_ground_suffices_expr(expr: str) -> str | None:
    """Safely evaluate ground Nat/Bool expressions (`0 + 0`, `1 + 1`, `Nat.succ 0`, `true && false`)."""
    if _has_non_nat_bool_type_ascription(expr):
        return None
    s, ok_ascr = _strip_inner_nat_bool_ascriptions(_strip_type_ascription(expr), allow_bool=True)
    if not ok_ascr:
        return None
    s = _strip_outer_parens(s)
    if not s or len(s) > 256:
        return None
    tok_re = re.compile(r"\s*(?:(&&|\|\||==|!=|[+\-*/%^!()])|(\d+)|([A-Za-z_][A-Za-z0-9_.]*)|(\S))")
    toks: list[str] = []
    pos = 0
    while pos < len(s):
        m = tok_re.match(s, pos)
        if not m or m.group(4) is not None:
            return None
        toks.append(m.group(1) or m.group(2) or m.group(3) or "")
        pos = m.end()
    if not toks:
        return None
    idx = 0

    def _peek() -> str | None:
        return toks[idx] if idx < len(toks) else None

    def _consume() -> str:
        nonlocal idx
        t = toks[idx]
        idx += 1
        return t

    def _parse_or() -> int | bool | None:
        val = _parse_and()
        if val is None:
            return None
        while _peek() == "||":
            _consume()
            rhs = _parse_and()
            if not isinstance(val, bool) or not isinstance(rhs, bool):
                return None
            val = val or rhs
        return val

    def _parse_and() -> int | bool | None:
        val = _parse_eq()
        if val is None:
            return None
        while _peek() == "&&":
            _consume()
            rhs = _parse_eq()
            if not isinstance(val, bool) or not isinstance(rhs, bool):
                return None
            val = val and rhs
        return val

    def _parse_eq() -> int | bool | None:
        val = _parse_add()
        if val is None:
            return None
        while _peek() in ("==", "!="):
            op = _consume()
            rhs = _parse_add()
            if rhs is None or type(val) is not type(rhs):
                return None
            val = (val == rhs) if op == "==" else (val != rhs)
        return val

    def _parse_add() -> int | bool | None:
        val = _parse_mul()
        if val is None:
            return None
        while _peek() in ("+", "-"):
            op = _consume()
            rhs = _parse_mul()
            if type(val) is not int or type(rhs) is not int:
                return None
            val = (val + rhs) if op == "+" else max(0, val - rhs)
        return val

    def _parse_mul() -> int | bool | None:
        val = _parse_pow()
        if val is None:
            return None
        while _peek() in ("*", "/", "%"):
            op = _consume()
            rhs = _parse_pow()
            if type(val) is not int or type(rhs) is not int:
                return None
            if op == "*":
                val = val * rhs
            elif op == "/":
                val = (val // rhs) if rhs != 0 else 0
            else:
                val = (val % rhs) if rhs != 0 else val
        return val

    def _parse_pow() -> int | bool | None:
        val = _parse_unary()
        if val is None:
            return None
        if _peek() == "^":
            _consume()
            rhs = _parse_pow()
            if type(val) is not int or type(rhs) is not int or rhs < 0 or rhs > 64:
                return None
            val = val ** rhs
        return val

    def _parse_unary() -> int | bool | None:
        nxt = _peek()
        if nxt == "!":
            _consume()
            sub = _parse_unary()
            return (not sub) if isinstance(sub, bool) else None
        if nxt == "Nat.succ":
            _consume()
            sub = _parse_atom()
            return (sub + 1) if type(sub) is int else None
        return _parse_atom()

    def _parse_atom() -> int | bool | None:
        nxt = _peek()
        if nxt is None:
            return None
        if nxt == "(":
            _consume()
            sub = _parse_or()
            if _peek() != ")":
                return None
            _consume()
            return sub
        if nxt.isdigit():
            _consume()
            return int(nxt)
        if nxt == "Nat.zero":
            _consume()
            return 0
        if nxt in ("true", "Bool.true"):
            _consume()
            return True
        if nxt in ("false", "Bool.false"):
            _consume()
            return False
        return None

    res = _parse_or()
    if res is None or idx != len(toks):
        return None
    if isinstance(res, bool):
        return "true" if res else "false"
    return str(res)


def _is_pure_nat_var_expr(expr: str, nat_vars: frozenset[str] | set[str]) -> bool:
    """Return True iff `expr` uses only `nat_vars`, Nat literals, `Nat.zero`/`Nat.succ`, `: Nat` ascriptions, and arithmetic ops."""
    if not nat_vars or _has_non_nat_bool_type_ascription(expr):
        return False
    s, ok_ascr = _strip_inner_nat_bool_ascriptions(_strip_type_ascription(expr), allow_bool=False)
    if not ok_ascr:
        return False
    s = _strip_outer_parens(s)
    if not s:
        return False
    tok_re = re.compile(rf"\s*(?:([+\-*/%^()])|(\d+)|({_LEAN_QUAL_IDENT})|(\S))")
    pos = 0
    saw_val = False
    while pos < len(s):
        m = tok_re.match(s, pos)
        if not m or m.group(4) is not None:
            return False
        if m.group(2) is not None:
            saw_val = True
        elif m.group(3) is not None:
            ident = m.group(3)
            if ident not in nat_vars and ident not in ("Nat.zero", "Nat.succ"):
                return False
            saw_val = True
        pos = m.end()
    return saw_val


def _strip_trailing_nat_add_zero(s: str, nat_vars: frozenset[str] | set[str]) -> str:
    """Strip top-level `+ 0` / `- 0` (including ground-zero RHS like `0 + 0`) on known `Nat` expressions."""
    cur = s
    while nat_vars:
        cur_inner = _strip_outer_parens(cur)
        depth = 0
        open_ch = set("([{⦃⟨")
        close_ch = set(")]}⦄⟩")
        last_op: int | None = None
        i = 0
        n = len(cur_inner)
        while i < n:
            ch = cur_inner[i]
            if ch == "«":
                i += 1
                while i < n and cur_inner[i] not in ("»", "\n"):
                    i += 1
                if i < n and cur_inner[i] == "»":
                    i += 1
                continue
            if ch in open_ch:
                depth += 1
            elif ch in close_ch and depth > 0:
                depth -= 1
            elif depth == 0 and ch in ("+", "-"):
                last_op = i
            i += 1
        if last_op is None:
            return cur_inner
        lhs = cur_inner[:last_op].strip()
        rhs = _strip_outer_parens(cur_inner[last_op + 1 :].strip())
        rhs_eval = _eval_ground_suffices_expr(rhs)
        rhs_is_zero = (rhs in ("0", "Nat.zero")) or (rhs_eval == "0")
        if rhs_is_zero and _is_pure_nat_var_expr(lhs, nat_vars):
            cur = lhs
            continue
        return cur_inner
    return cur


def _normalize_suffices_atom(
    expr: str,
    *,
    nat_vars: frozenset[str] | set[str] | None = None,
) -> str:
    """Normalize outer parens/type ascriptions, ground Nat/Bool exprs, trailing `Nat +/- 0`, and constructor aliases."""
    ground = _eval_ground_suffices_expr(expr)
    if ground is not None:
        return ground
    non_nat_ascr = _has_non_nat_bool_type_ascription(expr)
    s = re.sub(r"\s+", " ", _strip_type_ascription(expr)).strip()
    if s == "Nat.zero":
        return "0"
    if s == "Bool.true":
        return "true"
    if s == "Bool.false":
        return "false"
    if nat_vars and not non_nat_ascr:
        s = _strip_trailing_nat_add_zero(s, nat_vars)
        s = re.sub(r"\s+", " ", _strip_type_ascription(s)).strip()
    return s


def _split_top_level_conj(prop: str) -> list[str]:
    """Split `prop` on top-level `∧` / `/\\` at bracket depth 0."""
    parts: list[str] = []
    cur: list[str] = []
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    i = 0
    n = len(prop)
    while i < n:
        ch = prop[i]
        if ch == "«":
            cur.append(ch)
            i += 1
            while i < n and prop[i] not in ("»", "\n"):
                cur.append(prop[i])
                i += 1
            if i < n and prop[i] == "»":
                cur.append("»")
                i += 1
            continue
        if ch in open_ch:
            depth += 1
            cur.append(ch)
        elif ch in close_ch and depth > 0:
            depth -= 1
            cur.append(ch)
        elif depth == 0 and ch == "∧":
            seg = "".join(cur).strip()
            if seg:
                parts.append(seg)
            cur.clear()
        elif depth == 0 and prop.startswith("/\\", i):
            seg = "".join(cur).strip()
            if seg:
                parts.append(seg)
            cur.clear()
            i += 2
            continue
        else:
            cur.append(ch)
        i += 1
    tail = "".join(cur).strip()
    if tail:
        parts.append(tail)
    return parts


_REFL_PROP_KINDS = frozenset({"true", "eq_refl", "iff_refl", "conj_refl"})


def _classify_suffices_prop_detail(
    prop_raw: str,
    *,
    nat_vars: frozenset[str] | set[str] | None = None,
    _depth: int = 0,
) -> tuple[bool, str, bool]:
    """Return `(is_unsat, kind, is_conj)` where `kind` is `unsat|true|eq_refl|iff_refl|conj_refl|other`."""
    if _depth > 15:
        return False, "other", False
    prop = _strip_outer_parens(prop_raw.strip())
    cur_nat_vars = set(nat_vars) if nat_vars is not None else None
    zeta_subst: dict[str, str] = {}
    for _ in range(16):
        m_kw = re.match(r"^(?:let|have)(?![\w'»])", prop)
        if not m_kw:
            break
        peeled = _strip_leading_let_have(prop)
        if peeled is None:
            break
        lhs_chunk = prop[: len(prop) - len(peeled)]
        # Find top-level `:=` in `lhs_chunk` to separate LHS pattern/type from RHS value
        d_c = 0
        ic = m_kw.end()
        nc = len(lhs_chunk)
        assign_c: int | None = None
        while ic < nc:
            cc = lhs_chunk[ic]
            if cc == "«":
                ic += 1
                while ic < nc and lhs_chunk[ic] not in ("»", "\n"):
                    ic += 1
                if ic < nc and lhs_chunk[ic] == "»":
                    ic += 1
                continue
            if cc in "([{⦃⟨":
                d_c += 1
            elif cc in ")]}⦄⟩" and d_c > 0:
                d_c -= 1
            elif d_c == 0 and lhs_chunk.startswith(":=", ic):
                assign_c = ic
                break
            ic += 1
        if assign_c is not None:
            before_assign = lhs_chunk[m_kw.end() : assign_c].strip()
            after_assign = lhs_chunk[assign_c + 2 :].strip()
            val_str = after_assign[:-1].strip() if after_assign.endswith(";") else after_assign
            val_eff = _subst_lean_expr_capture_avoiding(val_str, zeta_subst) if zeta_subst else val_str
            col_c = _find_top_level_colon(before_assign)
            if col_c is not None:
                lhs_pat = before_assign[:col_c].strip()
                b_ty = _strip_outer_parens(before_assign[col_c + 1 :].strip())
            else:
                lhs_pat = before_assign
                b_ty = ""

            def _infer_is_nat(ty_s: str, rhs_s: str) -> bool:
                if ty_s:
                    return ty_s in _NAT_ONLY_ASCRIPTIONS
                if not rhs_s or _has_non_nat_bool_type_ascription(rhs_s):
                    return False
                ev_r = _eval_ground_suffices_expr(rhs_s)
                if ev_r is not None and ev_r not in ("true", "false"):
                    return True
                return bool(cur_nat_vars and _is_pure_nat_var_expr(rhs_s, cur_nat_vars))

            def _update_nat_var(nm: str, is_nat: bool) -> None:
                nonlocal cur_nat_vars
                if not nm or nm == "_":
                    return
                if cur_nat_vars is None:
                    if is_nat:
                        cur_nat_vars = {nm}
                elif is_nat:
                    cur_nat_vars.add(nm)
                else:
                    cur_nat_vars.discard(nm)

            def _unpack_tuple_elems(txt: str) -> list[str] | None:
                ts = txt.strip()
                if ts.startswith("(") and ts.endswith(")") and _strip_outer_parens(ts) != ts:
                    inner_t = _strip_outer_parens(ts)
                    if _has_top_level_comma(inner_t):
                        return [e.strip() for e in _split_top_level_commas(inner_t)]
                if ts.startswith("⟨") and ts.endswith("⟩"):
                    inner_t = ts[1:-1].strip()
                    if _has_top_level_comma(inner_t):
                        return [e.strip() for e in _split_top_level_commas(inner_t)]
                if _has_top_level_comma(ts):
                    return [e.strip() for e in _split_top_level_commas(ts)]
                return None

            if _LEAN_IDENT_SEG_RE.fullmatch(lhs_pat):
                is_nat_single = _infer_is_nat(b_ty, val_eff)
                _update_nat_var(lhs_pat, is_nat_single)
                zeta_bound: str | None = None
                if is_nat_single and val_eff and not _has_non_nat_bool_type_ascription(val_eff):
                    ev_z = _eval_ground_suffices_expr(val_eff)
                    if ev_z is not None and ev_z not in ("true", "false"):
                        zeta_bound = ev_z
                elif b_ty in ("Prop", "") and val_eff and _depth < 14:
                    _, rk, _ = _classify_suffices_prop_detail(val_eff, nat_vars=cur_nat_vars, _depth=_depth + 1)
                    if rk in _REFL_PROP_KINDS:
                        zeta_bound = f"({val_eff})" if any(c.isspace() for c in val_eff) else val_eff
                if zeta_bound is not None:
                    zeta_subst[lhs_pat] = zeta_bound
                else:
                    zeta_subst.pop(lhs_pat, None)
            elif lhs_pat.startswith(("(", "⟨", "{")) or _has_top_level_comma(lhs_pat):
                for nm in _extract_pattern_bound_names(lhs_pat):
                    zeta_subst.pop(nm, None)
                pat_elems = _unpack_tuple_elems(lhs_pat)
                val_elems = _unpack_tuple_elems(val_eff) if not b_ty else None
                if pat_elems is not None and val_elems is not None and len(pat_elems) == len(val_elems):
                    for pe, ve in zip(pat_elems, val_elems):
                        pe_s = _strip_outer_parens(pe)
                        p_col = _find_top_level_colon(pe_s)
                        if p_col is not None and not _has_top_level_comma(pe_s):
                            p_nm = pe_s[:p_col].strip()
                            p_ty = _strip_outer_parens(pe_s[p_col + 1 :].strip())
                            is_nat_e = p_ty in _NAT_ONLY_ASCRIPTIONS
                            for nm in _extract_pattern_bound_names(p_nm):
                                _update_nat_var(nm, is_nat_e)
                        else:
                            is_nat_e = _infer_is_nat("", ve)
                            for nm in _extract_pattern_bound_names(pe):
                                _update_nat_var(nm, is_nat_e)
                else:
                    for nm in _extract_pattern_bound_names(lhs_pat):
                        _update_nat_var(nm, False)
            else:
                m_fn_l = re.match(rf"^({_LEAN_IDENT_SEG})", lhs_pat)
                if m_fn_l:
                    _update_nat_var(m_fn_l.group(1), False)
                    zeta_subst.pop(m_fn_l.group(1), None)
        prop = _strip_outer_parens(peeled.strip())
    if zeta_subst:
        prop = _strip_outer_parens(_subst_lean_expr_capture_avoiding(prop, zeta_subst).strip())
    nat_vars = cur_nat_vars
    if prop == "False":
        return True, "unsat", False
    if prop == "True":
        return False, "true", False

    conj_parts = _split_top_level_conj(prop)
    if len(conj_parts) >= 2:
        sub_res = [_classify_suffices_prop_detail(p, nat_vars=nat_vars, _depth=_depth + 1) for p in conj_parts]
        any_unsat = any(u for u, _, _ in sub_res)
        all_refl = all(k in _REFL_PROP_KINDS for _, k, _ in sub_res)
        if any_unsat:
            return True, "unsat", True
        return False, ("conj_refl" if all_refl else "other"), True

    m_neg = re.match(r"^(?:¬\s*(.+)|Not(?=\s|\()(.+))$", prop, flags=re.S)
    if m_neg:
        inner = (m_neg.group(1) or m_neg.group(2) or "").strip()
        if inner:
            _, inner_kind, _ = _classify_suffices_prop_detail(inner, nat_vars=nat_vars, _depth=_depth + 1)
            if inner_kind in _REFL_PROP_KINDS:
                return True, "unsat", False
            return False, "other", False

    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    iff_pos: tuple[int, int] | None = None
    has_other_conn = False
    rel_pos: tuple[int, int, str] | None = None
    i = 0
    n = len(prop)
    while i < n:
        ch = prop[i]
        if ch == "«":
            i += 1
            while i < n and prop[i] not in ("»", "\n"):
                i += 1
            if i < n and prop[i] == "»":
                i += 1
            continue
        if ch in open_ch:
            depth += 1
        elif ch in close_ch and depth > 0:
            depth -= 1
        elif depth == 0:
            if prop.startswith(("->", "\\/"), i) or ch in ("→", "∨"):
                has_other_conn = True
                break
            if ch == "↔":
                if iff_pos is not None:
                    has_other_conn = True
                    break
                iff_pos = (i, i + 1)
                i += 1
                continue
            if prop.startswith("<->", i):
                if iff_pos is not None:
                    has_other_conn = True
                    break
                iff_pos = (i, i + 3)
                i += 3
                continue
            if ch == "≠":
                if rel_pos is not None:
                    rel_pos = None
                    break
                rel_pos = (i, i + 1, "≠")
                i += 1
                continue
            if prop.startswith("!=", i):
                if rel_pos is not None:
                    rel_pos = None
                    break
                rel_pos = (i, i + 2, "!=")
                i += 2
                continue
            if (
                ch == "="
                and not prop.startswith(("==", "=>"), i)
                and (i == 0 or prop[i - 1] not in (":", "=", "<", ">", "!"))
            ):
                if rel_pos is None:
                    rel_pos = (i, i + 1, "=")
                else:
                    # Multiple top-level `=` (only valid inside `lhs ↔ rhs` where each side has `=`)
                    rel_pos = (-1, -1, "multi")
                i += 1
                continue
        i += 1

    if has_other_conn:
        return False, "other", False

    if iff_pos is not None:
        lhs_iff = prop[: iff_pos[0]].strip()
        rhs_iff = prop[iff_pos[1] :].strip()
        if not lhs_iff or not rhs_iff:
            return False, "other", False
        lhs_norm = _normalize_suffices_atom(lhs_iff, nat_vars=nat_vars)
        rhs_norm = _normalize_suffices_atom(rhs_iff, nat_vars=nat_vars)
        if lhs_norm and lhs_norm == rhs_norm:
            return False, "iff_refl", False
        l_u, l_k, _ = _classify_suffices_prop_detail(lhs_iff, nat_vars=nat_vars, _depth=_depth + 1)
        r_u, r_k, _ = _classify_suffices_prop_detail(rhs_iff, nat_vars=nat_vars, _depth=_depth + 1)
        if (l_u and r_k in _REFL_PROP_KINDS) or (r_u and l_k in _REFL_PROP_KINDS):
            return True, "unsat", False
        return False, "other", False

    if rel_pos is None or rel_pos[0] < 0:
        return False, "other", False
    r_start, r_end, op = rel_pos
    lhs_raw = prop[:r_start].strip()
    rhs_raw = prop[r_end:].strip()
    if not lhs_raw or not rhs_raw:
        return False, "other", False
    lhs = _normalize_suffices_atom(lhs_raw, nat_vars=nat_vars)
    rhs = _normalize_suffices_atom(rhs_raw, nat_vars=nat_vars)
    if op in ("≠", "!="):
        if lhs and lhs == rhs:
            return True, "unsat", False
        return False, "other", False
    # op == "="
    if lhs and lhs == rhs:
        return False, "eq_refl", False
    if re.fullmatch(r"\d+", lhs) and re.fullmatch(r"\d+", rhs) and int(lhs) != int(rhs):
        return True, "unsat", False
    if {lhs, rhs} in ({"true", "false"}, {"True", "False"}):
        return True, "unsat", False
    if (
        (lhs.startswith('"') and lhs.endswith('"') and rhs.startswith('"') and rhs.endswith('"'))
        or (lhs.startswith("'") and lhs.endswith("'") and rhs.startswith("'") and rhs.endswith("'"))
    ) and lhs != rhs:
        return True, "unsat", False
    lhs_head = (_split_top_level_ws(lhs) or [""])[0]
    rhs_head = (_split_top_level_ws(rhs) or [""])[0]
    if {lhs_head, rhs_head} in (
        {"0", "Nat.succ"},
        {"none", "some"},
        {"Option.none", "Option.some"},
        {"[]", "List.cons"},
        {"List.nil", "List.cons"},
        {"Sum.inl", "Sum.inr"},
        {"Except.ok", "Except.error"},
    ):
        return True, "unsat", False
    if (lhs == "[]" and rhs.startswith("[") and rhs.endswith("]") and rhs != "[]") or (
        rhs == "[]" and lhs.startswith("[") and lhs.endswith("]") and lhs != "[]"
    ):
        return True, "unsat", False
    return False, "other", False


def _classify_suffices_prop(
    prop_raw: str,
    *,
    nat_vars: frozenset[str] | set[str] | None = None,
    _depth: int = 0,
) -> tuple[bool, bool, bool]:
    """Return `(is_unsat, is_refl_or_true, is_conj)` for a stripped proposition `prop_raw`."""
    is_unsat, kind, is_conj = _classify_suffices_prop_detail(prop_raw, nat_vars=nat_vars, _depth=_depth)
    return is_unsat, (kind in _REFL_PROP_KINDS), is_conj


def _classify_suffices_header(header_text: str) -> tuple[bool, bool]:
    """Return `(is_unsat, is_refl_or_true)` for a `suffices` hypothesis proposition."""
    h = header_text.strip()
    colon_idx = _find_top_level_colon(h)
    prop = h[colon_idx + 1 :].strip() if colon_idx is not None else h
    is_unsat, is_refl, _ = _classify_suffices_prop(prop)
    return is_unsat, is_refl


def _is_unsat_suffices_header(header_text: str) -> bool:
    """Return True iff `suffices` hypothesis proposition is syntactically unsatisfiable (`False`, `(0 : Nat) = 1`, `true = false`, etc.)."""
    is_unsat, _ = _classify_suffices_header(header_text)
    return is_unsat


def _extract_have_lhs_and_body(block_text: str) -> tuple[list[str], str]:
    """Extract bound identifier names and RHS/type body from a stripped `have`/`let` block."""
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    split_idx: int | None = None
    split_len = 1
    i = 0
    n = len(block_text)
    while i < n:
        ch = block_text[i]
        if ch == "«":
            i += 1
            while i < n and block_text[i] not in ("»", "\n"):
                i += 1
            if i < n and block_text[i] == "»":
                i += 1
            continue
        if ch in open_ch:
            depth += 1
        elif ch in close_ch and depth > 0:
            depth -= 1
        elif depth == 0:
            if block_text.startswith(":=", i):
                split_idx = i
                split_len = 2
                break
            if ch == ":":
                split_idx = i
                split_len = 1
                break
        i += 1
    if split_idx is None:
        return [], block_text
    lhs_raw = block_text[:split_idx].strip()
    body = block_text[split_idx + split_len :]
    if not lhs_raw:
        return ["this"], body
    if lhs_raw.startswith("{"):
        if (
            lhs_raw.endswith("}")
            and _is_single_balanced_brace_block(lhs_raw)
            and _split_struct_literal_fields(lhs_raw[1:-1], allow_pattern_shorthand=True) is not None
        ):
            return _extract_pattern_bound_names(lhs_raw) or ["this"], body
        return ["this"], body
    if lhs_raw.startswith("⦃"):
        return ["this"], body
    if lhs_raw.startswith("["):
        inner_sq = lhs_raw[1:-1] if lhs_raw.endswith("]") else lhs_raw[1:]
        if split_len == 1 or "," not in inner_sq:
            return ["this"], body
    if lhs_raw.startswith("("):
        # Single-level `(h : T)` binder (not `((h : T))`, `(⟨h, k⟩)`, `(Prod.mk ...)`, `(h@k)`) binds `this`
        if lhs_raw.endswith(")") and _strip_outer_parens(lhs_raw) == lhs_raw[1:-1].strip():
            once_inner = lhs_raw[1:-1].strip()
            colon_i = _find_top_level_colon(once_inner)
            if colon_i is not None and not _has_top_level_comma(once_inner):
                binder_head = once_inner[:colon_i].strip()
                if _LEAN_IDENT_SEG_RE.fullmatch(binder_head):
                    return ["this"], body
        return _extract_pattern_bound_names(lhs_raw) or ["this"], body
    if lhs_raw.startswith("⟨") or re.match(rf"^(?:{_LEAN_IDENT_SEG})?@", lhs_raw):
        return _extract_pattern_bound_names(lhs_raw) or ["this"], body
    # Strip trailing bracketed parameter groups `(x : T)` / `{x : T}` / `[Inst]` after a bound name
    lhs_head = re.sub(r"[\(\{⦃\[].*$", "", lhs_raw, flags=re.S).strip() or lhs_raw
    lhs_names = [
        tok
        for tok in _LEAN_IDENT_TOKEN_RE.findall(lhs_head)
        if tok not in _LEAN_TERM_KEYWORDS and tok != "_"
    ]
    return lhs_names, body


_CTOR_OPEN_LINE_RE = re.compile(
    r"(?<![\w'»])(?:constructor(?![\w'»])|"
    r"apply\s+\(*(?:@?(?:[A-Za-z_][A-Za-z0-9_'.?!]*)?\.mk|(?:And|Iff|Exists)\.intro)(?![\w'»])|"
    r"refine'?(?:\s+|(?=[⟨{(]))\(*(⟨|\{|@?(?:[A-Za-z_][A-Za-z0-9_'.?!]*)?\.mk\b|@?(?:And|Iff|Exists)\.intro\b))"
)


def _extract_struct_param_specs(header: str) -> list[tuple[str, bool, bool]]:
    """Return `[(param_name, is_explicit, is_nat), ...]` from a structure header."""
    h = re.sub(r"^\s*\.\{[^}]*\}", "", header).strip()
    h = re.sub(r"(?::=|where)\s*$", "", h).strip()
    m_ext = re.search(r"\bextends\b", h)
    if m_ext:
        h = h[: m_ext.start()].strip()
    c_idx = _find_top_level_colon(h)
    if c_idx is not None:
        h = h[:c_idx].strip()
    params: list[tuple[str, bool, bool]] = []
    open_ch = set("([{⦃")
    close_ch = set(")]}⦄")
    i = 0
    n = len(h)
    while i < n:
        ch = h[i]
        if ch.isspace():
            i += 1
            continue
        if ch in open_ch:
            depth = 1
            j = i + 1
            while j < n and depth > 0:
                if h[j] in open_ch:
                    depth += 1
                elif h[j] in close_ch:
                    depth -= 1
                j += 1
            inner = h[i + 1 : j - 1] if depth == 0 else h[i + 1 :]
            is_exp = ch == "("
            colon_i = _find_top_level_colon(inner)
            if colon_i is not None:
                lhs = inner[:colon_i]
                ty = _strip_outer_parens(inner[colon_i + 1 :].strip())
                is_nat = ty in ("Nat", "ℕ", "_root_.Nat")
                for tok in lhs.split():
                    if _LEAN_IDENT_SEG_RE.fullmatch(tok) and tok not in _LEAN_TERM_KEYWORDS and tok != "_":
                        params.append((tok, is_exp, is_nat))
            elif is_exp:
                for tok in inner.split():
                    if _LEAN_IDENT_SEG_RE.fullmatch(tok) and tok not in _LEAN_TERM_KEYWORDS and tok != "_":
                        params.append((tok, True, False))
            i = j
            continue
        j = i
        while j < n and not h[j].isspace() and h[j] not in open_ch:
            j += 1
        tok = h[i:j]
        if _LEAN_IDENT_SEG_RE.fullmatch(tok) and tok not in _LEAN_TERM_KEYWORDS and tok != "_":
            params.append((tok, True, False))
        i = j
    return params


def _extract_nat_binder_vars(decl_header: str, ret_type: str, preceding_clean: str) -> set[str]:
    """Extract binder variable names explicitly typed `Nat` or `ℕ`, respecting `section`/`namespace`/`mutual` scopes and shadowing."""
    top_colon = _find_top_level_colon(decl_header)
    param_header = decl_header[:top_colon] if top_colon is not None else decl_header

    def _collect_from_bracket_src(src: str, target_set: set[str]) -> None:
        open_ch = set("([{⦃")
        close_ch = set(")]}⦄")
        i = 0
        n = len(src)
        while i < n:
            ch = src[i]
            if ch in open_ch:
                start = i
                depth = 1
                i += 1
                while i < n and depth > 0:
                    if src[i] in open_ch:
                        depth += 1
                    elif src[i] in close_ch:
                        depth -= 1
                    i += 1
                inner = src[start + 1 : i - 1] if depth == 0 else src[start + 1 :]
                if ch in ("(", "{", "⦃"):
                    c_i = _find_top_level_colon(inner)
                    if c_i is not None:
                        ty = _strip_outer_parens(inner[c_i + 1 :].strip())
                        is_nat = ty in ("Nat", "ℕ", "_root_.Nat")
                        for tok in inner[:c_i].split():
                            if _LEAN_IDENT_SEG_RE.fullmatch(tok) and tok not in _LEAN_TERM_KEYWORDS and tok != "_":
                                if is_nat:
                                    target_set.add(tok)
                                else:
                                    target_set.discard(tok)
                continue
            i += 1

    def _collect_var_map_from_src(src: str, var_map: dict[str, bool]) -> None:
        open_ch = set("([{⦃")
        close_ch = set(")]}⦄")
        i = 0
        n = len(src)
        while i < n:
            ch = src[i]
            if ch in open_ch:
                start = i
                depth = 1
                i += 1
                while i < n and depth > 0:
                    if src[i] in open_ch:
                        depth += 1
                    elif src[i] in close_ch:
                        depth -= 1
                    i += 1
                inner = src[start + 1 : i - 1] if depth == 0 else src[start + 1 :]
                if ch in ("(", "{", "⦃"):
                    c_i = _find_top_level_colon(inner)
                    if c_i is not None:
                        ty = _strip_outer_parens(inner[c_i + 1 :].strip())
                        is_nat = ty in ("Nat", "ℕ", "_root_.Nat")
                        for tok in inner[:c_i].split():
                            if _LEAN_IDENT_SEG_RE.fullmatch(tok) and tok not in _LEAN_TERM_KEYWORDS and tok != "_":
                                var_map[tok] = is_nat
                continue
            i += 1

    module_vars: dict[str, bool] = {}
    pending_in_vars: dict[str, bool] = {}
    scope_stack: list[tuple[str, list[str], dict[str, bool]]] = []
    pre_lines = preceding_clean.splitlines()
    p_idx = 0
    _decl_consume_re = re.compile(
        r"(?:^|\s)(?:theorem|lemma|def|abbrev|example|instance|structure|class|inductive|axiom|opaque|end)\b"
    )
    while p_idx < len(pre_lines):
        pl = pre_lines[p_idx]
        p_idx += 1
        pls = pl.strip()
        if not pls:
            continue
        m_ns = re.match(rf"^\s*namespace\s+({_LEAN_QUAL_IDENT})", pl)
        if m_ns:
            pending_in_vars.clear()
            parts = [p for p in split_lean_qual_ident(m_ns.group(1)) if p != "_root_"]
            for part in parts:
                scope_stack.append(("ns", [part], {}))
            continue
        m_sec = re.match(rf"^\s*section(?:\s+({_LEAN_QUAL_IDENT}))?(?=\s|$)", pl)
        if m_sec:
            pending_in_vars.clear()
            sec_name = m_sec.group(1)
            sec_parts = [p for p in split_lean_qual_ident(sec_name) if p != "_root_"] if sec_name else []
            scope_stack.append(("sec", sec_parts, {}))
            continue
        if re.match(r"^\s*mutual(?=\s|$)", pl):
            pending_in_vars.clear()
            scope_stack.append(("mut", [], {}))
            continue
        m_end = re.match(rf"^\s*end(?:\s+({_LEAN_QUAL_IDENT}))?\s*$", pl)
        if m_end:
            pending_in_vars.clear()
            end_name = m_end.group(1)
            if not end_name:
                if scope_stack:
                    scope_stack.pop()
            else:
                end_parts = [p for p in split_lean_qual_ident(end_name) if p != "_root_"]
                if scope_stack:
                    if scope_stack[-1][1] == end_parts:
                        scope_stack.pop()
                    else:
                        rem = list(end_parts)
                        while rem and scope_stack:
                            _, top_parts, _ = scope_stack[-1]
                            if not top_parts:
                                scope_stack.pop()
                                continue
                            if len(rem) >= len(top_parts) and rem[-len(top_parts) :] == top_parts:
                                scope_stack.pop()
                                rem = rem[: -len(top_parts)]
                            else:
                                scope_stack.pop()
                                break
            continue
        m_var = re.match(r"^\s*variable\s+([^\n]+)", pl)
        if m_var:
            var_src = m_var.group(1)
            v_bal = sum(1 for c in var_src if c in "([{⦃") - sum(1 for c in var_src if c in ")]}⦄")
            while p_idx < len(pre_lines):
                nxt_v = pre_lines[p_idx]
                nxt_vs = nxt_v.strip()
                if v_bal > 0 or (nxt_vs and re.match(r"^(?:in(?=\s|$)|[\(\{⦃\[])", nxt_vs)):
                    p_idx += 1
                    var_src += " " + nxt_v
                    v_bal += sum(1 for c in nxt_v if c in "([{⦃") - sum(1 for c in nxt_v if c in ")]}⦄")
                    continue
                break
            # Detect `variable (...) in ...` at bracket depth 0 (scoped strictly to immediately following decl)
            in_split: tuple[int, int] | None = None
            vd = 0
            vi = 0
            vn = len(var_src)
            while vi < vn:
                vc = var_src[vi]
                if vc == "«":
                    vi += 1
                    while vi < vn and var_src[vi] not in ("»", "\n"):
                        vi += 1
                    if vi < vn and var_src[vi] == "»":
                        vi += 1
                    continue
                if vc in "([{⦃":
                    vd += 1
                elif vc in ")]}⦄" and vd > 0:
                    vd -= 1
                elif vd == 0 and (vi == 0 or not (var_src[vi - 1].isalnum() or var_src[vi - 1] in "_'«»")):
                    m_in_kw = re.match(r"^in(?=\s|$)", var_src[vi:])
                    if m_in_kw:
                        in_split = (vi, vi + 2)
                        break
                vi += 1
            if in_split is not None:
                in_map: dict[str, bool] = {}
                _collect_var_map_from_src(var_src[: in_split[0]], in_map)
                after_in_v = var_src[in_split[1] :].strip()
                if _decl_consume_re.search(after_in_v):
                    pending_in_vars.clear()
                else:
                    pending_in_vars.update(in_map)
            else:
                pending_in_vars.clear()
                target_map = scope_stack[-1][2] if scope_stack else module_vars
                _collect_var_map_from_src(var_src, target_map)
            continue
        if pending_in_vars and _decl_consume_re.search(pl):
            pending_in_vars.clear()

    merged_vars = dict(module_vars)
    for _, _, frame_vars in scope_stack:
        merged_vars.update(frame_vars)
    merged_vars.update(pending_in_vars)
    nat_vars: set[str] = {k for k, is_nat in merged_vars.items() if is_nat}
    _collect_from_bracket_src(param_header, nat_vars)
    return nat_vars


def _subst_lean_expr_capture_avoiding(expr: str, subst: dict[str, str]) -> str:
    """Substitute parameter names in `expr` according to `subst`, avoiding capture under Lean binders."""
    if not subst or not expr:
        return expr

    used_ids: set[str] = set(_LEAN_IDENT_TOKEN_RE.findall(expr))
    for k_s, v_s in subst.items():
        used_ids.add(k_s)
        used_ids.update(_LEAN_IDENT_TOKEN_RE.findall(v_s))

    def _active_rhs_ids(cur_s: dict[str, str], exclude: set[str] | None = None) -> set[str]:
        rhs_ids: set[str] = set()
        for k_s, v_s in cur_s.items():
            if exclude and k_s in exclude:
                continue
            for m_r in re.finditer(rf"(?<![.\w'»])({_LEAN_IDENT_SEG})(?![\w'»])", v_s):
                tok_r = m_r.group(1)
                if tok_r not in _LEAN_TERM_KEYWORDS:
                    rhs_ids.add(tok_r)
        return rhs_ids

    def _alloc_fresh(base: str) -> str:
        stem = base.strip("«»")
        is_guill = base.startswith("«") and base.endswith("»")
        idx_f = 1
        while True:
            cand_raw = f"{stem}_{idx_f}"
            cand = f"«{cand_raw}»" if is_guill else cand_raw
            if cand not in used_ids and cand_raw not in used_ids:
                used_ids.add(cand)
                used_ids.add(cand_raw)
                return cand
            idx_f += 1

    def _bind_name(tok_b: str, target_subst: dict[str, str]) -> str:
        if tok_b == "_" or tok_b in _LEAN_TERM_KEYWORDS:
            return tok_b
        if tok_b in _active_rhs_ids(target_subst, exclude={tok_b}):
            fresh_b = _alloc_fresh(tok_b)
            target_subst[tok_b] = fresh_b
            return fresh_b
        target_subst.pop(tok_b, None)
        return tok_b

    def _bind_names_in_lhs(lhs_text: str, target_subst: dict[str, str]) -> str:
        out_l: list[str] = []
        pos_l = 0
        for m_tok in _LEAN_IDENT_TOKEN_RE.finditer(lhs_text):
            out_l.append(lhs_text[pos_l : m_tok.start()])
            tok_b = m_tok.group(0)
            if m_tok.start() > 0 and lhs_text[m_tok.start() - 1] == ".":
                out_l.append(tok_b)
            else:
                out_l.append(_bind_name(tok_b, target_subst))
            pos_l = m_tok.end()
        out_l.append(lhs_text[pos_l:])
        return "".join(out_l)

    def _subst_binder_chunk(chunk: str, cur_subst: dict[str, str]) -> tuple[str, dict[str, str]]:
        """Substitute type annotations in a `∀`/`∃`/`fun` binder chunk and return `(rendered, body_subst)`."""
        out_c: list[str] = []
        next_subst = dict(cur_subst)
        pending_bare: list[tuple[int, str]] = []
        ci = 0
        cn = len(chunk)
        open_b = {"(": ")", "{": "}", "⦃": "⦄", "[": "]"}

        def _flush_pending_bare() -> None:
            nonlocal pending_bare
            for out_idx, tok_b in pending_bare:
                out_c[out_idx] = _bind_name(tok_b, next_subst)
            pending_bare = []

        while ci < cn:
            ch = chunk[ci]
            if ch.isspace():
                out_c.append(ch)
                ci += 1
                continue
            if ch in open_b:
                _flush_pending_bare()
                close_c = open_b[ch]
                depth_b = 1
                cj = ci + 1
                while cj < cn and depth_b > 0:
                    if chunk[cj] == "«":
                        cj += 1
                        while cj < cn and chunk[cj] not in ("»", "\n"):
                            cj += 1
                        if cj < cn and chunk[cj] == "»":
                            cj += 1
                        continue
                    if chunk[cj] == ch:
                        depth_b += 1
                    elif chunk[cj] == close_c:
                        depth_b -= 1
                    cj += 1
                if depth_b == 0:
                    inner = chunk[ci + 1 : cj - 1]
                    col_i = _find_top_level_colon(inner)
                    if ch == "[":
                        out_c.append(ch + _walk(inner, next_subst) + close_c)
                    elif col_i is not None:
                        lhs_b = inner[:col_i]
                        ty_b = inner[col_i + 1 :]
                        sub_ty = _walk(ty_b, next_subst)
                        rendered_lhs = _bind_names_in_lhs(lhs_b, next_subst)
                        out_c.append(ch + rendered_lhs + ":" + sub_ty + close_c)
                    else:
                        rendered_inner = _bind_names_in_lhs(inner, next_subst)
                        out_c.append(ch + rendered_inner + close_c)
                    ci = cj
                    continue
            if ch == ":" and not chunk.startswith((":=", "::"), ci):
                ty_rest = chunk[ci + 1 :]
                sub_ty = _walk(ty_rest, next_subst)
                _flush_pending_bare()
                out_c.append(":" + sub_ty)
                break
            m_id = _LEAN_IDENT_TOKEN_RE.match(chunk, ci)
            if m_id:
                tok_b = m_id.group(0)
                if tok_b != "_" and tok_b not in _LEAN_TERM_KEYWORDS:
                    pending_bare.append((len(out_c), tok_b))
                out_c.append(tok_b)
                ci = m_id.end()
                continue
            out_c.append(ch)
            ci += 1
        _flush_pending_bare()
        return "".join(out_c), next_subst

    def _walk(sub_expr: str, init_subst: dict[str, str]) -> str:
        if not init_subst or not sub_expr:
            return sub_expr
        out: list[str] = []
        cur_subst = dict(init_subst)
        frame_stack: list[tuple[str, dict[str, str]]] = []
        open_close = {"(": ")", "[": "]", "{": "}", "⦃": "⦄", "⟨": "⟩"}
        i = 0
        n = len(sub_expr)
        while i < n:
            ch = sub_expr[i]
            if ch == "«":
                j = i + 1
                while j < n and sub_expr[j] not in ("»", "\n"):
                    j += 1
                if j < n and sub_expr[j] == "»":
                    j += 1
                tok = sub_expr[i:j]
                if i > 0 and sub_expr[i - 1] == ".":
                    out.append(tok)
                else:
                    out.append(cur_subst.get(tok, tok))
                i = j
                continue
            if ch in open_close:
                close_ch = open_close[ch]
                if ch in ("(", "{", "⦃"):
                    depth_p = 1
                    j = i + 1
                    while j < n and depth_p > 0:
                        if sub_expr[j] == "«":
                            j += 1
                            while j < n and sub_expr[j] not in ("»", "\n"):
                                j += 1
                            if j < n and sub_expr[j] == "»":
                                j += 1
                            continue
                        if sub_expr[j] == ch:
                            depth_p += 1
                        elif sub_expr[j] == close_ch:
                            depth_p -= 1
                        j += 1
                    if depth_p == 0:
                        after_ws = sub_expr[j:].lstrip()
                        if after_ws.startswith(("→", "->")):
                            inner = sub_expr[i + 1 : j - 1]
                            col_i = _find_top_level_colon(inner)
                            if col_i is not None:
                                lhs_raw = inner[:col_i]
                                lhs_toks = _split_top_level_ws(lhs_raw.strip())
                                if lhs_toks and all(
                                    _LEAN_IDENT_SEG_RE.fullmatch(t) and t not in _LEAN_TERM_KEYWORDS
                                    for t in lhs_toks
                                ):
                                    ty_raw = inner[col_i + 1 :]
                                    sub_ty = _walk(ty_raw, cur_subst)
                                    rendered_lhs = _bind_names_in_lhs(lhs_raw, cur_subst)
                                    out.append(ch + rendered_lhs + ":" + sub_ty + close_ch)
                                    i = j
                                    continue
                frame_stack.append((close_ch, dict(cur_subst)))
                out.append(ch)
                i += 1
                continue
            if frame_stack and ch == frame_stack[-1][0]:
                _, saved_subst = frame_stack.pop()
                cur_subst = saved_subst
                out.append(ch)
                i += 1
                continue
            is_at_ident_start = i == 0 or not (sub_expr[i - 1].isalnum() or sub_expr[i - 1] in "_'».")
            m_lh = re.match(r"(let|have)(?=\s|[({«])", sub_expr[i:])
            if m_lh and is_at_ident_start and not (m_lh.group(1) == "let" and _preceded_by_kw(sub_expr, i, "if")):
                d_l = 0
                k_a = i + m_lh.end()
                assign_pos: int | None = None
                while k_a < n:
                    ck = sub_expr[k_a]
                    if ck == "«":
                        k_a += 1
                        while k_a < n and sub_expr[k_a] not in ("»", "\n"):
                            k_a += 1
                        if k_a < n and sub_expr[k_a] == "»":
                            k_a += 1
                        continue
                    if ck in open_close:
                        d_l += 1
                    elif ck in (")", "]", "}", "⦄", "⟩"):
                        if d_l == 0:
                            break
                        d_l -= 1
                    elif d_l == 0:
                        if sub_expr.startswith(":=", k_a):
                            assign_pos = k_a
                            break
                        if ck in (";", "\n"):
                            break
                    k_a += 1
                if assign_pos is not None:
                    lhs_let = sub_expr[i + m_lh.end() : assign_pos]
                    col_let = _find_top_level_colon(lhs_let)
                    if col_let is not None:
                        binders_let = lhs_let[:col_let]
                        ty_let: str | None = lhs_let[col_let + 1 :]
                    else:
                        binders_let = lhs_let
                        ty_let = None
                    val_start = assign_pos + 2
                    d_v = 0
                    k_v = val_start
                    val_end = n
                    sep_str = ""
                    body_start = n
                    while k_v < n:
                        ck = sub_expr[k_v]
                        if ck == "«":
                            k_v += 1
                            while k_v < n and sub_expr[k_v] not in ("»", "\n"):
                                k_v += 1
                            if k_v < n and sub_expr[k_v] == "»":
                                k_v += 1
                            continue
                        if ck in open_close:
                            d_v += 1
                        elif ck in (")", "]", "}", "⦄", "⟩"):
                            if d_v == 0:
                                val_end = k_v
                                body_start = k_v
                                break
                            d_v -= 1
                        elif d_v == 0:
                            if ck == ";":
                                val_end = k_v
                                sep_str = ";"
                                body_start = k_v + 1
                                break
                            if ck == "\n":
                                val_so_far = sub_expr[val_start:k_v].strip()
                                rest_after = sub_expr[k_v + 1 :].lstrip()
                                if (
                                    val_so_far
                                    and not _LET_HAVE_CONT_END_RE.search(val_so_far)
                                    and not _LET_HAVE_CONT_START_RE.match(rest_after)
                                ):
                                    val_end = k_v
                                    sep_str = "\n"
                                    body_start = k_v + 1
                                    break
                        k_v += 1
                    val_raw = sub_expr[val_start:val_end]
                    # Bind the let/have-defined identifier(s) (first token or pattern) for the body
                    b_stripped = binders_let.strip()
                    if not b_stripped:
                        sub_ty_let = _walk(ty_let, cur_subst) if ty_let is not None else None
                        sub_val_let = _walk(val_raw, cur_subst)
                        cur_subst.pop("this", None)
                        rendered_binders = binders_let
                    elif b_stripped.startswith(("(", "⟨", "{")) or _LEAN_IDENT_SEG_RE.fullmatch(b_stripped):
                        sub_ty_let = _walk(ty_let, cur_subst) if ty_let is not None else None
                        sub_val_let = _walk(val_raw, cur_subst)
                        rendered_binders = _bind_names_in_lhs(binders_let, cur_subst)
                    else:
                        # `let/have f (x : T) ...`: parameter binders scope over `ty_let` and `val_raw`; `f` is bound in the body
                        val_subst = dict(cur_subst)
                        m_fn = re.match(rf"^(\s*)({_LEAN_IDENT_SEG})([\s\S]*)$", binders_let)
                        if m_fn:
                            rendered_fn = _bind_name(m_fn.group(2), cur_subst)
                            rendered_params, val_subst = _subst_binder_chunk(m_fn.group(3), val_subst)
                            rendered_binders = m_fn.group(1) + rendered_fn + rendered_params
                        else:
                            rendered_binders = binders_let
                        sub_ty_let = _walk(ty_let, val_subst) if ty_let is not None else None
                        sub_val_let = _walk(val_raw, val_subst)
                    out.append(
                        m_lh.group(1)
                        + rendered_binders
                        + ((":" + sub_ty_let) if sub_ty_let is not None else "")
                        + ":="
                        + sub_val_let
                        + sep_str
                    )
                    i = body_start
                    continue
            # Binder introducers: `∀`/`forall`/`∃`/`exists` ... `,` and `fun`/`λ` ... `=>`
            m_q = re.match(r"(∀|∃|(?:forall|exists)(?=\s|[({\[⦃«]))", sub_expr[i:])
            if m_q and is_at_ident_start:
                d_q = 0
                k = i + m_q.end()
                comma_pos: int | None = None
                while k < n:
                    ck = sub_expr[k]
                    if ck == "«":
                        k += 1
                        while k < n and sub_expr[k] not in ("»", "\n"):
                            k += 1
                        if k < n and sub_expr[k] == "»":
                            k += 1
                        continue
                    if ck in open_close:
                        d_q += 1
                    elif ck in (")", "]", "}", "⦄", "⟩") and d_q > 0:
                        d_q -= 1
                    elif d_q == 0 and ck == ",":
                        comma_pos = k
                        break
                    elif d_q == 0 and ck in (")", "]", "}", "⦄", "⟩"):
                        break
                    k += 1
                if comma_pos is not None:
                    chunk_raw = sub_expr[i + m_q.end() : comma_pos]
                    rendered_chunk, next_subst = _subst_binder_chunk(chunk_raw, cur_subst)
                    out.append(m_q.group(1) + rendered_chunk + ",")
                    cur_subst = next_subst
                    i = comma_pos + 1
                    continue
            m_fun = re.match(r"(?:fun|λ)(?=\s|[({⦃⟨_])", sub_expr[i:])
            if m_fun and is_at_ident_start:
                d_f = 0
                k = i + m_fun.end()
                arrow_pos: int | None = None
                while k < n:
                    ck = sub_expr[k]
                    if ck == "«":
                        k += 1
                        while k < n and sub_expr[k] not in ("»", "\n"):
                            k += 1
                        if k < n and sub_expr[k] == "»":
                            k += 1
                        continue
                    if ck in open_close:
                        d_f += 1
                    elif ck in (")", "]", "}", "⦄", "⟩") and d_f > 0:
                        d_f -= 1
                    elif d_f == 0 and sub_expr.startswith("=>", k):
                        arrow_pos = k
                        break
                    elif d_f == 0 and ck in (")", "]", "}", "⦄", "⟩"):
                        break
                    k += 1
                if arrow_pos is not None:
                    chunk_raw = sub_expr[i + m_fun.end() : arrow_pos]
                    rendered_chunk, next_subst = _subst_binder_chunk(chunk_raw, cur_subst)
                    out.append(m_fun.group(0) + rendered_chunk + "=>")
                    cur_subst = next_subst
                    i = arrow_pos + 2
                    continue
            m_id = _LEAN_IDENT_TOKEN_RE.match(sub_expr, i)
            if m_id:
                tok = m_id.group(0)
                if i > 0 and sub_expr[i - 1] == ".":
                    out.append(tok)
                else:
                    out.append(cur_subst.get(tok, tok))
                i = m_id.end()
                continue
            out.append(ch)
            i += 1
        return "".join(out)

    return _walk(expr, subst)


def _instantiate_struct_field_types(
    type_expr: str,
    struct_specs: dict[str, tuple[list[tuple[str, bool, bool]], list[tuple[str, str]]]] | None,
) -> list[tuple[str, str]] | None:
    """Instantiate structure field types with concrete/variable arguments from `type_expr`."""
    if not struct_specs or not type_expr:
        return None
    s = _strip_outer_parens(type_expr.strip())
    m_head = re.match(rf"^({_LEAN_QUAL_IDENT})(?:\.\{{[^}}]*\}})?", s)
    if not m_head:
        return None
    head = m_head.group(1)
    spec = struct_specs.get(head) or struct_specs.get(lean_short_name(head))
    if not spec:
        return None
    params, base_fields = spec
    args_str = s[m_head.end() :].strip()
    subst: dict[str, str] = {}
    exp_params = [p_name for p_name, is_exp, _ in params if is_exp]
    pos_idx = 0
    for tok in _split_top_level_args(args_str):
        if tok.startswith(("{", "[", "⦃")):
            continue
        inner = _strip_outer_parens(tok)
        m_named = re.match(rf"^({_LEAN_IDENT_SEG})\s*:=\s*([\s\S]+)$", inner)
        if m_named:
            val_named = m_named.group(2).strip()
            if any(c.isspace() for c in val_named) and _strip_outer_parens(val_named) == val_named:
                val_named = f"({val_named})"
            subst[m_named.group(1)] = val_named
        else:
            while pos_idx < len(exp_params) and exp_params[pos_idx] in subst:
                pos_idx += 1
            if pos_idx < len(exp_params):
                subst[exp_params[pos_idx]] = tok
                pos_idx += 1
    if not subst:
        return list(base_fields)
    return [(fname, _subst_lean_expr_capture_avoiding(fty, subst)) for fname, fty in base_fields]


def _split_top_level_binary_and(prop: str) -> tuple[str, str] | None:
    """If `prop` is a top-level conjunction `A ∧ B` (with no looser top-level `∀`/`→`/`↔`/`∨`), return `(A, B)`."""
    s = _strip_outer_parens(prop.strip())
    if not s:
        return None
    if re.match(r"^(?:∀|forall(?=\s|[({\[⦃«])|∃|exists(?=\s|[({\[⦃«]))", s):
        return None
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    first_and: tuple[int, int] | None = None
    i = 0
    n = len(s)
    while i < n:
        ch = s[i]
        if ch == "«":
            i += 1
            while i < n and s[i] not in ("»", "\n"):
                i += 1
            if i < n and s[i] == "»":
                i += 1
            continue
        if ch in open_ch:
            depth += 1
        elif ch in close_ch and depth > 0:
            depth -= 1
        elif depth == 0:
            if s.startswith(("->", "↔", "<->", "\\/"), i) or ch in ("→", "∨"):
                return None
            if first_and is None:
                if ch == "∧":
                    first_and = (i, i + 1)
                elif s.startswith("/\\", i):
                    first_and = (i, i + 2)
        i += 1
    if first_and is None:
        return None
    lhs = s[: first_and[0]].strip()
    rhs = s[first_and[1] :].strip()
    return (lhs, rhs) if (lhs and rhs) else None


def _expr_has_hole(expr: str) -> bool:
    """Return True iff `expr` contains a Lean metavariable hole `?_` or `?ident`."""
    return bool(re.search(rf"(?<![\w'»])\?(?:_|{_LEAN_IDENT_SEG})(?![\w'»])", expr))


def _split_top_level_iff(prop: str) -> tuple[str, str] | None:
    """If `prop` has a single top-level `↔`/`<->` and no top-level `→`/`->`/`∨`/`\\/`, return `(lhs, rhs)`."""
    s = _strip_outer_parens(prop.strip())
    if not s:
        return None
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    iff_pos: tuple[int, int] | None = None
    i = 0
    n = len(s)
    while i < n:
        ch = s[i]
        if ch == "«":
            i += 1
            while i < n and s[i] not in ("»", "\n"):
                i += 1
            if i < n and s[i] == "»":
                i += 1
            continue
        if ch in open_ch:
            depth += 1
        elif ch in close_ch and depth > 0:
            depth -= 1
        elif depth == 0:
            if s.startswith(("->", "\\/"), i) or ch in ("→", "∨"):
                return None
            if ch == "↔":
                if iff_pos is not None:
                    return None
                iff_pos = (i, i + 1)
            elif s.startswith("<->", i):
                if iff_pos is not None:
                    return None
                iff_pos = (i, i + 3)
                i += 3
                continue
        i += 1
    if iff_pos is None:
        return None
    lhs = s[: iff_pos[0]].strip()
    rhs = s[iff_pos[1] :].strip()
    return (lhs, rhs) if (lhs and rhs) else None


def _extract_eq_goal_lhs(goal_prop: str) -> str | None:
    """Extract the LHS expression of a top-level `lhs = rhs` or `HEq lhs rhs` goal."""
    s = _strip_outer_parens(goal_prop.strip())
    if not s:
        return None
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    i = 0
    n = len(s)
    while i < n:
        ch = s[i]
        if ch == "«":
            i += 1
            while i < n and s[i] not in ("»", "\n"):
                i += 1
            if i < n and s[i] == "»":
                i += 1
            continue
        if ch in open_ch:
            depth += 1
        elif ch in close_ch and depth > 0:
            depth -= 1
        elif (
            depth == 0
            and ch == "="
            and not s.startswith(("==", "=>"), i)
            and (i == 0 or s[i - 1] not in (":", "=", "<", ">", "!"))
        ):
            lhs = s[:i].strip()
            return lhs or None
        i += 1
    toks = _split_top_level_ws(s)
    if toks and toks[0] == "HEq" and len(toks) == 3:
        return toks[1]
    if toks and toks[0] == "@HEq" and len(toks) >= 4:
        pos_t = [t for t in toks[1:] if not (t.strip().startswith("{") and t.strip().endswith("}"))]
        if len(pos_t) >= 2:
            return pos_t[-2]
    return None


def _eq_refl_matches_goal(
    expr: str,
    goal_prop: str | None,
    *,
    nat_vars: frozenset[str] | set[str] | None = None,
) -> bool:
    """Return True iff `Eq.refl x` / `@Eq.refl _ x` has wildcard `_` or `x` normalizing to `goal_prop` LHS."""
    arg = _extract_eq_refl_arg(expr)
    if arg is None:
        return False
    if arg.strip() == "_" or not goal_prop:
        return True
    goal_lhs = _extract_eq_goal_lhs(goal_prop)
    if goal_lhs is None:
        return True
    return _normalize_suffices_atom(arg, nat_vars=nat_vars) == _normalize_suffices_atom(goal_lhs, nat_vars=nat_vars)


def _split_top_level_semi_steps(tail_s: str) -> list[str]:
    """Split a tactic sequence on top-level `;` and non-continuing newlines."""
    steps: list[str] = []
    cur: list[str] = []
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    i = 0
    n = len(tail_s)
    while i < n:
        ch = tail_s[i]
        if ch == "«":
            cur.append(ch)
            i += 1
            while i < n and tail_s[i] not in ("»", "\n"):
                cur.append(tail_s[i])
                i += 1
            if i < n and tail_s[i] == "»":
                cur.append("»")
                i += 1
            continue
        if ch in open_ch:
            depth += 1
            cur.append(ch)
        elif ch in close_ch and depth > 0:
            depth -= 1
            cur.append(ch)
        elif depth == 0 and ch == ";":
            seg = "".join(cur).strip()
            if seg:
                steps.append(seg)
            cur.clear()
        elif depth == 0 and ch == "\n":
            seg_so_far = "".join(cur).strip()
            rest_l = tail_s[i + 1 :].lstrip()
            nxt_is_pipe = rest_l.startswith("|") and not rest_l.startswith(("||", "|>"))
            if (
                seg_so_far
                and not nxt_is_pipe
                and not re.search(
                    r"(?:\b(?:exact|refine'?|by|all_goals|any_goals|repeat'?|try|focus|first|"
                    r"with_reducible|with_reducible_and_instances|iterate(?:\s+\d+)?)|:=|=>)\s*$",
                    seg_so_far,
                )
            ):
                steps.append(seg_so_far)
                cur.clear()
            else:
                cur.append(" ")
        else:
            cur.append(ch)
        i += 1
    rem = "".join(cur).strip()
    if rem:
        steps.append(rem)
    return steps


def _resolve_ctor_scope_fields(
    ctor_text: str,
    parent_field_ty: str | None,
    struct_specs: dict[str, tuple[list[tuple[str, bool, bool]], list[tuple[str, str]]]] | None,
) -> list[tuple[str, str]] | None:
    """Resolve the ordered subgoal `(field_name, field_type)` list opened by `ctor_text`."""
    target_ty = parent_field_ty
    struct_param_names = (
        {k: {p_name for p_name, _, _ in p_specs} for k, (p_specs, _) in struct_specs.items()}
        if struct_specs
        else None
    )
    m_app_span = _match_ctor_apply_in_line(
        ctor_text,
        allow_trivial_field_args=True,
        struct_param_names=struct_param_names,
    )
    if m_app_span is not None:
        head_raw = re.sub(r"\.\{[^}]*\}$", "", m_app_span[2].lstrip("@"))
        if head_raw.endswith(".mk"):
            spec_name = head_raw[:-3]
            if not target_ty or lean_short_name(target_ty.split()[0]) != lean_short_name(spec_name):
                target_ty = spec_name
    else:
        m_app = re.search(
            rf"(?<![\w'»])(?:apply|refine'?)\s+\(*@?({_LEAN_QUAL_IDENT})\.mk(?=\s|$|\(|\))",
            ctor_text,
        )
        if m_app:
            spec_name = m_app.group(1)
            if not target_ty or lean_short_name(target_ty.split()[0]) != lean_short_name(spec_name):
                target_ty = spec_name
    base_fields = _instantiate_struct_field_types(target_ty or "", struct_specs)
    if base_fields is None and target_ty:
        bin_and = _split_top_level_binary_and(target_ty)
        if bin_and is not None:
            base_fields = [("left", bin_and[0]), ("right", bin_and[1])]
        else:
            iff_pair = _split_top_level_iff(_strip_outer_parens(target_ty))
            if iff_pair is not None:
                base_fields = [("mp", f"({iff_pair[0]}) → ({iff_pair[1]})"), ("mpr", f"({iff_pair[1]}) → ({iff_pair[0]})")]
    if base_fields is None:
        return None
    m_ref = re.search(r"(?<![\w'»])refine'?(?:\s+|(?=[⟨{(]))([\s\S]+)$", ctor_text)
    if not m_ref:
        if m_app_span is not None:
            app_body = ctor_text[m_app_span[0] : m_app_span[1]]
            app_toks = _unwrap_ctor_app_tokens(re.sub(r"^(?:apply)\s+", "", app_body.strip()))
            if len(app_toks) >= 2 and _CTOR_HEAD_RE.fullmatch(app_toks[0]):
                param_names = _ctor_param_names_for_head(app_toks[0], struct_param_names)
                base_field_names = {fn for fn, _ in base_fields}
                supplied_named: set[str] = set()
                for t in app_toks[1:]:
                    ts = t.strip()
                    if ts.startswith("{") and ts.endswith("}"):
                        continue
                    a_name, a_val = _parse_named_ctor_arg(ts)
                    if a_name is not None and a_name not in param_names and a_name in base_field_names:
                        if not _expr_has_hole(a_val):
                            supplied_named.add(a_name)
                if supplied_named:
                    return [(fn, fty) for fn, fty in base_fields if fn not in supplied_named]
        return base_fields
    ref_body = _strip_outer_parens(m_ref.group(1).strip())
    if ref_body.startswith("⟨") and ref_body.endswith("⟩"):
        args = _split_top_level_commas(ref_body[1:-1])
        if len(args) == len(base_fields):
            return [fld for fld, a in zip(base_fields, args) if _expr_has_hole(a)]
        if len(args) > len(base_fields) and target_ty:
            conj_all = _split_top_level_conj(_strip_outer_parens(target_ty))
            if len(conj_all) == len(args):
                return [(f"h{k + 1}", p) for k, (p, a) in enumerate(zip(conj_all, args)) if _expr_has_hole(a)]
    elif ref_body.startswith("{") and ref_body.endswith("}") and _is_single_balanced_brace_block(ref_body):
        pairs = _split_struct_literal_fields(ref_body[1:-1])
        if pairs:
            hole_fields = {fn for fn, val in pairs if _expr_has_hole(val)}
            return [(fn, fty) for fn, fty in base_fields if fn in hole_fields]
    else:
        toks = _unwrap_ctor_app_tokens(ref_body)
        if len(toks) >= 2 and _CTOR_HEAD_RE.fullmatch(toks[0]):
            head = toks[0]
            param_names = _ctor_param_names_for_head(head, struct_param_names)
            base_field_names = {fn for fn, _ in base_fields}
            named_map: dict[str, str] = {}
            pos_vals: list[str] = []
            for t in toks[1:]:
                ts = t.strip()
                if ts.startswith("{") and ts.endswith("}"):
                    continue
                arg_name, arg_val = _parse_named_ctor_arg(ts)
                if arg_name is not None:
                    if arg_name in param_names:
                        continue
                    if arg_name in base_field_names:
                        named_map[arg_name] = arg_val
                        continue
                pos_vals.append(arg_val)
            rem_fields = [fn for fn, _ in base_fields if fn not in named_map]
            if len(pos_vals) >= len(rem_fields):
                pos_tail = pos_vals[-len(rem_fields) :] if rem_fields else []
                assigned_vals = dict(named_map)
                for fn, pv in zip(rem_fields, pos_tail):
                    assigned_vals[fn] = pv
                return [(fn, fty) for fn, fty in base_fields if _expr_has_hole(assigned_vals.get(fn, ""))]
    return base_fields


def _unwrap_leaf_or_ctor_proof(tac_text: str) -> tuple[str, bool]:
    """Unwrap `exact`/`refine`/`by`/parens/`id`/`@id`/type-ascriptions, returning `(inner_expr, is_tactic_mode)`."""
    s = _strip_outer_parens(tac_text.strip())
    is_tactic = True
    for _ in range(10):
        s = _strip_outer_parens(s)
        s = re.sub(r"(?:<;>|;)\s*done\s*$", "", s).strip()
        m_ex = re.match(r"^(?:exact|refine'?)(?:\s+|(?=[⟨{(]))(.+)$", s, flags=re.S)
        if m_ex:
            expr = _strip_type_ascription(m_ex.group(1).strip())
            if re.match(r"^by(?=\s|$)", expr):
                s = expr[2:].strip()
                is_tactic = True
                continue
            return expr, False
        m_by = re.match(r"^by(?=\s|$)(.*)$", s, flags=re.S)
        if m_by:
            s = m_by.group(1).strip()
            is_tactic = True
            continue
        break
    return _strip_type_ascription(s) if not is_tactic else s, is_tactic


def _field_accepts_leaf_tactic(
    first_arm_no_done: str,
    first_arm_expr: str,
    field_ty: str | None,
    *,
    nat_vars: frozenset[str] | set[str] | None = None,
    is_tactic_mode: bool | None = None,
) -> bool:
    """Return True iff trivial leaf tactic `first_arm_no_done` is guaranteed to close `field_ty`."""
    if not field_ty:
        return False
    _, f_kind, _ = _classify_suffices_prop_detail(field_ty, nat_vars=nat_vars)
    if is_tactic_mode is None:
        is_tactic_mode = bool(re.fullmatch(r"trivial", first_arm_no_done.strip()))
    if is_tactic_mode and re.fullmatch(r"trivial", first_arm_expr.strip()):
        return f_kind in ("true", "eq_refl", "iff_refl")
    if re.fullmatch(r"(?:trivial|True\.intro)", first_arm_expr):
        return f_kind == "true"
    if re.fullmatch(r"Iff\.rfl", first_arm_expr):
        return f_kind == "iff_refl"
    if re.fullmatch(r"rfl", first_arm_expr):
        return f_kind == "eq_refl"
    if _is_eq_refl_expr(first_arm_expr):
        return f_kind == "eq_refl" and _eq_refl_matches_goal(first_arm_expr, field_ty, nat_vars=nat_vars)
    return False


def _split_top_level_arrow(type_expr: str) -> tuple[str, str] | None:
    """Split `A → B` or `A -> B` at the first top-level arrow outside brackets/guillemets."""
    s = _strip_outer_parens(type_expr.strip())
    if not s:
        return None
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    depth = 0
    i = 0
    n = len(s)
    while i < n:
        ch = s[i]
        if ch == "«":
            i += 1
            while i < n and s[i] not in ("»", "\n"):
                i += 1
            if i < n and s[i] == "»":
                i += 1
            continue
        if ch in open_ch:
            depth += 1
        elif ch in close_ch and depth > 0:
            depth -= 1
        elif depth == 0:
            if ch == "→":
                return s[:i].strip(), s[i + 1 :].strip()
            if s.startswith("->", i):
                return s[:i].strip(), s[i + 2 :].strip()
        i += 1
    return None


def _peel_explicit_goal_binder_with_dom(goal_ty: str) -> tuple[str | None, str | None, str | None]:
    """Peel one explicit leading `→`/`->` or `∀` binder from `goal_ty`, returning `(binder_name, dom_ty, codomain)`."""
    cur = _strip_outer_parens(goal_ty.strip())
    for _ in range(16):
        peeled = _strip_leading_let_have(cur)
        if peeled is not None:
            cur = _strip_outer_parens(peeled)
            continue
        arr = _split_top_level_arrow(cur)
        if arr is not None:
            dom, cod = arr
            if dom.startswith(("{", "[", "⦃")) and dom.endswith(("}", "]", "⦄")):
                cur = _strip_outer_parens(cod)
                continue
            if dom.startswith("(") and dom.endswith(")"):
                inner = dom[1:-1].strip()
                ci = _find_top_level_colon(inner)
                if ci is not None:
                    ty_raw = inner[ci + 1 :].strip()
                    ty = _strip_outer_parens(ty_raw)
                    names = _split_top_level_ws(inner[:ci].strip())
                    if len(names) >= 2:
                        rem_dom = "(" + " ".join(names[1:]) + f" : {ty_raw})"
                        b_nm = names[0] if _LEAN_IDENT_SEG_RE.fullmatch(names[0]) else None
                        return b_nm, ty, f"{rem_dom} → {cod}"
                    b_nm = names[0] if (len(names) == 1 and _LEAN_IDENT_SEG_RE.fullmatch(names[0])) else None
                    return b_nm, ty, cod
            return None, _strip_outer_parens(dom), cod
        m_forall = re.match(r"^(?:∀|forall(?=\s|[({\[⦃«]))", cur)
        if m_forall:
            comma_idx = _forall_comma_map(cur, _bracket_depths(cur)).get(0)
            if comma_idx is None:
                return None, None, None
            binder_chunk = cur[m_forall.end() : comma_idx].strip()
            cod = cur[comma_idx + 1 :].strip()
            bi = 0
            bn = len(binder_chunk)
            while bi < bn and binder_chunk[bi].isspace():
                bi += 1
            if bi < bn and binder_chunk[bi] in ("(", "{", "⦃", "["):
                b_ch = binder_chunk[bi]
                bd = 1
                bj = bi + 1
                while bj < bn and bd > 0:
                    if binder_chunk[bj] in ("(", "{", "⦃", "["):
                        bd += 1
                    elif binder_chunk[bj] in (")", "}", "⦄", "]"):
                        bd -= 1
                    bj += 1
                if bd != 0:
                    return None, None, None
                inner = binder_chunk[bi + 1 : bj - 1].strip()
                rest_chunk = binder_chunk[bj:].strip()
                if b_ch != "(":
                    cur = _strip_outer_parens(f"∀ {rest_chunk}, {cod}" if rest_chunk else cod)
                    continue
                ci = _find_top_level_colon(inner)
                ty_raw = inner[ci + 1 :].strip() if ci is not None else ""
                ty = _strip_outer_parens(ty_raw) if ci is not None else None
                lhs_toks = _split_top_level_ws(inner[:ci].strip() if ci is not None else inner) or ["_"]
                b_nm = lhs_toks[0] if _LEAN_IDENT_SEG_RE.fullmatch(lhs_toks[0]) else None
                if len(lhs_toks) >= 2:
                    rem_grp = "(" + " ".join(lhs_toks[1:]) + (f" : {ty_raw}" if ci is not None else "") + ")"
                    rem_chunk = (rem_grp + (" " + rest_chunk if rest_chunk else "")).strip()
                    return b_nm, ty, f"∀ {rem_chunk}, {cod}"
                rem_goal = f"∀ {rest_chunk}, {cod}" if rest_chunk else cod
                return b_nm, ty, rem_goal
            ci = _find_top_level_colon(binder_chunk)
            ty_raw = binder_chunk[ci + 1 :].strip() if ci is not None else ""
            ty = _strip_outer_parens(ty_raw) if ci is not None else None
            lhs_toks = _split_top_level_ws(binder_chunk[:ci].strip() if ci is not None else binder_chunk) or ["_"]
            b_nm = lhs_toks[0] if _LEAN_IDENT_SEG_RE.fullmatch(lhs_toks[0]) else None
            if len(lhs_toks) >= 2:
                rem_chunk = " ".join(lhs_toks[1:]) + (f" : {ty_raw}" if ci is not None else "")
                return b_nm, ty, f"∀ {rem_chunk}, {cod}"
            return b_nm, ty, cod
        return None, None, None
    return None, None, None


def _peel_explicit_goal_binder(goal_ty: str) -> str | None:
    """Peel one explicit leading `→`/`->` or `∀` domain from `goal_ty`, returning the codomain."""
    return _peel_explicit_goal_binder_with_dom(goal_ty)[2]


def _peel_intro_step(
    tac_str: str,
    goal_ty: str,
    cur_nat: frozenset[str] | set[str] | None,
) -> tuple[str | None, set[str]]:
    """Apply `intro`/`intros`/`rintro` in `tac_str` to `goal_ty`, returning `(new_goal_ty, new_nat_vars)`."""
    m_int = re.match(r"^(intro|intros|rintro)(?=\s|$)([\s\S]*)$", tac_str.strip())
    new_nat = set(cur_nat or ())
    if not m_int:
        return None, new_nat
    cmd = m_int.group(1)
    arg_str = m_int.group(2).strip()
    cur_ty = goal_ty
    if not arg_str:
        if cmd == "intros":
            for _ in range(16):
                b_nm, b_dom, next_ty = _peel_explicit_goal_binder_with_dom(cur_ty)
                if next_ty is None:
                    break
                if b_nm and b_nm != "_":
                    if b_dom in _NAT_ONLY_ASCRIPTIONS:
                        new_nat.add(b_nm)
                    else:
                        new_nat.discard(b_nm)
                cur_ty = next_ty
            return cur_ty, new_nat
        b_nm, b_dom, next_ty = _peel_explicit_goal_binder_with_dom(cur_ty)
        if next_ty is None:
            return None, new_nat
        if b_nm and b_nm != "_":
            if b_dom in _NAT_ONLY_ASCRIPTIONS:
                new_nat.add(b_nm)
            else:
                new_nat.discard(b_nm)
        return next_ty, new_nat
    for tok in _split_top_level_ws(arg_str):
        ts = tok.strip()
        if ts in ("|", "=>"):
            break
        if ts.startswith(("{", "[", "⦃")) and ts.endswith(("}", "]", "⦄")):
            continue
        if ts.startswith("(") and ts.endswith(")"):
            inner = ts[1:-1].strip()
            ci = _find_top_level_colon(inner)
            if ci is not None:
                ty = _strip_outer_parens(inner[ci + 1 :].strip())
                is_nat = ty in _NAT_ONLY_ASCRIPTIONS
                lhs_toks = _split_top_level_ws(inner[:ci].strip()) or ["_"]
                for lt in lhs_toks:
                    b_nm, b_dom, next_ty = _peel_explicit_goal_binder_with_dom(cur_ty)
                    if next_ty is None:
                        return None, new_nat
                    if b_nm and b_nm != "_":
                        if b_dom in _NAT_ONLY_ASCRIPTIONS:
                            new_nat.add(b_nm)
                        else:
                            new_nat.discard(b_nm)
                    for nm in _extract_pattern_bound_names(lt):
                        if is_nat:
                            new_nat.add(nm)
                        else:
                            new_nat.discard(nm)
                    cur_ty = next_ty
                continue
        b_nm, b_dom, next_ty = _peel_explicit_goal_binder_with_dom(cur_ty)
        if next_ty is None:
            return None, new_nat
        if b_nm and b_nm != "_":
            if b_dom in _NAT_ONLY_ASCRIPTIONS:
                new_nat.add(b_nm)
            else:
                new_nat.discard(b_nm)
        if _LEAN_IDENT_SEG_RE.fullmatch(ts) and ts not in _LEAN_TERM_KEYWORDS:
            if ts != "_":
                if b_dom in _NAT_ONLY_ASCRIPTIONS:
                    new_nat.add(ts)
                else:
                    new_nat.discard(ts)
        else:
            for nm in _extract_pattern_bound_names(ts):
                new_nat.discard(nm)
        cur_ty = next_ty
    return cur_ty, new_nat


def _split_top_level_bullet_groups(raw_tail: str) -> list[str] | None:
    """If `raw_tail` is a top-level bulleted tactic sequence (`·`/`•`), return each bullet group's body."""
    lines_b = [ln for ln in raw_tail.splitlines() if ln.strip()]
    if not lines_b:
        return None
    first_l = lines_b[0].lstrip()
    if not first_l.startswith(("·", "•")):
        return None
    outer_ind = len(lines_b[0][: len(lines_b[0]) - len(first_l)].replace("\t", "    "))
    groups: list[list[str]] = []
    for ln in lines_b:
        ln_l = ln.lstrip()
        ind = len(ln[: len(ln) - len(ln_l)].replace("\t", "    "))
        if ind == outer_ind and ln_l.startswith(("·", "•")):
            groups.append([ln_l[1:].lstrip()])
        elif ind > outer_ind and groups:
            groups[-1].append(ln)
        else:
            return None
    return ["\n".join(g).strip() for g in groups] if groups else None


def _dsimp_targets_goal(st: str) -> bool:
    """Return True iff `st` is a single `dsimp` tactic invocation that targets the goal `⊢`."""
    s = st.strip()
    m_ds = re.match(r"^dsimp(?=$|\s|\(|\[|\+|-)", s)
    if not m_ds:
        return False
    pos = m_ds.end()
    n = len(s)
    saw_at = False
    at_loc_parts: list[str] = []
    while pos < n:
        while pos < n and s[pos].isspace():
            pos += 1
        if pos >= n:
            break
        if s[pos] in ("(", "["):
            if saw_at:
                return False
            close_i = _find_matching_delim_lean(s, pos)
            if close_i is None:
                return False
            if re.search(r"\b(?:sorry|admit)\b", s[pos : close_i + 1]):
                return False
            pos = close_i + 1
            continue
        m_tok = re.match(r"\S+", s[pos:])
        if not m_tok:
            break
        tok = m_tok.group(0)
        if ";" in tok or "<;>" in tok or tok in ("sorry", "admit"):
            return False
        if not saw_at:
            if tok == "at":
                saw_at = True
            elif tok == "only" or tok.startswith(("+", "-")):
                pass
            else:
                return False
        else:
            at_loc_parts.append(tok)
        pos += len(tok)
    if not saw_at:
        return True
    if not at_loc_parts:
        return False
    return any("*" in t or "⊢" in t or t == "|-" for t in at_loc_parts)


def _can_fail_against_goal(
    expr: str,
    is_tactic: bool,
    goal_ty: str | None,
    *,
    in_ctor: bool = True,
    struct_specs: dict[str, tuple[list[tuple[str, bool, bool]], list[tuple[str, str]]]] | None = None,
    struct_field_counts: dict[str, int] | None = None,
    struct_param_names: dict[str, set[str]] | None = None,
    nat_vars: frozenset[str] | set[str] | None = None,
    _depth: int = 0,
) -> bool:
    """Return True iff `expr` (or tactic) can fail to close `goal_ty`."""
    if _depth > 15:
        return False
    s = _strip_outer_parens(expr.strip())
    if not s:
        return True
    if not is_tactic:
        s = _strip_type_ascription(s)
        if re.match(r"^by(?=\s|$)", s):
            s, is_tactic = _unwrap_leaf_or_ctor_proof(s)
    if is_tactic:
        for _ in range(8):
            while s.startswith("{") and s.endswith("}") and _is_single_balanced_brace_block(s):
                s = _strip_outer_parens(s[1:-1].strip())
            unwrapped, now_tactic = _unwrap_leaf_or_ctor_proof(s)
            if unwrapped == s and now_tactic == is_tactic:
                break
            s = unwrapped
            is_tactic = now_tactic
            if not is_tactic:
                break

    if re.fullmatch(r"(?:contradiction|done|sorry|admit)", s):
        return True
    if is_tactic and (re.fullmatch(r"simp(?:\s+only\s*\[\s*\])?", s) or _dsimp_targets_goal(s)):
        if not goal_ty:
            return not in_ctor
        is_u, g_k, _ = _classify_suffices_prop_detail(goal_ty, nat_vars=nat_vars)
        if s.startswith("dsimp"):
            return is_u or g_k not in ("eq_refl", "true")
        return is_u or g_k == "other"

    is_leaf = bool(
        re.fullmatch(r"(?:rfl|trivial|True\.intro|Iff\.rfl)", s) or _is_eq_refl_expr(s)
    )
    if is_leaf:
        if not in_ctor or not goal_ty:
            return True
        return not _field_accepts_leaf_tactic(
            s, s, goal_ty, nat_vars=nat_vars, is_tactic_mode=is_tactic
        )

    # Resolve target structure / conjunction fields if `goal_ty` is known
    target_fields: list[tuple[str, str]] | None = None
    goal_is_conj = False
    g_unsat = False
    g_kind = "other"
    if goal_ty:
        g_unsat, g_kind, goal_is_conj = _classify_suffices_prop_detail(goal_ty, nat_vars=nat_vars)
        if g_unsat:
            return True
        target_fields = _instantiate_struct_field_types(goal_ty, struct_specs)
        if target_fields is None:
            bin_and = _split_top_level_binary_and(goal_ty)
            if bin_and is not None:
                target_fields = [("left", bin_and[0]), ("right", bin_and[1])]
                goal_is_conj = True
            else:
                iff_pair = _split_top_level_iff(_strip_outer_parens(goal_ty))
                if iff_pair is not None:
                    target_fields = [
                        ("mp", f"({iff_pair[0]}) → ({iff_pair[1]})"),
                        ("mpr", f"({iff_pair[1]}) → ({iff_pair[0]})"),
                    ]

    if is_tactic:
        # Handle single-step `constructor <;> <leaf>` and sequential/bulleted `constructor` subgoal sequences
        m_all = re.match(r"^constructor\s*<;>\s*(.+)$", s, flags=re.S)
        if m_all:
            if not target_fields:
                return False
            sub_expr, sub_tac = _unwrap_leaf_or_ctor_proof(m_all.group(1))
            return any(
                _can_fail_against_goal(
                    sub_expr,
                    sub_tac,
                    fty,
                    in_ctor=True,
                    struct_specs=struct_specs,
                    struct_field_counts=struct_field_counts,
                    struct_param_names=struct_param_names,
                    nat_vars=nat_vars,
                    _depth=_depth + 1,
                )
                for _, fty in target_fields
            )
        m_semi = re.match(r"^constructor(?:\s*;\s*([\s\S]+)|\s*\n([\s\S]+))$", s)
        if m_semi:
            if not target_fields:
                return False
            raw_tail = (m_semi.group(1) or m_semi.group(2) or "").lstrip("\n").rstrip()
            bullet_groups = _split_top_level_bullet_groups(raw_tail)
            if bullet_groups is not None:
                if len(bullet_groups) > len(target_fields):
                    return False
                if len(bullet_groups) < len(target_fields):
                    return True
                return any(
                    _can_fail_against_goal(
                        grp,
                        True,
                        fty,
                        in_ctor=True,
                        struct_specs=struct_specs,
                        struct_field_counts=struct_field_counts,
                        struct_param_names=struct_param_names,
                        nat_vars=nat_vars,
                        _depth=_depth + 1,
                    )
                    for grp, (_, fty) in zip(bullet_groups, target_fields)
                )
            tail_s = raw_tail.strip()
            steps = _split_top_level_semi_steps(tail_s)
            goal_stack: list[tuple[str, str, set[str]]] = [
                (fn, fty, set(nat_vars or ())) for fn, fty in target_fields
            ]
            for idx_st, st in enumerate(steps):
                m_case = re.match(
                    r"^(?:[·•]\s*)?case'?\s+([^\s=>]+)((?:\s+[^\s=>]+)*)\s*=>\s*([\s\S]*)$",
                    st.strip(),
                )
                if m_case:
                    tag = m_case.group(1)
                    extra_args = (m_case.group(2) or "").strip()
                    st_c = _strip_outer_parens(m_case.group(3).strip())
                    match_idx = next(
                        (idx_g for idx_g, (g_fn, _, _) in enumerate(goal_stack) if g_fn == tag),
                        None,
                    )
                    if match_idx is not None and match_idx != 0:
                        goal_stack.insert(0, goal_stack.pop(match_idx))
                    if extra_args and goal_stack:
                        g_fn, g_ty, g_nat = goal_stack[0]
                        new_ty, new_nat = _peel_intro_step(f"intro {extra_args}", g_ty, g_nat)
                        if new_ty is None:
                            return True
                        goal_stack[0] = (g_fn, new_ty, new_nat)
                else:
                    st_c = _strip_outer_parens(_strip_tactic_arm_prefix(st))
                was_braced = False
                if st_c.startswith("{") and st_c.endswith("}") and _is_single_balanced_brace_block(st_c):
                    st_c = st_c[1:-1].strip()
                    was_braced = True
                if not st_c or st_c == "done":
                    continue
                if not goal_stack:
                    return False
                if (
                    was_braced
                    or len(_split_top_level_semi_steps(st_c)) >= 2
                    or _split_top_level_bullet_groups(st_c) is not None
                ):
                    if _can_fail_against_goal(
                        st_c,
                        True,
                        goal_stack[0][1],
                        in_ctor=True,
                        struct_specs=struct_specs,
                        struct_field_counts=struct_field_counts,
                        struct_param_names=struct_param_names,
                        nat_vars=goal_stack[0][2],
                        _depth=_depth + 1,
                    ):
                        return True
                    goal_stack.pop(0)
                    continue
                m_all_g = re.match(r"^(?:all_goals|any_goals|repeat'?)\s+(.+)$", st_c, flags=re.S)
                if m_all_g:
                    sub_expr, sub_tac = _unwrap_leaf_or_ctor_proof(m_all_g.group(1))
                    if any(
                        _can_fail_against_goal(
                            sub_expr,
                            sub_tac,
                            g_ty,
                            in_ctor=True,
                            struct_specs=struct_specs,
                            struct_field_counts=struct_field_counts,
                            struct_param_names=struct_param_names,
                            nat_vars=g_nat,
                            _depth=_depth + 1,
                        )
                        for _, g_ty, g_nat in goal_stack
                    ):
                        return True
                    goal_stack.clear()
                    break
                if re.fullmatch(r"constructor", st_c):
                    sub_fields = _resolve_ctor_scope_fields("constructor", goal_stack[0][1], struct_specs)
                    if not sub_fields:
                        return False
                    parent_nat = set(goal_stack[0][2])
                    goal_stack = [(sfn, sfty, set(parent_nat)) for sfn, sfty in sub_fields] + goal_stack[1:]
                    continue
                if _dsimp_targets_goal(st_c):
                    is_u_d, g_k_d, _ = _classify_suffices_prop_detail(goal_stack[0][1], nat_vars=goal_stack[0][2])
                    if not is_u_d and g_k_d in ("eq_refl", "true"):
                        goal_stack.pop(0)
                        continue
                    if idx_st < len(steps) - 1:
                        continue
                    return True
                if re.match(r"^(?:dsimp|unfold|change)(?=\s|$)", st_c):
                    if idx_st < len(steps) - 1:
                        continue
                    return True
                if re.match(r"^(?:intro|intros|rintro)(?=\s|$)", st_c):
                    g_fn, g_ty, g_nat = goal_stack[0]
                    new_ty, new_nat = _peel_intro_step(st_c, g_ty, g_nat)
                    if new_ty is None:
                        return True
                    goal_stack[0] = (g_fn, new_ty, new_nat)
                    if idx_st < len(steps) - 1:
                        continue
                    return True
                sub_expr, sub_tac = _unwrap_leaf_or_ctor_proof(st_c)
                if _can_fail_against_goal(
                    sub_expr,
                    sub_tac,
                    goal_stack[0][1],
                    in_ctor=True,
                    struct_specs=struct_specs,
                    struct_field_counts=struct_field_counts,
                    struct_param_names=struct_param_names,
                    nat_vars=goal_stack[0][2],
                    _depth=_depth + 1,
                ):
                    return True
                goal_stack.pop(0)
            return len(goal_stack) > 0
        steps_s = _split_top_level_semi_steps(s)
        while len(steps_s) >= 2 and _strip_outer_parens(_strip_tactic_arm_prefix(steps_s[-1])) == "done":
            steps_s.pop()
        if len(steps_s) == 1 and steps_s[0].strip() != s.strip():
            last_expr, last_tac = _unwrap_leaf_or_ctor_proof(steps_s[0])
            return _can_fail_against_goal(
                last_expr,
                last_tac,
                goal_ty,
                in_ctor=in_ctor,
                struct_specs=struct_specs,
                struct_field_counts=struct_field_counts,
                struct_param_names=struct_param_names,
                nat_vars=nat_vars,
                _depth=_depth + 1,
            )
        if len(steps_s) >= 2:
            cur_g_ty = goal_ty
            cur_g_nat = set(nat_vars or ())
            prefix_ok = True
            for st_s in steps_s[:-1]:
                st_sc = _strip_outer_parens(_strip_tactic_arm_prefix(st_s))
                if re.match(r"^(?:dsimp|unfold|change)(?=\s|$)", st_sc):
                    continue
                if re.match(r"^(?:intro|intros|rintro)(?=\s|$)", st_sc) and cur_g_ty:
                    new_ty, new_nat = _peel_intro_step(st_sc, cur_g_ty, cur_g_nat)
                    if new_ty is None:
                        return True
                    cur_g_ty, cur_g_nat = new_ty, new_nat
                    continue
                prefix_ok = False
                break
            if prefix_ok:
                last_expr, last_tac = _unwrap_leaf_or_ctor_proof(steps_s[-1])
                return _can_fail_against_goal(
                    last_expr,
                    last_tac,
                    cur_g_ty,
                    in_ctor=in_ctor,
                    struct_specs=struct_specs,
                    struct_field_counts=struct_field_counts,
                    struct_param_names=struct_param_names,
                    nat_vars=cur_g_nat,
                    _depth=_depth + 1,
                )
        return False

    # Lambda terms `fun ... => body` / `λ ... => body` against arrow / Pi goals
    m_lam = re.match(r"^(?:fun|λ)(?=\s|[({⦃⟨_])", s)
    if m_lam and goal_ty:
        depth_l = 0
        idx_l = m_lam.end()
        n_l = len(s)
        arrow_l: int | None = None
        while idx_l < n_l:
            ch_l = s[idx_l]
            if ch_l == "«":
                idx_l += 1
                while idx_l < n_l and s[idx_l] not in ("»", "\n"):
                    idx_l += 1
                if idx_l < n_l and s[idx_l] == "»":
                    idx_l += 1
                continue
            if ch_l in "([{⦃⟨":
                depth_l += 1
            elif ch_l in ")]}⦄⟩" and depth_l > 0:
                depth_l -= 1
            elif depth_l == 0 and s.startswith("=>", idx_l):
                arrow_l = idx_l
                break
            idx_l += 1
        if arrow_l is not None:
            binders_raw = s[m_lam.end() : arrow_l].strip()
            body_str = s[arrow_l + 2 :].strip()
            if binders_raw and body_str:
                ci_b = _find_top_level_colon(binders_raw)
                top_annot_ty = _strip_outer_parens(binders_raw[ci_b + 1 :].strip()) if ci_b is not None else None
                toks_raw = _split_top_level_ws(binders_raw[:ci_b].strip() if ci_b is not None else binders_raw)
                binder_items: list[tuple[list[str], str | None, bool]] = []
                for bt in toks_raw:
                    if bt.startswith(("{", "[", "⦃")) and bt.endswith(("}", "]", "⦄")):
                        binder_items.append(([], None, True))
                    elif bt.startswith("(") and bt.endswith(")"):
                        bt_in = bt[1:-1].strip()
                        ci_bt = _find_top_level_colon(bt_in)
                        if ci_bt is not None:
                            bt_ty = _strip_outer_parens(bt_in[ci_bt + 1 :].strip())
                            lhs_toks = _split_top_level_ws(bt_in[:ci_bt].strip()) or ["_"]
                            for lt in lhs_toks:
                                binder_items.append((_extract_pattern_bound_names(lt), bt_ty, False))
                        else:
                            binder_items.append((_extract_pattern_bound_names(bt_in), top_annot_ty, False))
                    else:
                        binder_items.append((_extract_pattern_bound_names(bt), top_annot_ty, False))
                cur_cod: str | None = goal_ty
                sub_nat = set(nat_vars or ())
                peeled_ok = any(not is_imp for _, _, is_imp in binder_items)
                for b_names, annot_ty, is_imp in binder_items:
                    if is_imp:
                        continue
                    b_nm, dom_ty, next_cod = _peel_explicit_goal_binder_with_dom(cur_cod) if cur_cod else (None, None, None)
                    if next_cod is None:
                        peeled_ok = False
                        break
                    cur_cod = next_cod
                    if b_nm and b_nm != "_":
                        if dom_ty in _NAT_ONLY_ASCRIPTIONS:
                            sub_nat.add(b_nm)
                        else:
                            sub_nat.discard(b_nm)
                    eff_ty = annot_ty if annot_ty is not None else dom_ty
                    is_nat_binder = eff_ty in _NAT_ONLY_ASCRIPTIONS
                    for nm in b_names:
                        if is_nat_binder:
                            sub_nat.add(nm)
                        else:
                            sub_nat.discard(nm)
                if peeled_ok and cur_cod is not None:
                    return _can_fail_against_goal(
                        body_str,
                        False,
                        cur_cod,
                        in_ctor=True,
                        struct_specs=struct_specs,
                        struct_field_counts=struct_field_counts,
                        struct_param_names=struct_param_names,
                        nat_vars=sub_nat,
                        _depth=_depth + 1,
                    )

    # Constructor-shaped term expressions: `⟨...⟩`, `{...}`, `@?T.mk ...`, `@?(And|Iff|Exists).intro ...`
    if s.startswith("⟨") and s.endswith("⟩"):
        args = _split_top_level_commas(s[1:-1])
        if not args:
            return True
        if target_fields is None:
            return g_kind in ("true", "eq_refl", "iff_refl", "unsat")
        if len(args) < len(target_fields):
            return True
        if len(args) == len(target_fields):
            return any(
                _can_fail_against_goal(
                    arg,
                    False,
                    fty,
                    in_ctor=True,
                    struct_specs=struct_specs,
                    struct_field_counts=struct_field_counts,
                    struct_param_names=struct_param_names,
                    nat_vars=nat_vars,
                    _depth=_depth + 1,
                )
                for arg, (_, fty) in zip(args, target_fields)
            )
        # `len(args) > len(target_fields)`: valid in Lean iff the trailing field flattens a nested conjunction/structure
        head_pairs = list(zip(args[: len(target_fields) - 1], target_fields[:-1]))
        if any(
            _can_fail_against_goal(
                arg,
                False,
                fty,
                in_ctor=True,
                struct_specs=struct_specs,
                struct_field_counts=struct_field_counts,
                struct_param_names=struct_param_names,
                nat_vars=nat_vars,
                _depth=_depth + 1,
            )
            for arg, (_, fty) in head_pairs
        ):
            return True
        tail_expr = "⟨" + ", ".join(args[len(target_fields) - 1 :]) + "⟩"
        tail_ty = " ∧ ".join(ft for _, ft in target_fields[len(target_fields) - 1 :]) if goal_is_conj else target_fields[-1][1]
        return _can_fail_against_goal(
            tail_expr,
            False,
            tail_ty,
            in_ctor=True,
            struct_specs=struct_specs,
            struct_field_counts=struct_field_counts,
            struct_param_names=struct_param_names,
            nat_vars=nat_vars,
            _depth=_depth + 1,
        )

    if s.startswith("{") and s.endswith("}") and _is_single_balanced_brace_block(s):
        pairs = _split_struct_literal_fields(s[1:-1])
        if pairs:
            if target_fields is None:
                return g_kind in ("true", "eq_refl", "iff_refl", "unsat")
            fmap = dict(target_fields)
            for fn, val in pairs:
                if fn not in fmap:
                    return True
                if _can_fail_against_goal(
                    val,
                    False,
                    fmap[fn],
                    in_ctor=True,
                    struct_specs=struct_specs,
                    struct_field_counts=struct_field_counts,
                    struct_param_names=struct_param_names,
                    nat_vars=nat_vars,
                    _depth=_depth + 1,
                ):
                    return True
            return False

    toks = _unwrap_ctor_app_tokens(s)
    if len(toks) >= 2 and _CTOR_HEAD_RE.fullmatch(toks[0]):
        head = toks[0]
        if target_fields is None:
            return g_kind in ("true", "eq_refl", "iff_refl", "unsat")
        param_names = _ctor_param_names_for_head(head, struct_param_names)
        base_field_names = {fn for fn, _ in target_fields}
        named_vals: dict[str, str] = {}
        pos_args: list[str] = []
        for t in toks[1:]:
            ts = t.strip()
            if ts.startswith("{") and ts.endswith("}"):
                continue
            a_name, a_val = _parse_named_ctor_arg(ts)
            if a_name is not None:
                if a_name in param_names:
                    continue
                if a_name in base_field_names:
                    named_vals[a_name] = a_val
                    continue
            pos_args.append(a_val)
        rem_fields = [(fn, fty) for fn, fty in target_fields if fn not in named_vals]
        if head.startswith("@") and len(pos_args) >= len(rem_fields):
            pos_args = pos_args[-len(rem_fields) :] if rem_fields else []
        if len(pos_args) < len(rem_fields):
            return True
        for fn, val in named_vals.items():
            fty = dict(target_fields)[fn]
            if _can_fail_against_goal(
                val,
                False,
                fty,
                in_ctor=True,
                struct_specs=struct_specs,
                struct_field_counts=struct_field_counts,
                struct_param_names=struct_param_names,
                nat_vars=nat_vars,
                _depth=_depth + 1,
            ):
                return True
        for val, (_, fty) in zip(pos_args, rem_fields):
            if _can_fail_against_goal(
                val,
                False,
                fty,
                in_ctor=True,
                struct_specs=struct_specs,
                struct_field_counts=struct_field_counts,
                struct_param_names=struct_param_names,
                nat_vars=nat_vars,
                _depth=_depth + 1,
            ):
                return True
        return False
    if not is_tactic and goal_ty and g_kind == "other":
        return True
    return False


def _suffices_aux_can_fail(
    hdr_kind: str,
    is_unsat_hdr: bool,
    aux_cand_text: str,
    *,
    hdr_prop: str | None = None,
    struct_specs: dict[str, tuple[list[tuple[str, bool, bool]], list[tuple[str, str]]]] | None = None,
    struct_field_counts: dict[str, int] | None = None,
    struct_param_names: dict[str, set[str]] | None = None,
    nat_vars: frozenset[str] | set[str] | None = None,
) -> bool:
    """Return True iff `suffices _ : P by ...; B` auxiliary proof `B` can fail for `P`."""
    if is_unsat_hdr:
        return True
    ax = _strip_outer_parens(aux_cand_text.strip())
    if not ax:
        return hdr_kind == "other"
    if re.fullmatch(r"(?:contradiction|done|sorry|admit)", ax):
        return True
    ax_tac = _strip_outer_parens(re.sub(r"^by(?=\s|$)", "", ax, flags=re.S).strip())
    if re.fullmatch(r"(?:simp|dsimp|simp\s+only\s*\[\s*\])", ax_tac):
        return hdr_kind == "other"
    if re.fullmatch(r"trivial", ax_tac):
        return hdr_kind not in ("true", "eq_refl", "iff_refl")
    ax_expr, ax_is_tac = _unwrap_leaf_or_ctor_proof(ax_tac)
    if ax_is_tac and re.fullmatch(r"trivial", ax_expr):
        return hdr_kind not in ("true", "eq_refl", "iff_refl")
    if re.fullmatch(r"(?:trivial|True\.intro)", ax_expr):
        return hdr_kind != "true"
    if re.fullmatch(r"Iff\.rfl", ax_expr):
        return hdr_kind != "iff_refl"
    if re.fullmatch(r"rfl", ax_expr):
        return hdr_kind != "eq_refl"
    if _is_eq_refl_expr(ax_expr):
        return hdr_kind != "eq_refl" or not _eq_refl_matches_goal(ax_expr, hdr_prop, nat_vars=nat_vars)
    if ax_is_tac and hdr_prop is not None and re.match(r"^constructor\b", ax_expr):
        return _can_fail_against_goal(
            ax_expr,
            True,
            hdr_prop,
            in_ctor=True,
            struct_specs=struct_specs,
            struct_field_counts=struct_field_counts,
            struct_param_names=struct_param_names,
            nat_vars=nat_vars,
        )
    ax_toks = _unwrap_ctor_app_tokens(ax_expr)
    if not ax_is_tac and (
        (ax_expr.startswith("⟨") and ax_expr.endswith("⟩"))
        or (ax_expr.startswith("{") and ax_expr.endswith("}") and ":=" in ax_expr)
        or (len(ax_toks) >= 2 and bool(_CTOR_HEAD_RE.fullmatch(ax_toks[0])))
    ):
        if hdr_prop is not None:
            return _can_fail_against_goal(
                ax_expr,
                False,
                hdr_prop,
                in_ctor=True,
                struct_specs=struct_specs,
                struct_field_counts=struct_field_counts,
                struct_param_names=struct_param_names,
                nat_vars=nat_vars,
            )
        if _is_trivial_proof_expr(
            ax_expr, struct_field_counts=struct_field_counts, struct_param_names=struct_param_names
        ):
            return hdr_kind != "conj_refl"
    return False


def _find_top_level_assign_with_depth(text: str, depth: int = 0) -> tuple[bool, int]:
    """Return `(found_top_level_assign, end_depth)` scanning brackets outside `«...»` and strings."""
    found = False
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    idx_t = 0
    nt = len(text)
    while idx_t < nt:
        ch_t = text[idx_t]
        if ch_t == "«":
            idx_t += 1
            while idx_t < nt and text[idx_t] not in ("»", "\n"):
                idx_t += 1
            if idx_t < nt and text[idx_t] == "»":
                idx_t += 1
            continue
        if ch_t == '"':
            idx_t += 1
            while idx_t < nt:
                if text[idx_t] == "\\" and idx_t + 1 < nt:
                    idx_t += 2
                    continue
                if text[idx_t] == '"':
                    idx_t += 1
                    break
                idx_t += 1
            continue
        if ch_t in open_ch:
            depth += 1
        elif ch_t in close_ch and depth > 0:
            depth -= 1
        elif depth == 0 and text.startswith(":=", idx_t):
            found = True
        idx_t += 1
    return found, depth


def _is_definite_single_line_subgoal_closer(line_s: str) -> bool:
    """Return True iff `line_s` is a single-line balanced leaf tactic guaranteed to close one subgoal."""
    s = _strip_outer_parens(line_s.strip())
    if not s or _expr_has_hole(s):
        return False
    if re.search(r"(?:\b(?:by|with)|:=|=>)\s*$", s):
        return False
    # Check bracket balance
    bal = 0
    for ch in s:
        if ch in "([{⦃⟨":
            bal += 1
        elif ch in ")]}⦄⟩":
            if bal <= 0:
                return False
            bal -= 1
    if bal != 0:
        return False
    if re.fullmatch(r"(?:rfl|trivial|True\.intro|Iff\.rfl|done|contradiction)", s):
        return True
    m_ex = re.match(r"^(?:exact|refine'?)(?:\s+|(?=[⟨{(]))(.+)$", s)
    if m_ex:
        rhs_ex = m_ex.group(1).strip()
        if rhs_ex and not re.match(r"^by(?=\s|$)", rhs_ex):
            return True
    return False


def _extract_leading_goal_binder_types(ret_type: str) -> list[str | None]:
    """Extract ordered explicit `∀`/`→` binder type strings from `ret_type` for `intro` shadowing."""
    types_out: list[str | None] = []
    s = ret_type.strip()
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    for _ in range(32):
        s = _strip_outer_parens(s)
        peeled_lh = _strip_leading_let_have(s)
        if peeled_lh is not None:
            s = peeled_lh
            continue
        m_forall = re.match(r"^(?:∀|forall(?=\s|[({\[⦃«]))", s)
        if m_forall:
            comma_idx = _forall_comma_map(s, _bracket_depths(s)).get(0)
            if comma_idx is None:
                break
            binder_chunk = s[m_forall.end() : comma_idx].strip()
            # Walk binder groups in `binder_chunk`
            bi = 0
            bn = len(binder_chunk)
            saw_explicit_group = False
            while bi < bn:
                while bi < bn and binder_chunk[bi].isspace():
                    bi += 1
                if bi >= bn:
                    break
                if binder_chunk[bi] in ("(", "{", "⦃", "["):
                    saw_explicit_group = True
                    b_ch = binder_chunk[bi]
                    bd = 1
                    bj = bi + 1
                    while bj < bn and bd > 0:
                        if binder_chunk[bj] in ("(", "{", "⦃", "["):
                            bd += 1
                        elif binder_chunk[bj] in (")", "}", "⦄", "]"):
                            bd -= 1
                        bj += 1
                    inner = binder_chunk[bi + 1 : bj - 1] if bd == 0 else binder_chunk[bi + 1 :]
                    if b_ch == "(":
                        ci = _find_top_level_colon(inner)
                        ty = _strip_outer_parens(inner[ci + 1 :].strip()) if ci is not None else None
                        lhs_toks = [
                            t
                            for t in (inner[:ci] if ci is not None else inner).split()
                            if _LEAN_IDENT_SEG_RE.fullmatch(t) and t not in _LEAN_TERM_KEYWORDS
                        ]
                        for _ in (lhs_toks or ["_"]):
                            types_out.append(ty)
                    bi = bj
                    continue
                break
            if not saw_explicit_group:
                ci = _find_top_level_colon(binder_chunk)
                ty = _strip_outer_parens(binder_chunk[ci + 1 :].strip()) if ci is not None else None
                lhs_toks = [
                    t
                    for t in (binder_chunk[:ci] if ci is not None else binder_chunk).split()
                    if _LEAN_IDENT_SEG_RE.fullmatch(t) and t not in _LEAN_TERM_KEYWORDS
                ]
                for _ in (lhs_toks or ["_"]):
                    types_out.append(ty)
            s = s[comma_idx + 1 :].strip()
            continue
        # Non-dependent arrow `A → B` / `(x : A) → B` (skipping implicit `{...}` / `[...]`)
        depth = 0
        arrow_pos: tuple[int, int] | None = None
        for idx_c, ch in enumerate(s):
            if ch in open_ch:
                depth += 1
            elif ch in close_ch and depth > 0:
                depth -= 1
            elif depth == 0:
                if ch == "→":
                    arrow_pos = (idx_c, idx_c + 1)
                    break
                if s.startswith("->", idx_c):
                    arrow_pos = (idx_c, idx_c + 2)
                    break
        if arrow_pos is not None:
            dom = s[: arrow_pos[0]].strip()
            if dom.startswith(("{", "[", "⦃")) and dom.endswith(("}", "]", "⦄")):
                s = s[arrow_pos[1] :].strip()
                continue
            dom_inner = _strip_outer_parens(dom)
            ci = _find_top_level_colon(dom_inner)
            if dom.startswith("(") and ci is not None:
                ty = _strip_outer_parens(dom_inner[ci + 1 :].strip())
                lhs_toks = [
                    t for t in dom_inner[:ci].split() if _LEAN_IDENT_SEG_RE.fullmatch(t) and t not in _LEAN_TERM_KEYWORDS
                ]
                for _ in (lhs_toks or ["_"]):
                    types_out.append(ty)
            else:
                types_out.append(dom_inner or None)
            s = s[arrow_pos[1] :].strip()
            continue
        break
    return types_out


def _apply_intro_shadowing(
    text: str,
    cur_nat_vars: set[str],
    cur_goal_binders: list[str | None],
) -> bool:
    """Apply `intro`/`intros`/`rintro` binder shadowing in `text` to `cur_nat_vars`/`cur_goal_binders`."""
    changed = False
    for seg in _split_top_level_semi_steps(text):
        s_clean = re.sub(r"^(?::=|by(?=\s|$))\s*", "", seg.strip()).strip()
        s_clean = _strip_tactic_arm_prefix(s_clean)
        s_clean = re.sub(r"^(?::=|by(?=\s|$))\s*", "", s_clean).strip()
        m_int = re.match(r"^(?:intro|intros|rintro)(?=\s|$)(.*)$", s_clean)
        if not m_int:
            m_fun = re.match(r"^(?:fun|λ)(?=\s|[({⦃⟨_])(.+?)=>", s_clean)
            if not m_fun:
                continue
            arg_str = m_fun.group(1).strip()
        else:
            arg_str = m_int.group(1).strip()
        changed = True
        if not arg_str:
            if cur_goal_binders:
                cur_goal_binders.pop(0)
            continue
        for tok in _split_top_level_ws(arg_str):
            ts = tok.strip()
            if ts in ("|", "=>"):
                break
            if ts.startswith(("(", "{", "⦃")) and ts.endswith((")", "}", "⦄")):
                inner = ts[1:-1].strip()
                ci = _find_top_level_colon(inner)
                if ci is not None:
                    ty = _strip_outer_parens(inner[ci + 1 :].strip())
                    is_nat = ty in _NAT_ONLY_ASCRIPTIONS
                    if cur_goal_binders and ts.startswith("("):
                        cur_goal_binders.pop(0)
                    for nm in _extract_pattern_bound_names(inner[:ci]):
                        if is_nat:
                            cur_nat_vars.add(nm)
                        else:
                            cur_nat_vars.discard(nm)
                    continue
            if _LEAN_IDENT_SEG_RE.fullmatch(ts) and ts not in _LEAN_TERM_KEYWORDS:
                b_ty = cur_goal_binders.pop(0) if cur_goal_binders else None
                if ts != "_":
                    if b_ty in _NAT_ONLY_ASCRIPTIONS:
                        cur_nat_vars.add(ts)
                    else:
                        cur_nat_vars.discard(ts)
            else:
                if cur_goal_binders and not ts.startswith(("{", "[", "⦃")):
                    cur_goal_binders.pop(0)
                for nm in _extract_pattern_bound_names(ts):
                    cur_nat_vars.discard(nm)
    return changed


def _strip_have_subblocks_with_liveness(
    tail: str,
    *,
    in_ctor_subgoal: bool = False,
    active_field_ty: str | None = None,
    struct_specs: dict[str, tuple[list[tuple[str, bool, bool]], list[tuple[str, str]]]] | None = None,
    struct_field_counts: dict[str, int] | None = None,
    struct_param_names: dict[str, set[str]] | None = None,
    root_goal_ty: str | None = None,
    root_ret_type: str | None = None,
    nat_vars: frozenset[str] | set[str] | None = None,
) -> tuple[str, list[tuple[list[str], str]], list[tuple[Any, ...]]]:
    """Remove `have`/`let` sub-blocks and dead `suffices` aux branches, returning stripped text, bindings, and liveness events."""
    lines = tail.splitlines()
    out: list[str] = []
    bindings: list[tuple[list[str], str]] = []
    events: list[tuple[Any, ...]] = []
    cur_nat_vars: set[str] = set(nat_vars or ())
    cur_goal_binders: list[str | None] = _extract_leading_goal_binder_types(root_ret_type or "")
    shadow_stack: list[tuple[int, bool, set[str], list[str | None]]] = []

    def _pop_shadow_scopes(cur_ind: int, is_pipe: bool, is_bul: bool) -> None:
        while shadow_stack:
            fr_ind, fr_is_arm, saved_vars, saved_binders = shadow_stack[-1]
            if cur_ind < fr_ind or (fr_is_arm and cur_ind == fr_ind and (is_pipe or is_bul)):
                shadow_stack.pop()
                cur_nat_vars.clear()
                cur_nat_vars.update(saved_vars)
                cur_goal_binders[:] = saved_binders
            else:
                break
    ctor_scopes: list[dict[str, Any]] = (
        [
            {
                "indent": -1,
                "kind": "plain",
                "fields": [("goal", active_field_ty)] if active_field_ty else None,
                "subgoal_idx": 0,
                "bullet_indent": None,
                "case_seen": False,
                "unbulleted_pending": None,
                "unbulleted_indent": None,
            }
        ]
        if in_ctor_subgoal
        else []
    )

    def _pop_ctor_scopes(cur_ind: int, is_pipe: bool, is_bul: bool) -> None:
        while ctor_scopes:
            sc = ctor_scopes[-1]
            sc_ind = sc["indent"]
            sc_kind = sc["kind"]
            if cur_ind < sc_ind:
                ctor_scopes.pop()
            elif cur_ind == sc_ind and (is_pipe or (sc_kind == "bul" and is_bul)):
                ctor_scopes.pop()
            else:
                break

    def _advance_ctor_subgoal(cur_line: str, cur_ind: int, is_bul: bool, is_pipe: bool = False) -> None:
        if not ctor_scopes:
            return
        sc = ctor_scopes[-1]
        if is_pipe:
            return
        if is_bul:
            sc["unbulleted_pending"] = None
            b_ind = sc["bullet_indent"]
            if b_ind is None:
                sc["bullet_indent"] = cur_ind
                sc["subgoal_idx"] = 0
            elif cur_ind == b_ind:
                if sc["subgoal_idx"] is not None:
                    sc["subgoal_idx"] += 1
            return
        m_case = re.match(r"^(?:case'?\s+([^\n=>]+?)|next(?:\s+[^\n=>]+?)?)\s*=>", cur_line.lstrip())
        if m_case:
            sc["unbulleted_pending"] = None
            tag = m_case.group(1)
            fields = sc["fields"]
            if tag and fields:
                tag_head = tag.strip().split()[0]
                for idx_f, (fn, _) in enumerate(fields):
                    if fn == tag_head:
                        sc["subgoal_idx"] = idx_f
                        sc["case_seen"] = True
                        return
            if sc["case_seen"] and sc["subgoal_idx"] is not None:
                sc["subgoal_idx"] += 1
            sc["case_seen"] = True
            return
        if sc["bullet_indent"] is None and not sc["case_seen"] and sc.get("unbulleted_pending") is not None:
            u_ind = sc.get("unbulleted_indent")
            if u_ind is not None and cur_ind <= u_ind:
                if sc["unbulleted_pending"] == "advance" and sc["subgoal_idx"] is not None:
                    sc["subgoal_idx"] += 1
                else:
                    sc["subgoal_idx"] = None
                sc["unbulleted_pending"] = None

    def _current_scope_field_ty() -> str | None:
        if not ctor_scopes:
            return root_goal_ty
        sc = ctor_scopes[-1]
        fields = sc["fields"]
        if not fields:
            return None
        s_idx = sc["subgoal_idx"]
        if s_idx is not None and 0 <= s_idx < len(fields):
            return fields[s_idx][1]
        return None

    def _apply_let_have_shadowing(
        lhs_names: list[str],
        block_src: str,
        body_part: str,
        fr_ind: int,
        fr_is_arm: bool,
    ) -> None:
        relevant = [nm for nm in lhs_names if nm and nm != "_"]
        if not relevant:
            return
        # Determine if `block_src` has a top-level `:` before `:=`
        has_colon_ty = False
        d_b = 0
        ib = 0
        nb = len(block_src)
        while ib < nb:
            cb = block_src[ib]
            if cb == "«":
                ib += 1
                while ib < nb and block_src[ib] not in ("»", "\n"):
                    ib += 1
                if ib < nb and block_src[ib] == "»":
                    ib += 1
                continue
            if cb in "([{⦃⟨":
                d_b += 1
            elif cb in ")]}⦄⟩" and d_b > 0:
                d_b -= 1
            elif d_b == 0:
                if block_src.startswith(":=", ib):
                    break
                if cb == ":":
                    has_colon_ty = True
                    break
            ib += 1
        saved_nat = set(cur_nat_vars)
        saved_binders = list(cur_goal_binders)
        is_nat_val = False
        if has_colon_ty:
            d_t = 0
            it = 0
            nt = len(body_part)
            assign_pos: int | None = None
            while it < nt:
                ct = body_part[it]
                if ct == "«":
                    it += 1
                    while it < nt and body_part[it] not in ("»", "\n"):
                        it += 1
                    if it < nt and body_part[it] == "»":
                        it += 1
                    continue
                if ct in "([{⦃⟨":
                    d_t += 1
                elif ct in ")]}⦄⟩" and d_t > 0:
                    d_t -= 1
                elif d_t == 0 and body_part.startswith(":=", it):
                    assign_pos = it
                    break
                it += 1
            ty_s = _strip_outer_parens((body_part[:assign_pos] if assign_pos is not None else body_part).strip())
            is_nat_val = ty_s in _NAT_ONLY_ASCRIPTIONS
        else:
            b_s = body_part.strip()
            if not _has_non_nat_bool_type_ascription(b_s):
                ev = _eval_ground_suffices_expr(b_s)
                if ev is not None and ev not in ("true", "false"):
                    is_nat_val = True
                elif _is_pure_nat_var_expr(b_s, cur_nat_vars):
                    is_nat_val = True
        shadow_stack.append((fr_ind, fr_is_arm, saved_nat, saved_binders))
        for nm in relevant:
            if is_nat_val:
                cur_nat_vars.add(nm)
            else:
                cur_nat_vars.discard(nm)

    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        m = _match_subblock_stmt(line)
        if m:
            prefix, kw, _kw_start, kw_end, has_nonbullet, bullet_end = m
            line_indent = len(line[: len(line) - len(line.lstrip())].replace("\t", "    "))
            bullet_indent = len(line[:bullet_end].replace("\t", "    "))
            stmt_col = len(prefix.replace("\t", "    "))
            wrap_depth = _count_unclosed_wrapper_depth(prefix[bullet_end:])
            line_s_l = line.lstrip()
            is_pipe_stmt = line_s_l.startswith("|")
            is_bul_stmt = bool(bullet_end > line_indent) and not is_pipe_stmt
            _pop_shadow_scopes(line_indent, is_pipe_stmt, is_bul_stmt)
            _pop_ctor_scopes(line_indent, is_pipe_stmt, is_bul_stmt)
            _advance_ctor_subgoal(line, line_indent, is_bul_stmt, is_pipe_stmt)
            eff_nat_vars = set(cur_nat_vars)
            if prefix:
                _apply_intro_shadowing(prefix, eff_nat_vars, list(cur_goal_binders))
            m_ctor_pre = _CTOR_OPEN_LINE_RE.search(prefix)
            m_app_pre = _match_ctor_apply_in_line(
                prefix,
                allow_trivial_field_args=True,
                struct_field_counts=struct_field_counts,
                struct_param_names=struct_param_names,
            )
            ctor_pre_start: int | None = None
            if m_ctor_pre is not None and (m_app_pre is None or m_ctor_pre.start() <= m_app_pre[0]):
                ctor_pre_start = m_ctor_pre.start()
            elif m_app_pre is not None:
                ctor_pre_start = m_app_pre[0]
            if ctor_pre_start is not None:
                pre_fields = _resolve_ctor_scope_fields(
                    prefix[ctor_pre_start:], _current_scope_field_ty(), struct_specs
                )
                eff_in_ctor = True
                eff_field_ty = pre_fields[0][1] if pre_fields else None
            else:
                eff_in_ctor = bool(ctor_scopes)
                eff_field_ty = _current_scope_field_ty() if ctor_scopes else None
            if kw in ("have", "let"):
                rhs_part = line[kw_end:]
                seen_assign, assign_depth = _find_top_level_assign_with_depth(rhs_part, 0)
                in_by_block = bool(re.search(r":=\s*by\b", rhs_part)) or bool(re.search(r"\bby\s*$", rhs_part))
                ends_cont = (not seen_assign) or bool(_SUBBLOCK_CONT_END_RE.search(rhs_part))
                if seen_assign:
                    semi_idx: int | None = None
                    if wrap_depth > 0:
                        semi_idx = _find_top_level_semi(rhs_part, initial_depth=wrap_depth)
                    elif not in_by_block:
                        semi_idx = _find_top_level_semi(rhs_part)
                    else:
                        m_by_brace = re.search(r":=\s*by\s*(?=\{)", rhs_part)
                        if m_by_brace:
                            rel_semi = _find_top_level_semi(rhs_part[m_by_brace.end() :])
                            if rel_semi is not None:
                                cand_semi = m_by_brace.end() + rel_semi
                                if _is_single_balanced_brace_block(rhs_part[m_by_brace.end() : cand_semi]):
                                    semi_idx = cand_semi
                    if semi_idx is not None:
                        after_semi = rhs_part[semi_idx + 1 :].strip()
                        if after_semi:
                            before_semi = rhs_part[:semi_idx]
                            if wrap_depth > 0:
                                before_semi = _strip_trailing_wrappers(before_semi, wrap_depth)
                            eff_prefix, eff_has_nonbullet = (
                                _trim_prefix_open_wrappers(prefix, bullet_end, wrap_depth)
                                if wrap_depth > 0
                                else (prefix, has_nonbullet)
                            )
                            if eff_has_nonbullet and eff_prefix.rstrip():
                                out_txt = eff_prefix.rstrip()
                                out.append(out_txt)
                                events.append(("out", line_indent, bool(bullet_end > line_indent), out_txt))
                            lhs_names, body_part = _extract_have_lhs_and_body(before_semi)
                            if lhs_names:
                                bindings.append((lhs_names, body_part))
                                is_bul_start = (not eff_has_nonbullet) and (bullet_end > line_indent)
                                events.append(("bind", line_indent, is_bul_start, lhs_names, body_part))
                                _apply_let_have_shadowing(
                                    lhs_names, before_semi, body_part, line_indent, is_pipe_stmt or is_bul_start
                                )
                            cont_indent = bullet_indent if (not eff_has_nonbullet and bullet_end > line_indent) else line_indent
                            lines[i] = (" " * cont_indent) + after_semi
                            continue
                if has_nonbullet and prefix.rstrip():
                    out_txt = prefix.rstrip()
                    out.append(out_txt)
                    events.append(("out", line_indent, bool(bullet_end > line_indent), out_txt))
                block_lines = [rhs_part]
                i += 1
                if not has_nonbullet:
                    base_indent = bullet_indent
                    while i < n:
                        nxt = lines[i]
                        nxt_stripped = nxt.strip()
                        if not nxt_stripped:
                            i += 1
                            continue
                        nxt_indent = len(nxt[: len(nxt) - len(nxt.lstrip())].replace("\t", "    "))
                        if not seen_assign:
                            found_a, assign_depth = _find_top_level_assign_with_depth(nxt, assign_depth)
                            if found_a:
                                seen_assign = True
                                in_by_block = bool(re.search(r":=\s*by\b", nxt)) or bool(re.search(r"\bby\s*$", nxt))
                            block_lines.append(nxt)
                            i += 1
                            continue
                        if nxt_indent > base_indent:
                            if re.search(r"\bby\s*$", nxt):
                                in_by_block = True
                            block_lines.append(nxt)
                            i += 1
                            continue
                        if in_by_block and nxt_stripped.startswith("|") and nxt_indent >= base_indent:
                            block_lines.append(nxt)
                            i += 1
                            continue
                        break
                else:
                    body_indent: int | None = None
                    while i < n:
                        nxt = lines[i]
                        nxt_stripped = nxt.strip()
                        if not nxt_stripped:
                            i += 1
                            continue
                        nxt_indent = len(nxt[: len(nxt) - len(nxt.lstrip())].replace("\t", "    "))
                        if not seen_assign:
                            found_a, assign_depth = _find_top_level_assign_with_depth(nxt, assign_depth)
                            if found_a:
                                seen_assign = True
                                in_by_block = bool(re.search(r":=\s*by\b", nxt)) or bool(re.search(r"\bby\s*$", nxt))
                                ends_cont = bool(_SUBBLOCK_CONT_END_RE.search(nxt))
                            block_lines.append(nxt)
                            i += 1
                            continue
                        if ends_cont:
                            if nxt_indent <= line_indent:
                                break
                            if body_indent is None:
                                body_indent = nxt_indent
                                if re.search(r"\bby\s*$", nxt):
                                    in_by_block = True
                                block_lines.append(nxt)
                                i += 1
                                continue
                            if nxt_indent >= body_indent:
                                if re.search(r"\bby\s*$", nxt):
                                    in_by_block = True
                                block_lines.append(nxt)
                                i += 1
                                continue
                            break
                        else:
                            if nxt_indent > stmt_col or (in_by_block and nxt_stripped.startswith("|") and nxt_indent > line_indent):
                                if body_indent is None:
                                    body_indent = nxt_indent
                                block_lines.append(nxt)
                                i += 1
                                continue
                            break
                block_joined = "\n".join(block_lines)
                lhs_names, body_part = _extract_have_lhs_and_body(block_joined)
                if lhs_names:
                    bindings.append((lhs_names, body_part))
                    is_bul_start = (not has_nonbullet) and (bullet_end > line_indent)
                    events.append(("bind", line_indent, is_bul_start, lhs_names, body_part))
                    _apply_let_have_shadowing(
                        lhs_names, block_joined, body_part, line_indent, is_pipe_stmt or is_bul_start
                    )
                continue

            # kw == "suffices": collect main `by`/`from` proof, strip recursively, preserve aux proof iff hyp is used
            stmt_start_idx = i
            cur = line[kw_end:]
            header_parts: list[str] = []
            m_bf = re.search(r"\b(?:by|from)\b", cur)
            while m_bf is None:
                if ":=" in cur:
                    break
                header_parts.append(cur)
                if i + 1 >= n:
                    break
                i += 1
                cur = lines[i]
                m_bf = re.search(r"\b(?:by|from)\b", cur)
            main_proof_lines: list[str] = []
            trailing_inline_aux = ""
            hyp_name = "this"
            eff_prefix = prefix
            eff_has_nonbullet = has_nonbullet
            if m_bf is not None:
                header_parts.append(cur[: m_bf.start()])
                hyp_name = _extract_suffices_hyp_name("\n".join(header_parts))
                after_bf = cur[m_bf.end() :].strip()
                is_by = m_bf.group(0) == "by" or bool(re.match(r"^\s*by\b", cur[m_bf.end() :]))
                if after_bf:
                    semi_idx = _find_top_level_semi(after_bf, initial_depth=wrap_depth)
                    if semi_idx is not None:
                        before_semi = after_bf[:semi_idx].strip()
                        if wrap_depth > 0:
                            before_semi = _strip_trailing_wrappers(before_semi, wrap_depth)
                        after_semi = after_bf[semi_idx + 1 :].strip()
                        should_split_semi = (
                            (m_bf.group(0) == "from" and not is_by)
                            or bool(_TERMINAL_TACTIC_BEFORE_SEMI_RE.match(before_semi))
                            or _is_single_balanced_brace_block(before_semi)
                            or (
                                bool(_REFINING_TACTIC_BEFORE_SEMI_RE.match(before_semi))
                                and (
                                    hyp_name == "_"
                                    or (
                                        hyp_name not in set(_LEAN_IDENT_TOKEN_RE.findall(after_semi))
                                        and not _ANON_HYP_TACTIC_RE.search(after_semi)
                                    )
                                )
                            )
                        )
                        if should_split_semi:
                            after_bf = before_semi
                            trailing_inline_aux = after_semi
                            if wrap_depth > 0:
                                eff_prefix, eff_has_nonbullet = _trim_prefix_open_wrappers(prefix, bullet_end, wrap_depth)
                    if after_bf:
                        main_proof_lines.append((eff_prefix if not eff_has_nonbullet else (" " * line_indent)) + after_bf)
                if re.search(r"\b(?:by|from)\s*$", cur) or re.search(r"\bfrom\s+by\s*$", cur):
                    anchor = bullet_indent if not has_nonbullet else line_indent
                    body_indent_s: int | None = None
                    while i + 1 < n:
                        nxt = lines[i + 1]
                        nxt_stripped = nxt.strip()
                        if not nxt_stripped:
                            i += 1
                            continue
                        nxt_indent = len(nxt[: len(nxt) - len(nxt.lstrip())].replace("\t", "    "))
                        if not has_nonbullet:
                            if nxt_indent > anchor or (is_by and nxt_stripped.startswith("|") and nxt_indent >= anchor):
                                main_proof_lines.append(nxt)
                                i += 1
                                continue
                            break
                        else:
                            if nxt_indent <= anchor:
                                break
                            if body_indent_s is None:
                                body_indent_s = nxt_indent
                                main_proof_lines.append(nxt)
                                i += 1
                                continue
                            if nxt_indent >= body_indent_s:
                                main_proof_lines.append(nxt)
                                i += 1
                                continue
                            break
            if main_proof_lines:
                stripped_main, main_bindings, main_events = _strip_have_subblocks_with_liveness(
                    "\n".join(main_proof_lines),
                    in_ctor_subgoal=eff_in_ctor,
                    active_field_ty=eff_field_ty,
                    struct_specs=struct_specs,
                    struct_field_counts=struct_field_counts,
                    struct_param_names=struct_param_names,
                    root_goal_ty=eff_field_ty if eff_in_ctor else root_goal_ty,
                    root_ret_type=eff_field_ty if eff_in_ctor else root_goal_ty,
                    nat_vars=eff_nat_vars,
                )
            else:
                stripped_main, main_bindings, main_events = "", [], []
            out_start_idx = len(out)
            if eff_has_nonbullet and eff_prefix.rstrip():
                if stripped_main and "\n" not in stripped_main:
                    out_txt = eff_prefix.rstrip() + " " + stripped_main.lstrip()
                    out.append(out_txt)
                else:
                    out.append(eff_prefix.rstrip())
                    if stripped_main:
                        out.append(stripped_main)
            elif stripped_main:
                out.append(stripped_main)

            live_vars, anon_live = _eval_subblock_liveness(main_events)
            is_bul = bool(bullet_end > line_indent)
            outer_vars = set(live_vars)
            if hyp_name != "_":
                outer_vars.discard(hyp_name)
            if outer_vars or anon_live:
                events.append(("out_anon", line_indent, is_bul, outer_vars, anon_live))
            elif eff_has_nonbullet and eff_prefix.rstrip():
                events.append(("out", line_indent, is_bul, eff_prefix.rstrip()))

            hyp_used = (
                (m_bf is not None)
                and (hyp_name != "_")
                and ((hyp_name in live_vars) or anon_live)
            )
            if hyp_used:
                if trailing_inline_aux:
                    cont_indent = bullet_indent if (not eff_has_nonbullet and bullet_end > line_indent) else line_indent
                    lines[i] = (" " * cont_indent) + trailing_inline_aux
                    continue
                i += 1
                continue
            i += 1
            pre_nonbullet = prefix[bullet_end:].strip()
            is_wrapper_only = bool(pre_nonbullet) and all(ch in "({⟨" or ch.isspace() for ch in pre_nonbullet)
            is_combinator_prefix = (
                not pre_nonbullet.lstrip().startswith("|")
                and bool(_COMBINATOR_PREFIX_RE.search(pre_nonbullet))
            )
            enclosing_comb_indent: int | None = None
            enclosing_comb_kws: list[str] = []
            enclosing_is_first = False
            comb_walk_re = re.compile(
                r"(?:focus|try|all_goals|any_goals|repeat'?|iterate(?:\s+\d+)?|"
                r"with_reducible_and_instances|with_reducible|with_unfolding_all|with_unfolding_none|"
                r"fail_if_success|success_if_fail)\s*\{?"
            )
            if pre_nonbullet.lstrip().startswith("|"):
                # Multiline `first\n  | suffices ...\n  | skip`: walk backward to find enclosing `first` + outer combinators
                k_back = stmt_start_idx - 1
                first_ind: int | None = None
                while k_back >= 0:
                    b_line = lines[k_back]
                    b_s = b_line.strip()
                    if not b_s:
                        k_back -= 1
                        continue
                    b_ind = len(b_line[: len(b_line) - len(b_line.lstrip())].replace("\t", "    "))
                    if b_ind > line_indent or b_s.startswith("|"):
                        k_back -= 1
                        continue
                    m_bul_b = _LEADING_BULLET_RE.match(b_s)
                    b_after_bul = b_s[m_bul_b.end() :].lstrip("({⟨ \t") if m_bul_b else b_s
                    if re.fullmatch(r"first", b_after_bul):
                        enclosing_is_first = True
                        enclosing_comb_kws.append("first")
                        enclosing_comb_indent = b_ind + (m_bul_b.end() if m_bul_b else 0)
                        first_ind = b_ind
                        k_back -= 1
                    break
                if first_ind is not None:
                    child_ind = first_ind
                    while k_back >= 0:
                        b_line = lines[k_back]
                        b_s = b_line.strip()
                        if not b_s:
                            k_back -= 1
                            continue
                        b_ind = len(b_line[: len(b_line) - len(b_line.lstrip())].replace("\t", "    "))
                        m_bul_b = _LEADING_BULLET_RE.match(b_s)
                        b_eff_ind = b_ind + (m_bul_b.end() if m_bul_b else 0)
                        b_after_bul = (b_s[m_bul_b.end() :] if m_bul_b else b_s).lstrip("({⟨ \t")
                        if b_eff_ind < child_ind and comb_walk_re.fullmatch(b_after_bul):
                            enclosing_comb_kws.append(b_after_bul)
                            child_ind = b_ind
                            k_back -= 1
                            continue
                        break
            elif not is_combinator_prefix and (not has_nonbullet or is_wrapper_only):
                # Multiline `try` / `focus` / `all_goals` / etc. on preceding line(s)
                child_ind = line_indent
                k_back = stmt_start_idx - 1
                while k_back >= 0:
                    b_line = lines[k_back]
                    b_s = b_line.strip()
                    if not b_s:
                        k_back -= 1
                        continue
                    b_ind = len(b_line[: len(b_line) - len(b_line.lstrip())].replace("\t", "    "))
                    m_bul_b = _LEADING_BULLET_RE.match(b_s)
                    b_eff_ind = b_ind + (m_bul_b.end() if m_bul_b else 0)
                    b_after_bul = (b_s[m_bul_b.end() :] if m_bul_b else b_s).lstrip("({⟨ \t")
                    if b_eff_ind < child_ind and comb_walk_re.fullmatch(b_after_bul):
                        enclosing_comb_indent = b_eff_ind
                        enclosing_comb_kws.append(b_after_bul)
                        child_ind = b_ind
                        k_back -= 1
                        continue
                    break
            enclosing_comb_kw = " ".join(enclosing_comb_kws)

            preserves_fallthrough = False
            arm1_can_fail = False
            found_inline_pipe = False
            inline_pipe_idx: int | None = None
            if is_combinator_prefix or enclosing_comb_indent is not None:
                first_arm = stripped_main.strip()
                has_skip_fallback = False
                has_any_inline_fallback = False
                is_first_mode = (re.search(r"\bfirst\b", pre_nonbullet) is not None) or enclosing_is_first
                if is_combinator_prefix and re.search(r"\bfirst\b", pre_nonbullet):
                    after_last_pipe = pre_nonbullet.rsplit("|", 1)[-1]
                    arm_init_depth = _count_unclosed_wrapper_depth(after_last_pipe)
                    arm_depth = arm_init_depth
                    for idx_a, ch_a in enumerate(first_arm):
                        if ch_a in "([{⦃⟨":
                            arm_depth += 1
                        elif ch_a in ")]}⦄⟩" and arm_depth > 0:
                            arm_depth -= 1
                        elif arm_depth == 0 and ch_a == "|" and not first_arm.startswith(("||", "|>"), idx_a):
                            after_pipe = first_arm[idx_a + 1 :].strip()
                            inline_pipe_idx = idx_a
                            first_arm = first_arm[:idx_a].strip()
                            has_any_inline_fallback = bool(after_pipe)
                            has_skip_fallback = bool(re.search(r"\bskip\b", after_pipe))
                            found_inline_pipe = True
                            break
                    if found_inline_pipe:
                        if arm_init_depth > 0:
                            first_arm = _strip_trailing_wrappers(first_arm, arm_init_depth)
                    elif wrap_depth > 0:
                        first_arm = _strip_trailing_wrappers(first_arm, wrap_depth)
                elif wrap_depth > 0:
                    first_arm = _strip_trailing_wrappers(first_arm, wrap_depth)
                if is_first_mode and not has_skip_fallback:
                    # Peek ahead for multiline sibling `| skip` arms
                    arm_base_ind = enclosing_comb_indent if enclosing_comb_indent is not None else line_indent
                    k_fwd = i
                    while k_fwd < n:
                        f_line = lines[k_fwd]
                        f_s = f_line.strip()
                        if not f_s:
                            k_fwd += 1
                            continue
                        f_ind = len(f_line[: len(f_line) - len(f_line.lstrip())].replace("\t", "    "))
                        if f_ind < arm_base_ind:
                            break
                        if f_s.startswith("|"):
                            if re.search(r"\bskip\b", f_s):
                                has_skip_fallback = True
                                break
                            k_fwd += 1
                            continue
                        if f_ind > line_indent:
                            k_fwd += 1
                            continue
                        break
                first_arm_inner = _strip_outer_parens(first_arm)
                first_arm_no_done = re.sub(r"(?:<;>|;)\s*done\s*$", "", first_arm_inner).strip()
                first_arm_expr, first_arm_is_tac = _unwrap_leaf_or_ctor_proof(first_arm_no_done)
                comb_src = f"{pre_nonbullet} {enclosing_comb_kw}"
                if re.search(r"\ball_goals\b|<;>", comb_src) and ctor_scopes and ctor_scopes[-1]["fields"]:
                    s_idx_cur = ctor_scopes[-1]["subgoal_idx"]
                    if s_idx_cur is None:
                        a_can_fail = bool(
                            re.fullmatch(
                                r"(?:rfl|trivial|True\.intro|Iff\.rfl|contradiction|done|simp|dsimp|simp\s+only\s*\[\s*\])",
                                first_arm_expr,
                            )
                            or _is_eq_refl_expr(first_arm_expr)
                        )
                    else:
                        rem_fields = ctor_scopes[-1]["fields"][s_idx_cur:]
                        a_can_fail = (not rem_fields) or any(
                            _can_fail_against_goal(
                                first_arm_expr,
                                first_arm_is_tac,
                                f_ty,
                                in_ctor=True,
                                struct_specs=struct_specs,
                                struct_field_counts=struct_field_counts,
                                struct_param_names=struct_param_names,
                                nat_vars=eff_nat_vars,
                            )
                            for _, f_ty in rem_fields
                        )
                else:
                    target_ty_arm1 = eff_field_ty if eff_in_ctor else root_goal_ty
                    a_can_fail = _can_fail_against_goal(
                        first_arm_expr,
                        first_arm_is_tac,
                        target_ty_arm1,
                        in_ctor=eff_in_ctor,
                        struct_specs=struct_specs,
                        struct_field_counts=struct_field_counts,
                        struct_param_names=struct_param_names,
                        nat_vars=eff_nat_vars,
                    )
                if (
                    not a_can_fail
                    and is_first_mode
                    and re.search(r"\b(?:rw|rewrite)\b", first_arm_no_done)
                ):
                    cand_fallback_arms: list[str] = []
                    if found_inline_pipe and after_pipe:
                        cand_fallback_arms.extend(_split_top_level_pipes(after_pipe))
                    arm_base_ind = enclosing_comb_indent if enclosing_comb_indent is not None else line_indent
                    k_sib_chk = i
                    cur_sib: list[str] = []
                    while k_sib_chk < n:
                        f_line = lines[k_sib_chk]
                        f_s = f_line.strip()
                        if not f_s:
                            k_sib_chk += 1
                            continue
                        f_ind = len(f_line[: len(f_line) - len(f_line.lstrip())].replace("\t", "    "))
                        if f_ind < arm_base_ind:
                            break
                        if f_s.startswith("|"):
                            if cur_sib:
                                cand_fallback_arms.append("\n".join(cur_sib))
                                cur_sib.clear()
                            cur_sib.append(f_s[1:].strip())
                            k_sib_chk += 1
                            continue
                        if cur_sib and f_ind > line_indent:
                            cur_sib.append(f_s)
                            k_sib_chk += 1
                            continue
                        if f_ind > line_indent:
                            k_sib_chk += 1
                            continue
                        break
                    if cur_sib:
                        cand_fallback_arms.append("\n".join(cur_sib))
                    if any(
                        _is_trivial_first_arm(
                            fb,
                            struct_field_counts=struct_field_counts,
                            struct_param_names=struct_param_names,
                        )
                        for fb in cand_fallback_arms
                    ):
                        a_can_fail = True

                aux_cand_lines: list[str] = []
                inline_fallback_tail = ""
                if trailing_inline_aux:
                    tr_aux = trailing_inline_aux
                    if is_combinator_prefix and re.search(r"\bfirst\b", pre_nonbullet):
                        after_last_pipe = pre_nonbullet.rsplit("|", 1)[-1]
                        tr_init_depth = _count_unclosed_wrapper_depth(after_last_pipe)
                        tr_depth = tr_init_depth
                        tr_pipe_idx: int | None = None
                        for idx_t, ch_t in enumerate(tr_aux):
                            if ch_t in "([{⦃⟨":
                                tr_depth += 1
                            elif ch_t in ")]}⦄⟩" and tr_depth > 0:
                                tr_depth -= 1
                            elif tr_depth == 0 and ch_t == "|" and not tr_aux.startswith(("||", "|>"), idx_t):
                                tr_pipe_idx = idx_t
                                break
                        if tr_pipe_idx is not None:
                            inline_fallback_tail = tr_aux[tr_pipe_idx:].strip()
                            tr_aux = tr_aux[:tr_pipe_idx].strip()
                            has_any_inline_fallback = has_any_inline_fallback or bool(inline_fallback_tail)
                            if re.search(r"\bskip\b", inline_fallback_tail):
                                has_skip_fallback = True
                    if wrap_depth > 0 and not inline_fallback_tail:
                        tr_aux = _strip_trailing_wrappers(tr_aux, wrap_depth)
                    if tr_aux:
                        aux_cand_lines.append(tr_aux)
                k_aux = i
                aux_probe_min = (
                    (line_indent + 1)
                    if enclosing_is_first
                    else (line_indent if enclosing_comb_indent is not None else (line_indent + 1))
                )
                while k_aux < n:
                    ax_line = lines[k_aux]
                    ax_s = ax_line.strip()
                    if not ax_s:
                        k_aux += 1
                        continue
                    ax_ind = len(ax_line[: len(ax_line) - len(ax_line.lstrip())].replace("\t", "    "))
                    if ax_ind < aux_probe_min:
                        break
                    if enclosing_is_first and ax_s.startswith("|"):
                        break
                    aux_cand_lines.append(ax_s)
                    k_aux += 1
                aux_cand_text = _strip_outer_parens("\n".join(aux_cand_lines).strip())

                hdr_joined = "\n".join(header_parts).strip()
                hdr_colon = _find_top_level_colon(hdr_joined)
                hdr_prop = hdr_joined[hdr_colon + 1 :].strip() if hdr_colon is not None else hdr_joined
                is_unsat_hdr, hdr_kind, _is_conj_hdr = _classify_suffices_prop_detail(hdr_prop, nat_vars=eff_nat_vars)
                b_can_fail = _suffices_aux_can_fail(
                    hdr_kind,
                    is_unsat_hdr,
                    aux_cand_text,
                    hdr_prop=hdr_prop,
                    struct_specs=struct_specs,
                    struct_field_counts=struct_field_counts,
                    struct_param_names=struct_param_names,
                    nat_vars=eff_nat_vars,
                )
                arm1_can_fail = a_can_fail or b_can_fail
                is_fallible_comb = (
                    bool(re.search(r"\b(?:try|repeat'?|any_goals)\b", comb_src))
                    or has_skip_fallback
                    or has_any_inline_fallback
                )
                if is_fallible_comb and arm1_can_fail:
                    preserves_fallthrough = True
                if preserves_fallthrough and inline_fallback_tail:
                    if out and len(out) > out_start_idx:
                        out[-1] = out[-1].rstrip() + " " + inline_fallback_tail
                    else:
                        out.append((" " * line_indent) + inline_fallback_tail)
                if found_inline_pipe and not preserves_fallthrough and inline_pipe_idx is not None:
                    # Arm 1 succeeded: strip unreachable inline `| <fallback>` arm(s) from emitted `out`
                    del out[out_start_idx:]
                    kept_arm = stripped_main.strip()[:inline_pipe_idx].strip()
                    if eff_has_nonbullet and eff_prefix.rstrip():
                        if kept_arm and "\n" not in kept_arm:
                            out.append(eff_prefix.rstrip() + " " + kept_arm.lstrip())
                        else:
                            out.append(eff_prefix.rstrip())
                            if kept_arm:
                                out.append(kept_arm)
                    elif kept_arm:
                        out.append(kept_arm)
            has_non_skip_sibling_arm = False
            if enclosing_is_first and arm1_can_fail:
                k_sib = i
                while k_sib < n:
                    s_line = lines[k_sib]
                    s_str = s_line.strip()
                    if not s_str:
                        k_sib += 1
                        continue
                    s_ind = len(s_line[: len(s_line) - len(s_line.lstrip())].replace("\t", "    "))
                    if enclosing_comb_indent is not None and s_ind < enclosing_comb_indent:
                        break
                    if s_str.startswith("|"):
                        arm_body = s_str[1:].strip()
                        if arm_body != "skip":
                            has_non_skip_sibling_arm = True
                            break
                        k_sib += 1
                        continue
                    if s_ind > line_indent:
                        k_sib += 1
                        continue
                    break

            if enclosing_comb_indent is not None and not preserves_fallthrough and not has_non_skip_sibling_arm:
                aux_min_indent = enclosing_comb_indent
            elif enclosing_is_first and (preserves_fallthrough or has_non_skip_sibling_arm):
                aux_min_indent = line_indent + 1
            else:
                aux_min_indent = bullet_indent if (
                    not has_nonbullet
                    or prefix.rstrip().endswith((";", "<;>"))
                    or is_wrapper_only
                    or (is_combinator_prefix and not preserves_fallthrough)
                ) else line_indent + 1
            while i < n:
                nxt = lines[i]
                nxt_stripped = nxt.strip()
                if not nxt_stripped:
                    i += 1
                    continue
                nxt_indent = len(nxt[: len(nxt) - len(nxt.lstrip())].replace("\t", "    "))
                if nxt_indent >= aux_min_indent:
                    i += 1
                    continue
                break
            if ctor_scopes and not is_pipe_stmt and not is_bul_stmt:
                sc_top = ctor_scopes[-1]
                if sc_top["bullet_indent"] is None and not sc_top["case_seen"]:
                    sc_top["unbulleted_pending"] = "ambiguous"
                    sc_top["unbulleted_indent"] = line_indent
            continue
        line_clean = re.sub(r"\b(?:have|let|suffices)\b[^;\n]*(?:;|$)", " ", line)
        out.append(line_clean)
        line_indent = len(line[: len(line) - len(line.lstrip())].replace("\t", "    "))
        line_s_l = line.lstrip()
        is_pipe_line = line_s_l.startswith("|")
        m_bul_line = _LEADING_BULLET_RE.match(line_s_l)
        is_bul_line = bool(m_bul_line and m_bul_line.group(0).strip()) and not is_pipe_line
        _pop_shadow_scopes(line_indent, is_pipe_line, is_bul_line)
        if line_s_l:
            saved_nat = set(cur_nat_vars)
            saved_binders = list(cur_goal_binders)
            if _apply_intro_shadowing(line_s_l, cur_nat_vars, cur_goal_binders):
                shadow_stack.append((line_indent, is_pipe_line or is_bul_line, saved_nat, saved_binders))
        _pop_ctor_scopes(line_indent, is_pipe_line, is_bul_line)
        _advance_ctor_subgoal(line, line_indent, is_bul_line, is_pipe_line)
        if (
            _CTOR_OPEN_LINE_RE.search(line)
            or _match_ctor_apply_in_line(
                line,
                allow_trivial_field_args=True,
                struct_field_counts=struct_field_counts,
                struct_param_names=struct_param_names,
            ) is not None
        ) and not _has_trivial_ctor_closure(
            line, struct_field_counts=struct_field_counts, struct_param_names=struct_param_names
        ):
            sc_kind = "pipe" if is_pipe_line else ("bul" if is_bul_line else "plain")
            parent_field_ty = _current_scope_field_ty()
            scope_fields = _resolve_ctor_scope_fields(line, parent_field_ty, struct_specs)
            ctor_scopes.append(
                {
                    "indent": line_indent,
                    "kind": sc_kind,
                    "fields": scope_fields,
                    "subgoal_idx": 0,
                    "bullet_indent": None,
                    "case_seen": False,
                    "unbulleted_pending": None,
                    "unbulleted_indent": None,
                }
            )
        elif ctor_scopes and not is_pipe_line and not is_bul_line and not re.match(
            r"^(?:case'?\s+[^\n=>]+?|next(?:\s+[^\n=>]+?)?)\s*=>", line_s_l
        ):
            sc_top = ctor_scopes[-1]
            if sc_top["bullet_indent"] is None and not sc_top["case_seen"] and line_s_l:
                if not re.fullmatch(r"first", line_s_l):
                    if _is_definite_single_line_subgoal_closer(line_s_l):
                        sc_top["unbulleted_pending"] = "advance"
                        sc_top["unbulleted_indent"] = line_indent
                    else:
                        sc_top["unbulleted_pending"] = "ambiguous"
                        sc_top["unbulleted_indent"] = line_indent
        events.append(("out", line_indent, is_bul_line, line_clean))
        i += 1
    return "\n".join(out), bindings, events


def _eval_subblock_liveness(events: list[tuple[Any, ...]]) -> tuple[set[str], bool]:
    """Compute live variables and anonymous-hyp tactic presence across `events` with scope-bounded shadowing."""
    n_ev = len(events)
    scope_end = [n_ev] * n_ev
    for idx, ev in enumerate(events):
        if ev[0] != "bind":
            continue
        _, scope_indent, is_bullet_start, _, _ = ev
        end_idx = n_ev
        for j in range(idx + 1, n_ev):
            ev_indent = events[j][1]
            ev_is_bullet = events[j][2]
            if is_bullet_start:
                if ev_indent <= scope_indent:
                    end_idx = j
                    break
            else:
                if ev_indent < scope_indent or (ev_is_bullet and ev_indent <= scope_indent):
                    end_idx = j
                    break
        scope_end[idx] = end_idx

    def _eval(lo: int, hi: int) -> tuple[set[str], bool]:
        live: set[str] = set()
        anon = False
        k = lo
        while k < hi:
            ev = events[k]
            if ev[0] == "out":
                _, _, _, txt = ev
                live.update(_LEAN_IDENT_TOKEN_RE.findall(txt))
                if _ANON_HYP_TACTIC_RE.search(txt):
                    anon = True
                k += 1
            elif ev[0] == "out_anon":
                _, _, _, vars_set, ev_anon = ev
                live.update(vars_set)
                if ev_anon:
                    anon = True
                k += 1
            else:
                _, _, _, lhs_names, body_part = ev
                se = min(hi, scope_end[k])
                in_vars, in_anon = _eval(k + 1, se)
                lhs_set = set(lhs_names)
                rem_vars = in_vars - lhs_set
                if (lhs_set & in_vars) or in_anon:
                    rem_vars.update(_LEAN_IDENT_TOKEN_RE.findall(body_part))
                    if _ANON_HYP_TACTIC_RE.search(body_part):
                        anon = True
                live.update(rem_vars)
                if in_anon:
                    anon = True
                k = se
        return live, anon

    return _eval(0, n_ev)


def _strip_have_subblocks_with_bindings(
    tail: str,
    **kwargs: Any,
) -> tuple[str, list[tuple[list[str], str]]]:
    """Remove `have`/`let` sub-blocks and dead `suffices` aux branches, returning stripped text + stripped bindings."""
    stripped, bindings, _ = _strip_have_subblocks_with_liveness(tail, **kwargs)
    return stripped, bindings


def _strip_have_subblocks(tail: str, **kwargs: Any) -> str:
    """Remove `have`/`let` sub-blocks and dead `suffices` aux branches while preserving live `suffices` proofs."""
    stripped, _ = _strip_have_subblocks_with_bindings(tail, **kwargs)
    return stripped


def _find_top_level_colon(s: str) -> int | None:
    depth = 0
    open_ch = set("([{⦃")
    close_ch = set(")]}⦄")
    i = 0
    n = len(s)
    while i < n:
        ch = s[i]
        if ch == "«":
            i += 1
            while i < n and s[i] not in ("»", "\n"):
                i += 1
            if i < n and s[i] == "»":
                i += 1
            continue
        if ch in open_ch:
            depth += 1
        elif ch in close_ch and depth > 0:
            depth -= 1
        elif depth == 0 and ch == ":" and not s.startswith(":=", i):
            return i
        i += 1
    return None


def _extract_bracket_binder_names(src: str, *, allow_untyped: bool = True) -> tuple[set[str], str]:
    """Extract binder variable names from bracketed `(x : T)`/`{x : T}`/`⦃x : T⦄` groups using balanced nesting."""
    names: set[str] = set()
    unparen_parts: list[str] = []
    open_ch = set("([{⦃")
    close_ch = set(")]}⦄")
    i = 0
    n = len(src)
    while i < n:
        ch = src[i]
        if ch in open_ch:
            start = i
            depth = 1
            i += 1
            while i < n and depth > 0:
                if src[i] in open_ch:
                    depth += 1
                elif src[i] in close_ch:
                    depth -= 1
                i += 1
            inner = src[start + 1 : i - 1] if depth == 0 else src[start + 1 :]
            if ch in ("(", "{", "⦃"):
                colon_idx = _find_top_level_colon(inner)
                if colon_idx is not None:
                    lhs = inner[:colon_idx]
                    for tok in lhs.split():
                        if _LEAN_IDENT_SEG_RE.fullmatch(tok) and tok not in _LEAN_TERM_KEYWORDS and tok != "_":
                            names.add(tok)
                elif allow_untyped:
                    toks = inner.split()
                    if toks and all(_LEAN_IDENT_SEG_RE.fullmatch(t) and t not in _LEAN_TERM_KEYWORDS for t in toks):
                        for t in toks:
                            if t != "_":
                                names.add(t)
            unparen_parts.append(" ")
            continue
        unparen_parts.append(ch)
        i += 1
    return names, "".join(unparen_parts)


_CONCRETE_BUILTIN_IDENTS = frozenset({
    "true", "false", "True", "False", "Prop", "Type", "Sort",
    "Nat", "Int", "Bool", "Real", "Complex", "Rat", "String", "Char",
    "Unit", "PUnit", "Empty", "PEmpty", "ℕ", "ℤ", "ℚ", "ℝ", "ℂ",
})
_EXPR_KEYWORDS = frozenset({
    "fun", "λ", "∀", "forall", "let", "have", "in", "if", "then", "else",
    "match", "with", "do", "by", "show", "from", "Type", "Sort", "Prop",
})


def _is_locally_defined(ident: str, preceding_clean: str) -> bool:
    return bool(
        re.search(
            rf"(?m)^\s*(?:@\[[^\n]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
            rf"(?:def|abbrev|opaque|structure|inductive|class|instance|axiom)\s+{re.escape(ident)}(?=\s|$|[:({{\[⦃]|\.\{{)",
            preceding_clean,
        )
    )


def _extract_binder_var_names(decl_header: str, ret_type: str, preceding_clean: str) -> set[str]:
    """Collect parameter identifier names from declaration binders, `∀`/Pi-arrow prefixes, and prior `variable` lines."""
    names: set[str] = set()
    top_colon = _find_top_level_colon(decl_header)
    param_header = decl_header[:top_colon] if top_colon is not None else decl_header
    sources = [param_header]
    for m_var in re.finditer(r"(?m)^\s*variable\s+([^\n]+)", preceding_clean):
        sources.append(m_var.group(1))
    for src in sources:
        found_names, _ = _extract_bracket_binder_names(src, allow_untyped=True)
        names.update(found_names)
    # Also peel leading `∀`/`forall` and dependent Pi-arrow `(x : T) →` / `{x : T} →` / `⦃x : T⦄ →` / `[T] →` binders from ret_type
    s = ret_type.strip()
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    while True:
        s = _strip_outer_parens(s)
        peeled_lh = _strip_leading_let_have(s)
        if peeled_lh is not None:
            s = peeled_lh
            continue
        m_forall = re.match(r"^(?:∀|forall(?=\s|[({\[⦃«]))", s)
        if m_forall:
            comma_idx = _forall_comma_map(s, _bracket_depths(s)).get(0)
            if comma_idx is None:
                break
            binder_chunk = s[m_forall.end() : comma_idx].strip()
            chunk_names, unparen = _extract_bracket_binder_names(binder_chunk, allow_untyped=True)
            names.update(chunk_names)
            # Unparenthesized `∀ x y : T` or `∀ x`
            lhs_part = unparen.split(":", 1)[0]
            for tok in lhs_part.split():
                if _LEAN_IDENT_SEG_RE.fullmatch(tok) and tok not in _LEAN_TERM_KEYWORDS and tok != "_":
                    names.add(tok)
            s = s[comma_idx + 1 :].strip()
            continue
        if s and s[0] in ("(", "{", "⦃", "["):
            opener = s[0]
            depth = 0
            close_idx: int | None = None
            for idx, ch in enumerate(s):
                if ch in open_ch:
                    depth += 1
                elif ch in close_ch:
                    depth -= 1
                    if depth == 0:
                        close_idx = idx
                        break
            if close_idx is not None:
                after = s[close_idx + 1 :].lstrip()
                arrow_len = 1 if after.startswith("→") else (2 if after.startswith("->") else 0)
                if arrow_len:
                    group = s[: close_idx + 1]
                    chunk_names, _ = _extract_bracket_binder_names(
                        group, allow_untyped=(opener in ("{", "⦃"))
                    )
                    names.update(chunk_names)
                    s = after[arrow_len:].strip()
                    continue
        break
    return names


def _split_top_level_args(args_str: str) -> list[str]:
    tokens: list[str] = []
    cur: list[str] = []
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    for ch in args_str:
        if ch in open_ch:
            depth += 1
            cur.append(ch)
        elif ch in close_ch:
            if depth > 0:
                depth -= 1
            cur.append(ch)
        elif depth == 0 and ch.isspace():
            if cur:
                tokens.append("".join(cur))
                cur.clear()
        else:
            cur.append(ch)
    if cur:
        tokens.append("".join(cur))
    return tokens


def _classify_model_args(
    ret_head: str,
    decl_header: str,
    ret_type: str,
    preceding_clean: str,
) -> tuple[bool, bool]:
    """Return `(has_non_binder_concrete, has_binder_derived_expr)` for `ret_head` arguments."""
    m_head = re.match(
        rf"^(?:{_LEAN_IDENT_SEG}\.)*{_LEAN_IDENT_SEG}(?:\.\{{[^}}]*\}})?",
        ret_head.strip(),
    )
    if not m_head:
        return False, False
    args_str = ret_head.strip()[m_head.end() :].strip()
    if not args_str:
        return False, False
    binder_vars = _extract_binder_var_names(decl_header, ret_type, preceding_clean)
    has_non_binder_concrete = False
    has_binder_derived_expr = False
    for tok in _split_top_level_args(args_str):
        if tok.startswith(("{", "[", "⦃")):
            continue
        inner = _strip_outer_parens(tok)
        if not inner:
            continue
        m_named = re.match(rf"^({_LEAN_IDENT_SEG})\s*:=\s*([\s\S]+)$", inner)
        if m_named:
            inner = _strip_outer_parens(m_named.group(2))
            if not inner:
                continue
        if _LEAN_IDENT_SEG_RE.fullmatch(inner):
            if inner in binder_vars:
                continue
            if inner in _CONCRETE_BUILTIN_IDENTS or _is_locally_defined(inner, preceding_clean):
                has_non_binder_concrete = True
            continue
        local_bound: set[str] = set()
        for m_lb in re.finditer(r"(?:fun|λ|∀|forall)\s+([^=⇒→,:\n]+)", inner):
            lb_names, unp = _extract_bracket_binder_names(m_lb.group(1), allow_untyped=True)
            local_bound.update(lb_names)
            for t in unp.split():
                if _LEAN_IDENT_SEG_RE.fullmatch(t) and t not in _LEAN_TERM_KEYWORDS and t != "_":
                    local_bound.add(t)
        depends_on_var = False
        for m_tok in _LEAN_QUAL_TOKEN_RE.finditer(inner):
            qtok = m_tok.group(0)
            if qtok.startswith("."):
                continue
            if "." in qtok:
                root_seg = split_lean_qual_ident(qtok)[0]
                if root_seg in binder_vars:
                    depends_on_var = True
                    break
                continue
            if (
                qtok not in _EXPR_KEYWORDS
                and qtok not in _CONCRETE_BUILTIN_IDENTS
                and qtok not in local_bound
                and (qtok in binder_vars or not _is_locally_defined(qtok, preceding_clean))
            ):
                depends_on_var = True
                break
        if depends_on_var:
            has_binder_derived_expr = True
        else:
            has_non_binder_concrete = True
    return has_non_binder_concrete, has_binder_derived_expr


def _has_concrete_model_args(
    ret_head: str,
    decl_header: str,
    ret_type: str,
    preceding_clean: str,
) -> bool:
    """Return True if `ret_head` instantiates concrete non-variable model arguments (Trap T17 witness)."""
    has_concrete, _ = _classify_model_args(ret_head, decl_header, ret_type, preceding_clean)
    return has_concrete


_SIG_HEAD_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\n]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|example|instance|structure|class|inductive|axiom|opaque)\b"
)


def _extract_signature_and_variable_text(clean: str) -> str:
    """Extract declaration signatures (before `:=`/`where`/`|`) and `variable` lines, excluding proof bodies."""
    parts = [m.group(1) for m in re.finditer(r"(?m)^\s*variable\s+([^\n]+)", clean)]
    for m in _SIG_HEAD_RE.finditer(clean):
        kw = m.group(0).split()[-1]
        if kw in ("axiom", "opaque"):
            end = min(len(clean), m.end() + 2000)
            nxt = re.search(r"(?m)^\S", clean[m.end() : end])
            parts.append(clean[m.start() : m.end() + nxt.start()] if nxt else clean[m.start() : end])
            continue
        _, split_pos, is_where = _find_decl_return_type_and_split(clean, m.end(), allow_where=True)
        if split_pos is not None:
            parts.append(clean[m.start() : split_pos])
            if kw == "inductive" and is_where:
                tail = clean[split_pos : min(len(clean), split_pos + 4000)]
                nxt = re.search(r"(?m)^(?!\|)\S", tail)
                if nxt:
                    tail = tail[: nxt.start()]
                parts.append(tail)
    return "\n".join(parts)


def _extract_struct_class_body_text(clean: str) -> str:
    """Extract field-declaration bodies of `structure` and `class` declarations only."""
    parts: list[str] = []
    open_brackets = set("([{⦃")
    close_brackets = set(")]}⦄")
    n = len(clean)
    for st in PROP_STRUCT_HEAD_START_RE.finditer(clean):
        head_line_start = clean.rfind("\n", 0, st.end()) + 1
        m_ws = re.match(r"^[ \t]*", clean[head_line_start:])
        struct_indent = len(m_ws.group(0).replace("\t", "    ")) if m_ws else 0
        i = st.end()
        limit = min(n, i + 4000)
        depth = 0
        while i < limit:
            ch = clean[i]
            if ch in open_brackets:
                depth += 1
                i += 1
                continue
            if ch in close_brackets:
                if depth > 0:
                    depth -= 1
                i += 1
                continue
            if depth == 0:
                if clean.startswith(":=", i):
                    line_end = clean.find("\n", i + 2)
                    if line_end == -1:
                        inline_rest = clean[i + 2 :].strip()
                        if inline_rest:
                            parts.append("  " + inline_rest)
                    else:
                        inline_rest = clean[i + 2 : line_end].strip()
                        if inline_rest:
                            parts.append("  " + inline_rest)
                        pos = line_end + 1
                        while pos < n:
                            nxt_nl = clean.find("\n", pos)
                            line = clean[pos:] if nxt_nl == -1 else clean[pos:nxt_nl]
                            if line.strip() == "":
                                if nxt_nl == -1:
                                    pos = n
                                    break
                                pos = nxt_nl + 1
                                continue
                            line_indent = len(line[: len(line) - len(line.lstrip())].replace("\t", "    "))
                            if line_indent > struct_indent:
                                if nxt_nl == -1:
                                    pos = n
                                    break
                                pos = nxt_nl + 1
                                continue
                            break
                        parts.append(clean[line_end + 1 : pos])
                    break
                if (
                    (i == 0 or not (clean[i - 1].isalnum() or clean[i - 1] in "_'»"))
                    and re.match(r"where\b", clean[i:])
                ):
                    where_end = i + 5
                    line_end = clean.find("\n", where_end)
                    if line_end == -1:
                        inline_rest = clean[where_end:].strip()
                        if inline_rest:
                            parts.append("  " + inline_rest)
                    else:
                        inline_rest = clean[where_end:line_end].strip()
                        if inline_rest:
                            parts.append("  " + inline_rest)
                        pos = line_end + 1
                        while pos < n:
                            nxt_nl = clean.find("\n", pos)
                            line = clean[pos:] if nxt_nl == -1 else clean[pos:nxt_nl]
                            if line.strip() == "":
                                if nxt_nl == -1:
                                    pos = n
                                    break
                                pos = nxt_nl + 1
                                continue
                            line_indent = len(line[: len(line) - len(line.lstrip())].replace("\t", "    "))
                            if line_indent > struct_indent:
                                if nxt_nl == -1:
                                    pos = n
                                    break
                                pos = nxt_nl + 1
                                continue
                            break
                        parts.append(clean[line_end + 1 : pos])
                    break
                if ch == "\n" and i + 1 < limit and _DECL_BOUNDARY_RE.match(clean[i + 1 :]):
                    break
            i += 1
    return "\n".join(parts)


def _bracket_depths(s: str) -> list[int]:
    depths: list[int] = []
    depth = 0
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")
    for ch in s:
        depths.append(depth)
        if ch in open_ch:
            depth += 1
        elif ch in close_ch and depth > 0:
            depth -= 1
    return depths


def _forall_comma_map(rt: str, depths: list[int]) -> dict[int, int]:
    """Return `{forall_open_idx: closing_comma_idx}` for `∀`/`forall` binders at matching bracket depth."""
    comma_map: dict[int, int] = {}
    binder_stack: list[tuple[int, str, int]] = []
    n = len(rt)
    i = 0
    while i < n:
        ch = rt[i]
        if ch == "«":
            i += 1
            while i < n and rt[i] not in ("»", "\n"):
                i += 1
            if i < n and rt[i] == "»":
                i += 1
            continue
        if ch == "∀":
            binder_stack.append((depths[i], "forall", i))
        elif (i == 0 or not (rt[i - 1].isalnum() or rt[i - 1] in "_'«».")) and re.match(
            r"forall(?=\s|[({\[⦃«])", rt[i:]
        ):
            binder_stack.append((depths[i], "forall", i))
            i += 6
            continue
        elif (i == 0 or not (rt[i - 1].isalnum() or rt[i - 1] in "_'«».")) and re.match(
            r"exists(?=\s|[({\[⦃«])", rt[i:]
        ):
            binder_stack.append((depths[i], "other", -1))
            i += 6
            continue
        elif ch in ("∃", "Σ", "∑", "∏", "∐", "⋃", "⋂", "⨆", "⨅", "∫"):
            binder_stack.append((depths[i], "other", -1))
        elif ch == ",":
            d_cur = depths[i]
            while binder_stack and binder_stack[-1][0] > d_cur:
                binder_stack.pop()
            if binder_stack and binder_stack[-1][0] == d_cur:
                _, kind, open_idx = binder_stack.pop()
                if kind == "forall" and open_idx >= 0:
                    comma_map[open_idx] = i
        i += 1
    return comma_map


def _forall_comma_indices(rt: str, depths: list[int]) -> set[int]:
    """Return indices of `,` that close a `∀`/`forall` binder at matching bracket depth."""
    return set(_forall_comma_map(rt, depths).values())


def _prop_structure_is_consumed_in_module(
    clean: str,
    type_name: str,
    decl_ret_types: list[str],
    sig_and_var_text: str | None = None,
    struct_body_text: str | None = None,
    ctor_names: tuple[str, ...] = ("mk",),
) -> bool:
    """Return True if a parameterized `: Prop` structure is consumed as a hypothesis/field/projection/conjunct."""
    short_name = lean_short_name(type_name)
    name_pat = rf"(?:{_LEAN_IDENT_SEG}\.)*{re.escape(short_name)}(?=\s|$|[:({{\[⦃,)\]\}}⦄])"
    if sig_and_var_text is None:
        sig_and_var_text = _extract_signature_and_variable_text(clean)
    if struct_body_text is None:
        struct_body_text = _extract_struct_class_body_text(clean)
    # 1. Binder / parameter / instance hypothesis `(h : T ...)`, `{h : T ...}`, `[h : T ...]` in signatures/variables ONLY
    for m in re.finditer(rf"([({{\[⦃])([^(){{}}\[\]⦃⦄:=\n]*?):\s*{name_pat}", sig_and_var_text):
        lhs = m.group(2).strip()
        toks = lhs.split()
        if (
            toks
            and all(_LEAN_IDENT_SEG_RE.fullmatch(tok) for tok in toks)
            and not any(tok in _LEAN_TERM_KEYWORDS for tok in toks)
        ):
            return True
    # 2. Field type inside another `structure` or `class` body ONLY
    if re.search(rf"(?m)^\s+(?:(?:private|protected)\s+)?{_LEAN_IDENT_SEG}\s*:(?![:=])\s*{name_pat}", struct_body_text):
        return True
    # 3. Dot projection / method outside `.mk` (or custom `<ctor>`) and outside declaration head names
    clean_no_decl_names = _DECL_HEAD_NAME_RE.sub(
        lambda m: m.group(1) + (" " * len(m.group(2))),
        clean,
    )
    ctor_alt = "|".join(re.escape(c) for c in ctor_names)
    if re.search(
        rf"(?<![^\s({{\[⦃]){re.escape(short_name)}\.(?!(?:{ctor_alt})(?:\.\{{[^}}]*\}})?(?=\s|$|[)\]\}}⦄,;])){_LEAN_IDENT_SEG}",
        clean_no_decl_names,
    ):
        return True
    # 4. Bracket-depth-aware arrow domain (`T ... → ...`) or compound synthesis (`T ... ∧ ...` / `↔` / `∃`)
    def _has_sep_at_max_depth(
        rt_s: str, rt_depths: list[int], f_commas: set[int], start: int, end: int, max_d: int
    ) -> bool:
        for idx in range(start, end):
            if rt_depths[idx] <= max_d and (
                rt_s[idx] == "→" or rt_s.startswith("->", idx) or idx in f_commas
            ):
                return True
        return False

    short_pat = re.compile(rf"(?<![^\s.({{\[⦃]){re.escape(short_name)}(?=\s|$|[:({{\[⦃,)\]\}}⦄→-])")
    for rt in decl_ret_types:
        matches = list(short_pat.finditer(rt))
        if not matches:
            continue
        depths = _bracket_depths(rt)
        f_commas = _forall_comma_indices(rt, depths)
        for m in matches:
            d_match = depths[m.start()]
            # 4a. `→` / `->` at depth <= d_match after `T`
            for j in range(m.end(), len(rt)):
                if depths[j] <= d_match and (rt[j] == "→" or rt.startswith("->", j)):
                    return True
            # 4b. `∧` / `↔` / `∃` at depth <= d_match, with no intervening depth <= d_match `→`/`->` or `∀`-closing `,`
            for k, ch in enumerate(rt):
                if depths[k] <= d_match:
                    if ch in ("∧", "↔"):
                        if k < m.start() and not _has_sep_at_max_depth(rt, depths, f_commas, k + 1, m.start(), d_match):
                            return True
                        if k > m.end() and not _has_sep_at_max_depth(rt, depths, f_commas, m.end(), k, d_match):
                            return True
                    elif ch == "∃" and k < m.start() and not _has_sep_at_max_depth(rt, depths, f_commas, k + 1, m.start(), d_match):
                        return True
    return False


def _ret_matches_prop_head(ret_type: str, ret_head_re: re.Pattern[str]) -> str | None:
    """Return matching `ret_head` if `ret_type` (possibly under `∀`/arrow/`let`/`if-then-else`) targets `ret_head_re`."""
    head = _strip_leading_forall_and_arrow(ret_type)
    if ret_head_re.match(head):
        return head
    branches = _extract_if_then_else_branches(head)
    if branches is not None:
        h1 = _ret_matches_prop_head(branches[0], ret_head_re)
        h2 = _ret_matches_prop_head(branches[1], ret_head_re)
        if h1 is not None and h2 is not None:
            return h1
    return None


def _is_trivial_first_arm(
    arm_txt: str,
    *,
    struct_field_counts: dict[str, int] | None = None,
    struct_param_names: dict[str, set[str]] | None = None,
) -> bool:
    """Return True iff a `first` fallback arm closes the goal trivially without `rw`/lemmas."""
    a_s = arm_txt.strip()
    if not a_s:
        return False
    # Remove placeholder `skip` / `(skip)` steps inserted when stripping `try rw` blocks
    cleaned_steps = [
        st for st in _split_top_level_semi_steps(a_s) if _strip_outer_parens(st.strip()) != "skip"
    ]
    a_eff = "; ".join(cleaned_steps) if cleaned_steps else a_s
    if _is_trivial_tactic_seq(
        a_eff,
        struct_field_counts=struct_field_counts,
        struct_param_names=struct_param_names,
    ):
        return True
    return bool(
        re.fullmatch(
            r"constructor\s*<;>\s*(?:exact\s+)?(?:rfl|trivial|True\.intro|Iff\.rfl)",
            a_eff,
        )
    )


def _find_matching_delim_lean(text: str, open_idx: int) -> int | None:
    """Return index of matching closing delimiter for `text[open_idx]`, skipping `«...»`."""
    open_c = text[open_idx]
    close_map = {"(": ")", "{": "}", "[": "]", "⦃": "⦄", "⟨": "⟩"}
    close_c = close_map.get(open_c)
    if close_c is None:
        return None
    depth = 1
    i = open_idx + 1
    n = len(text)
    while i < n:
        ch = text[i]
        if ch == "«":
            i += 1
            while i < n and text[i] not in ("»", "\n"):
                i += 1
            if i < n and text[i] == "»":
                i += 1
            continue
        if ch == open_c:
            depth += 1
        elif ch == close_c:
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return None


def _strip_concrete_fallible_rw_blocks(
    tail_no_have: str,
    *,
    struct_field_counts: dict[str, int] | None = None,
    struct_param_names: dict[str, set[str]] | None = None,
) -> str:
    """Strip `try rw/rewrite ...` and `first` blocks that have a trivial fallback arm for concrete-model checks."""
    text = tail_no_have
    open_ch = set("([{⦃⟨")
    close_ch = set(")]}⦄⟩")

    def _strip_one_try_rw(src: str) -> str | None:
        n_s = len(src)
        for m_try in re.finditer(r"(?<![.\w'»])try(?=\s|[({])", src):
            t_start = m_try.start()
            p = m_try.end()
            while p < n_s and src[p] in (" ", "\t"):
                p += 1
            if p >= n_s:
                continue
            if src[p] in ("{", "("):
                close_idx = _find_matching_delim_lean(src, p)
                if close_idx is not None:
                    body = src[p + 1 : close_idx]
                    if re.search(r"\b(?:rw|rewrite)\b", body):
                        return src[:t_start] + "skip" + src[close_idx + 1 :]
            elif src[p] == "\n":
                k_prev = t_start - 1
                while k_prev >= 0 and src[k_prev].isspace():
                    k_prev -= 1
                if k_prev >= 0 and src[k_prev] in ("(", "{"):
                    close_idx = _find_matching_delim_lean(src, k_prev)
                    if close_idx is not None:
                        body = src[m_try.end() : close_idx]
                        if re.search(r"\b(?:rw|rewrite)\b", body):
                            return src[:t_start] + "skip" + src[close_idx:]
                line_start = src.rfind("\n", 0, t_start) + 1
                raw_pref = src[line_start:t_start]
                if not raw_pref.strip() or re.search(r"(?:[·•|({;]|<;>|=>|\bby)\s*$", raw_pref):
                    line_ind = len(raw_pref[: len(raw_pref) - len(raw_pref.lstrip())].replace("\t", "    "))
                    t_col = len(raw_pref.replace("\t", "    "))
                    min_ind = t_col if re.fullmatch(r"\s*(?:[·•|]\s*)?", raw_pref) else line_ind
                    pos_ln = p + 1
                    last_end = p
                    d_try = 0
                    collected: list[str] = []
                    while pos_ln < n_s:
                        nl_i = src.find("\n", pos_ln)
                        ln_end = n_s if nl_i == -1 else nl_i
                        ln_txt = src[pos_ln:ln_end]
                        ln_strip = ln_txt.strip()
                        if ln_strip:
                            ln_ind = len(ln_txt[: len(ln_txt) - len(ln_txt.lstrip())].replace("\t", "    "))
                            if d_try == 0 and ln_ind <= min_ind:
                                break
                            # Stop cleanly if an enclosing `)`/`}`/`]` closes on this line
                            cut_idx: int | None = None
                            idx_c = 0
                            ln_n = len(ln_txt)
                            while idx_c < ln_n:
                                chc = ln_txt[idx_c]
                                if chc == "«":
                                    idx_c += 1
                                    while idx_c < ln_n and ln_txt[idx_c] not in ("»", "\n"):
                                        idx_c += 1
                                    if idx_c < ln_n and ln_txt[idx_c] == "»":
                                        idx_c += 1
                                    continue
                                if chc in open_ch:
                                    d_try += 1
                                elif chc in close_ch:
                                    if d_try == 0:
                                        cut_idx = idx_c
                                        break
                                    d_try -= 1
                                idx_c += 1
                            if cut_idx is not None:
                                part_c = ln_txt[:cut_idx].strip()
                                if part_c:
                                    collected.append(part_c)
                                    last_end = pos_ln + cut_idx
                                break
                            collected.append(ln_strip)
                            last_end = ln_end
                        if nl_i == -1:
                            break
                        pos_ln = nl_i + 1
                    if collected and re.search(r"\b(?:rw|rewrite)\b", "\n".join(collected)):
                        return src[:t_start] + "skip" + src[last_end:]
            elif re.match(r"(?:rw|rewrite)\b", src[p:]):
                d = 0
                q = p
                while q < n_s:
                    ch_q = src[q]
                    if ch_q == "«":
                        q += 1
                        while q < n_s and src[q] not in ("»", "\n"):
                            q += 1
                        if q < n_s and src[q] == "»":
                            q += 1
                        continue
                    if ch_q in open_ch:
                        d += 1
                    elif ch_q in close_ch:
                        if d == 0:
                            break
                        d -= 1
                    elif d == 0 and (
                        ch_q in (";", "\n")
                        or (ch_q == "|" and not src.startswith(("||", "|>"), q))
                        or src.startswith("<;>", q)
                    ):
                        break
                    q += 1
                return src[:t_start] + "skip" + src[q:]
        return None

    def _strip_one_first(src: str, min_pos: int) -> tuple[str | None, int]:
        n_s = len(src)
        for m_fst in re.finditer(r"(?<![.\w'»])first(?=\s*\|)", src[min_pos:]):
            f_start = min_pos + m_fst.start()
            pipe_idx = src.find("|", min_pos + m_fst.end())
            if pipe_idx == -1:
                continue
            # Check if `first` is directly inside `(...)` or `{...}`
            k_prev = f_start - 1
            while k_prev >= 0 and src[k_prev].isspace():
                k_prev -= 1
            wrapper_close: int | None = None
            if k_prev >= 0 and src[k_prev] in ("(", "{"):
                wrapper_close = _find_matching_delim_lean(src, k_prev)

            if wrapper_close is not None:
                f_end = wrapper_close
            else:
                line_start = src.rfind("\n", 0, f_start) + 1
                line_end_init = src.find("\n", line_start)
                if line_end_init == -1:
                    line_end_init = n_s
                raw_line_pref = src[line_start:]
                line_ind = len(
                    raw_line_pref[: len(raw_line_pref) - len(raw_line_pref.lstrip())].replace("\t", "    ")
                )
                first_col = len(src[line_start:f_start].replace("\t", "    "))
                pipe_line_start = src.rfind("\n", 0, pipe_idx) + 1
                first_pipe_col = len(src[pipe_line_start:pipe_idx].replace("\t", "    "))
                base_arm_col = first_pipe_col if src[pipe_line_start:pipe_idx].strip() == "" else first_col
                arm_col = base_arm_col
                d = 0
                q = pipe_idx
                f_end = n_s
                while q < n_s:
                    ch_q = src[q]
                    if ch_q == "«":
                        q += 1
                        while q < n_s and src[q] not in ("»", "\n"):
                            q += 1
                        if q < n_s and src[q] == "»":
                            q += 1
                        continue
                    if ch_q in open_ch:
                        d += 1
                    elif ch_q in close_ch:
                        if d == 0:
                            f_end = q
                            break
                        d -= 1
                    elif ch_q == "\n" and d == 0:
                        # Peek at next non-empty line to see if it continues `first`
                        peek = q + 1
                        nxt_ind = -1
                        nxt_s = ""
                        while peek < n_s:
                            nl_p = src.find("\n", peek)
                            ln_raw = src[peek:] if nl_p == -1 else src[peek:nl_p]
                            if ln_raw.strip():
                                nxt_s = ln_raw.lstrip()
                                nxt_ind = len(ln_raw[: len(ln_raw) - len(nxt_s)].replace("\t", "    "))
                                break
                            if nl_p == -1:
                                break
                            peek = nl_p + 1
                        if not nxt_s:
                            f_end = q
                            break
                        is_cont_pipe = (
                            nxt_s.startswith("|")
                            and not nxt_s.startswith(("||", "|>"))
                            and nxt_ind >= min(line_ind, first_col)
                        )
                        is_cont_body = nxt_ind > min(arm_col, base_arm_col)
                        if is_cont_pipe:
                            arm_col = nxt_ind
                        elif not is_cont_body:
                            f_end = q
                            break
                    q += 1
            arms = _split_top_level_pipes(src[pipe_idx + 1 : f_end])
            if arms and any(
                _is_trivial_first_arm(
                    a,
                    struct_field_counts=struct_field_counts,
                    struct_param_names=struct_param_names,
                )
                for a in arms
            ):
                return src[:f_start] + "exact trivial" + src[f_end:], f_start + len("exact trivial")
            return None, min_pos + m_fst.end()
        return None, n_s

    for _ in range(16):
        changed = False
        while True:
            nxt_try = _strip_one_try_rw(text)
            if nxt_try is None:
                break
            text = nxt_try
            changed = True
        cursor = 0
        while cursor < len(text):
            nxt_fst, nxt_cursor = _strip_one_first(text, cursor)
            if nxt_fst is not None:
                text = nxt_fst
                changed = True
                break
            if nxt_cursor <= cursor:
                break
            cursor = nxt_cursor
        if not changed:
            break
    return text


def scan_parameterized_prop_bundlers(source: str) -> list[tuple[str, str]]:
    """Catch unparameterized and write-only trivial parameterized multi-field `: Prop` bundler sinks."""
    clean = strip_lean_comments_and_strings(source)
    ctors_parsed: list[tuple[re.Match[str], str, int, bool]] = []
    decl_ret_types: list[str] = []
    for ctor in PROP_CONSTRUCTOR_HEAD_RE.finditer(clean):
        ret_type, split_pos, is_where = _find_decl_return_type_and_split(
            clean, ctor.end(), allow_where=True
        )
        if ret_type is not None and split_pos is not None:
            ctors_parsed.append((ctor, ret_type, split_pos, is_where))
            decl_ret_types.append(ret_type)

    sig_and_var_text: str | None = None
    struct_body_text: str | None = None
    known_prop_fields: dict[str, set[str]] = {}
    known_prop_ancestor_projs: dict[str, set[str]] = {}
    known_prop_field_types: dict[str, list[tuple[str, str]]] = {}
    known_struct_specs: dict[str, tuple[list[tuple[str, bool, bool]], list[tuple[str, str]]]] = {}
    struct_field_counts: dict[str, int] = {}
    found: list[tuple[str, str]] = []
    for type_name, header, body, is_assign_syntax, is_parameterized, parents, parent_projs in _iter_prop_structures(clean):
        short_name = lean_short_name(type_name)
        local_field_types = _extract_struct_field_types(body, is_assign_syntax)
        local_fields = [name for name, _ in local_field_types]
        local_field_set = set(local_fields)
        field_set = set(local_field_set)
        all_field_types: list[tuple[str, str]] = []
        for par in parents:
            par_ft = known_prop_field_types.get(par) or known_prop_field_types.get(lean_short_name(par), [])
            all_field_types.extend(par_ft)
        all_field_types.extend(local_field_types)
        param_specs = _extract_struct_param_specs(header)
        all_projs = set(parent_projs) | {f"to{lean_short_name(p)}" for p in parents}
        for par in parents:
            field_set.update(known_prop_fields.get(par) or known_prop_fields.get(lean_short_name(par), set()))
            all_projs.update(
                known_prop_ancestor_projs.get(par) or known_prop_ancestor_projs.get(lean_short_name(par), set())
            )
        known_prop_fields[type_name] = field_set
        known_prop_ancestor_projs[type_name] = all_projs
        known_prop_field_types[type_name] = all_field_types
        known_struct_specs[type_name] = (param_specs, all_field_types)
        struct_field_counts[type_name] = len(all_field_types)
        if short_name not in known_prop_fields:
            known_prop_fields[short_name] = field_set
        if short_name not in known_prop_ancestor_projs:
            known_prop_ancestor_projs[short_name] = all_projs
        if short_name not in known_prop_field_types:
            known_prop_field_types[short_name] = all_field_types
        if short_name not in known_struct_specs:
            known_struct_specs[short_name] = (param_specs, all_field_types)
        if short_name not in struct_field_counts:
            struct_field_counts[short_name] = len(all_field_types)
        if len(field_set) < 2:
            continue
        ctor_names = _extract_struct_ctor_names(body)
        ctor_alt = "|".join(re.escape(c) for c in ctor_names)
        ctor_min_args = len(local_field_set) + len(parents)
        if is_parameterized and sig_and_var_text is None:
            sig_and_var_text = _extract_signature_and_variable_text(clean)
        if is_parameterized and struct_body_text is None:
            struct_body_text = _extract_struct_class_body_text(clean)
        is_consumed = is_parameterized and _prop_structure_is_consumed_in_module(
            clean, type_name, decl_ret_types, sig_and_var_text, struct_body_text, ctor_names
        )
        if is_consumed:
            continue

        ret_head_re = re.compile(
            rf"^(?:(?:{_LEAN_IDENT_SEG}\.)*{re.escape(short_name)}|{re.escape(type_name)})"
            rf"(?:\s|$|\(|\{{|\[|\.\{{)"
        )
        for ctor, ret_type, split_pos, is_where in ctors_parsed:
            ret_head = _ret_matches_prop_head(ret_type, ret_head_re)
            if ret_head is None:
                continue
            tail = clean[split_pos:]
            is_eq_style = clean[split_pos : split_pos + 1] == "|"
            next_decl_pat = (
                r"(?m)^(?:@\[|(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+|"
                r"(?:theorem|lemma|example|def|abbrev|structure|class|inductive|instance|axiom|opaque|end|namespace|section|#)\b"
                + (r"|(?!\|)(?!where(?![\w'»]))\S)" if is_eq_style else r"|(?!where(?![\w'»]))\S)")
            )
            next_decl = re.search(next_decl_pat, tail)
            if next_decl:
                tail = tail[: next_decl.start()]
            # For parameterized standalone predicates/witnesses (Trap T17 compliant),
            # exempt constructors ONLY if they use goal-level structural induction/case analysis
            # outside `have ... :=` / `suffices` aux sub-blocks, OR instantiate concrete non-binder
            # model arguments with a non-trivial proof (and no binder-derived expressions),
            # OR prove a binder-derived model expression via `calc`.
            if is_parameterized:
                decl_header = clean[ctor.end() : split_pos]
                nat_vars = _extract_nat_binder_vars(decl_header, ret_type, clean[: ctor.start()])
                struct_param_names = {
                    k: {p_name for p_name, _, _ in p_specs}
                    for k, (p_specs, _) in known_struct_specs.items()
                }
                tail_no_have = _strip_have_subblocks(
                    tail,
                    struct_specs=known_struct_specs,
                    struct_field_counts=struct_field_counts,
                    struct_param_names=struct_param_names,
                    root_goal_ty=ret_head,
                    root_ret_type=ret_type,
                    nat_vars=nat_vars,
                )
                if STRUCTURAL_PROP_PROOF_RE.search(tail_no_have):
                    continue
                has_concrete, has_binder_expr = _classify_model_args(
                    ret_head, decl_header, ret_type, clean[: ctor.start()]
                )
                if has_concrete and not has_binder_expr:
                    concrete_tail = _strip_concrete_fallible_rw_blocks(
                        tail_no_have,
                        struct_field_counts=struct_field_counts,
                        struct_param_names=struct_param_names,
                    )
                    if _NON_SIMP_NONTRIVIAL_PROP_PROOF_RE.search(concrete_tail):
                        continue
                    if re.search(r"\bsimp\s+(?:only\s+)?\[", concrete_tail) and not _has_trivial_ctor_closure(
                        concrete_tail,
                        struct_field_counts=struct_field_counts,
                        struct_param_names=struct_param_names,
                    ):
                        continue
                if has_binder_expr and re.search(r"\bcalc\b", tail_no_have):
                    continue
            head_snippet = clean[ctor.start() : split_pos].strip().splitlines()[0]
            parent_to_fields = set(all_projs)
            if is_where:
                assigns = re.findall(rf"(?m)^\s+({_LEAN_IDENT_SEG})\s*:=\s*([^\n]+)", tail)
                assign_names = {name for name, _ in assigns}
                if field_set <= assign_names or (
                    bool(parents)
                    and local_field_set <= assign_names
                    and bool(parent_to_fields & assign_names or not local_field_set)
                ):
                    found.append((type_name, head_snippet))
                    continue
            else:
                rhs = tail.strip()
                brace_assigns = set(re.findall(rf"(?<![^\s{{,(])({_LEAN_IDENT_SEG})\s*:=\s*(?=\S)", rhs))
                if field_set <= brace_assigns or (
                    bool(parents)
                    and local_field_set <= brace_assigns
                    and bool(parent_to_fields & brace_assigns or not local_field_set)
                ):
                    found.append((type_name, head_snippet))
                    continue
                if _count_anon_ctor_args(rhs) >= ctor_min_args:
                    found.append((type_name, head_snippet))
                    continue
                if re.search(
                    rf"(?:(?<![^\s({{\[⦃.@]){re.escape(short_name)}|(?<![A-Za-z0-9_.]))\.(?:{ctor_alt})(?:\.\{{[^}}]*\}})?(?=\s|$|[)\]\}}⦄,;.(])",
                    rhs,
                ):
                    found.append((type_name, head_snippet))
                    continue
                struct_param_names_all = {
                    k: {p_name for p_name, _, _ in p_specs}
                    for k, (p_specs, _) in known_struct_specs.items()
                }
                if (
                    re.search(r"\bby\b[\s\S]*?\bconstructor\b", rhs)
                    or re.search(r"\b(?:And|Iff|Exists)\.intro\b", rhs)
                    or re.search(r"\b(?:exact|refine'?)(?:\s+|(?=[⟨{(]))(?:(?:\(|\bid\s+)*)⟨", rhs)
                    or _has_trivial_ctor_closure(
                        rhs,
                        struct_field_counts=struct_field_counts,
                        struct_param_names=struct_param_names_all,
                    )
                ):
                    found.append((type_name, head_snippet))
                    continue
    return found


def check_t1_lean_01_copyright_header(targets: list[ResolvedTarget]) -> CheckOutcome:
    """T1-LEAN-01: Exact 5-line REQUIRED_LEAN_COPYRIGHT_HEADER at byte 0."""
    existing = [t for t in targets if t.exists]
    if not existing:
        return CheckOutcome("T1-LEAN-01", 1, "F9", "FAIL", "No existing target .lean files to check copyright header")
    bad = [t.rel_path for t in existing if not check_lean_copyright_header(t.path)]
    if bad:
        return CheckOutcome(
            "T1-LEAN-01",
            1,
            "F9",
            "FAIL",
            f"Missing exact 5-line Apache copyright header at byte 0 in: {bad}",
            {"failed_files": bad},
        )
    return CheckOutcome(
        "T1-LEAN-01",
        1,
        "F9",
        "PASS",
        f"Exact 5-line copyright header verified at byte 0 ({len(existing)}/{len(existing)} files)",
    )


def check_t1_lean_02_style_and_module_doc(
    repo_root: Path,
    targets: list[ResolvedTarget],
    *,
    strict_live: bool,
) -> CheckOutcome:
    """T1-LEAN-02: style_lint.py + module_doc_lint.py verification."""
    style_lint = repo_root / "scripts" / "lint" / "required" / "style_lint.py"
    module_doc_lint = repo_root / "scripts" / "lint" / "required" / "module_doc_lint.py"
    existing = [t for t in targets if t.exists]
    if not style_lint.is_file() or not module_doc_lint.is_file():
        return CheckOutcome("T1-LEAN-02", 1, "F9", "FAIL", "Missing style_lint.py or module_doc_lint.py")
    if not existing:
        return CheckOutcome("T1-LEAN-02", 1, "F9", "FAIL", "No existing target .lean files for style/module-doc lint")

    file_args = [str(t.path) for t in existing]
    p_style = run_subprocess_safe([sys.executable, str(style_lint), *file_args], cwd=repo_root, timeout=60)
    p_mod = run_subprocess_safe([sys.executable, str(module_doc_lint), *file_args], cwd=repo_root, timeout=60)

    if strict_live:
        failures: list[str] = []
        if p_style.returncode != 0:
            failures.append(f"style_lint rc={p_style.returncode}: {p_style.stderr.strip() or p_style.stdout.strip()}")
        if p_mod.returncode != 0:
            failures.append(f"module_doc_lint rc={p_mod.returncode}: {p_mod.stderr.strip() or p_mod.stdout.strip()}")
        if failures:
            return CheckOutcome(
                "T1-LEAN-02",
                1,
                "F9",
                "FAIL",
                "Style/module-doc lint failed: " + "; ".join(failures),
            )
        return CheckOutcome(
            "T1-LEAN-02",
            1,
            "F9",
            "PASS",
            f"style_lint.py & module_doc_lint.py passed on {len(existing)} target file(s)",
        )

    # Non-strict baseline smoke mode: style_lint must pass; module_doc_lint debt on legacy files is recorded without failing
    if p_style.returncode != 0:
        return CheckOutcome(
            "T1-LEAN-02",
            1,
            "F9",
            "FAIL",
            f"style_lint failed on baseline smoke target: {p_style.stderr.strip()}",
        )
    mod_note = "passed" if p_mod.returncode == 0 else "legacy module_doc debt observed (non-blocking in baseline smoke)"
    return CheckOutcome(
        "T1-LEAN-02",
        1,
        "F9",
        "PASS",
        f"style_lint.py passed ({len(existing)} file(s)); module_doc_lint.py: {mod_note}",
        {"module_doc_rc": p_mod.returncode},
    )


def check_t1_lean_03_theorem_lint(
    repo_root: Path,
    targets: list[ResolvedTarget],
    *,
    strict_live: bool,
) -> CheckOutcome:
    """T1-LEAN-03: scripts/lint/required/theorem_lint.py docstring & Theorems.txt compliance."""
    theorem_lint = repo_root / "scripts" / "lint" / "required" / "theorem_lint.py"
    existing = [t for t in targets if t.exists]
    if not theorem_lint.is_file():
        return CheckOutcome("T1-LEAN-03", 1, "F9", "FAIL", "Missing scripts/lint/required/theorem_lint.py")
    if not existing:
        return CheckOutcome("T1-LEAN-03", 1, "F9", "FAIL", "No existing target .lean files for theorem_lint")
    proc = run_subprocess_safe(
        [sys.executable, str(theorem_lint), *[str(t.path) for t in existing]],
        cwd=repo_root,
        timeout=60,
    )
    if strict_live and proc.returncode != 0:
        return CheckOutcome(
            "T1-LEAN-03",
            1,
            "F9",
            "FAIL",
            f"theorem_lint.py failed (rc={proc.returncode}): {(proc.stdout + proc.stderr).strip()[:400]}",
        )
    note = "passed" if proc.returncode == 0 else "legacy theorem_lint debt observed (non-blocking in baseline smoke)"
    return CheckOutcome(
        "T1-LEAN-03",
        1,
        "F9",
        "PASS",
        f"theorem_lint.py ({len(existing)} file(s)): {note}",
        {"returncode": proc.returncode},
    )


def run_static_placeholder_vacuity_suite(
    repo_root: Path,
    lean_files: list[Path],
    *,
    strict_opengauss: bool,
) -> tuple[bool, list[str], dict[str, Any]]:
    """Run axiom_audit, placeholder_audit, semantic_vacuity_gate, detect_hollow_theorems, opengauss_screener, aggregate_prop_constructors, and native_decide/:True scan."""
    file_args = [str(p) for p in lean_files]
    failures: list[str] = []
    details: dict[str, Any] = {}

    # 1. axiom_audit.py --fail-on-gaps (NEVER pass --output or --write-report!)
    p_ax = run_subprocess_safe(
        [sys.executable, str(repo_root / "tools/infra/axiom_audit.py"), "--fail-on-gaps", *file_args],
        cwd=repo_root,
        timeout=60,
    )
    details["axiom_audit_rc"] = p_ax.returncode
    if p_ax.returncode != 0:
        failures.append(f"axiom_audit.py rc={p_ax.returncode}: {(p_ax.stderr or p_ax.stdout).strip()[:240]}")

    # 2. placeholder_audit.py --strict --format json
    p_ph = run_subprocess_safe(
        [sys.executable, str(repo_root / "tools/quality/placeholder_audit.py"), "--strict", "--format", "json", *file_args],
        cwd=repo_root,
        timeout=60,
    )
    details["placeholder_audit_rc"] = p_ph.returncode
    if p_ph.returncode != 0:
        failures.append(f"placeholder_audit.py --strict rc={p_ph.returncode}: {p_ph.stdout.strip()[:240]}")

    # 3. semantic_vacuity_gate.py --fail-on error
    p_vac = run_subprocess_safe(
        [sys.executable, str(repo_root / "tools/quality/semantic_vacuity_gate.py"), "--fail-on", "error", *file_args],
        cwd=repo_root,
        timeout=60,
    )
    details["semantic_vacuity_gate_rc"] = p_vac.returncode
    if p_vac.returncode != 0:
        failures.append(f"semantic_vacuity_gate.py rc={p_vac.returncode}: {p_vac.stdout.strip()[:240]}")

    # 4. detect_hollow_theorems.py --strict
    p_hol = run_subprocess_safe(
        [sys.executable, str(repo_root / "tools/quality/detect_hollow_theorems.py"), "--strict", *file_args],
        cwd=repo_root,
        timeout=60,
    )
    details["detect_hollow_theorems_rc"] = p_hol.returncode
    if p_hol.returncode != 0:
        failures.append(f"detect_hollow_theorems.py --strict rc={p_hol.returncode}: {p_hol.stdout.strip()[:240]}")

    # 5. opengauss_screener.py [--strict] --json (NEVER pass --quarantine!)
    og_cmd = [sys.executable, str(repo_root / "tools/infra/opengauss_screener.py"), "--json"]
    if strict_opengauss:
        og_cmd.append("--strict")
    og_cmd.extend(file_args)
    p_og = run_subprocess_safe(og_cmd, cwd=repo_root, timeout=60)
    details["opengauss_screener_rc"] = p_og.returncode
    if p_og.returncode != 0:
        failures.append(f"opengauss_screener.py rc={p_og.returncode}: {p_og.stdout.strip()[:240]}")

    # 6. aggregate_prop_constructors + parameterized Prop bundlers + comment/string-stripped native_decide & : True scan
    from tools.quality.proof_proxy_staged_gate import aggregate_prop_constructors

    for p in lean_files:
        src = p.read_text(encoding="utf-8")
        wrappers = aggregate_prop_constructors(src)
        if wrappers:
            failures.append(f"{p.name}: aggregate_prop_constructors flagged {wrappers}")
        param_wrappers = scan_parameterized_prop_bundlers(src)
        if param_wrappers:
            failures.append(f"{p.name}: parameterized Prop bundler flagged {param_wrappers}")
        lex_hits = scan_native_decide_and_vacuous_true(src)
        if lex_hits:
            failures.append(f"{p.name}: " + "; ".join(lex_hits))

    return len(failures) == 0, failures, details


def check_t1_lean_04_placeholder_and_vacuity(
    repo_root: Path,
    targets: list[ResolvedTarget],
    *,
    strict_live: bool,
) -> CheckOutcome:
    """T1-LEAN-04: Placeholder, vacuity, hollow theorem, opengauss screener, Prop wrapper & native_decide gates."""
    existing = [t.path for t in targets if t.exists]
    if not existing:
        return CheckOutcome("T1-LEAN-04", 1, "F9", "FAIL", "No existing target .lean files for placeholder/vacuity checks")
    ok, failures, details = run_static_placeholder_vacuity_suite(
        repo_root,
        existing,
        strict_opengauss=strict_live,
    )
    if not ok:
        return CheckOutcome(
            "T1-LEAN-04",
            1,
            "F9",
            "FAIL",
            f"Placeholder/vacuity gates failed ({len(failures)} issue(s)): " + "; ".join(failures[:4]),
            details,
        )
    return CheckOutcome(
        "T1-LEAN-04",
        1,
        "F9",
        "PASS",
        f"All 6 placeholder/vacuity/opengauss/Prop-wrapper/native_decide checks passed ({len(existing)} file(s), strict={strict_live})",
        details,
    )


def check_t1_lean_05_workspace_and_declarations(
    repo_root: Path,
    targets: list[ResolvedTarget],
    expected_decls_by_module: dict[str, list[str]] | None = None,
) -> CheckOutcome:
    """T1-LEAN-05: Lake workspace integrity, non-blocking lock inspection, and declaration presence."""
    from tools.build_lock import read_lock_metadata
    from tools.infra.build import _validate_lake_workspace_integrity

    ws_err = _validate_lake_workspace_integrity(repo_root)
    if ws_err is not None:
        return CheckOutcome("T1-LEAN-05", 1, "F9", "FAIL", f"Lake workspace integrity failed: {ws_err}")

    lock_meta = read_lock_metadata(DEFAULT_BUILD_LOCK_PATH)
    missing_decls: list[str] = []
    checked_decls = 0
    if expected_decls_by_module:
        by_mod = {t.module: t for t in targets if t.module and t.exists}
        for mod_key, decls in expected_decls_by_module.items():
            group_mods = [m.strip() for m in mod_key.split(",") if m.strip()]
            if not any(m in by_mod for m in group_mods):
                continue
            group_paths: list[Path] = []
            for m in group_mods:
                if m in by_mod:
                    group_paths.append(by_mod[m].path)
                else:
                    rel = module_to_rel_path(m)
                    if rel and (repo_root / rel).is_file():
                        group_paths.append(repo_root / rel)
            if len(group_paths) < len(group_mods):
                continue
            found: set[str] = set()
            for gp in group_paths:
                found.update(extract_non_opaque_lean_declarations(gp.read_text(encoding="utf-8")))
            for decl in decls:
                checked_decls += 1
                short = lean_short_name(decl)
                if short not in found and decl not in found:
                    missing_decls.append(f"{mod_key}.{short}")
    if missing_decls:
        return CheckOutcome(
            "T1-LEAN-05",
            1,
            "F9",
            "FAIL",
            f"Expected Lean declarations missing on disk: {missing_decls[:6]}",
            {"lock_metadata": lock_meta, "missing": missing_decls},
        )
    return CheckOutcome(
        "T1-LEAN-05",
        1,
        "F9",
        "PASS",
        f"Lake workspace integrity clean (lock_owner={lock_meta.get('owner') if lock_meta else 'none'}, decls_checked={checked_decls})",
        {"lock_metadata": lock_meta, "decls_checked": checked_decls},
    )


def run_tier1_lean_checks(
    repo_root: Path,
    targets: list[ResolvedTarget],
    *,
    strict_live: bool,
    expected_decls_by_module: dict[str, list[str]] | None = None,
) -> list[CheckOutcome]:
    return [
        check_t1_lean_01_copyright_header(targets),
        check_t1_lean_02_style_and_module_doc(repo_root, targets, strict_live=strict_live),
        check_t1_lean_03_theorem_lint(repo_root, targets, strict_live=strict_live),
        check_t1_lean_04_placeholder_and_vacuity(repo_root, targets, strict_live=strict_live),
        check_t1_lean_05_workspace_and_declarations(repo_root, targets, expected_decls_by_module),
    ]
