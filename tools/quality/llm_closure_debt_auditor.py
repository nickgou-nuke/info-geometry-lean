#!/usr/bin/env python3
from __future__ import annotations

"""
LLM closure-debt auditor (file-by-file Lean audit).

Design:
- Deterministic pre-scan on full file (proof holes, axioms, opaque, placeholders).
- LLM reasoning pass per file with strict JSON schema + line-referenced evidence.
- Per-file artifacts plus aggregate JSON/Markdown report.

Authority policy:
- This is an advisory lane only.
- Lean kernel/build remain proof authority.
"""

import argparse
import json
import re
import sys
import time
import urllib.error
import urllib.request
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.pathing import normalize_user_path, repo_root
else:
    from tools.pathing import normalize_user_path, repo_root

ROOT = repo_root()

HARD_PATTERNS = {
    "proof-hole": re.compile(r"\b(?:sorry|admit|sorryAx|admitAx)\b"),
    "axiom": re.compile(r"^\s*axiom\b", re.M),
    "postulate": re.compile(r"^\s*postulate\b", re.M),
}

SOFT_PATTERNS = {
    "opaque": re.compile(r"^\s*(?:noncomputable\s+)?(?:private\s+|protected\s+|local\s+)?opaque\b", re.M),
    "vacuous-prop": re.compile(
        r"(?ms)^\s*(?:theorem|lemma|def|abbrev)\s+[A-Za-z0-9_'.]+\b"
        r"[\s\S]{0,700}?:\s*Prop\s*:=\s*(?:--[^\n]*\n\s*)*(?:True|False)\b"
    ),
}

ADVISORY_PATTERNS = {
    "section-variable-assumption": re.compile(r"^\s*variable\s*\([^\n]*:[^\n]*\)\s*$", re.M),
    "placeholder-name": re.compile(r"\b(?:external|hyp|unproven|todo|stub|bridge)_[A-Za-z0-9_']*\b", re.I),
    "existential-packaging": re.compile(r"\b(?:Nonempty|Exists|Classical\.choose|choose_spec)\b|∃"),
}

LINE_DECL_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:partial\s+)?(?:private\s+|protected\s+|local\s+)?"
    r"(theorem|lemma|example|def|abbrev|structure|class|instance|axiom|postulate|inductive)\b"
)

JSON_FENCE_RE = re.compile(r"```(?:json)?\s*(\{[\s\S]*?\})\s*```", re.I)

SYSTEM_JSON_INSTRUCTION = "You are a strict JSON emitting Lean audit assistant."


@dataclass(frozen=True)
class Finding:
    source: str  # deterministic|llm
    severity: str  # hard|soft|advisory
    category: str
    line_start: int
    line_end: int
    snippet: str
    why: str
    fix_strategy: str
    confidence: float


@dataclass(frozen=True)
class FileAudit:
    path: str
    module: str
    status: str
    finding_count: int
    hard_count: int
    soft_count: int
    advisory_count: int
    findings: list[Finding]
    deterministic_counts: dict[str, int]
    llm_summary: str
    llm_raw_response: str


def rel(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def module_name(path: Path) -> str:
    try:
        rp = path.resolve().relative_to(ROOT / "lean").with_suffix("").as_posix()
        return rp.replace("/", ".")
    except ValueError:
        try:
            rp = path.resolve().relative_to(ROOT).with_suffix("").as_posix()
            return rp.replace("/", ".")
        except ValueError:
            return path.stem


def iter_lean_files(root: Path) -> list[Path]:
    if root.is_file():
        return [root] if root.suffix == ".lean" else []
    skip_dirs = {".git", ".lake", "lake-packages", ".cache", "node_modules", ".venv"}
    files = []
    for p in sorted(root.rglob("*.lean")):
        if any(part in skip_dirs for part in p.parts):
            continue
        if p.is_file():
            files.append(p)
    return files


def line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def safe_line(lines: list[str], idx: int) -> str:
    if 1 <= idx <= len(lines):
        return lines[idx - 1].rstrip()
    return ""


def deterministic_scan(text: str) -> tuple[list[Finding], dict[str, int], list[int]]:
    lines = text.splitlines()
    findings: list[Finding] = []
    counts: dict[str, int] = {}
    suspicious_lines: set[int] = set()

    def emit(pattern_name: str, severity: str, m: re.Match[str], why: str, fix: str) -> None:
        ln = line_of(text, m.start())
        snippet = safe_line(lines, ln)
        findings.append(
            Finding(
                source="deterministic",
                severity=severity,
                category=pattern_name,
                line_start=ln,
                line_end=ln,
                snippet=snippet,
                why=why,
                fix_strategy=fix,
                confidence=1.0,
            )
        )
        suspicious_lines.add(ln)

    for name, pat in HARD_PATTERNS.items():
        rows = list(pat.finditer(text))
        counts[name] = len(rows)
        for m in rows:
            if name == "proof-hole":
                why = "proof hole token allows unfinished proof to compile"
                fix = "replace with proved lemma or isolate in quarantined debt module"
            elif name == "axiom":
                why = "axiom introduces global trust assumption"
                fix = "replace with theorem parameter or proved bridge lemma"
            else:
                why = "postulate introduces global assumption"
                fix = "replace with local hypothesis or proved theorem"
            emit(name, "hard", m, why, fix)

    for name, pat in SOFT_PATTERNS.items():
        rows = list(pat.finditer(text))
        counts[name] = len(rows)
        for m in rows:
            if name == "opaque":
                why = "opaque hides implementation; behavior must be justified by lemmas"
                fix = "add/readback proved laws and eventual concrete implementation"
            else:
                why = "proposition appears vacuous"
                fix = "strengthen statement with meaningful mathematical content"
            emit(name, "soft", m, why, fix)

    for name, pat in ADVISORY_PATTERNS.items():
        rows = list(pat.finditer(text))
        counts[name] = len(rows)
        for m in rows:
            if name == "section-variable-assumption":
                why = "local hypothesis injection surface detected"
                fix = "track closure plan and replace with proved theorem when available"
            elif name == "placeholder-name":
                why = "placeholder-style naming suggests temporary bridge"
                fix = "document debt owner and retirement criterion"
            else:
                why = "existential packaging may hide constructive witness obligations"
                fix = "add explicit witness/readback lemmas"
            emit(name, "advisory", m, why, fix)

    # declaration headers are useful context points for excerpting
    for m in LINE_DECL_RE.finditer(text):
        suspicious_lines.add(line_of(text, m.start()))

    return findings, counts, sorted(suspicious_lines)


def build_excerpt(text: str, suspicious_lines: list[int], *, max_chars: int) -> str:
    lines = text.splitlines()
    n = len(lines)
    windows: list[tuple[int, int]] = []

    if not suspicious_lines:
        suspicious_lines = [1, min(n, 50), min(n, 100)]

    for ln in suspicious_lines:
        a = max(1, ln - 2)
        b = min(n, ln + 4)
        windows.append((a, b))

    # merge windows
    windows.sort()
    merged: list[tuple[int, int]] = []
    for a, b in windows:
        if not merged or a > merged[-1][1] + 1:
            merged.append((a, b))
        else:
            merged[-1] = (merged[-1][0], max(merged[-1][1], b))

    out: list[str] = []
    for a, b in merged:
        out.append(f"--- lines {a}-{b} ---")
        for i in range(a, b + 1):
            out.append(f"{i:5d}| {lines[i-1]}")
        out.append("")
        if sum(len(x) + 1 for x in out) > max_chars:
            out.append("[... excerpt truncated due to max_chars budget ...]")
            break

    excerpt = "\n".join(out)
    if len(excerpt) > max_chars:
        excerpt = excerpt[: max_chars - 64] + "\n[... hard-truncated ...]"
    return excerpt


def llm_prompt(path: str, module: str, deterministic_counts: dict[str, int], excerpt: str) -> str:
    return (
        "You are a Lean4 closure-debt auditor.\n"
        "Task: audit this Lean file excerpt for temporary trust constructs and unfinished closure debt.\n"
        "Rules:\n"
        "1) Do NOT invent declarations.\n"
        "2) Every finding must cite line_start/line_end from excerpt and include exact snippet text from excerpt.\n"
        "3) Distinguish severity: hard|soft|advisory.\n"
        "4) file_status must be one of clean|advisory|open_gap.\n"
        "5) If uncertain, lower confidence.\n"
        "6) Keep focus on: proof holes, axioms/postulates, opaque stubs without laws, placeholder assumptions, vacuous theorems, existential packaging without readback.\n"
        "Return JSON only with schema:\n"
        "{\n"
        "  \"file_status\": \"clean|advisory|open_gap\",\n"
        "  \"summary\": \"...\",\n"
        "  \"findings\": [\n"
        "    {\n"
        "      \"severity\": \"hard|soft|advisory\",\n"
        "      \"category\": \"string\",\n"
        "      \"line_start\": 1,\n"
        "      \"line_end\": 1,\n"
        "      \"snippet\": \"exact excerpt line(s)\",\n"
        "      \"why\": \"reason\",\n"
        "      \"fix_strategy\": \"suggested closure strategy\",\n"
        "      \"confidence\": 0.0\n"
        "    }\n"
        "  ]\n"
        "}\n\n"
        f"File: {path}\n"
        f"Module: {module}\n"
        f"Deterministic counts: {json.dumps(deterministic_counts, ensure_ascii=True)}\n\n"
        "Lean excerpt (line-numbered):\n"
        f"{excerpt}\n"
    )


def estimate_prompt_tokens(*, prompt: str) -> int:
    # Conservative rough estimate for mixed prose/code prompts.
    return max(1, (len(prompt) + 3) // 4)


def discover_model_context_limit(base_url: str, model: str, timeout: int) -> int | None:
    url = base_url.rstrip("/")
    if url.endswith("/chat/completions"):
        url = url[: -len("/chat/completions")]
    if not url.endswith("/v1/models"):
        if url.endswith("/v1"):
            url = url + "/models"
        else:
            url = url + "/v1/models"

    req = urllib.request.Request(url, headers={"Content-Type": "application/json"}, method="GET")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:  # noqa: S310 local endpoint
            data = json.loads(resp.read().decode("utf-8", errors="replace"))
    except Exception:
        return None

    rows = data.get("data", []) if isinstance(data, dict) else []
    if not isinstance(rows, list):
        return None

    targets = {model, model.removeprefix("/models/")}
    for row in rows:
        if not isinstance(row, dict):
            continue
        rid = str(row.get("id", ""))
        rid_norm = rid.removeprefix("/models/")
        if rid not in targets and rid_norm not in targets:
            continue
        candidates: list[Any] = [
            row.get("context_length"),
            row.get("max_context_length"),
            row.get("n_ctx"),
            row.get("max_seq_len"),
        ]
        for k in ("metadata", "extra", "details"):
            v = row.get(k)
            if isinstance(v, dict):
                candidates.extend([
                    v.get("context_length"),
                    v.get("max_context_length"),
                    v.get("n_ctx"),
                    v.get("max_seq_len"),
                ])
        for c in candidates:
            try:
                iv = int(c)
            except Exception:
                continue
            if iv > 0:
                return iv
    return None


def excerpt_budget_for_context_limit(
    *,
    model_context_limit: int,
    max_tokens: int,
    prompt_overhead_tokens: int,
    default_max_chars: int,
) -> int:
    # Keep a safety margin to avoid context_length_exceeded.
    safety = max(128, model_context_limit // 10)
    available_prompt_tokens = model_context_limit - max_tokens - prompt_overhead_tokens - safety
    if available_prompt_tokens <= 200:
        return 1200
    approx_chars = available_prompt_tokens * 4
    return max(1200, min(default_max_chars, approx_chars))


def post_chat(base_url: str, model: str, prompt: str, timeout: int, max_tokens: int) -> str:
    url = base_url.rstrip("/")
    if not url.endswith("/chat/completions"):
        if url.endswith("/v1"):
            url = url + "/chat/completions"
        else:
            url = url + "/v1/chat/completions"

    payload = {
        "model": model,
        "messages": [
            {"role": "system", "content": SYSTEM_JSON_INSTRUCTION},
            {"role": "user", "content": prompt},
        ],
        "temperature": 0.0,
        "max_tokens": max_tokens,
    }

    req = urllib.request.Request(
        url,
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    with urllib.request.urlopen(req, timeout=timeout) as resp:  # noqa: S310 local endpoint
        data = json.loads(resp.read().decode("utf-8", errors="replace"))
    return str(data["choices"][0]["message"]["content"])


def _extract_first_json_object(raw: str) -> dict[str, Any]:
    # Prefer fenced JSON blocks if present.
    fenced = JSON_FENCE_RE.search(raw)
    candidate = fenced.group(1) if fenced else raw

    decoder = json.JSONDecoder()
    for idx, ch in enumerate(candidate):
        if ch != "{":
            continue
        try:
            obj, _end = decoder.raw_decode(candidate[idx:])
        except json.JSONDecodeError:
            continue
        if isinstance(obj, dict):
            return obj
    raise ValueError("no JSON object found in LLM response")


def parse_llm_json(raw: str) -> dict[str, Any]:
    obj = _extract_first_json_object(raw)
    if not isinstance(obj, dict):
        raise ValueError("LLM JSON root is not an object")
    return obj


def normalize_llm_findings(obj: dict[str, Any]) -> tuple[str, str, list[Finding]]:
    status = str(obj.get("file_status", "advisory")).strip().lower()
    if status not in {"clean", "advisory", "open_gap"}:
        status = "advisory"
    summary = str(obj.get("summary", "")).strip()

    out: list[Finding] = []
    rows = obj.get("findings", [])
    if not isinstance(rows, list):
        rows = []

    for row in rows:
        if not isinstance(row, dict):
            continue
        try:
            sev = str(row.get("severity", "advisory")).strip().lower()
            if sev not in {"hard", "soft", "advisory"}:
                sev = "advisory"
            cat = str(row.get("category", "llm-finding")).strip() or "llm-finding"
            ls = int(row.get("line_start", 1) or 1)
            le = int(row.get("line_end", ls) or ls)
            snippet = str(row.get("snippet", "")).strip()
            why = str(row.get("why", "")).strip()
            fix = str(row.get("fix_strategy", "")).strip()
            try:
                conf = float(row.get("confidence", 0.5))
            except Exception:
                conf = 0.5
            conf = max(0.0, min(1.0, conf))
            out.append(
                Finding(
                    source="llm",
                    severity=sev,
                    category=cat,
                    line_start=max(1, ls),
                    line_end=max(1, le),
                    snippet=snippet,
                    why=why,
                    fix_strategy=fix,
                    confidence=conf,
                )
            )
        except Exception:
            # Ignore malformed LLM rows instead of failing whole-file parsing.
            continue

    return status, summary, out


def verify_llm_findings(findings: list[Finding], text: str) -> list[Finding]:
    lines = text.splitlines()
    verified: list[Finding] = []

    for f in findings:
        ls = max(1, min(f.line_start, len(lines) if lines else 1))
        le = max(ls, min(f.line_end, len(lines) if lines else ls))
        window = "\n".join(lines[ls - 1 : le]) if lines else ""

        snippet_ok = True
        if f.snippet:
            if f.snippet in window:
                snippet_ok = True
            else:
                # Allow a small neighborhood fallback for off-by-few-line references.
                near_a = max(1, ls - 3)
                near_b = min(len(lines), le + 3)
                near_window = "\n".join(lines[near_a - 1 : near_b]) if lines else ""
                snippet_ok = f.snippet in near_window

        # hard claims require lexical evidence.
        lexical_ok = True
        if f.severity == "hard":
            cat = f.category.lower()
            if "proof-hole" in cat:
                lexical_ok = bool(re.search(r"\b(?:sorry|admit|sorryAx|admitAx)\b", window + "\n" + f.snippet))
            elif "axiom" in cat:
                lexical_ok = bool(re.search(r"\baxiom\b", window + "\n" + f.snippet))
            elif "postulate" in cat:
                lexical_ok = bool(re.search(r"\bpostulate\b", window + "\n" + f.snippet))
            else:
                # Deny-by-default for unknown hard categories.
                lexical_ok = False

        if snippet_ok and lexical_ok:
            verified.append(
                Finding(
                    source=f.source,
                    severity=f.severity,
                    category=f.category,
                    line_start=ls,
                    line_end=le,
                    snippet=f.snippet,
                    why=f.why,
                    fix_strategy=f.fix_strategy,
                    confidence=f.confidence,
                )
            )
            continue

        # downgrade unverifiable claims to advisory evidence-mismatch
        verified.append(
            Finding(
                source="llm",
                severity="advisory",
                category="llm-evidence-mismatch",
                line_start=ls,
                line_end=le,
                snippet=f.snippet,
                why=f"LLM claim could not be verified against source excerpt/category lexical checks: {f.category}",
                fix_strategy="review file manually or rerun with larger excerpt",
                confidence=0.0,
            )
        )

    return verified


def merge_status(findings: list[Finding], llm_status: str) -> str:
    if any(f.severity == "hard" for f in findings):
        return "open_gap"
    if any(f.severity in {"soft", "advisory"} for f in findings):
        return "advisory"
    return llm_status if llm_status in {"clean", "advisory", "open_gap"} else "clean"


def audit_file(
    path: Path,
    *,
    base_url: str,
    model: str,
    timeout: int,
    max_tokens: int,
    max_chars: int,
    retries: int,
    model_context_limit: int | None = None,
    print_budget: bool = False,
) -> FileAudit:
    text = path.read_text(encoding="utf-8")
    det_findings, det_counts, suspicious_lines = deterministic_scan(text)

    raw = ""
    llm_status = "advisory"
    llm_summary = ""
    llm_findings: list[Finding] = []
    current_max_chars = max_chars

    if model_context_limit:
        overhead_prompt = llm_prompt(
            rel(path),
            module_name(path),
            det_counts,
            "--- lines 1-1 ---\n    1| x\n",
        )
        overhead_tokens = estimate_prompt_tokens(prompt=overhead_prompt) + estimate_prompt_tokens(
            prompt=SYSTEM_JSON_INSTRUCTION
        )
        current_max_chars = excerpt_budget_for_context_limit(
            model_context_limit=model_context_limit,
            max_tokens=max_tokens,
            prompt_overhead_tokens=overhead_tokens,
            default_max_chars=max_chars,
        )

    if print_budget:
        init_excerpt = build_excerpt(text, suspicious_lines, max_chars=current_max_chars)
        init_prompt = llm_prompt(rel(path), module_name(path), det_counts, init_excerpt)
        init_prompt_tokens = estimate_prompt_tokens(prompt=init_prompt) + estimate_prompt_tokens(
            prompt=SYSTEM_JSON_INSTRUCTION
        )
        print(
            "[llm-audit-budget] "
            f"file={rel(path)} "
            f"context_limit={model_context_limit} "
            f"max_tokens={max_tokens} "
            f"excerpt_chars={current_max_chars} "
            f"est_prompt_tokens={init_prompt_tokens}"
        )

    for attempt in range(1, retries + 1):
        try:
            excerpt = build_excerpt(text, suspicious_lines, max_chars=current_max_chars)
            prompt = llm_prompt(rel(path), module_name(path), det_counts, excerpt)
            raw = post_chat(base_url, model, prompt, timeout=timeout, max_tokens=max_tokens)
            parsed = parse_llm_json(raw)
            llm_status, llm_summary, llm_findings = normalize_llm_findings(parsed)
            llm_findings = verify_llm_findings(llm_findings, text)
            break
        except Exception as ex:  # noqa: BLE001
            raw = f"llm_error_attempt_{attempt}: {ex}"
            msg = str(ex).lower()
            if any(k in msg for k in ["context length", "maximum context", "context_length_exceeded", "too many tokens"]):
                current_max_chars = max(1200, current_max_chars // 2)
            if attempt == retries:
                llm_findings = [
                    Finding(
                        source="llm",
                        severity="advisory",
                        category="llm-audit-failure",
                        line_start=1,
                        line_end=1,
                        snippet="",
                        why=str(ex),
                        fix_strategy="rerun with larger timeout or smaller excerpt",
                        confidence=0.0,
                    )
                ]
                llm_summary = "LLM audit failed; deterministic findings only"
            else:
                time.sleep(min(2 * attempt, 6))

    findings = det_findings + llm_findings

    # de-dup
    dedup: dict[tuple[str, str, str, int, int, str], Finding] = {}
    for f in findings:
        key = (f.source, f.severity, f.category, f.line_start, f.line_end, f.snippet)
        dedup[key] = f
    findings = sorted(dedup.values(), key=lambda x: (x.line_start, x.severity, x.source, x.category))

    hard = sum(1 for f in findings if f.severity == "hard")
    soft = sum(1 for f in findings if f.severity == "soft")
    advisory = sum(1 for f in findings if f.severity == "advisory")

    return FileAudit(
        path=rel(path),
        module=module_name(path),
        status=merge_status(findings, llm_status),
        finding_count=len(findings),
        hard_count=hard,
        soft_count=soft,
        advisory_count=advisory,
        findings=findings,
        deterministic_counts=det_counts,
        llm_summary=llm_summary,
        llm_raw_response=raw,
    )


def build_payload(
    root: Path,
    reports: list[FileAudit],
    *,
    model: str,
    base_url: str,
    model_context_limit: int | None,
) -> dict[str, Any]:
    hard = sum(r.hard_count for r in reports)
    soft = sum(r.soft_count for r in reports)
    advisory = sum(r.advisory_count for r in reports)
    status_counts = {
        "clean": sum(1 for r in reports if r.status == "clean"),
        "advisory": sum(1 for r in reports if r.status == "advisory"),
        "open_gap": sum(1 for r in reports if r.status == "open_gap"),
    }
    top = sorted(reports, key=lambda r: (-r.hard_count, -r.soft_count, -r.advisory_count, r.path))[:50]

    return {
        "schema": "info_geometry.llm_closure_debt_audit.v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "root": rel(root),
        "model": model,
        "endpoint": base_url,
        "model_context_limit": model_context_limit,
        "summary": {
            "file_count": len(reports),
            "status_counts": status_counts,
            "finding_count": hard + soft + advisory,
            "hard_count": hard,
            "soft_count": soft,
            "advisory_count": advisory,
        },
        "top_debt_files": [asdict(x) for x in top],
        "files": [{**asdict(r), "findings": [asdict(f) for f in r.findings]} for r in reports],
    }


def to_markdown(payload: dict[str, Any]) -> str:
    s = payload["summary"]
    lines = [
        "# LLM Closure Debt Audit",
        "",
        f"Generated: `{payload['generated_at']}`",
        f"Root: `{payload['root']}`",
        f"Endpoint: `{payload['endpoint']}`",
        f"Model: `{payload['model']}`",
        f"Model context limit: `{payload.get('model_context_limit')}`",
        "",
        "## Summary",
        f"- Files scanned: **{s['file_count']}**",
        f"- Findings: **{s['finding_count']}**",
        f"- Hard: **{s['hard_count']}**",
        f"- Soft: **{s['soft_count']}**",
        f"- Advisory: **{s['advisory_count']}**",
        (
            "- Status counts: "
            f"clean={s['status_counts']['clean']}, "
            f"advisory={s['status_counts']['advisory']}, "
            f"open_gap={s['status_counts']['open_gap']}"
        ),
        "",
        "## Per-file overview",
        "",
        "| file | status | hard | soft | advisory | findings |",
        "| --- | --- | ---: | ---: | ---: | ---: |",
    ]
    for r in payload["files"]:
        lines.append(
            f"| `{r['path']}` | `{r['status']}` | {r['hard_count']} | {r['soft_count']} | {r['advisory_count']} | {r['finding_count']} |"
        )

    lines.append("")
    lines.append("## Detailed findings")
    lines.append("")
    for r in payload["files"]:
        lines.append(f"### `{r['path']}`")
        lines.append(f"- module: `{r['module']}`")
        lines.append(f"- status: `{r['status']}`")
        lines.append(f"- llm summary: {r['llm_summary']}")
        if not r["findings"]:
            lines.append("- findings: none")
            lines.append("")
            continue
        for f in r["findings"]:
            lines.append(
                f"- L{f['line_start']}-{f['line_end']} [{f['severity']}] ({f['source']}) `{f['category']}`: {f['why']}"
            )
            if f["fix_strategy"]:
                lines.append(f"  - fix: {f['fix_strategy']}")
            if f["snippet"]:
                lines.append(f"  - snippet: `{f['snippet']}`")
            lines.append(f"  - confidence: {f['confidence']:.2f}")
        lines.append("")

    return "\n".join(lines) + "\n"


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="LLM file-by-file closure debt audit for Lean code")
    p.add_argument("--root", default="lean/InfoGeometry", help="Root directory or .lean file")
    p.add_argument("--endpoint", default="http://127.0.0.1:18889/v1", help="Local OpenAI-compatible endpoint")
    p.add_argument("--model", default="leanstral-gguf", help="Model id")
    p.add_argument("--timeout", type=int, default=120)
    p.add_argument("--max-tokens", type=int, default=900)
    p.add_argument("--max-chars", type=int, default=12000, help="Max excerpt chars sent per file")
    p.add_argument("--max-context-tokens", type=int, default=0, help="Override model context window (0 = auto-detect)")
    p.add_argument("--retries", type=int, default=2)
    p.add_argument("--limit", type=int, default=0, help="Limit file count for smoke runs (0 = all)")
    p.add_argument("--json-out", default="reports/audit/llm-closure-debt-audit.json")
    p.add_argument("--md-out", default="reports/audit/llm-closure-debt-audit.md")
    p.add_argument("--per-file-dir", default="reports/audit/llm-file-reports", help="Write one JSON per file")
    p.add_argument("--print-progress", action="store_true")
    p.add_argument("--print-budget", action="store_true", help="Print per-file computed excerpt/token budget")
    p.add_argument("--strict", action="store_true", help="Exit nonzero if any hard finding")
    return p.parse_args()


def main() -> int:
    args = parse_args()
    root = normalize_user_path(args.root, ROOT / "lean" / "InfoGeometry")
    files = iter_lean_files(root)
    if args.limit > 0:
        files = files[: args.limit]

    reports: list[FileAudit] = []
    per_file_dir = normalize_user_path(args.per_file_dir, ROOT / "reports" / "audit" / "llm-file-reports")
    per_file_dir.mkdir(parents=True, exist_ok=True)

    model_context_limit = args.max_context_tokens if args.max_context_tokens > 0 else discover_model_context_limit(
        args.endpoint, args.model, args.timeout
    )

    total = len(files)
    for idx, f in enumerate(files, start=1):
        if args.print_progress:
            print(f"[llm-audit] {idx}/{total} {rel(f)}")
        try:
            rep = audit_file(
                f,
                base_url=args.endpoint,
                model=args.model,
                timeout=args.timeout,
                max_tokens=args.max_tokens,
                max_chars=args.max_chars,
                retries=args.retries,
                model_context_limit=model_context_limit,
                print_budget=args.print_budget,
            )
        except urllib.error.URLError as ex:
            raise SystemExit(f"[llm-audit] endpoint failure {args.endpoint}: {ex}") from ex

        reports.append(rep)

        file_out = per_file_dir / (rep.path.replace("/", "__") + ".json")
        file_out.parent.mkdir(parents=True, exist_ok=True)
        file_out.write_text(json.dumps({**asdict(rep), "findings": [asdict(x) for x in rep.findings]}, indent=2), encoding="utf-8")

    reports.sort(key=lambda r: r.path)
    payload = build_payload(
        root,
        reports,
        model=args.model,
        base_url=args.endpoint,
        model_context_limit=model_context_limit,
    )

    json_out = normalize_user_path(args.json_out, ROOT / "reports" / "audit" / "llm-closure-debt-audit.json")
    md_out = normalize_user_path(args.md_out, ROOT / "reports" / "audit" / "llm-closure-debt-audit.md")
    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    md_out.write_text(to_markdown(payload), encoding="utf-8")

    s = payload["summary"]
    print(
        f"[llm-audit] files={s['file_count']} findings={s['finding_count']} "
        f"hard={s['hard_count']} soft={s['soft_count']} advisory={s['advisory_count']}"
    )
    print(f"[llm-audit] model_context_limit={model_context_limit}")
    print(f"[llm-audit] json={json_out}")
    print(f"[llm-audit] md={md_out}")

    if not args.strict:
        return 0
    return 1 if s["hard_count"] > 0 else 0


if __name__ == "__main__":
    raise SystemExit(main())
