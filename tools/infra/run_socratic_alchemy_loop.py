#!/usr/bin/env python3
"""Run a guarded Gemini -> Codex -> guarded Gemini Socratic alchemy loop.

Features:
- N conceptual Gemini/Codex rounds
- Codex Lean4 hypothesis generation
- N compile/repair cycles
- optional lean_interact_wrapper proof-state probe for repair guidance
- packetization into autonomous_math evidence format
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[2]))

from tools.infra.autonomous_math.memory_ingest import ingest  # type: ignore
from tools.infra.autonomous_math.socratic_packet import build_packet_from_loop  # type: ignore


_THEOREM_BLOCK_RE = re.compile(
    r"(?P<doc>(?:\s*/-[-!].*?-\/\s*)*)^\s*(?P<kind>theorem|lemma|axiom)\s+(?P<name>[A-Za-z0-9_'.]+)(?P<body>.*?)(?=\n\s*(?:theorem|lemma|axiom|def|structure|class|namespace|end)\b|\Z)",
    re.S | re.M,
)


def run(cmd: list[str], cwd: Path, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    merged_env = None
    if env is not None:
        merged_env = dict(__import__("os").environ)
        merged_env.update(env)
    return subprocess.run(cmd, cwd=cwd, text=True, capture_output=True, check=False, env=merged_env)


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def strip_code_fences(text: str) -> str:
    lines = text.strip().splitlines()
    if lines and lines[0].strip().startswith("```"):
        lines = lines[1:]
    if lines and lines[-1].strip().startswith("```"):
        lines = lines[:-1]
    return "\n".join(lines).strip()


def compile_lean(repo_root: Path, lean_file: Path) -> subprocess.CompletedProcess[str]:
    return run(["lake", "env", "lean", str(lean_file)], repo_root)


def module_name_from_file(module_root: Path, lean_file: Path) -> str:
    rel = lean_file.resolve().relative_to(module_root.resolve())
    return ".".join(rel.with_suffix("").parts)


def extract_compiled_decl_names(repo_root: Path, module_root: Path, lean_file: Path, timeout: int = 120) -> dict[str, object]:
    module_name = module_name_from_file(module_root, lean_file)
    olean_file = lean_file.with_suffix(".olean")
    build_proc = run(
        ["lake", "env", "lean", "--root", str(module_root), str(lean_file), "-o", str(olean_file)],
        repo_root,
        env={"LEAN_PATH": f"{module_root}:{__import__('os').environ.get('LEAN_PATH', '')}"},
    )
    result: dict[str, object] = {
        "module_name": module_name,
        "olean_file": str(olean_file),
        "build_returncode": build_proc.returncode,
        "build_stdout": build_proc.stdout or "",
        "build_stderr": build_proc.stderr or "",
        "decl_names": [],
    }
    if build_proc.returncode != 0:
        return result
    probe_file = module_root / f".__compiled_decl_probe__{lean_file.stem}.lean"
    probe_file.write_text(
        "import Lean\n"
        "open Lean in\n"
        "#eval do\n"
        f"  let env <- importModules #[{{ module := `{module_name} }}] {{}}\n"
        f"  let some targetIdx := env.getModuleIdx? `{module_name} |\n"
        f"    IO.println \"ERROR:NO_MODULE_IDX:{module_name}\"\n"
        "    return\n"
        "  for (entry : Name × ConstantInfo) in env.constants.toList do\n"
        "    let declName := entry.fst\n"
        "    if env.getModuleIdxFor? declName == some targetIdx then\n"
        "      IO.println s!\"DECL:{declName}\"\n",
        encoding="utf-8",
    )
    probe_proc = run(
        ["lake", "env", "lean", str(probe_file)],
        repo_root,
        env={"LEAN_PATH": f"{module_root}:{__import__('os').environ.get('LEAN_PATH', '')}"},
    )
    decl_names: list[str] = []
    for line in (probe_proc.stdout or "").splitlines():
        if line.startswith("DECL:"):
            name = line[len("DECL:") :].strip()
            if name and name not in decl_names:
                decl_names.append(name)
    result.update(
        {
            "probe_file": str(probe_file),
            "probe_returncode": probe_proc.returncode,
            "probe_stdout": probe_proc.stdout or "",
            "probe_stderr": probe_proc.stderr or "",
            "decl_names": decl_names,
        }
    )
    return result


def extract_first_theorem_surface(lean_code: str) -> dict[str, str]:
    text = strip_code_fences(lean_code)
    match = _THEOREM_BLOCK_RE.search(text)
    if not match:
        return {"kind": "", "name": "", "goal": "", "tactic": "", "doc": ""}
    body = match.group("body") or ""
    goal = ""
    tactic = ""
    if ":=" in body:
        before, after = body.split(":=", 1)
        goal = before.strip().lstrip(": ").rstrip(":")
        after = after.strip()
        if after.startswith("by"):
            tactic = after[2:].strip()
        else:
            tactic = after.strip()
    else:
        goal = body.strip().lstrip(": ").rstrip(":")
    return {
        "kind": match.group("kind") or "",
        "name": match.group("name") or "",
        "goal": goal,
        "tactic": tactic,
        "doc": (match.group("doc") or "").strip(),
    }


def _referenced_identifiers(text: str) -> set[str]:
    tokens = {tok for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", text or "") if tok}
    expanded = set(tokens)
    for token in list(tokens):
        if "." in token:
            expanded.update(part for part in token.split(".") if part)
    return expanded


def _sanitize_where_block(block: str) -> str:
    lines = block.splitlines()
    if not lines or " where" not in lines[0]:
        return block
    out: list[str] = []
    skip_indent: int | None = None
    field_re = re.compile(r"^(\s+)([A-Za-z0-9_'.]+(?:\s+[A-Za-z0-9_'.]+)*)\s*:=\s*by\s*$")
    for line in lines:
        stripped = line.strip()
        indent = len(line) - len(line.lstrip())
        if skip_indent is not None:
            if stripped and indent <= skip_indent and ":=" in stripped:
                skip_indent = None
            else:
                continue
        m = field_re.match(line)
        if m:
            base_indent = len(m.group(1))
            out.append(line)
            out.append(" " * (base_indent + 2) + "sorry")
            skip_indent = base_indent
            continue
        out.append(line)
    return "\n".join(out)


def _extract_named_decl_blocks(context: str) -> list[dict[str, str]]:
    chunks = re.split(r"\n\s*\n", context)
    blocks: list[dict[str, str]] = []
    # Updated to capture docstrings before the declaration
    decl_re = re.compile(r"(?P<doc>(?:\s*/-[-!].*?-\/\s*)*)^(?:@[A-Za-z0-9_\[\]().,'`\s-]+\n)*(?P<head>(?:noncomputable\s+)?(?:def|abbrev|opaque|structure|class|inductive)\s+(?P<name>[A-Za-z0-9_'.]+))", re.M | re.S)
    for idx, chunk in enumerate(chunks):
        text = chunk.strip()
        if not text:
            continue
        first_line = next((line.strip() for line in text.splitlines() if line.strip()), "")
        if first_line.startswith("instance ") or first_line == "instance":
            blocks.append({"index": str(idx), "kind": "instance", "name": f"__instance_{idx}", "text": text})
            continue
        m = decl_re.search(text)
        if not m:
            continue
        head = m.group("head") or ""
        kind = head.split()[0]
        if kind == "noncomputable":
            kind = head.split()[1]
        name = m.group("name") or ""
        # The regex match m.group(0) already includes the captured docstring if it was part of the chunk
        blocks.append({"index": str(idx), "kind": kind, "name": name, "text": text})
    return blocks


def strip_lean_comments(text: str, keep_docstrings: bool = False) -> str:
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    is_doc = False
    in_string = False
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if block_depth > 0:
            if ch == '/' and nxt == '-':
                block_depth += 1
                if is_doc:
                    out.extend(['/', '-'])
                i += 2
                continue
            if ch == '-' and nxt == '/':
                block_depth -= 1
                if is_doc:
                    out.extend(['-', '/'])
                if block_depth == 0:
                    is_doc = False
                i += 2
                continue
            if is_doc:
                out.append(ch)
            elif ch == '\n':
                out.append('\n')
            i += 1
            continue
        if in_string:
            out.append(ch)
            if ch == '"' and text[i - 1] != '\\':
                in_string = False
            i += 1
            continue
        if ch == '"':
            in_string = True
            out.append(ch)
            i += 1
            continue
        if ch == '/' and nxt == '-':
            block_depth = 1
            nnxt = text[i + 2] if i + 2 < n else ""
            if keep_docstrings and (nnxt == '-' or nnxt == '!'):
                is_doc = True
                out.extend(['/', '-'])
            i += 2
            continue
        if ch == '-' and nxt == '-':
            while i < n and text[i] != '\n':
                i += 1
            continue
        out.append(ch)
        i += 1
    return ''.join(out)


def extract_probe_context(lean_code: str) -> str:
    text = strip_code_fences(lean_code)
    match = _THEOREM_BLOCK_RE.search(text)
    if not match:
        return ""
    prefix = text[: match.start()].rstrip()
    if not prefix:
        return ""
    # Structurally preserve docstrings in minimal probe context as requested.
    prefix = strip_lean_comments(prefix, keep_docstrings=True)
    chunks = [chunk.strip() for chunk in re.split(r"\n\s*\n", prefix) if chunk.strip()]
    header_re = re.compile(r"^(import\s+|open\s+|namespace\s+|section\b|noncomputable\s+section\b|noncomputable\s+theory\b|attribute\s+|local\s+attribute\s+|set_option\s+|end\b|variable\s+|universe\s+)")
    surface = extract_first_theorem_surface(lean_code)
    needed = _referenced_identifiers(surface.get("goal", "") + "\n" + surface.get("tactic", "") + "\n" + surface.get("name", ""))
    selected_names: set[str] = set()
    blocks = _extract_named_decl_blocks(prefix)
    changed = True
    while changed:
        changed = False
        for block in blocks:
            name = block.get("name", "")
            kind = block.get("kind", "")
            if not name or name in selected_names:
                continue
            if kind == "instance":
                selected_names.add(name)
                continue
            short = name.split(".")[-1]
            if name not in needed and short not in needed:
                continue
            selected_names.add(name)
            block_tokens = _referenced_identifiers(_sanitize_where_block(block.get("text", "")))
            if not block_tokens.issubset(needed):
                needed.update(block_tokens)
                changed = True
    selected_indices = {int(block.get("index", "-1")) for block in blocks if block.get("name", "") in selected_names}
    combined: list[str] = []
    for idx, chunk in enumerate(chunks):
        if idx in selected_indices:
            block = next((row for row in blocks if int(row.get("index", "-1")) == idx), None)
            if block is not None:
                combined.append(_sanitize_where_block(block.get("text", "")))
            continue
        first_line = next((line.strip() for line in chunk.splitlines() if line.strip()), "")
        if header_re.match(first_line):
            combined.append(chunk)
    context = "\n\n".join(part for part in combined if part.strip())
    if "Real.log" in context and "noncomputable section" not in context:
        if context.startswith("import "):
            lines = context.splitlines()
            insert_at = 0
            while insert_at < len(lines) and lines[insert_at].startswith("import "):
                insert_at += 1
            lines[insert_at:insert_at] = ["", "noncomputable section", ""]
            context = "\n".join(lines)
        else:
            context = "noncomputable section\n\n" + context
    return context


def normalize_probe_goal(goal_stmt: str) -> str:
    goal = " ".join(goal_stmt.strip().split())
    if not goal:
        return ""
    if not goal.startswith(("(", "{", "[", "⦃")):
        return goal
    parts = goal.rsplit(":", 1)
    if len(parts) != 2:
        return goal
    binders, conclusion = parts[0].strip(), parts[1].strip()
    if not conclusion:
        return goal
    return f"∀ {binders}, {conclusion}"


def normalize_probe_tactic(goal_stmt: str, tactic: str) -> str:
    cleaned_lines = [
        line.strip()
        for line in tactic.strip().splitlines()
        if line.strip() and not line.strip().startswith("@[")
    ]
    cleaned = "\n".join(cleaned_lines)
    if not cleaned:
        return cleaned
    normalized_goal = normalize_probe_goal(goal_stmt)
    needs_intro = normalized_goal.startswith("∀ ") and normalized_goal != " ".join(goal_stmt.strip().split())
    if not needs_intro:
        normalized = cleaned
    else:
        first_line = next((line.strip() for line in cleaned.splitlines() if line.strip()), "")
        normalized = cleaned if first_line.startswith(("intro", "intros", "rintro", "repeat intro")) else "repeat intro\n" + cleaned
    tactic_lines = [line for line in normalized.splitlines() if line.strip()]
    first_line = tactic_lines[0].strip() if tactic_lines else ""
    known_tactic_prefixes = (
        "intro", "intros", "rintro", "repeat intro", "exact", "refine", "apply", "rw", "simp", "simpa", "ring",
        "linarith", "omega", "aesop", "constructor", "cases", "induction", "unfold", "change", "have", "let", "show",
        "calc", "conv", "nth_rewrite", "refl", "rfl", "trivial", "assumption", "tauto", "abel",
    )
    if first_line and not first_line.startswith(known_tactic_prefixes):
        tactic_lines[0] = f"exact {first_line}"
        normalized = "\n".join(tactic_lines)
    return normalized


def probe_goal(
    repo_root: Path,
    goal_stmt: str,
    *,
    context: str = "",
    imports: list[str] | None = None,
    timeout: int = 60,
) -> dict[str, object] | None:
    if not goal_stmt.strip():
        return None
    wrapper = repo_root / "tools/infra/lean_interact_wrapper.py"
    if not wrapper.exists():
        return None
    normalized_goal = normalize_probe_goal(goal_stmt)
    cmd = ["python3", str(wrapper), "--goal", normalized_goal, "--timeout", str(timeout)]
    for item in imports or []:
        cmd.extend(["--import", item])
    if context.strip():
        cmd.extend(["--context", context])
    proc = run(cmd, repo_root)
    out = (proc.stdout or "").strip()
    if not out:
        return {"returncode": proc.returncode, "raw": out, "stderr": proc.stderr or ""}
    try:
        payload = json.loads(out)
    except Exception:
        payload = {"raw": out, "stderr": proc.stderr or "", "returncode": proc.returncode}
    if isinstance(payload, dict):
        payload["normalized_goal"] = normalized_goal
    return payload


def probe_tactic(
    repo_root: Path,
    goal_stmt: str,
    tactic: str,
    *,
    context: str = "",
    imports: list[str] | None = None,
    timeout: int = 60,
) -> dict[str, object] | None:
    if not goal_stmt.strip() or not tactic.strip():
        return None
    wrapper = repo_root / "tools/infra/lean_interact_wrapper.py"
    if not wrapper.exists():
        return None
    normalized_goal = normalize_probe_goal(goal_stmt)
    normalized_tactic = normalize_probe_tactic(goal_stmt, tactic)
    cmd = ["python3", str(wrapper), "--tactic", normalized_goal, normalized_tactic, "--timeout", str(timeout)]
    for item in imports or []:
        cmd.extend(["--import", item])
    if context.strip():
        cmd.extend(["--context", context])
    proc = run(cmd, repo_root)
    out = (proc.stdout or "").strip()
    if not out:
        return {"returncode": proc.returncode, "raw": out, "stderr": proc.stderr or ""}
    try:
        payload = json.loads(out)
    except Exception:
        payload = {"raw": out, "stderr": proc.stderr or "", "returncode": proc.returncode}
    if isinstance(payload, dict):
        payload["normalized_goal"] = normalized_goal
        payload["normalized_tactic"] = normalized_tactic
    return payload


def check_gemini_guard(repo_root: Path) -> dict[str, object]:
    proc = run(["./tools/infra/run_gemini_guarded.sh", "--check", "--loop-burst"], repo_root)
    raw = (proc.stdout or "").strip()
    if raw:
        try:
            payload = json.loads(raw)
            if isinstance(payload, dict):
                return payload
        except Exception:
            pass
    return {
        "allowed": proc.returncode == 0,
        "reason": ((proc.stderr or "") + "\n" + (proc.stdout or "")).strip(),
        "wait_seconds": 0,
        "raw": raw,
    }


def is_daily_limit_guard(payload: dict[str, object]) -> bool:
    reason = str(payload.get("reason", "")).lower()
    return "daily gemini cli limit reached" in reason


def _extract_distilled_concept(text: str) -> str:
    marker = "DISTILLED CONCEPT"
    idx = text.find(marker)
    if idx == -1:
        return text.strip()
    rest = text[idx + len(marker) :]
    rest = rest.lstrip(" :\n\t")
    lines: list[str] = []
    for line in rest.splitlines():
        if line.startswith("## ") and lines:
            break
        lines.append(line)
    extracted = "\n".join(lines).strip()
    return extracted or text.strip()


def _latest_matching_file(root: Path, patterns: list[str]) -> Path | None:
    matches: list[Path] = []
    for pattern in patterns:
        matches.extend(root.glob(pattern))
    files = [p for p in matches if p.is_file()]
    if not files:
        return None
    files.sort(key=lambda p: p.stat().st_mtime, reverse=True)
    return files[0]


def load_concept_from_packet(path: Path) -> dict[str, object] | None:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None
    if not isinstance(payload, dict):
        return None
    invariants = payload.get("candidate_invariants", [])
    evidence = payload.get("evidence", [])
    targets = payload.get("formalization_targets", [])
    concept = ""
    if isinstance(invariants, list):
        for item in reversed(invariants):
            text = str(item).strip()
            if text:
                concept = text
                break
    if not concept and isinstance(evidence, list):
        for item in reversed(evidence):
            if isinstance(item, dict):
                text = str(item.get("claim", "")).strip()
                if text:
                    concept = text
                    break
    if not concept:
        concept = str(payload.get("research_goal", "")).strip()
    if not concept:
        return None
    target_names: list[str] = []
    if isinstance(targets, list):
        for item in targets:
            if isinstance(item, dict):
                name = str(item.get("name", "")).strip()
                if name:
                    target_names.append(name)
    summary = concept
    if target_names:
        summary = f"{concept}\n\nRecovered formalization targets from packet:\n- " + "\n- ".join(target_names[:12])
    return {
        "mode": "packet",
        "path": str(path),
        "concept": summary,
        "target_names": target_names,
    }


def load_concept_from_transcript(path: Path) -> dict[str, object] | None:
    text = path.read_text(encoding="utf-8")
    matches = list(re.finditer(r"^## Gemini round \d+\n", text, re.M))
    if matches:
        start = matches[-1].end()
        end = len(text)
        trailing = re.search(r"^## ", text[start:], re.M)
        if trailing:
            end = start + trailing.start()
        block = text[start:end].strip()
    else:
        block = text.strip()
    concept = _extract_distilled_concept(block)
    if not concept:
        return None
    return {
        "mode": "transcript",
        "path": str(path),
        "concept": concept,
        "target_names": [],
    }


def resolve_gemini_limit_fallback(
    repo_root: Path,
    *,
    packet_dir: Path,
    transcript_dir: Path,
    prompt_file: Path,
    run_name: str,
    fallback_packet_arg: str,
    fallback_transcript_arg: str,
) -> dict[str, object] | None:
    packet_candidates: list[Path] = []
    transcript_candidates: list[Path] = []
    if fallback_packet_arg:
        packet_candidates.append(Path(fallback_packet_arg).expanduser())
    if fallback_transcript_arg:
        transcript_candidates.append(Path(fallback_transcript_arg).expanduser())
    prompt_stem = prompt_file.stem
    auto_packet = _latest_matching_file(
        packet_dir,
        [
            f"{run_name}-*.json",
            f"*{prompt_stem}*.json",
            "*.json",
        ],
    )
    auto_transcript = _latest_matching_file(
        transcript_dir,
        [
            f"{run_name}-*.md",
            f"*{prompt_stem}*.md",
            "*.md",
        ],
    )
    if auto_packet is not None:
        packet_candidates.append(auto_packet)
    if auto_transcript is not None:
        transcript_candidates.append(auto_transcript)

    for raw in packet_candidates:
        candidate = raw if raw.is_absolute() else (repo_root / raw).resolve()
        if not candidate.exists():
            continue
        loaded = load_concept_from_packet(candidate)
        if loaded is not None:
            return loaded
    for raw in transcript_candidates:
        candidate = raw if raw.is_absolute() else (repo_root / raw).resolve()
        if not candidate.exists():
            continue
        loaded = load_concept_from_transcript(candidate)
        if loaded is not None:
            return loaded
    return None


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--prompt-file", required=True, help="Path to the original hypothesis prompt.")
    p.add_argument("--run-name", default="socratic-loop")
    p.add_argument("--reason", default="socratic alchemy loop")
    p.add_argument("--output-dir", default="docs/future_pass/dialogues/runs")
    p.add_argument("--artifacts-dir", default="artifacts/socratic_loops")
    p.add_argument("--packet-out-dir", default="reports/research/socratic_packets")
    p.add_argument("--memory-log", default="reports/research/autonomous_memory.jsonl")
    p.add_argument("--codex-extra", default="")
    p.add_argument("--lean-import", action="append", default=["Mathlib"], help="Lean imports for generated hypothesis file.")
    p.add_argument("--lean-preamble", default="")
    p.add_argument("--concept-rounds", type=int, default=2)
    p.add_argument("--repair-rounds", type=int, default=1)
    p.add_argument("--lean-timeout", type=int, default=120)
    p.add_argument("--skip-lean-interact", action="store_true")
    p.add_argument("--fallback-packet", default="", help="Optional Socratic packet to reuse when Gemini daily limit blocks a fresh conceptual round.")
    p.add_argument("--fallback-transcript", default="", help="Optional prior transcript to reuse when Gemini daily limit blocks a fresh conceptual round.")
    return p.parse_args()


def main() -> int:
    args = parse_args()
    repo_root = Path(__file__).resolve().parents[2]
    prompt_file = Path(args.prompt_file)
    if not prompt_file.is_absolute():
        prompt_file = (repo_root / prompt_file).resolve()
    if not prompt_file.exists():
        raise SystemExit(f"missing prompt file: {prompt_file}")

    stamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
    run_dir = (repo_root / args.artifacts_dir / f"{args.run_name}-{stamp}").resolve()
    out_dir = (repo_root / args.output_dir).resolve()
    packet_dir = (repo_root / args.packet_out_dir).resolve()
    run_dir.mkdir(parents=True, exist_ok=True)
    out_dir.mkdir(parents=True, exist_ok=True)
    packet_dir.mkdir(parents=True, exist_ok=True)

    original = read(prompt_file)
    write(run_dir / "original_prompt.txt", original)

    concept_rounds = max(1, int(args.concept_rounds))
    repair_rounds = max(0, int(args.repair_rounds))

    gemini_rounds: list[str] = []
    codex_critiques: list[str] = []
    fallback_info: dict[str, object] | None = None

    current_prompt = original
    final_concept = ""
    for round_idx in range(1, concept_rounds + 1):
        guard_status = check_gemini_guard(repo_root)
        write(run_dir / f"gemini_guard_round{round_idx}.json", json.dumps(guard_status, indent=2, sort_keys=True))
        if not bool(guard_status.get("allowed", False)):
            if is_daily_limit_guard(guard_status):
                fallback_info = resolve_gemini_limit_fallback(
                    repo_root,
                    packet_dir=packet_dir,
                    transcript_dir=out_dir,
                    prompt_file=prompt_file,
                    run_name=args.run_name,
                    fallback_packet_arg=args.fallback_packet,
                    fallback_transcript_arg=args.fallback_transcript,
                )
                if fallback_info is not None:
                    final_concept = str(fallback_info.get("concept", "")).strip()
                    fallback_info = {
                        **fallback_info,
                        "trigger_round": round_idx,
                        "guard_status": guard_status,
                    }
                    write(run_dir / "gemini_fallback_used.json", json.dumps(fallback_info, indent=2, sort_keys=True))
                    write(run_dir / "final_concept_from_fallback.md", final_concept)
                    break
            raise SystemExit(f"gemini round {round_idx} blocked: {guard_status.get('reason', 'unknown reason')}")

        gemini = run(
            [
                "./tools/infra/run_gemini_guarded.sh",
                "--loop-burst",
                "--reason",
                f"{args.reason} gemini round {round_idx}",
                "--",
                "gemini",
                "--prompt",
                current_prompt,
            ],
            repo_root,
        )
        if gemini.returncode != 0:
            write(run_dir / f"gemini_round{round_idx}.stderr.txt", (gemini.stderr or "") + (gemini.stdout or ""))
            raise SystemExit(f"gemini round {round_idx} failed with exit code {gemini.returncode}")
        gemini_text = gemini.stdout
        gemini_rounds.append(gemini_text)
        write(run_dir / f"gemini_round{round_idx}.md", gemini_text)

        if round_idx == concept_rounds:
            break

        codex_prompt = f"""You are the critical interlocutor in a Socratic alchemical loop.

Original hypothesis prompt:
{original}

Current Gemini output:
{gemini_text}

Your task:
- identify inflation, vagueness, and false grandeur
- preserve the strongest nucleus
- name the exact conceptual compression achieved
- say what must be fed back into Gemini to intensify the concept without drifting

Output format:
NUCLEUS:
INFLATIONS_TO_REMOVE:
AMPLIFICATION_VECTOR:
DISTILLED_COUNTERPROMPT:
"""
        write(run_dir / f"codex_prompt_round{round_idx}.txt", codex_prompt)
        codex_cmd = ["codex", "exec", codex_prompt]
        if args.codex_extra.strip():
            codex_cmd.extend(args.codex_extra.split())
        codex = run(codex_cmd, repo_root)
        if codex.returncode != 0:
            write(run_dir / f"codex_round{round_idx}.stderr.txt", (codex.stderr or "") + (codex.stdout or ""))
            raise SystemExit(f"codex critique round {round_idx} failed with exit code {codex.returncode}")
        codex_text = codex.stdout
        codex_critiques.append(codex_text)
        write(run_dir / f"codex_round{round_idx}.md", codex_text)

        current_prompt = f"""Original prompt:
{original}

Previous Gemini output:
{gemini_text}

Codex critique:
{codex_text}

Now perform the next Socratic alchemical pass.
Requirements:
- remove the inflation identified by Codex
- preserve the nucleus
- amplify only along the vector Codex identified
- produce a denser, cleaner, more archetypally charged concept
- end with a section titled DISTILLED CONCEPT
"""
        write(run_dir / f"gemini_round{round_idx + 1}_prompt.txt", current_prompt)

    if not final_concept:
        if not gemini_rounds:
            raise SystemExit("no Gemini concept produced and no fallback concept available")
        final_concept = gemini_rounds[-1]

    lean_prompt = f"""You are Codex CLI acting as the coding/proof agent in an autonomous proofing system.

Original hypothesis prompt:
{original}

Gemini final distilled concept:
{final_concept}

Task:
Produce a single standalone Lean4 hypothesis file snippet.
Requirements:
- output Lean code only
- include at least one theorem or lemma
- do not use prose outside Lean comments
- prefer a minimal compileable hypothesis surface over grand claims
- if unsure, create a small lawful definition/lemma scaffold that captures the distilled concept conservatively
"""
    write(run_dir / "codex_lean_prompt.txt", lean_prompt)
    codex_lean = run(["codex", "exec", lean_prompt], repo_root)
    if codex_lean.returncode != 0:
        write(run_dir / "codex_lean.stderr.txt", (codex_lean.stderr or "") + (codex_lean.stdout or ""))
        raise SystemExit(f"codex lean generation failed with exit code {codex_lean.returncode}")

    lean_rounds: list[str] = []
    current_lean = strip_code_fences(codex_lean.stdout)
    lean_rounds.append(current_lean)
    write(run_dir / "codex_lean_round1.lean", current_lean)

    imports = "\n".join(f"import {item}" for item in args.lean_import)
    preamble = args.lean_preamble.strip()

    compile_attempts: list[dict[str, object]] = []
    lean_interact_probes: list[dict[str, object]] = []
    compiled_decl_extractions: list[dict[str, object]] = []
    theorem_surfaces: list[dict[str, object]] = []

    def round_probe_bundle(round_no: int) -> dict[str, object]:
        surface = next((row for row in theorem_surfaces if int(row.get("round", -1)) == round_no), {"round": round_no, "surface": {}})
        probes = [row for row in lean_interact_probes if int(row.get("round", -1)) == round_no]
        compiled = next((row for row in compiled_decl_extractions if int(row.get("round", -1)) == round_no), None)
        return {
            "round": round_no,
            "surface": surface.get("surface", {}),
            "probes": probes,
            "compiled_decl_extraction": compiled,
        }

    def record_probe(round_no: int, lean_code: str) -> str:
        surface = extract_first_theorem_surface(lean_code)
        theorem_surfaces.append({"round": round_no, "surface": surface})
        write(run_dir / f"theorem_surface_round{round_no}.json", json.dumps({"round": round_no, "surface": surface}, indent=2, sort_keys=True))
        probe_context = extract_probe_context(lean_code)
        if args.skip_lean_interact:
            return ""
        goal_stmt = surface.get("goal", "").strip()
        tactic = surface.get("tactic", "").strip()
        if goal_stmt:
            goal_probe = probe_goal(
                repo_root,
                goal_stmt,
                context=probe_context,
                imports=args.lean_import,
                timeout=min(60, args.lean_timeout),
            )
            if goal_probe is not None:
                entry = {"round": round_no, "kind": "goal", "surface": surface, "probe": goal_probe}
                lean_interact_probes.append(entry)
                write(run_dir / f"lean_interact_goal_round{round_no}.json", json.dumps(entry, indent=2, sort_keys=True))
        if goal_stmt and tactic:
            tactic_probe = probe_tactic(
                repo_root,
                goal_stmt,
                tactic,
                context=probe_context,
                imports=args.lean_import,
                timeout=min(60, args.lean_timeout),
            )
            if tactic_probe is not None:
                entry = {"round": round_no, "kind": "tactic", "surface": surface, "probe": tactic_probe}
                lean_interact_probes.append(entry)
                write(run_dir / f"lean_interact_tactic_round{round_no}.json", json.dumps(entry, indent=2, sort_keys=True))
        return goal_stmt

    def materialize(round_no: int, source: str) -> Path:
        lean_file = run_dir / f"generated_hypothesis_round{round_no}.lean"
        payload = f"{imports}\n\n{preamble}\n\n{source}\n"
        write(lean_file, payload)
        return lean_file

    round_no = 1
    lean_file = materialize(round_no, current_lean)
    goal_stmt = record_probe(round_no, current_lean)

    compile_proc = compile_lean(repo_root, lean_file)
    compile_attempts.append({
        "round": round_no,
        "file": str(lean_file),
        "returncode": compile_proc.returncode,
        "stdout": compile_proc.stdout or "",
        "stderr": compile_proc.stderr or "",
    })
    write(run_dir / f"compile_round{round_no}.stdout.txt", compile_proc.stdout or "")
    write(run_dir / f"compile_round{round_no}.stderr.txt", compile_proc.stderr or "")
    if compile_proc.returncode == 0:
        compiled_info = extract_compiled_decl_names(repo_root, run_dir, lean_file, timeout=args.lean_timeout)
        compiled_info["round"] = round_no
        compiled_decl_extractions.append(compiled_info)
        write(run_dir / f"compiled_decl_names_round{round_no}.json", json.dumps(compiled_info, indent=2, sort_keys=True))

    repair_idx = 0
    while compile_proc.returncode != 0 and repair_idx < repair_rounds:
        repair_idx += 1
        next_round = round_no + 1
        current_bundle = round_probe_bundle(round_no)
        prior_compile_attempts = [row for row in compile_attempts if int(row.get("round", -1)) == round_no]
        current_bundle_json = json.dumps(current_bundle, indent=2, sort_keys=True)
        compile_history_json = json.dumps(prior_compile_attempts, indent=2, sort_keys=True)
        repair_prompt = f"""You are Codex CLI in repair mode.

Original hypothesis prompt:
{original}

Current Lean code:
{current_lean}

Compiler stderr:
{compile_proc.stderr}

Compiler stdout:
{compile_proc.stdout}

Current round theorem surface + Lean-interact probes + compiled declaration info:
{current_bundle_json}

Current round compile attempt history:
{compile_history_json}

Task:
- repair the Lean code so it compiles
- use the theorem surface explicitly: keep the declaration kind/name when possible
- if the goal probe exposes the real goal state, align the theorem statement and proof with that goal instead of guessing
- if the tactic probe failed, treat that failure as primary evidence about the broken proof body and replace the tactic, not just the surrounding syntax
- if compiled declaration names exist from an earlier accepted round, preserve those accepted names unless compiler errors force a rename
- preserve as much conceptual content as possible
- be conservative
- output Lean code only
"""
        write(run_dir / f"codex_repair_prompt_round{next_round}.txt", repair_prompt)
        codex_repair = run(["codex", "exec", repair_prompt], repo_root)
        if codex_repair.returncode != 0:
            write(run_dir / f"codex_repair_round{next_round}.stderr.txt", (codex_repair.stderr or "") + (codex_repair.stdout or ""))
            break
        current_lean = strip_code_fences(codex_repair.stdout)
        lean_rounds.append(current_lean)
        write(run_dir / f"codex_lean_round{next_round}.lean", current_lean)
        round_no = next_round
        lean_file = materialize(round_no, current_lean)
        goal_stmt = record_probe(round_no, current_lean)
        compile_proc = compile_lean(repo_root, lean_file)
        compile_attempts.append({
            "round": round_no,
            "file": str(lean_file),
            "returncode": compile_proc.returncode,
            "stdout": compile_proc.stdout or "",
            "stderr": compile_proc.stderr or "",
        })
        write(run_dir / f"compile_round{round_no}.stdout.txt", compile_proc.stdout or "")
        write(run_dir / f"compile_round{round_no}.stderr.txt", compile_proc.stderr or "")
        if compile_proc.returncode == 0:
            compiled_info = extract_compiled_decl_names(repo_root, run_dir, lean_file, timeout=args.lean_timeout)
            compiled_info["round"] = round_no
            compiled_decl_extractions.append(compiled_info)
            write(run_dir / f"compiled_decl_names_round{round_no}.json", json.dumps(compiled_info, indent=2, sort_keys=True))

    transcript_parts = [
        f"# Socratic alchemy loop run — {args.run_name}\n",
        f"Timestamp: {stamp}\n",
        f"Prompt file: {prompt_file}\n",
        f"Artifact directory: {run_dir.relative_to(repo_root)}\n\n",
        "## Original prompt\n",
        original,
        "\n\n",
    ]
    if fallback_info is not None:
        guard_reason = str(((fallback_info.get("guard_status") or {}) if isinstance(fallback_info.get("guard_status"), dict) else {}).get("reason", ""))
        transcript_parts.append(
            "## Gemini limit fallback\n"
            f"- trigger round: {fallback_info.get('trigger_round')}\n"
            f"- source mode: {fallback_info.get('mode')}\n"
            f"- source path: {fallback_info.get('path')}\n"
            f"- guard reason: {guard_reason}\n\n"
            "### Recovered concept\n"
            f"{final_concept}\n\n"
        )
    for idx, gem in enumerate(gemini_rounds, start=1):
        transcript_parts.append(f"## Gemini round {idx}\n{gem}\n\n")
        if idx <= len(codex_critiques):
            transcript_parts.append(f"## Codex critique round {idx}\n{codex_critiques[idx-1]}\n\n")
    for idx, lean_code in enumerate(lean_rounds, start=1):
        transcript_parts.append(f"## Codex Lean hypothesis round {idx}\n```lean\n{lean_code}\n```\n\n")
        round_probes = [p for p in lean_interact_probes if int(p.get("round", -1)) == idx]
        round_surfaces = [row for row in theorem_surfaces if int(row.get("round", -1)) == idx]
        for surface_row in round_surfaces:
            transcript_parts.append(
                f"## Theorem surface round {idx}\n```json\n{json.dumps(surface_row, indent=2, sort_keys=True)}\n```\n\n"
            )
        for probe in round_probes:
            transcript_parts.append(
                f"## Lean interact {probe.get('kind', 'probe')} round {idx}\n```json\n{json.dumps(probe, indent=2, sort_keys=True)}\n```\n\n"
            )
        if idx <= len(compile_attempts):
            attempt = compile_attempts[idx-1]
            transcript_parts.append(
                f"## Compile round {idx}\n- returncode: {attempt['returncode']}\n\n### stderr\n```\n{str(attempt['stderr']).strip()}\n```\n\n### stdout\n```\n{str(attempt['stdout']).strip()}\n```\n\n"
            )
        compiled_rows = [row for row in compiled_decl_extractions if int(row.get("round", -1)) == idx]
        for row in compiled_rows:
            transcript_parts.append(
                f"## Compiled declaration names round {idx}\n```json\n{json.dumps(row, indent=2, sort_keys=True)}\n```\n\n"
            )

    transcript = "".join(transcript_parts)
    transcript_path = out_dir / f"{args.run_name}-{stamp}.md"
    write(transcript_path, transcript)

    run_data = {
        "run_name": args.run_name,
        "original_prompt": original,
        "gemini_rounds": gemini_rounds,
        "codex_critiques": codex_critiques,
        "lean_rounds": lean_rounds,
        "compile_attempts": compile_attempts,
        "compiled_decl_extractions": compiled_decl_extractions,
        "theorem_surfaces": theorem_surfaces,
        "fallback_info": fallback_info or {},
    }
    packet = build_packet_from_loop(run_data)
    packet_path = packet_dir / f"{args.run_name}-{stamp}.json"
    write(packet_path, json.dumps(packet.to_dict(), indent=2, sort_keys=True))

    run_state = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "status": "completed" if compile_attempts and int(compile_attempts[-1].get("returncode", 1)) == 0 else "frontier_residue",
        "report_out": str(transcript_path),
    }
    memory_log = Path(args.memory_log)
    if not memory_log.is_absolute():
        memory_log = (repo_root / memory_log).resolve()
    ingest(packet=packet, run_state=run_state, out_file=memory_log)

    print(transcript_path.relative_to(repo_root))
    print(packet_path.relative_to(repo_root))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
