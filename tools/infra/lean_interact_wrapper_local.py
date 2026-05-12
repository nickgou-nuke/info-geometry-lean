#!/usr/bin/env python3
from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_IMPORTS = ["Mathlib"]


@dataclass(frozen=True)
class LeanProbe:
    goal: str
    tactic: str | None
    imports: list[str]
    context: str


def _clean_lines(value: str | None) -> list[str]:
    if not value:
        return []
    return [line.rstrip() for line in value.splitlines() if line.strip()]


def _build_source(probe: LeanProbe, *, trace_state: bool) -> str:
    imports = probe.imports or DEFAULT_IMPORTS
    lines: list[str] = []
    lines.extend(f"import {name}" for name in imports)
    lines.append("")
    if probe.context.strip():
        lines.extend(_clean_lines(probe.context))
        lines.append("")
    lines.append(f"theorem hermes_probe : {probe.goal} := by")
    if trace_state:
        lines.append("  trace_state")
    if probe.tactic:
        for line in probe.tactic.splitlines():
            lines.append(f"  {line}" if line.strip() else "")
    else:
        lines.append("  sorry")
    lines.append("")
    return "\n".join(lines)


def run_lean_source(source: str, *, timeout: int) -> dict[str, object]:
    env = os.environ.copy()
    env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{env.get('PATH', '')}"
    with tempfile.NamedTemporaryFile(
        "w", suffix=".lean", prefix="hermes_probe_", encoding="utf-8", delete=False
    ) as f:
        f.write(source)
        path = Path(f.name)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=os.getcwd(),
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
        ok = proc.returncode == 0
        if ok and ("warning: declaration uses `sorry`" in proc.stdout or "warning: declaration uses `sorry`" in proc.stderr):
            ok = False

        return {
            "returncode": proc.returncode,
            "ok": ok,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
            "source_path": str(path),
            "source": source,
        }

    except subprocess.TimeoutExpired as exc:
        return {
            "returncode": None,
            "ok": False,
            "stdout": exc.stdout or "",
            "stderr": exc.stderr or "",
            "source_path": str(path),
            "source": source,
            "error_type": "TimeoutExpired",
            "error": f"Lean probe timed out after {timeout}s",
        }
    finally:
        path.unlink(missing_ok=True)


def get_proof_state(
    goal: str,
    *,
    imports: list[str] | None = None,
    context: str = "",
    timeout: int = 60,
) -> dict[str, object]:
    probe = LeanProbe(
        goal=goal.strip(),
        tactic=None,
        imports=imports or DEFAULT_IMPORTS,
        context=context,
    )
    result = run_lean_source(_build_source(probe, trace_state=True), timeout=timeout)
    return {
        "schema": "lean_interact.proof_state.v1",
        "status": "ok" if result["ok"] else "error",
        "goal": probe.goal,
        "context": probe.context,
        "imports": probe.imports,
        "proof_state": result["stdout"].strip(),
        "lean": result,
    }


def apply_tactic(
    goal: str,
    tactic: str,
    *,
    imports: list[str] | None = None,
    context: str = "",
    timeout: int = 60,
) -> dict[str, object]:
    probe = LeanProbe(
        goal=goal.strip(),
        tactic=tactic.strip(),
        imports=imports or DEFAULT_IMPORTS,
        context=context,
    )
    result = run_lean_source(_build_source(probe, trace_state=True), timeout=timeout)
    return {
        "schema": "lean_interact.tactic_probe.v1",
        "status": "success" if result["ok"] else "failure",
        "goal": probe.goal,
        "tactic": probe.tactic,
        "context": probe.context,
        "imports": probe.imports,
        "proof_state_before": result["stdout"].strip(),
        "lean": result,
    }


def parse_imports(values: list[str]) -> list[str]:
    imports: list[str] = []
    for value in values:
        for item in value.split(","):
            item = item.strip()
            if item:
                imports.append(item)
    return imports or DEFAULT_IMPORTS


def _usage() -> str:
    return (
        "Usage:\n"
        "  lean_interact_wrapper.py --goal GOAL [--context CTX] [--import MOD] [--timeout SEC]\n"
        "  lean_interact_wrapper.py --tactic GOAL TACTIC [--context CTX] [--import MOD] [--timeout SEC]\n"
    )


def _pop_option(args: list[str], name: str, default: str | None = None) -> str | None:
    if name not in args:
        return default
    idx = args.index(name)
    try:
        value = args[idx + 1]
    except IndexError as exc:
        raise SystemExit(f"{name} requires a value\n{_usage()}") from exc
    del args[idx : idx + 2]
    return value


def _pop_repeated(args: list[str], name: str) -> list[str]:
    values: list[str] = []
    while name in args:
        idx = args.index(name)
        try:
            value = args[idx + 1]
        except IndexError as exc:
            raise SystemExit(f"{name} requires a value\n{_usage()}") from exc
        values.append(value)
        del args[idx : idx + 2]
    return values


def main(argv: list[str] | None = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    if not args or args[0] not in {"--goal", "--tactic"}:
        print(_usage(), file=sys.stderr)
        return 2

    cmd = args.pop(0)
    timeout = int(_pop_option(args, "--timeout", "60") or "60")
    context = _pop_option(args, "--context", "") or ""
    imports = parse_imports(_pop_repeated(args, "--import"))

    if cmd == "--goal":
        if len(args) != 1:
            print(_usage(), file=sys.stderr)
            return 2
        payload = get_proof_state(
            args[0],
            imports=imports,
            context=context,
            timeout=timeout,
        )
    elif cmd == "--tactic":
        if len(args) != 2:
            print(_usage(), file=sys.stderr)
            return 2
        payload = apply_tactic(
            args[0],
            args[1],
            imports=imports,
            context=context,
            timeout=timeout,
        )
    else:
        print(_usage(), file=sys.stderr)
        return 2
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
