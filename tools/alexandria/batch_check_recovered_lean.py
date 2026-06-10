#!/usr/bin/env python3
"""Batch-check recovered Lean snippets with ``lake env lean``.

This consumes ``recovered_pdf_code_blocks.jsonl`` from
``recover_pdf_source_fragments.py`` and validates Lean-looking candidates in
generated batch files.  Batches that compile mark every member as kernel
accepted.  Failed batches can optionally be recursively split to isolate the
smallest failing fragments.

The input recovery layer is not proof authority.  This checker records only
what the Lean frontend/kernel accepts.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Iterable


if __package__ in (None, ""):
    ROOT = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(ROOT))
else:
    ROOT = Path(__file__).resolve().parents[2]

from tools.alexandria.schema import stable_key  # noqa: E402
from tools.pathing import normalize_user_path, repo_root  # noqa: E402


SCHEMA = "info_geometry.alexandria.recovered_lean_batch_check.v1"
AUTHORITY = "lean_kernel_checked_recovered_pdf_candidate"


@dataclass(frozen=True)
class LeanCandidate:
    key: str
    text: str
    pageStart: int | None
    pageEnd: int | None
    metadata: dict[str, Any]


@dataclass(frozen=True)
class LeanCheckResult:
    key: str
    candidateKey: str
    status: str
    message: str
    batchKey: str
    batchFile: str | None
    pageStart: int | None
    pageEnd: int | None
    metadata: dict[str, Any]


def canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"))


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(canonical_json(row) + "\n")
            count += 1
    return count


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if line:
                rows.append(json.loads(line))
    return rows


def load_lean_candidates(
    path: Path,
    *,
    max_candidates: int,
    min_page: int,
    max_page: int,
    candidate_keys: set[str],
) -> list[LeanCandidate]:
    candidates: list[LeanCandidate] = []
    for row in load_jsonl(path):
        if row.get("language") != "lean4":
            continue
        key = str(row.get("key"))
        if candidate_keys and key not in candidate_keys:
            continue
        page_start = row.get("pageStart") if isinstance(row.get("pageStart"), int) else None
        page_end = row.get("pageEnd") if isinstance(row.get("pageEnd"), int) else None
        if min_page > 0 and page_end is not None and page_end < min_page:
            continue
        if max_page > 0 and page_start is not None and page_start > max_page:
            continue
        text = str(row.get("text", "")).strip()
        if not text:
            continue
        candidates.append(
            LeanCandidate(
                key=key,
                text=text,
                pageStart=page_start,
                pageEnd=page_end,
                metadata=row.get("metadata") if isinstance(row.get("metadata"), dict) else {},
            )
        )
        if max_candidates > 0 and len(candidates) >= max_candidates:
            break
    return candidates


def safe_namespace_name(candidate: LeanCandidate, index: int) -> str:
    suffix = re.sub(r"[^A-Za-z0-9_]", "_", candidate.key)[-24:]
    if not suffix or suffix[0].isdigit():
        suffix = f"C_{suffix}"
    return f"Candidate_{index:05d}_{suffix}"


def normalize_snippet(snippet: str) -> str:
    lines = []
    for line in snippet.splitlines():
        stripped = line.rstrip()
        if stripped.startswith("import "):
            lines.append(f"-- skipped recovered import command: {stripped}")
        else:
            lines.append(stripped)
    return "\n".join(lines).strip()


def build_batch_source(
    candidates: list[LeanCandidate],
    *,
    preamble: str,
    namespace: str,
    start_index: int,
) -> str:
    parts: list[str] = []
    if preamble.strip():
        parts.append(preamble.strip())
    parts.extend(
        [
            "set_option autoImplicit true",
            "set_option linter.unusedVariables false",
            "",
            f"namespace {namespace}",
            "",
        ]
    )
    for offset, candidate in enumerate(candidates):
        idx = start_index + offset
        local_ns = safe_namespace_name(candidate, idx)
        parts.extend(
            [
                f"/- BEGIN recovered candidate {candidate.key} page={candidate.pageStart} -/",
                f"namespace {local_ns}",
                normalize_snippet(candidate.text),
                f"end {local_ns}",
                f"/- END recovered candidate {candidate.key} -/",
                "",
            ]
        )
    parts.append(f"end {namespace}")
    return "\n".join(parts).rstrip() + "\n"


def run_lean(path: Path, *, timeout: int, cwd: Path) -> tuple[bool, str]:
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=cwd,
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return False, f"lake env lean timed out after {timeout}s"
    output = (proc.stdout + "\n" + proc.stderr).strip()
    compact = re.sub(r"\s+", " ", output).strip()
    if proc.returncode == 0:
        return True, "lake env lean accepted batch"
    return False, compact[:1200] if compact else f"lean exited with code {proc.returncode}"


def result_for(
    candidate: LeanCandidate,
    *,
    status: str,
    message: str,
    batch_key: str,
    batch_file: Path | None,
    extra: dict[str, Any] | None = None,
) -> LeanCheckResult:
    return LeanCheckResult(
        key=stable_key("leancheck", candidate.key, status, batch_key),
        candidateKey=candidate.key,
        status=status,
        message=message,
        batchKey=batch_key,
        batchFile=batch_file.as_posix() if batch_file else None,
        pageStart=candidate.pageStart,
        pageEnd=candidate.pageEnd,
        metadata={"authority": AUTHORITY, **(extra or {})},
    )


def check_partition(
    candidates: list[LeanCandidate],
    *,
    output: Path,
    preamble: str,
    timeout: int,
    namespace: str,
    batch_counter: list[int],
    isolate_failures: bool,
    start_index: int,
) -> list[LeanCheckResult]:
    if not candidates:
        return []
    batch_id = batch_counter[0]
    batch_counter[0] += 1
    batch_key = stable_key("leanbatch", batch_id, [candidate.key for candidate in candidates])
    source = build_batch_source(
        candidates,
        preamble=preamble,
        namespace=f"{namespace}.Batch_{batch_id:05d}",
        start_index=start_index,
    )
    batch_dir = output / "lean_batch_sources"
    batch_dir.mkdir(parents=True, exist_ok=True)
    batch_file = batch_dir / f"batch_{batch_id:05d}_{len(candidates):04d}.lean"
    batch_file.write_text(source, encoding="utf-8")
    ok, message = run_lean(batch_file, timeout=timeout, cwd=repo_root())
    if ok:
        return [
            result_for(
                candidate,
                status="passed",
                message=message,
                batch_key=batch_key,
                batch_file=batch_file,
                extra={"batchSize": len(candidates)},
            )
            for candidate in candidates
        ]
    if not isolate_failures or len(candidates) == 1:
        status = "failed" if len(candidates) == 1 else "batch_failed"
        return [
            result_for(
                candidate,
                status=status,
                message=message,
                batch_key=batch_key,
                batch_file=batch_file,
                extra={"batchSize": len(candidates)},
            )
            for candidate in candidates
        ]
    midpoint = len(candidates) // 2
    left = check_partition(
        candidates[:midpoint],
        output=output,
        preamble=preamble,
        timeout=timeout,
        namespace=namespace,
        batch_counter=batch_counter,
        isolate_failures=isolate_failures,
        start_index=start_index,
    )
    right = check_partition(
        candidates[midpoint:],
        output=output,
        preamble=preamble,
        timeout=timeout,
        namespace=namespace,
        batch_counter=batch_counter,
        isolate_failures=isolate_failures,
        start_index=start_index + midpoint,
    )
    return left + right


def chunks(values: list[LeanCandidate], size: int) -> Iterable[tuple[int, list[LeanCandidate]]]:
    for idx in range(0, len(values), size):
        yield idx, values[idx : idx + size]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="recovered_pdf_code_blocks.jsonl")
    parser.add_argument("--output", type=Path, required=True, help="Output directory for batch-check results.")
    parser.add_argument("--preamble", default="import Std")
    parser.add_argument("--batch-size", type=int, default=16)
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--max-candidates", type=int, default=0)
    parser.add_argument("--min-page", type=int, default=0)
    parser.add_argument("--max-page", type=int, default=0)
    parser.add_argument("--candidate-key", action="append", default=[])
    parser.add_argument("--namespace", default="PdfRecoveredLean")
    parser.add_argument("--isolate-failures", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = repo_root()
    input_path = normalize_user_path(str(args.input), root)
    output = normalize_user_path(str(args.output), root)
    output.mkdir(parents=True, exist_ok=True)
    candidates = load_lean_candidates(
        input_path,
        max_candidates=max(0, int(args.max_candidates)),
        min_page=max(0, int(args.min_page)),
        max_page=max(0, int(args.max_page)),
        candidate_keys=set(args.candidate_key or []),
    )
    batch_counter = [1]
    results: list[LeanCheckResult] = []
    batch_size = max(1, int(args.batch_size))
    for start, group in chunks(candidates, batch_size):
        results.extend(
            check_partition(
                group,
                output=output,
                preamble=args.preamble,
                timeout=max(1, int(args.timeout)),
                namespace=args.namespace,
                batch_counter=batch_counter,
                isolate_failures=args.isolate_failures,
                start_index=start + 1,
            )
        )

    rows = [asdict(result) for result in results]
    result_count = write_jsonl(output / "lean_batch_results.jsonl", rows)
    status_counts: dict[str, int] = {}
    for result in results:
        status_counts[result.status] = status_counts.get(result.status, 0) + 1
    manifest = {
        "schema": f"{SCHEMA}.manifest",
        "input": input_path.as_posix(),
        "output": output.as_posix(),
        "authority": AUTHORITY,
        "candidateCount": len(candidates),
        "resultCount": result_count,
        "statusCounts": status_counts,
        "batchSize": batch_size,
        "isolateFailures": bool(args.isolate_failures),
        "minPage": max(0, int(args.min_page)),
        "maxPage": max(0, int(args.max_page)),
        "candidateKeys": list(args.candidate_key or []),
        "preamble": args.preamble,
        "timeout": max(1, int(args.timeout)),
        "notes": [
            "Only status=passed means Lean accepted the recovered snippet in a generated batch file.",
            "status=batch_failed means the containing batch failed and was not isolated further.",
            "Recovered snippets are not original PDF sources; they are text-layer reconstructions.",
        ],
    }
    (output / "manifest.json").write_text(
        json.dumps(manifest, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(
        "[batch-check-recovered-lean] "
        f"candidates={len(candidates)} results={result_count} statuses={status_counts} output={output}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
