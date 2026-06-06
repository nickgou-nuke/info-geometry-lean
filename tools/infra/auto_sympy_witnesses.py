#!/usr/bin/env python3
"""Extract, repair, and run archived SymPy witness code.

This resurrects the old aiClaw "right hemisphere" lane without accepting
printed success text as a proof. Known-broken archive witnesses are emitted as
strict repaired scripts with explicit assertions; the original code is kept in
the manifest for audit.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DEFAULT_ARCHIVE_KB = Path("/media/goutev/SP DS72/auto/knowledge_base.json")
DEFAULT_OUT_DIR = Path("witnesses/auto_sympy")
DEFAULT_MANIFEST = Path("artifacts/auto_sympy/resurrected_witnesses.json")
DEFAULT_TIMEOUT = 30


@dataclass
class WitnessRecord:
    key: str
    title: str
    source: str
    status: str
    original_path: str | None
    strict_path: str | None
    repair_note: str | None
    runnable: bool
    returncode: int | None = None
    stdout: str = ""
    stderr: str = ""
    result: str = "not_run"
    warnings: list[str] | None = None


def safe_key(value: str) -> str:
    value = value.strip() or "unnamed_witness"
    value = re.sub(r"[^A-Za-z0-9_.-]+", "_", value)
    value = value.strip("._-")
    return value[:180] or "unnamed_witness"


def entry_key(entry: dict[str, Any], index: int) -> str:
    raw = entry.get("id") or entry.get("_key") or entry.get("title") or f"entry_{index:04d}"
    return safe_key(str(raw))


def is_python_like(code: str) -> bool:
    stripped = code.strip()
    if not stripped:
        return False
    if stripped.startswith("[") and stripped.endswith("]"):
        return False
    return any(token in stripped for token in ("import ", "def ", "print(", "assert ", "sp."))


def repaired_code_for(entry: dict[str, Any]) -> tuple[str | None, str | None]:
    key = str(entry.get("id") or "")
    title = str(entry.get("title") or "")

    if key == "FibAnyon_Thm1_FusionRules":
        return (
            """import sympy as sp

phi = (1 + sp.sqrt(5)) / 2
tau_conjugate = (1 - sp.sqrt(5)) / 2
N_tau = sp.Matrix([[0, 1], [1, 1]])
lam = sp.Symbol("lambda")

checks = {
    "phi_minpoly": sp.simplify(phi**2 - phi - 1),
    "tau_conjugate_minpoly": sp.simplify(tau_conjugate**2 - tau_conjugate - 1),
    "tau_conjugate_times_phi": sp.simplify(tau_conjugate * phi + 1),
    "fusion_matrix_charpoly": sp.factor(N_tau.charpoly(lam).as_expr() - (lam**2 - lam - 1)),
}

for name, value in checks.items():
    print(f"{name} = {value}")
    assert value == 0, (name, value)

print("strict_fibonacci_fusion_witness = ok")
""",
            "Repaired false archive check tau^2 + tau = 1. The conjugate root satisfies "
            "tau^2 - tau - 1 = 0 and tau*phi = -1.",
        )

    if key == "FibAnyon_Thm4_YangBaxter":
        return (
            """import sympy as sp

# Exact Fibonacci braid witness.
# q is a primitive 10th root with cyclotomic relation Phi_10(q) = 0.
# a = 1/phi is tied to q by a = q^2 - q^3, and s^2 = a.
q, a, s = sp.symbols("q a s")
F = sp.Matrix([[a, s], [s, -a]])
R = sp.Matrix([[q**4, 0], [0, q**7]])  # diag(exp(4*pi*i/5), exp(-3*pi*i/5))
B = F * R * F

relations = [
    q**4 - q**3 + q**2 - q + 1,
    a - (q**2 - q**3),
    s**2 - a,
]
gb = sp.groebner(relations, q, a, s, order="lex")
remainders = [sp.factor(gb.reduce(sp.expand(entry))[1]) for entry in (R * B * R - B * R * B)]

for idx, rem in enumerate(remainders):
    print(f"yang_baxter_remainder_{idx} = {rem}")
    assert rem == 0, (idx, rem)

print("strict_fibonacci_yang_baxter_witness = ok")
""",
            "Archive phases made R*B*R = B*R*B false. Repaired to the standard "
            "Fibonacci phases q=exp(pi*i/5), R=diag(q^4,q^-3), with exact "
            "cyclotomic/golden-ratio compatibility.",
        )

    if key == "FibAnyon_Thm5_BraidGroup":
        return (
            """import sympy as sp

q, a, s = sp.symbols("q a s")
F = sp.Matrix([[a, s], [s, -a]])
R = sp.Matrix([[q**4, 0], [0, q**7]])
B = F * R * F
b1, b2, b3 = R, B, R

relations = [
    q**4 - q**3 + q**2 - q + 1,
    a - (q**2 - q**3),
    s**2 - a,
]
gb = sp.groebner(relations, q, a, s, order="lex")

def reduce_entries(matrix):
    return [sp.factor(gb.reduce(sp.expand(entry))[1]) for entry in matrix]

checks = {
    "far_commutativity": reduce_entries(b1 * b3 - b3 * b1),
    "artin_relation": reduce_entries(b1 * b2 * b1 - b2 * b1 * b2),
}

for name, remainders in checks.items():
    for idx, rem in enumerate(remainders):
        print(f"{name}_{idx} = {rem}")
        assert rem == 0, (name, idx, rem)

print("strict_fibonacci_braid_group_witness = ok")
""",
            "Archive B4 witness only checked b1*b3=b3*b1. Repaired witness also "
            "checks the Artin relation using the same exact Fibonacci data as Thm4.",
        )

    if key == "FibAnyon_Thm6_ConformalDims":
        return (
            """def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a

expected = {4: 2, 5: 3, 6: 5, 7: 8, 8: 13}
for n, dim in expected.items():
    value = fib(n - 1)
    print(f"V_{n} = {value}")
    assert value == dim, (n, value, dim)

print("strict_fibonacci_conformal_dimensions_witness = ok")
""",
            "Repaired archive indentation error and made the dimension checks asserted.",
        )

    if "Fibonacci braided monoidal category" in title:
        return (
            """import sympy as sp

q, a, s = sp.symbols("q a s")
F = sp.Matrix([[a, s], [s, -a]])
R = sp.Matrix([[q**4, 0], [0, q**7]])
B = F * R * F
relations = [q**4 - q**3 + q**2 - q + 1, a - (q**2 - q**3), s**2 - a]
gb = sp.groebner(relations, q, a, s, order="lex")

checks = {
    "F_squared": F * F - sp.eye(2),
    "yang_baxter": R * B * R - B * R * B,
}
for name, matrix in checks.items():
    for idx, entry in enumerate(matrix):
        rem = sp.factor(gb.reduce(sp.expand(entry))[1])
        print(f"{name}_{idx} = {rem}")
        assert rem == 0, (name, idx, rem)

print("strict_fibonacci_braided_surface_witness = ok")
""",
            "Added executable strict witness for the prose-only Fibonacci braided category entry.",
        )

    return None, None


def find_python(repo: Path, configured: str | None) -> str:
    candidates = []
    if configured:
        candidates.append(configured)
    candidates.extend(
        [
            str(repo / ".venv-py312" / "bin" / "python"),
            str(repo / ".venv" / "bin" / "python3"),
            str(repo / ".venv" / "bin" / "python"),
            "python3",
            "python",
        ]
    )
    for candidate in candidates:
        try:
            subprocess.run(
                [candidate, "-c", "import sympy"],
                check=True,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=5,
            )
            return candidate
        except Exception:
            continue
    return candidates[0]


def run_python(python: str, path: Path, timeout: int) -> tuple[int, str, str]:
    proc = subprocess.run(
        [python, str(path)],
        text=True,
        capture_output=True,
        timeout=timeout,
    )
    return proc.returncode, proc.stdout, proc.stderr


def load_entries(path: Path) -> list[dict[str, Any]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(data, list):
        return [entry for entry in data if isinstance(entry, dict)]
    if isinstance(data, dict):
        return [data]
    raise ValueError(f"Unsupported knowledge base shape in {path}")


def extract(args: argparse.Namespace) -> tuple[list[WitnessRecord], dict[str, Any]]:
    repo = Path.cwd()
    source = Path(args.source)
    out_dir = Path(args.out_dir)
    original_dir = out_dir / "original"
    strict_dir = out_dir / "strict"
    original_dir.mkdir(parents=True, exist_ok=True)
    strict_dir.mkdir(parents=True, exist_ok=True)

    entries = load_entries(source)
    python = find_python(repo, args.python)
    records: list[WitnessRecord] = []

    for index, entry in enumerate(entries):
        code = entry.get("sympy_code")
        if not code:
            continue

        key = entry_key(entry, index)
        title = str(entry.get("title") or key)
        source_name = str(entry.get("source") or "")
        status = str(entry.get("status") or "")
        warnings: list[str] = []

        original_path: Path | None = None
        runnable_original = is_python_like(str(code))
        if runnable_original:
            original_path = original_dir / f"{key}.py"
            original_path.write_text(str(code).rstrip() + "\n", encoding="utf-8")
            if "assert " not in str(code):
                warnings.append("original_has_no_assertions")
        else:
            warnings.append("sympy_code_is_not_python")

        repaired, repair_note = repaired_code_for(entry)
        strict_code = repaired if repaired is not None else (str(code) if runnable_original else None)
        strict_path: Path | None = None
        if strict_code is not None:
            strict_path = strict_dir / f"{key}.py"
            strict_path.write_text(strict_code.rstrip() + "\n", encoding="utf-8")

        record = WitnessRecord(
            key=key,
            title=title,
            source=source_name,
            status=status,
            original_path=str(original_path) if original_path else None,
            strict_path=str(strict_path) if strict_path else None,
            repair_note=repair_note,
            runnable=strict_path is not None,
            warnings=warnings,
        )

        if args.run and strict_path is not None:
            try:
                returncode, stdout, stderr = run_python(python, strict_path, args.timeout)
                record.returncode = returncode
                record.stdout = stdout
                record.stderr = stderr
                false_output = bool(re.search(r"(^|[^A-Za-z])False([^A-Za-z]|$)", stdout))
                if returncode == 0 and not false_output:
                    record.result = "pass"
                elif returncode == 0 and false_output:
                    record.result = "fail_false_output"
                else:
                    record.result = "fail_exit"
            except subprocess.TimeoutExpired as exc:
                record.returncode = None
                record.stdout = exc.stdout or ""
                record.stderr = exc.stderr or ""
                record.result = "timeout"
        elif args.run:
            record.result = "skipped_not_python"

        records.append(record)

    summary = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "source": str(source),
        "out_dir": str(out_dir),
        "python": python,
        "total_sympy_entries": len(records),
        "runnable": sum(1 for record in records if record.runnable),
        "repaired": sum(1 for record in records if record.repair_note),
        "passed": sum(1 for record in records if record.result == "pass"),
        "failed": sum(1 for record in records if record.result.startswith("fail") or record.result == "timeout"),
        "skipped": sum(1 for record in records if record.result == "skipped_not_python"),
    }
    return records, summary


def write_manifest(records: list[WitnessRecord], summary: dict[str, Any], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "summary": summary,
        "records": [asdict(record) for record in records],
    }
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", default=str(DEFAULT_ARCHIVE_KB if DEFAULT_ARCHIVE_KB.exists() else Path("knowledge_base.json")))
    parser.add_argument("--out-dir", default=str(DEFAULT_OUT_DIR))
    parser.add_argument("--manifest", default=str(DEFAULT_MANIFEST))
    parser.add_argument("--python", default=None)
    parser.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT)
    parser.add_argument("--run", action="store_true", help="Run strict witnesses after extraction.")
    parser.add_argument("--strict", action="store_true", help="Exit nonzero if any runnable witness fails.")
    args = parser.parse_args()

    records, summary = extract(args)
    write_manifest(records, summary, Path(args.manifest))

    print(json.dumps(summary, indent=2, ensure_ascii=False))
    if args.strict and summary["failed"]:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
