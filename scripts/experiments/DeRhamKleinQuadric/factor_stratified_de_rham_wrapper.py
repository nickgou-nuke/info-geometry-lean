#!/usr/bin/env python3
"""Factor-stratified de Rham audit wrapper for f = q(a) q(b) q(a-b).

This wrapper combines:
- Singular intersection-strata data,
- Macaulay2 BernsteinSato + Dmodules certificates,
- bounded Macaulay2 de Rham probes,
- exact finite-field formulas already implemented in audit_rank32.py.

It is deliberately honest: timeouts remain timeouts, and no de Rham Betti claim is
promoted unless a backend actually returns one.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import time
from pathlib import Path
from typing import Any

import audit_rank32 as base

ROOT = Path(__file__).resolve().parents[3]
ARTIFACT_DIR = ROOT / "artifacts" / "de_rham_klein_quadric"


def _tail(text: str, lines: int = 12) -> str:
    rows = text.splitlines()
    if not rows:
        return ""
    return "\n".join(rows[-lines:])


def _trim(text: str, limit: int = 4000) -> str:
    if len(text) <= limit:
        return text
    return text[:limit] + "\n...[truncated]"


def _as_text(value: str | bytes | None) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode(errors="replace")
    return value


def _run_and_record(
    cmd: list[str],
    *,
    cwd: Path,
    timeout: int,
    script_path: Path | None = None,
    script_content: str | None = None,
    stdout_path: Path | None = None,
    stderr_path: Path | None = None,
) -> dict[str, Any]:
    if script_path is not None and script_content is not None:
        script_path.parent.mkdir(parents=True, exist_ok=True)
        script_path.write_text(script_content)
    started = time.time()
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(cwd),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
        elapsed = time.time() - started
        if stdout_path is not None:
            stdout_path.write_text(proc.stdout)
        if stderr_path is not None:
            stderr_path.write_text(proc.stderr)
        return {
            "status": "ok" if proc.returncode == 0 else "error",
            "command": cmd,
            "timeout_s": timeout,
            "returncode": proc.returncode,
            "elapsed_s": round(elapsed, 3),
            "script_path": str(script_path) if script_path else None,
            "stdout_path": str(stdout_path) if stdout_path else None,
            "stderr_path": str(stderr_path) if stderr_path else None,
            "stdout_tail": _tail(proc.stdout),
            "stderr_tail": _tail(proc.stderr),
            "stdout_excerpt": _trim(proc.stdout),
            "stderr_excerpt": _trim(proc.stderr),
        }
    except subprocess.TimeoutExpired as exc:
        elapsed = time.time() - started
        stdout = _as_text(exc.stdout)
        stderr = _as_text(exc.stderr)
        if stdout_path is not None:
            stdout_path.write_text(stdout)
        if stderr_path is not None:
            stderr_path.write_text(stderr)
        return {
            "status": "timeout",
            "command": cmd,
            "timeout_s": timeout,
            "returncode": None,
            "elapsed_s": round(elapsed, 3),
            "script_path": str(script_path) if script_path else None,
            "stdout_path": str(stdout_path) if stdout_path else None,
            "stderr_path": str(stderr_path) if stderr_path else None,
            "stdout_tail": _tail(stdout),
            "stderr_tail": _tail(stderr),
            "stdout_excerpt": _trim(stdout),
            "stderr_excerpt": _trim(stderr),
            "error": str(exc),
        }


def _m2_factor_script(dim: int, signature: str) -> str:
    vars_total = base.vars_for_dim(dim)
    avars = vars_total[:dim]
    bvars = vars_total[dim:]
    var_decl = ",".join(vars_total)
    qA = base.q_expr(avars, signature)
    qB = base.q_expr(bvars, signature)
    qAB = base.q_expr(tuple(f"({a}-{b})" for a, b in zip(avars, bvars)), signature)
    return f'''needsPackage "BernsteinSato";
needsPackage "Dmodules";
R = QQ[{var_decl}];
qA = {qA};
qB = {qB};
qAB = {qAB};
f = qA*qB*qAB;

print("M2FACT:Dmodules=loaded");
print("M2FACT:ambientVars={2 * dim}");
print("M2FACT:qA_raw=" | toString(globalBFunction qA));
print("M2FACT:qA_factor=" | toString factor(globalBFunction qA));
print("M2FACT:qB_raw=" | toString(globalBFunction qB));
print("M2FACT:qB_factor=" | toString factor(globalBFunction qB));
print("M2FACT:qAB_raw=" | toString(globalBFunction qAB));
print("M2FACT:qAB_factor=" | toString factor(globalBFunction qAB));
GB = generalB {{qA, qB, qAB}};
print("M2FACT:generalB_raw=" | toString GB);
print("M2FACT:generalB_factor=" | toString factor GB);
'''


def _m2_full_product_script(dim: int, signature: str) -> str:
    vars_total = base.vars_for_dim(dim)
    avars = vars_total[:dim]
    bvars = vars_total[dim:]
    var_decl = ",".join(vars_total)
    qA = base.q_expr(avars, signature)
    qB = base.q_expr(bvars, signature)
    qAB = base.q_expr(tuple(f"({a}-{b})" for a, b in zip(avars, bvars)), signature)
    return f'''needsPackage "BernsteinSato";
needsPackage "Dmodules";
R = QQ[{var_decl}];
qA = {qA};
qB = {qB};
qAB = {qAB};
f = qA*qB*qAB;
print("M2FULL:Dmodules=loaded");
print("M2FULL:ambientVars={2 * dim}");
print("M2FULL:fDegree=" | toString(degree f));
print("M2FULL:probe=globalBFunction");
print("M2FULL:full_raw=" | toString(globalBFunction f));
print("M2FULL:full_factor=" | toString factor(globalBFunction f));
'''


def _stratum_specs() -> list[dict[str, Any]]:
    """Factor/pair/triple strata for f=qA*qB*qAB.

    `vanish` are equations imposed on the stratum.  `invert` is the product of
    remaining factors used as the localizing denominator on that stratum.  These
    are surgical probes: they certify what the D-module engine can compute on
    bounded pieces, but they do not by themselves imply Betti ranks.
    """
    return [
        {"name": "factor_qA", "vanish": ["qA"], "invert": ["qB", "qAB"]},
        {"name": "factor_qB", "vanish": ["qB"], "invert": ["qA", "qAB"]},
        {"name": "factor_qAB", "vanish": ["qAB"], "invert": ["qA", "qB"]},
        {"name": "pair_qA_qB", "vanish": ["qA", "qB"], "invert": ["qAB"]},
        {"name": "pair_qA_qAB", "vanish": ["qA", "qAB"], "invert": ["qB"]},
        {"name": "pair_qB_qAB", "vanish": ["qB", "qAB"], "invert": ["qA"]},
        {"name": "triple_qA_qB_qAB", "vanish": ["qA", "qB", "qAB"], "invert": []},
    ]


def _m2_stratum_script(dim: int, signature: str, spec: dict[str, Any], *, attempt_derham0: bool) -> str:
    vars_total = base.vars_for_dim(dim)
    dvars = tuple(f"d{v}" for v in vars_total)
    avars = vars_total[:dim]
    bvars = vars_total[dim:]
    var_decl = ",".join(vars_total)
    weyl_decl = ",".join(vars_total + dvars)
    weyl_pairs = ", ".join(f"{v} => d{v}" for v in vars_total)
    qA = base.q_expr(avars, signature)
    qB = base.q_expr(bvars, signature)
    qAB = base.q_expr(tuple(f"({a}-{b})" for a, b in zip(avars, bvars)), signature)
    vanish = list(spec["vanish"])
    invert = list(spec["invert"])
    vanish_expr = ",".join(vanish) if vanish else "0"
    invert_expr = "*".join(invert) if invert else "1"
    dvar_expr = ",".join(dvars)
    derham_block = ""
    if attempt_derham0 and invert:
        derham_block = f'''
try (
  H0 = deRham(0, localizer);
  print("M2STRAT:deRham0_rank=" | toString(rank H0));
  print("M2STRAT:deRham0_module=" | toString H0);
) else (
  print("M2STRAT:deRham0_error=true");
);
'''
    return f'''needsPackage "BernsteinSato";
needsPackage "Dmodules";
R = QQ[{var_decl}];
qA = {qA};
qB = {qB};
qAB = {qAB};
f = qA*qB*qAB;
stratumIdeal = ideal({vanish_expr});
localizer = {invert_expr};
print("M2STRAT:Dmodules=loaded");
print("M2STRAT:name={spec['name']}");
print("M2STRAT:ambientVars={2 * dim}");
print("M2STRAT:vanish={'+'.join(vanish)}");
print("M2STRAT:invert={'*'.join(invert) if invert else 'none'}");
print("M2STRAT:comm_dim=" | toString(dim stratumIdeal));
print("M2STRAT:comm_codim=" | toString(codim stratumIdeal));
if localizer != 1 then (
  try (
    print("M2STRAT:localizer_b_raw=" | toString(globalBFunction localizer));
    print("M2STRAT:localizer_b_factor=" | toString factor(globalBFunction localizer));
  ) else (
    print("M2STRAT:localizer_b_error=true");
  );
) else (
  print("M2STRAT:localizer_b_skipped=no_remaining_factor");
);
W = QQ[{weyl_decl}, WeylAlgebra => {{{weyl_pairs}}}];
qA = {qA};
qB = {qB};
qAB = {qAB};
localizer = {invert_expr};
stratumDIdeal = ideal({vanish_expr}, {dvar_expr});
print("M2STRAT:dmodule_ideal_gens=" | toString(numgens stratumDIdeal));
if localizer != 1 then (
  try (
    M = Dlocalize(stratumDIdeal, localizer);
    print("M2STRAT:dlocalize_class=" | toString(class M));
    E = rationalFunctionExt(M);
    print("M2STRAT:dlocalize_ext=" | toString E);
  ) else (
    print("M2STRAT:dlocalize_error=true");
  );
) else (
  print("M2STRAT:dlocalize_skipped=no_remaining_factor");
);
{derham_block}
'''



def _run_singular_factor_strata(dim: int, signature: str, *, cwd: Path, out_dir: Path, timeout: int) -> dict[str, Any]:
    exe = shutil.which("Singular") or shutil.which("singular")
    if exe is None:
        return {"status": "missing", "error": "Singular binary not found"}
    script = base.singular_script(dim, signature)
    record = _run_and_record(
        [exe, "-q", str(out_dir / "factor_strata.sing")],
        cwd=cwd,
        timeout=timeout,
        script_path=out_dir / "factor_strata.sing",
        script_content=script,
        stdout_path=out_dir / "factor_strata.stdout.log",
        stderr_path=out_dir / "factor_strata.stderr.log",
    )
    payload = base.parse_kv(record.get("stdout_excerpt", "") if record["status"] == "timeout" else (out_dir / "factor_strata.stdout.log").read_text(), "SINGULAR:")
    record["payload"] = payload
    return record


def _run_m2_factor_bernstein(dim: int, signature: str, *, cwd: Path, out_dir: Path, timeout: int) -> dict[str, Any]:
    exe = shutil.which("M2") or shutil.which("Macaulay2") or shutil.which("m2")
    if exe is None:
        return {"status": "missing", "error": "Macaulay2 binary not found"}
    script = _m2_factor_script(dim, signature)
    record = _run_and_record(
        [exe, "--script", str(out_dir / "factor_bernstein.m2")],
        cwd=cwd,
        timeout=timeout,
        script_path=out_dir / "factor_bernstein.m2",
        script_content=script,
        stdout_path=out_dir / "factor_bernstein.stdout.log",
        stderr_path=out_dir / "factor_bernstein.stderr.log",
    )
    payload = base.parse_kv((out_dir / "factor_bernstein.stdout.log").read_text() if (out_dir / "factor_bernstein.stdout.log").exists() else "", "M2FACT:")
    record["payload"] = payload
    return record


def _run_m2_full_product_probe(dim: int, signature: str, *, cwd: Path, out_dir: Path, timeout: int) -> dict[str, Any]:
    exe = shutil.which("M2") or shutil.which("Macaulay2") or shutil.which("m2")
    if exe is None:
        return {"status": "missing", "error": "Macaulay2 binary not found"}
    script = _m2_full_product_script(dim, signature)
    record = _run_and_record(
        [exe, "--script", str(out_dir / "full_product_probe.m2")],
        cwd=cwd,
        timeout=timeout,
        script_path=out_dir / "full_product_probe.m2",
        script_content=script,
        stdout_path=out_dir / "full_product_probe.stdout.log",
        stderr_path=out_dir / "full_product_probe.stderr.log",
    )
    payload = base.parse_kv((out_dir / "full_product_probe.stdout.log").read_text() if (out_dir / "full_product_probe.stdout.log").exists() else "", "M2FULL:")
    record["payload"] = payload
    return record


def _run_m2_de_rham_probe(
    dim: int,
    signature: str,
    *,
    cwd: Path,
    out_dir: Path,
    timeout: int,
    name: str,
    degree: int | None,
    method: str,
) -> dict[str, Any]:
    exe = shutil.which("M2") or shutil.which("Macaulay2") or shutil.which("m2")
    if exe is None:
        return {"status": "missing", "error": "Macaulay2 binary not found"}
    script = base.mac2_script(dim, signature, attempt_derham=True, derham_degree=degree, derham_method=method)
    record = _run_and_record(
        [exe, "--script", str(out_dir / f"{name}.m2")],
        cwd=cwd,
        timeout=timeout,
        script_path=out_dir / f"{name}.m2",
        script_content=script,
        stdout_path=out_dir / f"{name}.stdout.log",
        stderr_path=out_dir / f"{name}.stderr.log",
    )
    payload = base.parse_kv((out_dir / f"{name}.stdout.log").read_text() if (out_dir / f"{name}.stdout.log").exists() else "", "MACAULAY2:")
    record["payload"] = payload
    record["de_rham_method"] = method
    record["de_rham_degree"] = degree
    return record


def _run_m2_stratum_probe(
    dim: int,
    signature: str,
    spec: dict[str, Any],
    *,
    cwd: Path,
    out_dir: Path,
    timeout: int,
    attempt_derham0: bool,
) -> dict[str, Any]:
    exe = shutil.which("M2") or shutil.which("Macaulay2") or shutil.which("m2")
    if exe is None:
        return {"status": "missing", "error": "Macaulay2 binary not found", "stratum": spec["name"]}
    script_dir = out_dir / "stage2_strata_scripts"
    log_dir = out_dir / "stage2_strata_logs"
    script_dir.mkdir(parents=True, exist_ok=True)
    log_dir.mkdir(parents=True, exist_ok=True)
    script = _m2_stratum_script(dim, signature, spec, attempt_derham0=attempt_derham0)
    name = spec["name"]
    record = _run_and_record(
        [exe, "--script", str(script_dir / f"{name}.m2")],
        cwd=cwd,
        timeout=timeout,
        script_path=script_dir / f"{name}.m2",
        script_content=script,
        stdout_path=log_dir / f"{name}.stdout.log",
        stderr_path=log_dir / f"{name}.stderr.log",
    )
    payload = base.parse_kv((log_dir / f"{name}.stdout.log").read_text() if (log_dir / f"{name}.stdout.log").exists() else "", "M2STRAT:")
    record["payload"] = payload
    record["stratum"] = name
    record["vanish"] = spec["vanish"]
    record["invert"] = spec["invert"]
    return record


def _run_m2_stage2_strata(
    dim: int,
    signature: str,
    *,
    cwd: Path,
    out_dir: Path,
    timeout: int,
    attempt_derham0: bool,
) -> dict[str, Any]:
    records = []
    for spec in _stratum_specs():
        records.append(
            _run_m2_stratum_probe(
                dim,
                signature,
                spec,
                cwd=cwd,
                out_dir=out_dir,
                timeout=timeout,
                attempt_derham0=attempt_derham0,
            )
        )
    return {
        "status": "ok" if all(r.get("status") == "ok" for r in records) else "partial",
        "records": records,
        "script_dir": str(out_dir / "stage2_strata_scripts"),
        "log_dir": str(out_dir / "stage2_strata_logs"),
        "actual_de_rham_payloads": [
            r for r in records
            if r.get("payload", {}).get("deRham0_rank") is not None
            and r.get("payload", {}).get("deRham0_error") != "true"
        ],
        "note": "Stage-2 strata are bounded local D-module probes. They are not promoted to Betti/rank claims unless deRham payloads return explicitly.",
    }


def build_report(
    dim: int,
    signature: str,
    fields: tuple[int, ...],
    out_dir: Path,
    timeout_m2: int,
    timeout_singular: int,
    *,
    stage2_strata: bool = False,
    stage2_timeout: int | None = None,
    stage2_derham0: bool = False,
) -> dict[str, Any]:
    out_dir.mkdir(parents=True, exist_ok=True)
    finite_field = {
        str(p): base.finite_field_count_closed_form(dim, signature, p) for p in fields
    }
    report = {
        "dimension": dim,
        "signature": signature,
        "polynomial": "q(a) * q(b) * q(a-b)",
        "paper_reference": {
            "path": "/home/goutev/Downloads/collection_for_formalization/Bulletin of London Math Soc - 2025 - Branman - Graphical models for topological groups  A case study on countable Stone.pdf",
            "note": "Used as countable-Stone / clopen-cylinder motivation for the mathlib-facing boundary, not as a de Rham certificate.",
        },
        "finite_field": {
            "sampled": finite_field,
            "symbolic": base.finite_field_symbolic_formula(dim, signature),
        },
        "factor_stratification": _run_singular_factor_strata(dim, signature, cwd=ROOT, out_dir=out_dir, timeout=timeout_singular),
        "bernstein_sato_factors": _run_m2_factor_bernstein(dim, signature, cwd=ROOT, out_dir=out_dir, timeout=timeout_m2),
        "full_product_probe": _run_m2_full_product_probe(dim, signature, cwd=ROOT, out_dir=out_dir, timeout=timeout_m2),
        "de_rham_probes": {
            "degree0": _run_m2_de_rham_probe(dim, signature, cwd=ROOT, out_dir=out_dir, timeout=timeout_m2, name="de_rham_degree0", degree=0, method="derham"),
            "full": _run_m2_de_rham_probe(dim, signature, cwd=ROOT, out_dir=out_dir, timeout=timeout_m2, name="de_rham_full", degree=None, method="derham"),
            "dlocalize_ext": _run_m2_de_rham_probe(dim, signature, cwd=ROOT, out_dir=out_dir, timeout=timeout_m2, name="de_rham_dlocalize_ext", degree=None, method="dlocalize-ext"),
        },
    }
    if stage2_strata:
        report["stage2_stratified_m2"] = _run_m2_stage2_strata(
            dim,
            signature,
            cwd=ROOT,
            out_dir=out_dir,
            timeout=stage2_timeout or timeout_m2,
            attempt_derham0=stage2_derham0,
        )
    singular_payload = report["factor_stratification"].get("payload", {})
    if singular_payload:
        try:
            ambient = 2 * dim
            pair_dim = int(singular_payload["dim_pair_qA_qB"])
            triple_dim = int(singular_payload["dim_triple_qA_qB_qC"])
            singular_dim = int(singular_payload["dim_singular_locus"])
            report["derived_strata"] = {
                "ambient_dim": ambient,
                "pair_codim": ambient - pair_dim,
                "triple_codim": ambient - triple_dim,
                "singular_locus_codim": ambient - singular_dim,
            }
        except Exception:
            report["derived_strata"] = {"status": "parse_error"}
    report["summary"] = {
        "rank32_status": "not_assumed",
        "de_rham_closed": all(
            item.get("status") == "ok" and item.get("payload", {}).get("deRham_error") != "true"
            for item in report["de_rham_probes"].values()
        ) and report["full_product_probe"].get("status") == "ok",
        "factor_bernstein_ready": report["bernstein_sato_factors"].get("status") == "ok",
        "next_step": "Use factor strata + factor-level Bernstein-Sato output to guide bounded D-module attempts; do not promote a Betti-rank claim until an actual deRham payload returns.",
    }
    if stage2_strata:
        stage2 = report.get("stage2_stratified_m2", {})
        report["summary"]["stage2_strata_status"] = stage2.get("status")
        report["summary"]["stage2_actual_de_rham_payload_count"] = len(stage2.get("actual_de_rham_payloads", []))
        report["summary"]["stage2_scripts"] = stage2.get("script_dir")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description="Run the factor-stratified Klein-quadric de Rham wrapper")
    parser.add_argument("--dimension", type=int, default=4)
    parser.add_argument("--signature", choices=["euclidean", "minkowski"], default="euclidean")
    parser.add_argument("--fields", default="3,5,7")
    parser.add_argument("--m2-timeout", type=int, default=45)
    parser.add_argument("--singular-timeout", type=int, default=60)
    parser.add_argument(
        "--stage2-strata",
        action="store_true",
        help="Run second-stage Macaulay2 probes on factor/pair/triple strata and emit one script per stratum.",
    )
    parser.add_argument(
        "--stage2-timeout",
        type=int,
        default=None,
        help="Per-stratum Macaulay2 timeout for --stage2-strata; defaults to --m2-timeout.",
    )
    parser.add_argument(
        "--stage2-derham0",
        action="store_true",
        help="Also try deRham(0, localizer) inside each remaining-factor stratum probe.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=ARTIFACT_DIR / "factor_stratified_audit.json",
    )
    args = parser.parse_args()

    fields = tuple(int(piece) for piece in args.fields.split(",") if piece.strip())
    report = build_report(
        args.dimension,
        args.signature,
        fields,
        args.out.parent,
        args.m2_timeout,
        args.singular_timeout,
        stage2_strata=args.stage2_strata,
        stage2_timeout=args.stage2_timeout,
        stage2_derham0=args.stage2_derham0,
    )
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True))
    print(args.out)
    print(json.dumps(report["summary"], indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
