#!/usr/bin/env python3
"""Numerical conformance checks for LLM thermo/operator identities.

This script audits runtime trace rows against the finite owner lane identities:
- softmax simplex normalization
- softmax = Gibbs/KMS weights (when energies are present)
- log-partition / Massieu consistency
- entropy/free-energy identities
- defect-lane quarantine checks (when defect metrics are present)

Input format: JSONL (one trace row per line).
"""

from __future__ import annotations

import argparse
import json
import math
import statistics
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.append(str(Path(__file__).resolve().parents[2]))

try:
    import jsonschema
except Exception:
    jsonschema = None


@dataclass
class CheckAccumulator:
    name: str
    theorem_ref: str
    count: int = 0
    passed: int = 0
    residuals: list[float] = field(default_factory=list)

    def add(self, residual: float, ok: bool) -> None:
        self.count += 1
        if ok:
            self.passed += 1
        self.residuals.append(float(abs(residual)))

    @property
    def failed(self) -> int:
        return self.count - self.passed


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Audit runtime LLM traces against thermo identities")
    parser.add_argument("--input", required=True, help="Input JSONL with runtime trace rows")
    parser.add_argument("--json-out", default="reports/llm/thermo_conformance.json")
    parser.add_argument("--md-out", default="reports/llm/thermo_conformance.md")
    parser.add_argument("--abs-tol", type=float, default=1e-6)
    parser.add_argument("--rel-tol", type=float, default=1e-6)
    parser.add_argument("--nonneg-tol", type=float, default=1e-12)
    parser.add_argument("--max-violations", type=int, default=200)
    parser.add_argument("--schema", default="tools/schema/llm_thermo_trace.schema.json")
    parser.add_argument(
        "--strict-schema",
        action="store_true",
        help="Treat schema-invalid rows as hard failures in the summary",
    )
    parser.add_argument(
        "--fail-on-violation",
        action="store_true",
        help="Exit non-zero when any conformance check fails",
    )
    return parser.parse_args()


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        s = line.strip()
        if not s:
            continue
        try:
            row = json.loads(s)
        except json.JSONDecodeError:
            continue
        if isinstance(row, dict):
            row.setdefault("_line_no", line_no)
            rows.append(row)
    return rows


def as_float(v: Any) -> float | None:
    if isinstance(v, bool):
        return None
    if isinstance(v, (int, float)):
        x = float(v)
        if math.isfinite(x):
            return x
    return None


def as_float_list(v: Any) -> list[float] | None:
    if not isinstance(v, list):
        return None
    out: list[float] = []
    for item in v:
        x = as_float(item)
        if x is None:
            return None
        out.append(x)
    return out


def logsumexp(xs: list[float]) -> float:
    if not xs:
        return float("-inf")
    m = max(xs)
    if not math.isfinite(m):
        return m
    return m + math.log(sum(math.exp(x - m) for x in xs))


def softmax_from_logits(logits: list[float]) -> list[float]:
    if not logits:
        return []
    lse = logsumexp(logits)
    return [math.exp(x - lse) for x in logits]


def close(lhs: float, rhs: float, abs_tol: float, rel_tol: float) -> tuple[bool, float, float]:
    residual = abs(lhs - rhs)
    tol = abs_tol + rel_tol * max(1.0, abs(rhs))
    return residual <= tol, residual, tol


def pct(values: list[float], q: float) -> float:
    if not values:
        return 0.0
    if len(values) == 1:
        return values[0]
    xs = sorted(values)
    k = (len(xs) - 1) * q
    f = int(k)
    c = min(f + 1, len(xs) - 1)
    if f == c:
        return xs[f]
    return xs[f] + (xs[c] - xs[f]) * (k - f)


def row_id(row: dict[str, Any], idx: int) -> str:
    explicit = row.get("trace_id")
    if isinstance(explicit, str) and explicit.strip():
        return explicit
    line_no = row.get("_line_no")
    return f"row:{idx + 1}@line:{line_no}"


def schema_validator(schema_path: Path):
    if jsonschema is None or not schema_path.exists():
        return None
    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    return jsonschema.Draft202012Validator(schema)


def main() -> int:
    args = parse_args()

    input_path = Path(args.input)
    if not input_path.exists():
        print(f"input not found: {input_path}", file=sys.stderr)
        return 2

    rows = load_jsonl(input_path)

    checks: dict[str, CheckAccumulator] = {
        "softmaxWeight_sum_one": CheckAccumulator(
            "softmaxWeight_sum_one",
            "InfoGeometry.LLM.KMSSoftmaxBridge.softmaxWeight_sum_one",
        ),
        "softmaxWeight_nonneg": CheckAccumulator(
            "softmaxWeight_nonneg",
            "InfoGeometry.LLM.ThermodynamicSwitching.maskedNormalizedWeight_nonneg (all-top specialization)",
        ),
        "softmaxWeight_eq_kmsWeight": CheckAccumulator(
            "softmaxWeight_eq_kmsWeight",
            "InfoGeometry.LLM.KMSSoftmaxBridge.softmaxWeight_eq_kmsWeight",
        ),
        "softmaxWeight_eq_logitsSoftmax": CheckAccumulator(
            "softmaxWeight_eq_logitsSoftmax",
            "InfoGeometry.LLM.KMSSoftmaxBridge.softmaxWeight_eq_exp_routerLogit_div_partition",
        ),
        "partition_eq_sum_exp_logit": CheckAccumulator(
            "partition_eq_sum_exp_logit",
            "InfoGeometry.LLM.ThermodynamicSwitching.routerPartition_eq_exp_logSumExp",
        ),
        "kmsLogPartition_eq_logSumExpRouter": CheckAccumulator(
            "kmsLogPartition_eq_logSumExpRouter",
            "InfoGeometry.LLM.KMSSoftmaxBridge.kmsLogPartition_eq_logSumExpRouter",
        ),
        "internalEnergy_weighted_sum": CheckAccumulator(
            "internalEnergy_weighted_sum",
            "InfoGeometry.Thermo.FiniteDiagonal.internalEnergy",
        ),
        "entropy_from_weights": CheckAccumulator(
            "entropy_from_weights",
            "InfoGeometry.Thermo.FiniteDiagonal.entropy",
        ),
        "kmsEntropy_eq_beta_internal_plus_logPartition": CheckAccumulator(
            "kmsEntropy_eq_beta_internal_plus_logPartition",
            "InfoGeometry.LLM.KMSSoftmaxBridge.kmsEntropy_eq_beta_internal_plus_logPartition",
        ),
        "beta_mul_routerFreeEnergy_eq_neg_kmsLogPartition": CheckAccumulator(
            "beta_mul_routerFreeEnergy_eq_neg_kmsLogPartition",
            "InfoGeometry.LLM.KMSSoftmaxBridge.beta_mul_routerFreeEnergy_eq_neg_kmsLogPartition",
        ),
        "routerFreeEnergyEps_eq_neg_eps_kmsLogPartition": CheckAccumulator(
            "routerFreeEnergyEps_eq_neg_eps_kmsLogPartition",
            "InfoGeometry.LLM.KMSSoftmaxBridge.routerFreeEnergyEps_eq_neg_eps_kmsLogPartition",
        ),
        "defect_quarantined_on_mixed_input": CheckAccumulator(
            "defect_quarantined_on_mixed_input",
            "InfoGeometry.LLM.PromptDefectRegularization.defect_quarantined_on_mixed_input",
        ),
        "defect_weight_sum_zero": CheckAccumulator(
            "defect_weight_sum_zero",
            "InfoGeometry.LLM.TrialityMoE.SparseRouter.defectWeight_eq_zero",
        ),
        "active_plus_defect_sum_one": CheckAccumulator(
            "active_plus_defect_sum_one",
            "InfoGeometry.LLM.TrialityMoE.SparseRouter.router_weight_split",
        ),
    }

    violations: list[dict[str, Any]] = []
    schema_errors = 0

    validator = schema_validator(Path(args.schema))

    for idx, row in enumerate(rows):
        rid = row_id(row, idx)

        if validator is not None:
            errs = list(validator.iter_errors(row))
            if errs:
                schema_errors += 1
                if len(violations) < args.max_violations:
                    violations.append(
                        {
                            "row": rid,
                            "check": "schema",
                            "residual": None,
                            "tolerance": None,
                            "message": errs[0].message,
                        }
                    )
                if args.strict_schema:
                    continue

        beta = as_float(row.get("beta"))
        weights = as_float_list(row.get("weights"))
        energies = as_float_list(row.get("energies"))
        logits = as_float_list(row.get("logits"))
        partition = as_float(row.get("partition"))
        massieu = as_float(row.get("massieu"))
        internal_energy = as_float(row.get("internal_energy"))
        entropy = as_float(row.get("entropy"))
        free_energy = as_float(row.get("free_energy"))
        epsilon = as_float(row.get("epsilon"))
        free_energy_eps = as_float(row.get("free_energy_eps"))
        kms_log_partition = as_float(row.get("kms_log_partition"))
        defect_output_norm = as_float(row.get("defect_output_norm"))
        defect_weight_sum = as_float(row.get("defect_weight_sum"))
        active_weight_sum = as_float(row.get("active_weight_sum"))

        def report_failure(name: str, residual: float, tolerance: float, message: str) -> None:
            if len(violations) < args.max_violations:
                violations.append(
                    {
                        "row": rid,
                        "check": name,
                        "residual": residual,
                        "tolerance": tolerance,
                        "message": message,
                    }
                )

        if weights is not None and weights:
            sum_w = sum(weights)
            ok, residual, tol = close(sum_w, 1.0, args.abs_tol, args.rel_tol)
            checks["softmaxWeight_sum_one"].add(residual, ok)
            if not ok:
                report_failure("softmaxWeight_sum_one", residual, tol, f"sum(weights)={sum_w}")

            min_w = min(weights)
            residual_nonneg = max(0.0, -min_w)
            ok_nonneg = min_w >= -args.nonneg_tol
            checks["softmaxWeight_nonneg"].add(residual_nonneg, ok_nonneg)
            if not ok_nonneg:
                report_failure(
                    "softmaxWeight_nonneg",
                    residual_nonneg,
                    args.nonneg_tol,
                    f"min(weights)={min_w}",
                )

        if logits is not None and logits:
            if partition is not None:
                partition_hat = math.exp(logsumexp(logits))
                ok, residual, tol = close(partition_hat, partition, args.abs_tol, args.rel_tol)
                checks["partition_eq_sum_exp_logit"].add(residual, ok)
                if not ok:
                    report_failure(
                        "partition_eq_sum_exp_logit",
                        residual,
                        tol,
                        f"partition_hat={partition_hat}, partition={partition}",
                    )

            if weights is not None and len(weights) == len(logits):
                weights_hat = softmax_from_logits(logits)
                max_diff = max(abs(a - b) for a, b in zip(weights_hat, weights)) if weights else 0.0
                tol = args.abs_tol + args.rel_tol
                ok = max_diff <= tol
                checks["softmaxWeight_eq_logitsSoftmax"].add(max_diff, ok)
                if not ok:
                    report_failure(
                        "softmaxWeight_eq_logitsSoftmax",
                        max_diff,
                        tol,
                        "weights != softmax(logits)",
                    )

        if beta is not None and energies is not None and weights is not None and len(energies) == len(weights):
            logits_from_energy = [-beta * e for e in energies]
            gibbs_hat = softmax_from_logits(logits_from_energy)
            max_diff = max(abs(a - b) for a, b in zip(gibbs_hat, weights)) if weights else 0.0
            tol = args.abs_tol + args.rel_tol
            ok = max_diff <= tol
            checks["softmaxWeight_eq_kmsWeight"].add(max_diff, ok)
            if not ok:
                report_failure(
                    "softmaxWeight_eq_kmsWeight",
                    max_diff,
                    tol,
                    "weights != Gibbs(beta, energies)",
                )

        if massieu is not None and partition is not None and partition > 0:
            massieu_hat = math.log(partition)
            ok, residual, tol = close(massieu_hat, massieu, args.abs_tol, args.rel_tol)
            checks["kmsLogPartition_eq_logSumExpRouter"].add(residual, ok)
            if not ok:
                report_failure(
                    "kmsLogPartition_eq_logSumExpRouter",
                    residual,
                    tol,
                    f"log(partition)={massieu_hat}, massieu={massieu}",
                )

        if internal_energy is not None and weights is not None and energies is not None and len(weights) == len(energies):
            u_hat = sum(w * e for w, e in zip(weights, energies))
            ok, residual, tol = close(u_hat, internal_energy, args.abs_tol, args.rel_tol)
            checks["internalEnergy_weighted_sum"].add(residual, ok)
            if not ok:
                report_failure(
                    "internalEnergy_weighted_sum",
                    residual,
                    tol,
                    f"U_hat={u_hat}, internal_energy={internal_energy}",
                )

        if entropy is not None and weights is not None and weights:
            tiny = 1e-300
            s_hat = -sum(w * math.log(max(w, tiny)) for w in weights)
            ok, residual, tol = close(s_hat, entropy, args.abs_tol, args.rel_tol)
            checks["entropy_from_weights"].add(residual, ok)
            if not ok:
                report_failure(
                    "entropy_from_weights",
                    residual,
                    tol,
                    f"S_hat={s_hat}, entropy={entropy}",
                )

        if entropy is not None and beta is not None and internal_energy is not None and massieu is not None:
            rhs = beta * internal_energy + massieu
            ok, residual, tol = close(entropy, rhs, args.abs_tol, args.rel_tol)
            checks["kmsEntropy_eq_beta_internal_plus_logPartition"].add(residual, ok)
            if not ok:
                report_failure(
                    "kmsEntropy_eq_beta_internal_plus_logPartition",
                    residual,
                    tol,
                    f"entropy={entropy}, beta*U+psi={rhs}",
                )

        if free_energy is not None and beta is not None and massieu is not None and abs(beta) > args.abs_tol:
            lhs = beta * free_energy
            rhs = -massieu
            ok, residual, tol = close(lhs, rhs, args.abs_tol, args.rel_tol)
            checks["beta_mul_routerFreeEnergy_eq_neg_kmsLogPartition"].add(residual, ok)
            if not ok:
                report_failure(
                    "beta_mul_routerFreeEnergy_eq_neg_kmsLogPartition",
                    residual,
                    tol,
                    f"beta*F={lhs}, -psi={rhs}",
                )

        if epsilon is not None and free_energy_eps is not None and kms_log_partition is not None:
            lhs = free_energy_eps
            rhs = -epsilon * kms_log_partition
            ok, residual, tol = close(lhs, rhs, args.abs_tol, args.rel_tol)
            checks["routerFreeEnergyEps_eq_neg_eps_kmsLogPartition"].add(residual, ok)
            if not ok:
                report_failure(
                    "routerFreeEnergyEps_eq_neg_eps_kmsLogPartition",
                    residual,
                    tol,
                    f"F_eps={lhs}, -eps*psi={rhs}",
                )

        if defect_output_norm is not None:
            ok, residual, tol = close(defect_output_norm, 0.0, args.abs_tol, args.rel_tol)
            checks["defect_quarantined_on_mixed_input"].add(residual, ok)
            if not ok:
                report_failure(
                    "defect_quarantined_on_mixed_input",
                    residual,
                    tol,
                    f"defect_output_norm={defect_output_norm}",
                )

        if defect_weight_sum is not None:
            ok, residual, tol = close(defect_weight_sum, 0.0, args.abs_tol, args.rel_tol)
            checks["defect_weight_sum_zero"].add(residual, ok)
            if not ok:
                report_failure(
                    "defect_weight_sum_zero",
                    residual,
                    tol,
                    f"defect_weight_sum={defect_weight_sum}",
                )

        if active_weight_sum is not None and defect_weight_sum is not None:
            lhs = active_weight_sum + defect_weight_sum
            ok, residual, tol = close(lhs, 1.0, args.abs_tol, args.rel_tol)
            checks["active_plus_defect_sum_one"].add(residual, ok)
            if not ok:
                report_failure(
                    "active_plus_defect_sum_one",
                    residual,
                    tol,
                    f"active+defect={lhs}",
                )

    used_checks = {name: acc for name, acc in checks.items() if acc.count > 0}
    total_check_rows = sum(acc.count for acc in used_checks.values())
    total_failed = sum(acc.failed for acc in used_checks.values())

    summary_checks: dict[str, dict[str, Any]] = {}
    for name, acc in sorted(used_checks.items()):
        residuals = sorted(acc.residuals)
        summary_checks[name] = {
            "theorem_ref": acc.theorem_ref,
            "count": acc.count,
            "passed": acc.passed,
            "failed": acc.failed,
            "pass_rate": (acc.passed / acc.count) if acc.count else 1.0,
            "max_abs_residual": residuals[-1] if residuals else 0.0,
            "p95_abs_residual": pct(residuals, 0.95),
            "mean_abs_residual": statistics.fmean(residuals) if residuals else 0.0,
        }

    report = {
        "input": str(input_path),
        "rows": len(rows),
        "schema": {
            "path": str(args.schema),
            "strict": args.strict_schema,
            "jsonschema_available": jsonschema is not None,
            "schema_errors": schema_errors,
        },
        "tolerances": {
            "abs_tol": args.abs_tol,
            "rel_tol": args.rel_tol,
            "nonneg_tol": args.nonneg_tol,
        },
        "checks": summary_checks,
        "totals": {
            "check_instances": total_check_rows,
            "failed_instances": total_failed,
            "overall_pass_rate": ((total_check_rows - total_failed) / total_check_rows)
            if total_check_rows
            else 1.0,
        },
        "violations": violations,
    }

    json_out = Path(args.json_out)
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(report, ensure_ascii=True, indent=2) + "\n", encoding="utf-8")

    md_out = Path(args.md_out)
    md_out.parent.mkdir(parents=True, exist_ok=True)

    md_lines: list[str] = []
    md_lines.append("# LLM Thermo Conformance Report")
    md_lines.append("")
    md_lines.append(f"- input: `{input_path}`")
    md_lines.append(f"- rows: `{len(rows)}`")
    md_lines.append(f"- check instances: `{total_check_rows}`")
    md_lines.append(f"- failed instances: `{total_failed}`")
    md_lines.append(f"- overall pass rate: `{report['totals']['overall_pass_rate']:.6f}`")
    md_lines.append(f"- schema errors: `{schema_errors}`")
    md_lines.append("")
    md_lines.append("## Per-check summary")
    md_lines.append("")
    md_lines.append("| Check | Theorem Ref | Count | Failed | Max | P95 |")
    md_lines.append("|---|---|---:|---:|---:|---:|")
    for name, row in summary_checks.items():
        md_lines.append(
            f"| `{name}` | `{row['theorem_ref']}` | `{row['count']}` | `{row['failed']}` | "
            f"`{row['max_abs_residual']:.6g}` | `{row['p95_abs_residual']:.6g}` |"
        )

    md_lines.append("")
    md_lines.append("## Violations")
    md_lines.append("")
    if violations:
        for v in violations:
            md_lines.append(
                f"- `{v['row']}` `{v['check']}` residual=`{v['residual']}` tol=`{v['tolerance']}` {v['message']}"
            )
    else:
        md_lines.append("- none")

    md_out.write_text("\n".join(md_lines) + "\n", encoding="utf-8")

    print(json_out)
    print(md_out)

    if args.fail_on_violation and (total_failed > 0 or (args.strict_schema and schema_errors > 0)):
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
