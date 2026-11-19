#!/usr/bin/env python3
"""Reproduce the arithmetic audit of the supplied nine-cartridge radon draft.

This is a descriptive audit, not an inferential uncertainty analysis. Net peak
areas are used exactly as supplied; no Poisson variance model is assumed.
The fixed-claim audit and original exploratory fits retain the source's index
parameterizations. Separate supplementary fits use a common physical endpoint
and cell centers. The original attachment is never changed.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import math
import re
from datetime import datetime
from pathlib import Path

import numpy as np
from scipy.optimize import least_squares


def metrics(y, prediction):
    residual = np.asarray(y) - np.asarray(prediction)
    sse = float(residual @ residual)
    sst = float(np.sum((y - np.mean(y)) ** 2))
    return {
        "sse_cps_squared": sse,
        "rmse_cps": float(np.sqrt(np.mean(residual ** 2))),
        "r_squared_raw_rate": 1 - sse / sst,
        "max_abs_relative_residual": float(np.max(np.abs(residual / y))),
    }


def profile(kind, index, amplitude, mu):
    if kind == "cosh":
        return amplitude * np.cosh(mu * (9.5 - index))
    if kind == "sinh":
        return amplitude * np.sinh(mu * (10 - index))
    if kind == "exp":
        return amplitude * np.exp(-mu * index)
    raise ValueError(kind)


def common_geometry_profile(kind, index, amplitude, mu):
    """Nine equal cells on [0, 9*dx], centers (i-1/2)*dx.

    Amplitude absorbs the common uniform cell-average factor
    2*sinh(mu/2)/mu. No identification with source concentration is implied.
    """
    if kind == "cosh":
        return amplitude * np.cosh(mu * (9.5 - index))
    if kind == "sinh":
        return amplitude * np.sinh(mu * (9.5 - index))
    if kind == "exp":
        return amplitude * np.exp(-mu * (index - 0.5))
    raise ValueError(kind)


def write_csv(path, rows):
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def audit(source, output):
    output.mkdir(parents=True, exist_ok=True)
    source_text = source.read_text(encoding="utf-8")
    embedded = re.search(r"```csv\n(.*?)\n```", source_text, re.S).group(1)
    csv_rows = list(csv.reader(io.StringIO(embedded)))
    numbered_rows = list(enumerate(csv_rows, start=1))
    observed_rows = [(n, row) for n, row in numbered_rows
                     if row and re.fullmatch(r"[1-9]", row[0])]
    assert len(observed_rows) == 9
    lam = float(csv_rows[6][1])
    mu = float(csv_rows[8][1])
    amplitudes = {
        "609": {"cosh": float(csv_rows[11][1]),
                "sinh": float(csv_rows[12][1]),
                "exp": float(csv_rows[13][1])},
        "352": {"cosh": float(csv_rows[14][1]),
                "sinh": float(csv_rows[15][1]),
                "exp": float(csv_rows[16][1])},
    }
    records = []
    for csv_row, row in observed_rows:
        index = int(row[0])
        d = {
            "cartridge": index, "csv_row": csv_row, "start_time": row[1],
            "real_time_min": float(row[2]), "live_time_min": float(row[3]),
            "elapsed_s": int(row[4]), "counts_609": int(row[5]),
            "counts_352": int(row[6]),
            "corrected_rate_basis": "source_start_time_point_correction_no_finite_acquisition_factor",
        }
        for energy in ("609", "352"):
            d[f"raw_rate_{energy}_cps"] = d[f"counts_{energy}"] / (60 * d["live_time_min"])
            d[f"corrected_rate_{energy}_cps"] = d[f"raw_rate_{energy}_cps"] * math.exp(lam * d["elapsed_s"])
            for kind in ("cosh", "sinh", "exp"):
                d[f"fixed_{kind}_{energy}_cps"] = float(profile(kind, index, amplitudes[energy][kind], mu))
        d["peak_ratio_352_to_609"] = d["counts_352"] / d["counts_609"]
        d["linear_factor_source"] = 10 - index
        d["normalized_data_609"] = d["corrected_rate_609_cps"] / d["linear_factor_source"]
        d["normalized_fixed_sinh_609"] = d["fixed_sinh_609_cps"] / d["linear_factor_source"]
        d["dead_time_fraction"] = 1 - d["live_time_min"] / d["real_time_min"]
        duration = 60 * d["real_time_min"]
        d["uniform_live_exposure_finite_acquisition_factor"] = lam * duration / (-math.expm1(-lam * duration))
        records.append(d)
    for k, d in enumerate(records):
        for energy in ("609", "352"):
            d[f"adjacent_ratio_{energy}"] = (
                d[f"corrected_rate_{energy}_cps"] / records[k+1][f"corrected_rate_{energy}_cps"]
                if k < 8 else None)
    t0 = datetime.strptime(records[-1]["start_time"], "%H:%M:%S")
    elapsed_checks = [
        {"cartridge": d["cartridge"], "supplied_elapsed_s": d["elapsed_s"],
         "computed_elapsed_s": int((datetime.strptime(d["start_time"], "%H:%M:%S") - t0).total_seconds())}
        for d in records
    ]
    assert all(d["supplied_elapsed_s"] == d["computed_elapsed_s"] for d in elapsed_checks)

    formula_defects = []
    for actual_row, row in observed_rows:
        for j, expression in enumerate(row, start=1):
            if not expression.startswith("="):
                continue
            col = chr(ord("A") + j - 1)
            # Parameter references with absolute rows must stay unchanged.
            refs = re.findall(r"(?<![A-Z0-9_])\$?[A-Z]+(?!\$)([0-9]+)", expression)
            corrected = re.sub(r"(?<![A-Z0-9_])(\$?[A-Z]+)([0-9]+)",
                               lambda m: m[1] + str(int(m[2])+1), expression)
            formula_defects.append({
                "cell": f"{col}{actual_row}", "original_formula": expression,
                "correct_formula_for_original_layout": corrected,
                "relative_referenced_rows": [int(x) for x in refs],
                "issue": "All relative references were written for a data table starting one row too early.",
            })
    assert len(formula_defects) == 125
    assert formula_defects[0]["correct_formula_for_original_layout"] == "=F21/(D21*60)"
    assert next(d for d in formula_defects if d["cell"] == "P21")["correct_formula_for_original_layout"] == "=$B$12*COSH($B$9*(9.5-A21))"

    fixed_metrics = []
    fitted = []
    index = np.array([d["cartridge"] for d in records], dtype=float)
    for lo, hi in ((1, 9), (2, 9), (2, 8)):
        mask = (index >= lo) & (index <= hi)
        x = index[mask]
        for energy in ("609", "352"):
            y = np.array([d[f"corrected_rate_{energy}_cps"] for d in records])[mask]
            for kind in ("cosh", "sinh", "exp"):
                p = profile(kind, x, amplitudes[energy][kind], mu)
                fixed_metrics.append({"energy_keV": int(energy), "model": kind,
                                      "range": f"{lo}-{hi}", "amplitude": amplitudes[energy][kind],
                                      "mu": mu, **metrics(y, p)})
                # Positive parameterization, repeated starting values to avoid
                # interpreting a single failed local step as an optimum.
                candidates = []
                for initial_mu in (0.3, 0.686, 1.0):
                    basis = profile(kind, x, 1.0, initial_mu)
                    initial_a = float(basis @ y / (basis @ basis))
                    result = least_squares(
                        lambda z: profile(kind, x, np.exp(z[0]), np.exp(z[1])) - y,
                        np.log([initial_a, initial_mu]),
                        bounds=([-30, -12], [30, math.log(3)]),
                        max_nfev=5000, ftol=1e-13, xtol=1e-13, gtol=1e-13,
                    )
                    candidates.append(result)
                fit = min(candidates, key=lambda z: float(z.fun @ z.fun))
                a_fit, mu_fit = np.exp(fit.x)
                pred = profile(kind, x, a_fit, mu_fit)
                fitted.append({"energy_keV": int(energy), "model": kind,
                               "range": f"{lo}-{hi}", "objective": "unweighted squared residuals of corrected rates",
                               "amplitude": float(a_fit), "mu": float(mu_fit),
                               "optimizer_success": bool(fit.success), **metrics(y, pred)})
            coefficient, intercept = np.polyfit(x, np.log(y), 1)
            pred = np.exp(intercept + coefficient * x)
            fitted.append({"energy_keV": int(energy), "model": "exp",
                           "range": f"{lo}-{hi}", "objective": "unweighted squared residuals of log corrected rates",
                           "amplitude": float(np.exp(intercept)), "mu": float(-coefficient),
                           "optimizer_success": True, **metrics(y, pred)})

    # Supplementary comparison only. Preserve the source-claim audit above.
    common_fits = []
    for lo, hi in ((1, 9), (2, 9)):
        mask = (index >= lo) & (index <= hi)
        x = index[mask]
        for energy in ("609", "352"):
            y = np.array([d[f"corrected_rate_{energy}_cps"] for d in records])[mask]
            for kind in ("cosh", "sinh", "exp"):
                for scale in ("rate", "log_rate"):
                    def residual(z):
                        predicted = common_geometry_profile(kind, x, np.exp(z[0]), np.exp(z[1]))
                        return predicted - y if scale == "rate" else np.log(predicted) - np.log(y)

                    candidates = []
                    for initial_mu in (0.3, 0.686, 1.0):
                        basis = common_geometry_profile(kind, x, 1.0, initial_mu)
                        initial_a = (float(basis @ y / (basis @ basis)) if scale == "rate"
                                     else float(np.exp(np.mean(np.log(y)-np.log(basis)))))
                        result = least_squares(
                            residual, np.log([initial_a, initial_mu]),
                            bounds=([-30, -12], [30, math.log(3)]),
                            max_nfev=5000, ftol=1e-13, xtol=1e-13, gtol=1e-13,
                        )
                        candidates.append(result)
                    fit = min(candidates, key=lambda z: float(z.fun @ z.fun))
                    a_fit, mu_fit = np.exp(fit.x)
                    pred = common_geometry_profile(kind, x, a_fit, mu_fit)
                    average_factor = 2 * np.sinh(mu_fit / 2) / mu_fit
                    common_fits.append({
                        "energy_keV": int(energy), "model": kind, "range": f"{lo}-{hi}",
                        "objective": "unweighted_squared_" + scale + "_residuals",
                        "rate_basis": "source_start_time_point_correction_no_finite_acquisition_factor",
                        "cell_average_shape_amplitude_cps": float(a_fit),
                        "center_profile_amplitude_if_uniform_cell_response_cps": float(a_fit / average_factor),
                        "mu": float(mu_fit),
                        "uniform_cell_average_factor": float(average_factor),
                        "optimizer_success": bool(fit.success),
                        "sse_log_rate": float(np.sum((np.log(pred)-np.log(y))**2)),
                        **metrics(y, pred),
                    })

    table_rows = []
    for line in source_text.splitlines():
        if re.match(r"\| \*\*[1-9]\*\* \|", line):
            values = [float(x.strip().replace("*", "")) for x in line.split("|")[1:-1]]
            table_rows.append(values)
    expected_keys = ["cartridge", "elapsed_s", "corrected_rate_609_cps",
                     "fixed_cosh_609_cps", "fixed_sinh_609_cps", "normalized_data_609",
                     "normalized_fixed_sinh_609", "corrected_rate_352_cps", "fixed_cosh_352_cps"]
    table_comparisons = []
    for supplied, record in zip(table_rows, records, strict=True):
        for key, value in zip(expected_keys[2:], supplied[2:], strict=True):
            expected = record[key]
            table_comparisons.append({
                "cartridge": record["cartridge"], "quantity": key,
                "supplied": value, "recomputed": expected,
                "recomputed_at_supplied_precision": round(expected, 2),
                "difference_supplied_minus_recomputed": value - expected,
                "agrees_to_2_decimals": value == round(expected, 2),
            })
    peak_first8 = np.array([d["peak_ratio_352_to_609"] for d in records[:8]])
    adjacent_summaries = []
    for energy in ("609", "352"):
        for lo, hi in ((2, 7), (2, 8)):
            ratios = np.array([d[f"adjacent_ratio_{energy}"] for d in records if lo <= d["cartridge"] <= hi])
            adjacent_summaries.append({"energy_keV": int(energy),
                                       "ratio_numerator_cartridges": f"{lo}-{hi}",
                                       "ratios": ratios.tolist(), "mean": float(np.mean(ratios)),
                                       "sample_sd": float(np.std(ratios, ddof=1)),
                                       "geometric_mean": float(np.exp(np.mean(np.log(ratios))))})

    report = {
        "source": {"name": source.name, "sha256": hashlib.sha256(source.read_bytes()).hexdigest()},
        "method": {
            "rates": "net peak area / 900 s times exp(supplied lambda * supplied elapsed start-time seconds)",
            "rate_basis": "source start-time point correction of acquisition-averaged rates; the finite-acquisition factor is NOT applied",
            "lambda_s_inverse": lam,
            "lambda_from_supplied_half_life": math.log(2)/(3.8235*86400),
            "fixed_fit_geometry": "source index formulas: cosh(mu*(9.5-i)), sinh(mu*(10-i)), exp(-mu*i)",
            "r_squared": "1 - sum((observed-predicted)^2)/sum((observed-mean(observed))^2), on untransformed rates",
            "inference": "descriptive only; no experimental uncertainty, background model, efficiency correction, or daughter equilibrium assumed",
        },
        "data": records,
        "elapsed_time_checks": elapsed_checks,
        "spreadsheet_audit": {
            "header_row": 20, "first_data_row": 21, "last_data_row": 29,
            "incorrect_data_formula_count": len(formula_defects),
            "formula_defects": formula_defects,
            "other_issues": [
                "A19 says data occupy rows 20-28; actual data occupy 21-29.",
                "D10 (= dx / mu) and D11 (= lambda * Ld^2) are intended descriptions but parse as formulas with undefined names if imported as formulas.",
                "CSV carries literal strings, without workbook cell types, styles, or guarantee that a chosen Excel import route evaluates formulas.",
                "B8=1.50 cm is explicitly a placeholder; it is not a confirmed measurement.",
            ],
        },
        "fixed_fit_metrics": fixed_metrics,
        "exploratory_refits": fitted,
        "common_geometry_refit_method": {
            "geometry": "9 equal cells covering [0,9*dx], with common centers x_i=(i-1/2)*dx",
            "profiles": "cosh(mu*(9.5-i)), sinh(mu*(9.5-i)), exp(-mu*(i-0.5))",
            "amplitude": "free positive amplitude absorbs uniform whole-cell factor 2*sinh(mu/2)/mu",
            "objectives": "separate unweighted squared rate residuals and unweighted squared log-rate residuals",
            "rate_basis": "same source start-time point-corrected rates as the fixed-claim audit; no finite-acquisition factor applied",
            "interpretation": "descriptive sensitivity comparison; no test, confidence interval, equilibrium determination, or calibrated concentration estimate",
            "exclusion": "range 2-9 repeats the draft's exclusion of cartridge1; range1-9 provides a sensitivity comparison without that exclusion",
        },
        "common_geometry_exploratory_refits": common_fits,
        "summary_table_comparisons": table_comparisons,
        "summary_table_disagreement_count": sum(not d["agrees_to_2_decimals"] for d in table_comparisons),
        "peak_ratio_first8": {"mean": float(np.mean(peak_first8)), "sample_sd": float(np.std(peak_first8, ddof=1)),
                               "minimum": float(np.min(peak_first8)), "maximum": float(np.max(peak_first8))},
        "adjacent_ratio_summaries": adjacent_summaries,
        "parameter_arithmetic": {"mu": mu, "exp_mu": math.exp(mu), "Ld_per_dx": 1/mu,
                                 "Ld_cm_if_dx_1_50_cm": 1.5/mu,
                                 "De_m2_s_if_dx_1_50_cm": lam*(0.015/mu)**2},
    }
    (output / "radon_audit.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    write_csv(output / "recomputed_rates_and_models.csv", records)
    write_csv(output / "fixed_fit_metrics.csv", fixed_metrics)
    write_csv(output / "exploratory_refits.csv", fitted)
    write_csv(output / "common_geometry_exploratory_refits.csv", common_fits)
    write_csv(output / "summary_table_comparisons.csv", table_comparisons)
    write_csv(output / "spreadsheet_formula_corrections.csv", formula_defects)
    compact = {key: report[key] for key in (
        "method", "peak_ratio_first8", "adjacent_ratio_summaries", "parameter_arithmetic",
        "summary_table_disagreement_count")}
    compact["fixed_fit_metrics_range_2_9"] = [r for r in fixed_metrics if r["range"] == "2-9"]
    compact["exploratory_refits_range_2_9"] = [r for r in fitted if r["range"] == "2-9"]
    compact["rates_and_ratios"] = [{key: r[key] for key in
                                   ("cartridge", "corrected_rate_609_cps", "corrected_rate_352_cps",
                                    "adjacent_ratio_609", "adjacent_ratio_352", "peak_ratio_352_to_609")}
                                  for r in records]
    print(json.dumps(compact, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    options = parser.parse_args()
    audit(options.source, options.output)
