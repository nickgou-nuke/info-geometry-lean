#!/usr/bin/env python3
"""Reconcile the decimal five-line and compact rounded two-line fixtures.

All normalization, regression, and control calculations use Python binary64
with math.fsum and stable logsumexp. NumPy is used only for descriptive SVD.
No uncertainty intervals or physical mechanisms are inferred.
"""
from __future__ import annotations

import argparse
import csv
from decimal import Decimal
import hashlib
import json
import math
from pathlib import Path
import platform
import numpy as np
from fixtures import (DATA_DIR, DEFAULT_OUTPUT_DIR, ROUNDED_ORIGINAL_SHA,
                      public_path, read_reference, read_rounded_fixture)

CHANNELS = ["77", "242", "295", "352", "609"]
SUBSETS = {"all5": CHANNELS, "gamma4": CHANNELS[1:],
           "pb3": ["242", "295", "352"], "pb_bi2": ["352", "609"]}
SOURCE_SHA = "30a4bc1781ebade1636f74fe3703faea04d5584d72b4a178cc84f4bd11e6fa6d"
ROUNDED_SHA = ROUNDED_ORIGINAL_SHA


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def avg(values):
    return math.fsum(values) / len(values)


def center(values):
    mean = avg(values)
    return [x - mean for x in values]


def lse(values):
    top = max(values)
    return top + math.log(math.fsum(math.exp(x - top) for x in values))


def geo(log_matrix):
    rows = [avg(row) for row in log_matrix]
    grand = avg(rows)
    columns = [avg([row[j] for row in log_matrix]) for j in range(len(log_matrix[0]))]
    interaction = [[x - rows[i] - columns[j] + grand for j, x in enumerate(row)]
                   for i, row in enumerate(log_matrix)]
    return {"log_sample": [x-grand for x in rows],
            "log_line": [x-grand for x in columns],
            "log_global": grand, "interaction": interaction}


def sinkhorn(log_matrix, tolerance=5e-14, max_iterations=1000):
    m, n = len(log_matrix), len(log_matrix[0])
    assert m > 0 and n > 0 and all(len(row) == n for row in log_matrix)
    assert all(math.isfinite(x) for row in log_matrix for x in row)
    lr, lc = -math.log(m), -math.log(n)
    beta = [0.0] * n
    history = []
    for iteration in range(1, max_iterations + 1):
        alpha = [lr-lse([x+beta[j] for j, x in enumerate(row)]) for row in log_matrix]
        beta = [lc-lse([log_matrix[i][j]+alpha[i] for i in range(m)]) for j in range(n)]
        logp = [[x+alpha[i]+beta[j] for j, x in enumerate(row)] for i, row in enumerate(log_matrix)]
        re = max(abs(math.expm1(lse(row)-lr)) for row in logp)
        ce = max(abs(math.expm1(lse([row[j] for row in logp])-lc)) for j in range(n))
        history.append([iteration, re, ce])
        if max(re, ce) <= tolerance:
            break
    else:
        raise ArithmeticError("Sinkhorn failed to reach the stated tolerance")
    return {"log_sample": center([-x for x in alpha]),
            "log_line": center([-x for x in beta]),
            "plan": [[math.exp(x) for x in row] for row in logp],
            "log_plan": logp, "iterations": iteration, "history": history}


def slope(xs, values):
    xc, yc = center(xs), center(values)
    return math.fsum(x*y for x, y in zip(xc, yc)) / math.fsum(x*x for x in xc)


def fit(xs, values):
    b = slope(xs, values)
    a = avg(values) - b*avg(xs)
    h = [y-a-b*x for x, y in zip(xs, values)]
    return {"mu": -b, "intercept": a, "residual_log": h,
            "max_abs_relative_residual": max(abs(math.expm1(x)) for x in h),
            "sum_squared_log_residual": math.fsum(x*x for x in h),
            "algebraic_residual_dimension": len(xs)-2}


def max_relative(a, b):
    aa, bb = center(a), center(b)
    d = [x-y for x, y in zip(aa, bb)]
    return {"max_abs_relative": max(abs(math.expm1(x)) for x in d),
            "max_abs_percent": 100*max(abs(math.expm1(x)) for x in d),
            "centered_log_difference": d}


def read_decimal(path):
    assert sha(path) == SOURCE_SHA, "five-line source hash changed"
    rows = list(csv.reader(path.open(newline="", encoding="utf-8-sig")))
    lam = Decimal(next(row[1] for row in rows if row and row[0] == "Rn-222 Decay Constant (lambda)"))
    start = next(i for i, row in enumerate(rows) if row and row[0] == "Cartridge (i)")
    records = []
    for row in rows[start+1:]:
        records.append({"cartridge": int(row[0]), "start_time": row[1],
                        "real_seconds": Decimal(row[2])*60,
                        "live_seconds": Decimal(row[3]), "elapsed_seconds": Decimal(row[4]),
                        "areas": dict(zip(CHANNELS, map(Decimal, row[5:10])))})
    assert [row["cartridge"] for row in records] == list(range(1,10))
    return records, lam


def log_rates(records, channels, lam, finite=False):
    matrix = []
    for row in records:
        common = -math.log(float(row["live_seconds"])) + float(lam*row["elapsed_seconds"])
        if finite:
            u = float(lam*row["real_seconds"])
            common += math.log(u/(-math.expm1(-u)))
        matrix.append([math.log(float(row["areas"][c])) + common for c in channels])
    return matrix


def energy_metrics(log_matrix, indices):
    g = geo(log_matrix)
    h = fit(indices, [avg(row) for row in log_matrix])
    E = g["interaction"]
    ez = math.fsum(x*x for row in E for x in row)
    eh = len(log_matrix[0])*h["sum_squared_log_residual"]
    singular = np.linalg.svd(np.array(E), compute_uv=False)
    return {"max_abs_interaction": max(abs(x) for row in E for x in row),
            "rms_interaction": math.sqrt(ez/(len(E)*len(E[0]))),
            "interaction_energy": ez, "common_spatial_energy": eh,
            "common_fraction_among_common_plus_interaction": eh/(eh+ez),
            "interaction_dimension": (len(E)-1)*(len(E[0])-1),
            "common_residual_dimension": len(E)-2,
            "singular_values": singular.tolist(),
            "leading_squared_singular_share": float(singular[0]**2/np.sum(singular**2)),
            "common_fit": h, "interaction": E}


def domains(records, channels, lam):
    L = log_rates(records, channels, lam)
    LS = L[1:8]
    fullg, fulls, intg, ints = geo(L), sinkhorn(L), geo(LS), sinkhorn(LS)
    fullgS, fullsS = fullg["log_sample"][1:8], fulls["log_sample"][1:8]
    geom_constant = [x-y for x, y in zip(fullgS, intg["log_sample"])]
    assert max(geom_constant)-min(geom_constant) < 4e-15
    full_mu = fit(list(range(2,9)), fullgS)["mu"]
    int_mu = fit(list(range(2,9)), intg["log_sample"])["mu"]
    assert abs(full_mu-int_mu) < 5e-15
    # Restricting full Q and multiplying by 9/7 restores row mass but generally
    # fails to restore the desired line-column margins.
    restricted_plan = [[(9/7)*v for v in row] for row in fulls["plan"][1:8]]
    residual_columns = [math.fsum(row[j] for row in restricted_plan)*len(channels)-1
                        for j in range(len(channels))]
    finite_L = log_rates(records, channels, lam, finite=True)
    finite_s = sinkhorn(finite_L[1:8])
    finite_g = geo(finite_L[1:8])
    field_change = max(abs(x-y) for a,b in zip(finite_g["interaction"],intg["interaction"])
                       for x,y in zip(a,b))
    assert field_change < 5e-15
    return {
        "channels": channels, "normalization_domains": {"all": list(range(1,10)), "interior": list(range(2,9))},
        "baseline": "point corrected rates N/live*exp(lambda*elapsed)",
        "full9": {"geometric": fullg, "sinkhorn": fulls,
                  "all9_method_difference": max_relative(fulls["log_sample"], fullg["log_sample"]),
                  "interaction": energy_metrics(L, list(range(1,10)))},
        "interior7": {"geometric": intg, "sinkhorn": ints,
                      "method_difference": max_relative(ints["log_sample"],intg["log_sample"]),
                      "interaction": energy_metrics(LS, list(range(2,9)))},
        "full9_restricted_and_recentered_to_interior": {
            "method_difference": max_relative(fullsS, fullgS),
            "geometric_vs_refit_interior": max_relative(fullgS,intg["log_sample"]),
            "sinkhorn_vs_refit_interior": max_relative(fullsS,ints["log_sample"]),
            "line_margin_relative_errors_after_rescaling_plan": residual_columns,
            "max_abs_line_margin_relative_error": max(abs(x) for x in residual_columns)},
        "slopes": {f"{lo}_{hi}": {
            "geometric": -slope(list(range(lo,hi+1)),fullg["log_sample"][lo-1:hi]),
            "sinkhorn_full9": -slope(list(range(lo,hi+1)),fulls["log_sample"][lo-1:hi]),
            "sinkhorn_interior7": -slope(list(range(lo,hi+1)),ints["log_sample"][lo-2:hi-1])}
                   for lo,hi in [(2,8),(4,8)]},
        "finite_acquisition_sensitivity": {
            "formula": "f=lambda*Treal/(-expm1(-lambda*Treal)); assumes pure parent decay and constant live fraction",
            "finite_minus_point_geometric_mu_2_8": -slope(list(range(2,9)),finite_g["log_sample"])-int_mu,
            "finite_minus_point_sinkhorn_mu_2_8": -slope(list(range(2,9)),finite_s["log_sample"])+slope(list(range(2,9)),ints["log_sample"]),
            "interaction_max_change": field_change},
    }


def two_line_parameters(records, lam):
    # Common exposure factors cancel before logarithms are evaluated.
    d=[math.log(float(row["areas"]["352"]/row["areas"]["609"])) for row in records[1:8]]
    z=[x/2 for x in center(d)]
    lo,hi=-2*max(map(abs,z)),2*max(map(abs,z))
    for _ in range(100):
        mid=(lo+hi)/2
        score=math.fsum(math.tanh(x-mid/2) for x in z)
        if score > 0:lo=mid
        else:hi=mid
    delta=(lo+hi)/2
    M=max(map(abs,z))
    c3=(2/3)*math.cosh(2*M)**2*avg([abs(x)**3 for x in z])
    cmax=(2/3)*math.cosh(2*M)**2*M**3
    # log(cosh x)=log1p(2*sinh(x/2)^2) avoids near-one cancellation.
    corrections=center([math.log1p(2*math.sinh((x-delta/2)/2)**2) for x in z])
    quadratic=center([x*x/2 for x in z])
    rem=[x-y for x,y in zip(corrections,quadratic)]
    return {"scope":"binary64 deterministic comparison, not an interval certificate",
            "z":z,"M":M,"delta":delta,"C3":c3,"Cmax":cmax,
            "R_actual_root":abs(delta)*M/2+(M+abs(delta)/2)**4/12,
            "max_centered_quadratic_remainder":max(map(abs,rem))}


def main(args):
    records,lam=read_decimal(args.five_line_csv)
    rounded,oldlam,rounded_provenance=read_rounded_fixture(args.rounded_fixture)
    assert lam==oldlam
    differences=[]
    for a,b in zip(records,rounded):
        for key in ["cartridge","start_time","real_seconds","live_seconds","elapsed_seconds"]:
            assert a[key]==b[key],(a["cartridge"],key,a[key],b[key])
        for c in ["352","609"]:
            differences.append({"cartridge":a["cartridge"],"channel":c,
                "decimal_area":str(a["areas"][c]),"rounded_area":str(b["areas"][c]),
                "decimal_minus_rounded":str(a["areas"][c]-b["areas"][c]),
                "relative_difference":float(a["areas"][c]/b["areas"][c]-1)})
    old=read_reference(args.prior_balancing,"prior_five_line_balancing_results.json")
    prior_inter=read_reference(args.prior_two_line_audit,"prior_two_line_bounds_audit.json")
    calculated={name:domains(records,channels,lam) for name,channels in SUBSETS.items()}
    rounded_calc=domains(rounded,["352","609"],lam)
    verification=[]
    for name in ["all5","gamma4","pb3"]:
        for interval in ["2_8","4_8"]:
            o=old["subsets"][name]["slopes"][interval]
            n=calculated[name]["slopes"][interval]
            for key in ["geometric","sinkhorn_full9"]:
                old_key="geometric_mu" if key=="geometric" else "sinkhorn_mu"
                error=abs(n[key]-o[old_key]);assert error<1e-13
                verification.append({"subset":name,"interval":interval,"quantity":key,"absolute_error":error})
        error=abs(calculated[name]["full9"]["all9_method_difference"]["max_abs_relative"]
                  -old["subsets"][name]["sample_factor_comparison"]["max_abs_relative_difference"])
        assert error<1e-13
        for new_key,old_key in [
            ("max_abs_interaction","max_abs_log"),
            ("rms_interaction","rms_log"),
            ("leading_squared_singular_share","leading_squared_singular_value_share")]:
            error=abs(calculated[name]["full9"]["interaction"][new_key]
                      -old["subsets"][name]["geometric_interaction_metrics"][old_key])
            assert error<1e-12,(name,new_key,error)
    assert prior_inter["source"]["sha256"]==ROUNDED_SHA
    reference_z=[row["z"]["display_midpoint_float"]
                 for row in prior_inter["two_line_bounds"]["per_cartridge"]]
    z_error=max(abs(x[0]-y) for x,y in zip(rounded_calc["interior7"]["geometric"]["interaction"],
                                        reference_z))
    assert z_error<1e-13
    output={"method":{
        "orientation":"samples/cartridges are rows; spectral channels are columns",
        "floating_point":"Python binary64, math.fsum, stable max-shift logsumexp",
        "svd":"NumPy descriptive SVD only; no mechanism or statistical significance inferred",
        "python":platform.python_version(),"numpy":np.__version__,
        "normalization_targets":"uniform probability row and column targets on each selected normalization domain",
        "factor_comparison":"each log-sample factor is re-centered on the same comparison rows before comparison",
        "uncertainty":"No peak-area covariance/background/replicate errors supplied; no statistical uncertainty calculated",
        "77_keV_status":"Nominal unresolved ROI; kept as a positive channel with no guessed photon yield"},
        "provenance":{name:{"filename":path.name,"sha256":sha(path)} for name,path in [
            ("five_line_csv",args.five_line_csv),("rounded_fixture",args.rounded_fixture),
            ("prior_balancing",args.prior_balancing),("prior_two_line_audit",args.prior_two_line_audit)]},
        "rounded_fixture_provenance":rounded_provenance,
        "source_comparison":{"identical_acquisition_fields":True,"lambda":str(lam),
             "data_not_identical":any(Decimal(x["decimal_minus_rounded"])!=0 for x in differences),
             "decimal_and_rounded_areas":differences,
             "max_absolute_area_difference":str(max(abs(Decimal(x["decimal_minus_rounded"])) for x in differences)),
             "max_absolute_relative_area_difference":max(abs(x["relative_difference"]) for x in differences),
             "same_baseline_correction":True},
        "reported_full9_results_reproduced":verification,
        "rounded_two_line_interaction_match_max_abs":z_error,
        "decimal_subsets":calculated,"rounded_two_line":rounded_calc,
        "two_line_source_sensitivity":{"decimal":two_line_parameters(records,lam),
                                      "rounded":two_line_parameters(rounded,lam)}}
    results_dir=args.output_dir/"results"
    results_dir.mkdir(parents=True,exist_ok=True)
    (results_dir/"spectral_domains_audit.json").write_text(json.dumps(output,indent=2,allow_nan=False)+"\n")
    table=[]
    for name,x in calculated.items():
        table.append({"subset":name,"channels":",".join(x["channels"]),
             "geometric_mu_2_8":x["slopes"]["2_8"]["geometric"],
             "sinkhorn_mu_2_8_normalize_all9":x["slopes"]["2_8"]["sinkhorn_full9"],
             "sinkhorn_mu_2_8_normalize_interior7":x["slopes"]["2_8"]["sinkhorn_interior7"],
             "geometric_mu_4_8":x["slopes"]["4_8"]["geometric"],
             "sinkhorn_mu_4_8_normalize_all9":x["slopes"]["4_8"]["sinkhorn_full9"],
             "sinkhorn_mu_4_8_normalize_interior7":x["slopes"]["4_8"]["sinkhorn_interior7"],
             "full9_SK_geom_max_difference_percent_all9":x["full9"]["all9_method_difference"]["max_abs_percent"],
             "full9_SK_geom_max_difference_percent_on_recentered_interior7":x["full9_restricted_and_recentered_to_interior"]["method_difference"]["max_abs_percent"],
             "interior7_SK_geom_max_difference_percent":x["interior7"]["method_difference"]["max_abs_percent"],
             "SK_all9_vs_interior7_max_difference_percent":x["full9_restricted_and_recentered_to_interior"]["sinkhorn_vs_refit_interior"]["max_abs_percent"],
             "interior7_max_abs_E":x["interior7"]["interaction"]["max_abs_interaction"],
             "interior7_h_max_relative_residual_percent":100*x["interior7"]["interaction"]["common_fit"]["max_abs_relative_residual"],
             "interior7_interaction_dof":x["interior7"]["interaction"]["interaction_dimension"],
             "interior7_common_residual_dof":5,
             "interior7_common_fraction_residual_energy_percent":100*x["interior7"]["interaction"]["common_fraction_among_common_plus_interaction"]})
    with (results_dir/"spectral_domains_summary.csv").open("w",newline="") as f:
        w=csv.DictWriter(f,fieldnames=list(table[0]));w.writeheader();w.writerows(table)
    (results_dir/"spectral_domains_summary.json").write_text(json.dumps(table,indent=2)+"\n")
    print(json.dumps({"output":public_path(results_dir),"summary":table,
                      "source_sensitivity":output["two_line_source_sensitivity"]},indent=2))


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--five-line-csv",type=Path,default=DATA_DIR/"Radon_5Line_Master_Analysis.csv")
    parser.add_argument("--rounded-fixture",type=Path,default=DATA_DIR/"rounded_two_line.json")
    parser.add_argument("--prior-balancing",type=Path,default=DATA_DIR/"prior_five_line_balancing_results.json")
    parser.add_argument("--prior-two-line-audit",type=Path,default=DATA_DIR/"prior_two_line_bounds_audit.json")
    parser.add_argument("--output-dir",type=Path,default=DEFAULT_OUTPUT_DIR)
    main(parser.parse_args())
