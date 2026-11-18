#!/usr/bin/env python3
"""Numerical audit of proposed radon floor, shifted-sinh, and manuscript claims.

This is a descriptive reproduction of supplied formulas, not a physical model
selection or uncertainty analysis. It preserves the source start-time point
correction and does not apply the finite-acquisition factor. No input is edited.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import math
import re
from collections import Counter
from pathlib import Path

import numpy as np


def file_metadata(path):
    content = path.read_bytes()
    return {"name": path.name, "size_bytes": len(content),
            "sha256": hashlib.sha256(content).hexdigest()}


def write_csv(path, rows):
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def numerical_cell(cell):
    match = re.search(r"(?<![A-Za-z])([0-9]+(?:\.[0-9]+)?)", cell)
    if match is None:
        raise ValueError(cell)
    raw = match[1]
    precision = len(raw.partition(".")[2])
    return float(raw), precision


def predict(model, index):
    argument = model["mu"] * (model["index_zero_or_center"] - index)
    shape = math.sinh(argument) if model["shape"] == "sinh" else math.cosh(argument)
    return model["amplitude_cps"] * shape + model["constant_floor_cps"]


def fit_metrics(y, prediction):
    residual = [a-b for a,b in zip(y,prediction)]
    mean = sum(y)/len(y)
    sse = sum(r*r for r in residual)
    return {"sse_cps_squared": sse, "rmse_cps": math.sqrt(sse/len(y)),
            "r_squared_unlogged_point_corrected_rate": 1-sse/sum((a-mean)**2 for a in y),
            "maximum_absolute_relative_residual": max(abs(r/a) for r,a in zip(residual,y)),
            "mean_observed_minus_model_cps": sum(residual)/len(residual)}


def audit(original, leak_a, leak_b, manuscript, output):
    output.mkdir(parents=True,exist_ok=True)
    source = original.read_text(encoding="utf-8")
    embedded = source.split("```csv\n",1)[1].split("\n```",1)[0]
    rows = list(csv.reader(io.StringIO(embedded)))
    parameters = {r[0]:r[1] for r in rows if len(r)>=2}
    decay = float(parameters["Rn-222 Decay Constant (lambda)"])
    mu = float(parameters["Fitted Attenuation per Cartridge (mu)"])
    records = []
    for r in rows:
        if not r or r[0] not in list("123456789"):
            continue
        live = float(r[3])*60
        records.append({"cartridge":int(r[0]), "start_time":r[1],
                        "elapsed_s":int(r[4]), "live_seconds":live,
                        "point_corrected_rate_609_cps":int(r[5])/live*math.exp(decay*int(r[4])),
                        "point_corrected_rate_352_cps":int(r[6])/live*math.exp(decay*int(r[4]))})
    assert len(records)==9

    models = []
    for energy,shift_amplitude,floor_amplitude,floor in (
        (609,0.675,1.41,1.55),
        (352,1.061,2.21,2.55),
    ):
        source_sinh=float(parameters[f"Fit Amplitude A_sinh ({energy} keV)"])
        source_cosh=float(parameters[f"Fit Amplitude A_cosh ({energy} keV)"])
        models.extend([
            {"id":f"original_sinh_{energy}", "energy_keV":energy,
             "shape":"sinh", "amplitude_cps":source_sinh, "mu":mu,
             "index_zero_or_center":10.0, "constant_floor_cps":0.0,
             "parameter_provenance":"original embedded CSV"},
            {"id":f"original_cosh_{energy}", "energy_keV":energy,
             "shape":"cosh", "amplitude_cps":source_cosh, "mu":mu,
             "index_zero_or_center":9.5, "constant_floor_cps":0.0,
             "parameter_provenance":"original embedded CSV and explicit manuscript plot"},
            {"id":f"ln2_floor_draft_{energy}", "energy_keV":energy,
             "shape":"sinh", "amplitude_cps":floor_amplitude, "mu":math.log(2),
             "index_zero_or_center":9.5, "constant_floor_cps":floor,
             "parameter_provenance":"identical leak drafts, section3; ln(2) evaluated rather than rounded0.693"},
            {"id":f"shift_delta_1_1_draft_{energy}", "energy_keV":energy,
             "shape":"sinh", "amplitude_cps":shift_amplitude, "mu":mu,
             "index_zero_or_center":10.6, "constant_floor_cps":0.0,
             "parameter_provenance":"identical leak drafts, final Excel formulas, delta1.10"},
        ])
    models.append({"id":"original_sinh_plus_075_609", "energy_keV":609,
                   "shape":"sinh", "amplitude_cps":float(parameters["Fit Amplitude A_sinh (609 keV)"]), "mu":mu,
                   "index_zero_or_center":10.0, "constant_floor_cps":0.75,
                   "parameter_provenance":"additional requested0.75cps scenario applied to original609sinh"})
    by_id = {m["id"]:m for m in models}
    predictions=[]
    metrics=[]
    for model in models:
        key=f"point_corrected_rate_{model['energy_keV']}_cps"
        for record in records:
            i=record["cartridge"]
            observed=record[key]
            prediction=predict(model,i)
            predictions.append({"model_id":model["id"], "energy_keV":model["energy_keV"],
                                "cartridge":i, "observed_point_corrected_rate_cps":observed,
                                "predicted_rate_cps":prediction,
                                "residual_observed_minus_model_cps":observed-prediction,
                                "relative_residual_observed_minus_model":(observed-prediction)/observed})
        for lo,hi in ((1,9),(2,9)):
            selected=records[lo-1:hi]
            y=[r[key] for r in selected]
            prediction=[predict(model,r["cartridge"]) for r in selected]
            metrics.append({"model_id":model["id"], "energy_keV":model["energy_keV"],
                            "range":f"{lo}-{hi}", **fit_metrics(y,prediction)})

    # Check both leak-draft printed columns against their explicitly declared formula.
    leak_table=[]
    for line in leak_a.read_text(encoding="utf-8").splitlines():
        if re.match(r"\| \*\*[1-9]\*\* \|",line):
            cells=line.split("|")[1:-1]
            i=int(numerical_cell(cells[0])[0])
            for energy,column in ((609,2),(352,4)):
                supplied,precision=numerical_cell(cells[column])
                calculated=predict(by_id[f"ln2_floor_draft_{energy}"],i)
                leak_table.append({"cartridge":i, "energy_keV":energy,
                                   "supplied_prediction_cps":supplied,
                                   "supplied_decimal_places":precision,
                                   "recomputed_prediction_cps":calculated,
                                   "agrees_at_supplied_precision":round(calculated,precision)==supplied,
                                   "supplied_minus_recomputed_cps":supplied-calculated})
    assert len(leak_table)==18

    # Manuscript model table. Explicitly record which coefficients are not in
    # this manuscript and are inherited from the companion supplied documents.
    manuscript_text=manuscript.read_text(encoding="utf-8")
    model_section=manuscript_text.split(r"\label{tab:model_comparison}",1)[1].split(r"\end{table}",1)[0]
    manuscript_comparisons=[]
    inferred_shift_amplitudes=[]
    column_specs=[
        ("observed609","source observed count areas"),
        ("original_sinh_609","explicit manuscript609sinh plot"),
        ("shift_delta_1_1_draft_609","amplitude0.675 from companion leak draft; manuscript omits this amplitude"),
        ("original_cosh_609","explicit manuscript609cosh plot"),
        ("normalized_observed609","source observed count areas divided by10-i"),
        ("normalized_original_sinh_609","explicit manuscript normalized609sinh plot"),
        ("observed352","source observed count areas"),
        ("original_sinh_352","amplitude1.533 from original CSV; manuscript omits this amplitude"),
        ("original_cosh_352","explicit manuscript352cosh plot despite tablelabel Leaking/cosh"),
    ]
    for line in model_section.splitlines():
        if not re.match(r"^\s*[1-9]\s*&",line):
            continue
        cells=line.split("&")
        i=int(cells[0].strip())
        for cell,(quantity,provenance) in zip(cells[1:],column_specs,strict=True):
            supplied,precision=numerical_cell(cell)
            if quantity=="observed609": calculated=records[i-1]["point_corrected_rate_609_cps"]
            elif quantity=="observed352": calculated=records[i-1]["point_corrected_rate_352_cps"]
            elif quantity=="normalized_observed609": calculated=records[i-1]["point_corrected_rate_609_cps"]/(10-i)
            elif quantity=="normalized_original_sinh_609": calculated=predict(by_id["original_sinh_609"],i)/(10-i)
            else: calculated=predict(by_id[quantity],i)
            manuscript_comparisons.append({"cartridge":i,"quantity":quantity,
                                           "parameter_provenance":provenance,
                                           "supplied":supplied,"recomputed":calculated,
                                           "agrees_at_supplied_precision":round(calculated,precision)==supplied,
                                           "supplied_minus_recomputed":supplied-calculated})
            if quantity=="shift_delta_1_1_draft_609":
                basis=math.sinh(mu*(10.6-i))
                half_rounding=0.5*10**(-precision)
                inferred_shift_amplitudes.append({
                    "cartridge":i,"amplitude_implied_by_printed_value":supplied/basis,
                    "lower_amplitude_from_printed_rounding":(supplied-half_rounding)/basis,
                    "upper_amplitude_from_printed_rounding":(supplied+half_rounding)/basis,
                })
    assert len(manuscript_comparisons)==81

    deficit=[]
    for energy in (609,352):
        r1=records[0][f"point_corrected_rate_{energy}_cps"]
        r2=records[1][f"point_corrected_rate_{energy}_cps"]
        for basis,reference in (("assumed_exact_halving_2_times_R2",2*r2),
                                ("original_fixed_cosh_at_i1",predict(by_id[f"original_cosh_{energy}"],1))):
            deficit.append({"energy_keV":energy,"conditional_baseline":basis,
                            "baseline_rate_cps":reference,"observed_rate_cps":r1,
                            "deficit_cps":reference-r1,"fractional_deficit":1-r1/reference,
                            "interpretation":"arithmetic relative to a chosen baseline; not measured desorption or moisture loss"})
    phi=9*mu
    transmission={"phi_definition":"L/Ld=N*mu with N9, mu0.686", "phi":phi,
                  "sinh_phi":math.sinh(phi), "phi_over_sinh_phi":phi/math.sinh(phi),
                  "percent":100*phi/math.sinh(phi),"manuscript_value":0.0258,
                  "manuscript_percent":2.58,
                  "scope":"ideal same-inlet Dirichlet-to-linear outlet flux ratio / endpoint profile-ratio limit; not a measured Robin-column transmission"}

    interior=[]
    x=np.arange(2,8,dtype=float)
    for energy in (609,352):
        y=np.array([r[f"point_corrected_rate_{energy}_cps"] for r in records[1:7]])
        slope,intercept=np.polyfit(x,np.log(y),1)
        fitted=np.exp(intercept+slope*x)
        ratios=(y[:-1]/y[1:]).tolist()
        interior.append({"energy_keV":energy,"range":"2-7",
                         "objective":"unweighted squared residuals of log point-corrected rates, free amplitude",
                         "fitted_mu":float(-slope),"ln2":math.log(2),
                         "mu_minus_ln2":float(-slope-math.log(2)),
                         "amplitude_at_index_zero_cps":float(np.exp(intercept)),
                         "adjacent_ratios_within_range":ratios,
                         "mean_adjacent_ratio":sum(ratios)/len(ratios),
                         "sse_log_rate":float(np.sum((np.log(y)-np.log(fitted))**2)),
                         **fit_metrics(y.tolist(),fitted.tolist()),
                         "interpretation":"descriptive fit; no intrinsic diffusivity, exact halving law, or confidence interval inferred"})

    report={
        "source_files":[file_metadata(p) for p in (original,leak_a,leak_b,manuscript)],
        "duplicate_leak_files":leak_a.read_bytes()==leak_b.read_bytes(),
        "method":{
            "rate_basis":"source start-time point correction N/live*exp(lambda*elapsed); no finite-acquisition factor applied",
            "residual_sign":"observed minus model",
            "r_squared":"1-SSE/SST on unlogged point-corrected rates, independently perenergy/range",
            "uncertainty":"none inferred; net peak areas have no supplied background/error model",
            "new_scenarios":"frozen supplied parameters; no amplitude/mu/background refitting except explicitly labeled interior log fit",
        },
        "observations":records,"models":models,"per_point_predictions":predictions,
        "fixed_model_metrics":metrics,"leak_draft_table_comparisons":leak_table,
        "leak_draft_table_disagreements":sum(not r["agrees_at_supplied_precision"] for r in leak_table),
        "manuscript_table_comparisons":manuscript_comparisons,
        "manuscript_comparison_scope":"81cells; leakage609andopen352checks conditionally inherit coefficients from companiondocuments, separately labeled",
        "manuscript_table_disagreement_counts":dict(Counter(r["quantity"] for r in manuscript_comparisons if not r["agrees_at_supplied_precision"])),
        "manuscript_shift_amplitude_rounding_check":{
            "mu":mu,"delta":1.1,"intervals_are":"printed rounding intervals, not measurement uncertainty",
            "rows":inferred_shift_amplitudes,
            "largest_lower_bound":max(r["lower_amplitude_from_printed_rounding"] for r in inferred_shift_amplitudes),
            "smallest_upper_bound":min(r["upper_amplitude_from_printed_rounding"] for r in inferred_shift_amplitudes),
            "single_amplitude_possible_at_printed_precision":max(r["lower_amplitude_from_printed_rounding"] for r in inferred_shift_amplitudes)<=min(r["upper_amplitude_from_printed_rounding"] for r in inferred_shift_amplitudes),
        },
        "conditional_inlet_deficits":deficit,
        "clock_span":{"seconds":records[0]["elapsed_s"],"minutes":records[0]["elapsed_s"]/60,
                      "hours":records[0]["elapsed_s"]/3600,"clock_difference":"12:25:47 minus10:16:34 =2h9m13s",
                      "scope":"start of cartridge1measurement minus start of cartridge9measurement; disassembly time is not established"},
        "transmission_arithmetic":transmission,
        "interior_log_fits":interior,
        "manuscript_parameter_definitions":{
            "gas_and_bulk_concentrations":"lines151–170: C_g is pore-gas activity concentration; q=K_a*C_g; C=(epsilon+rho_b*K_a)*C_g is total activity per bulkvolume",
            "flux_coefficient":"lines158–177: J=-D_pore*C_g_x, D_pore=(epsilon/tau)*D0; D_e=D_pore/(epsilon+rho_b*K_a)",
            "consequence":"for constant storage J=-D_e*C_x in total-C coordinates; porosity is already included in definedD_pore",
            "common_geometry_mismatch":"L=9dx, centers(i−0.5)dx imply9.5−i for both finitecolumnshapes, whereas manuscriptDirichletandlinearformulas retain10−i",
            "leaking_plot":"the manuscript's curve labeled Leaking-End/cosh literally uses originalcosh; it does not plot the advertised shifted-sinh atdelta1.10",
            "omitted_coefficients":"manuscript does not numerically specify A_leak or A_sinh352; companion coefficients are marked as inherited in comparisons",
        },
        "endpoint_examples":[{
            "model_id":m["id"],"cartridge9_center_prediction_cps":predict(m,9),
            "physical_outlet_index9_5_prediction_cps":predict(m,9.5),
            "note":"center of cartridge9 is half a cartridge before physical outlet; these are distinct evaluations",
        } for m in models if "draft" in m["id"]],
    }
    (output/'leak_extension_audit.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    write_csv(output/'per_point_predictions.csv',predictions)
    write_csv(output/'fixed_model_metrics.csv',metrics)
    write_csv(output/'leak_draft_table_comparisons.csv',leak_table)
    write_csv(output/'manuscript_table_comparisons.csv',manuscript_comparisons)
    write_csv(output/'conditional_inlet_deficits.csv',deficit)
    write_csv(output/'interior_log_fits.csv',interior)
    print(json.dumps({k:report[k] for k in (
        'source_files','duplicate_leak_files','fixed_model_metrics','leak_draft_table_disagreements',
        'conditional_inlet_deficits','clock_span','transmission_arithmetic','interior_log_fits','endpoint_examples')},indent=2))


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('original',type=Path)
    parser.add_argument('leak_a',type=Path)
    parser.add_argument('leak_b',type=Path)
    parser.add_argument('manuscript',type=Path)
    parser.add_argument('output',type=Path)
    args=parser.parse_args()
    audit(args.original,args.leak_a,args.leak_b,args.manuscript,args.output)
