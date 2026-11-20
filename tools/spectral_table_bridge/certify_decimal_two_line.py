#!/usr/bin/env python3
"""Apply the existing exact-rational interval kernel to both source variants.

No float decides a bound. The reused interval implementation is hash pinned.
This is a Python numerical certificate, not a Lean interval proof or an
experimental uncertainty assessment.
"""
from __future__ import annotations
import argparse
import csv
from fractions import Fraction as F
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from fixtures import (DATA_DIR, DEFAULT_OUTPUT_DIR, TOOLS_DIR,
                      public_path, read_rounded_fixture)

KERNEL_SHA = "b22d93a4a44ec5e2d2b43c1b7c3d96585f2c76f5aea22b79218602efbacb5784"
DECIMAL_SHA = "30a4bc1781ebade1636f74fe3703faea04d5584d72b4a178cc84f4bd11e6fa6d"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_kernel(path):
    if sha(path) != KERNEL_SHA:
        raise ValueError("interval-kernel source hash differs from the audited version")
    spec=importlib.util.spec_from_file_location("spectral_exact_interval_kernel", path)
    module=importlib.util.module_from_spec(spec)
    sys.modules[spec.name]=module
    spec.loader.exec_module(module)
    return module


def certify(kern, ratios):
    d=[kern.log_fraction(r) for r in ratios]
    mean=kern.interval_mean(d)
    z=[(v-mean)/2 for v in d]
    M=kern.interval_max([v.absolute() for v in z])
    k,root_record=kern.rational_root(ratios)
    delta=kern.log_interval(k)-mean
    D=delta.absolute()
    cosh2=kern.cosh_interval(2*M).power(2)
    C3=F(2,3)*cosh2*kern.interval_mean(v.absolute().power(3) for v in z)
    Cmax=F(2,3)*cosh2*M.power(3)
    def R(a):
        return a*M/2+(M+a/2).power(4)/12
    corrections=kern.interval_center([kern.log_interval(kern.cosh_interval(v-delta/2)) for v in z])
    quadratic=kern.interval_center([v.power(2)/2 for v in z])
    residuals=[a-b for a,b in zip(corrections,quadratic)]
    actual=kern.interval_max([v.absolute() for v in residuals])
    if not (D.hi<C3.lo and C3.hi<Cmax.lo):
        raise ArithmeticError("root-bound ordering was not certified")
    if not actual.hi<R(D).lo:
        raise ArithmeticError("centered remainder is not below its analytic upper expression")
    values={"M":M,"k":k,"delta":delta,"C3":C3,"Cmax":Cmax,
            "R_actual_root":R(D),"R_C3":R(C3),"R_Cmax":R(Cmax),
            "actual_max_centered_quadratic_remainder":actual}
    return {"root_sign_certificate":root_record,
            "quantities":{name:kern.serialize_interval(v) for name,v in values.items()},
            "z":[kern.serialize_interval(v) for v in z],
            "root_abs_bound_order_verified":True,
            "actual_remainder_below_root_bound_verified":True},values


def main(args):
    kern=load_kernel(args.interval_module)
    if sha(args.five_line_csv)!=DECIMAL_SHA:
        raise ValueError("decimal source hash changed")
    rows=list(csv.reader(args.five_line_csv.open(newline="",encoding="utf-8-sig")))
    start=next(i for i,row in enumerate(rows) if row and row[0]=="Cartridge (i)")
    source=rows[start+1:]
    if [int(row[0]) for row in source]!=list(range(1,10)):
        raise ValueError("unexpected sample ordering")
    decimal_ratios=[F(row[8])/F(row[9]) for row in source[1:8]]
    rounded,_,rounded_provenance=read_rounded_fixture(args.rounded_fixture)
    rounded_ratios=[F(row["areas"]["352"])/F(row["areas"]["609"]) for row in rounded[1:8]]
    decimal, dv=certify(kern,decimal_ratios)
    old,ov=certify(kern,rounded_ratios)
    short_limits={
        "M_le_0_009794326":("M","0.009794326"),
        "delta_abs_le_4_449430e_8":("delta","4.449430e-8"),
        "C3_le_1_457894e_7":("C3","1.457894e-7"),
        "Cmax_le_6_266124e_7":("Cmax","6.266124e-7"),
        "R_actual_root_le_9_848e_10":("R_actual_root","9.848e-10"),
        "R_C3_le_1_480839e_9":("R_C3","1.480839e-9"),
        "R_Cmax_le_3_835582e_9":("R_Cmax","3.835582e-9"),
        "actual_quadratic_remainder_le_3_988e_10":("actual_max_centered_quadratic_remainder","3.988e-10"),
    }
    certificates={}
    for label,(key,limit) in short_limits.items():
        value=dv[key].absolute() if key=="delta" else dv[key]
        if not value.hi <= F(limit):
            raise ArithmeticError("short upper bound did not certify: "+label)
        certificates[label]={"bound":limit,"verified":True}
    decimal["short_certified_upper_bounds"]=certificates
    output={
        "scope":"Exact Fraction computations with explicit analytic series-tail enclosures; not Lean-checked numerical enclosures or measurement uncertainty.",
        "source_provenance":{"decimal":{"filename":args.five_line_csv.name,"sha256":sha(args.five_line_csv)},
                             "rounded":rounded_provenance,
                             "interval_implementation":{"filename":args.interval_module.name,"sha256":sha(args.interval_module)}},
        "method":{"source_ratio":"352/609 decimal net areas converted directly to exact rational numbers",
                  "columns":"cartridges2 through8; seven equal weights",
                  "common_correction":"cancels exactly from every line ratio",
                  "root_bisections":kern.ROOT_STEPS,"log_terms":kern.LOG_TERMS,"cosh_terms":kern.COSH_TERMS,
                  "outward_rational_lattice_decimal_places":kern.DECIMAL_PLACES},
        "decimal_source":decimal,"rounded_source":old,
        "source_difference":{name:kern.serialize_interval(dv[name]-ov[name]) for name in
                             ["M","delta","C3","Cmax","R_actual_root","actual_max_centered_quadratic_remainder"]},
    }
    target=args.output_dir/"results"/"decimal_two_line_certificate.json"
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_text(json.dumps(output,indent=2,allow_nan=False)+"\n")
    print(json.dumps({"output":public_path(target),"decimal_quantities":decimal["quantities"],
                      "source_difference":output["source_difference"]},indent=2))


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--five-line-csv",type=Path,default=DATA_DIR/"Radon_5Line_Master_Analysis.csv")
    parser.add_argument("--rounded-fixture",type=Path,default=DATA_DIR/"rounded_two_line.json")
    parser.add_argument("--interval-module",type=Path,default=TOOLS_DIR/"audit_exact_two_line_bounds.py")
    parser.add_argument("--output-dir",type=Path,default=DEFAULT_OUTPUT_DIR)
    main(parser.parse_args())
