#!/usr/bin/env python3
"""SymPy-side exact checks for the factor-stratified de Rham audit artifact."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import sympy as sp

ROOT = Path(__file__).resolve().parents[3]
DEFAULT_AUDIT = ROOT / "artifacts" / "de_rham_klein_quadric" / "factor_stratified_audit.json"
DEFAULT_OUT = ROOT / "artifacts" / "de_rham_klein_quadric" / "factor_stratified_sympy.json"


def parse_m2_poly(expr: str) -> Any:
    return sp.sympify(expr.replace("^", "**"))


def verify_factorization(raw: str, factored: str, sym: sp.Symbol) -> dict[str, Any]:
    raw_expr = parse_m2_poly(raw)
    factored_expr = parse_m2_poly(factored)
    return {
        "raw": raw,
        "factored": factored,
        "expanded_factored": str(sp.expand(factored_expr)),
        "is_equal": sp.expand(raw_expr - factored_expr) == 0,
        "roots": [str(r) for r in sp.factor_list(raw_expr, sym)[1]],
    }


def build_report(audit: dict[str, Any]) -> dict[str, Any]:
    s = sp.symbols("s")
    factors = audit["bernstein_sato_factors"]["payload"]
    factor_checks = {
        name: verify_factorization(factors[f"{name}_raw"], factors[f"{name}_factor"], s)
        for name in ["qA", "qB", "qAB"]
    }
    generalB = verify_factorization(factors["generalB_raw"], factors["generalB_factor"], s)
    derived = audit.get("derived_strata", {})
    ambient = derived.get("ambient_dim", 2 * audit["dimension"])
    pair_dim = int(audit["factor_stratification"]["payload"]["dim_pair_qA_qB"])
    triple_dim = int(audit["factor_stratification"]["payload"]["dim_triple_qA_qB_qC"])
    singular_dim = int(audit["factor_stratification"]["payload"]["dim_singular_locus"])

    finite_symbolic = audit["finite_field"].get("symbolic") or {}
    complement_factored = finite_symbolic.get("complement_count_factored")
    complement_expanded = finite_symbolic.get("complement_count_expanded")
    finite_field_check = None
    if complement_factored and complement_expanded:
        finite_field_check = sp.expand(parse_m2_poly(complement_factored) - parse_m2_poly(complement_expanded)) == 0

    return {
        "factor_checks": factor_checks,
        "generalB_check": generalB,
        "strata_arithmetic": {
            "ambient_dim": ambient,
            "pair_dim": pair_dim,
            "triple_dim": triple_dim,
            "singular_locus_dim": singular_dim,
            "pair_codim": ambient - pair_dim,
            "triple_codim": ambient - triple_dim,
            "singular_locus_codim": ambient - singular_dim,
            "pair_codim_is_two": ambient - pair_dim == 2,
            "triple_codim_is_three": ambient - triple_dim == 3,
        },
        "finite_field_symbolic_check": finite_field_check,
        "de_rham_closed": audit["summary"]["de_rham_closed"],
        "honesty_note": "This SymPy layer certifies exact polynomial/arithmetic equalities read from the CAS artifact; it does not certify de Rham Betti numbers.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Verify the factor-stratified audit artifact with SymPy")
    parser.add_argument("--audit", type=Path, default=DEFAULT_AUDIT)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args()

    audit = json.loads(args.audit.read_text())
    report = build_report(audit)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True))
    print(args.out)
    print(json.dumps({
        "all_factor_checks_equal": all(item["is_equal"] for item in report["factor_checks"].values()),
        "generalB_equal": report["generalB_check"]["is_equal"],
        "pair_codim_is_two": report["strata_arithmetic"]["pair_codim_is_two"],
        "triple_codim_is_three": report["strata_arithmetic"]["triple_codim_is_three"],
        "de_rham_closed": report["de_rham_closed"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
