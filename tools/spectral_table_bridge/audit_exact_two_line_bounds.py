#!/usr/bin/env python3
"""Exact rational enclosures for two-line Sinkhorn bounds and projection energy.

No floating-point result is used to certify an inequality. Fractions, exact
bisection of a rational monotone root equation, and explicit convergent-series
remainders supply enclosures. Floats in the JSON are display approximations.
This is a reproducible Python interval certificate, not a Lean-checked theorem.
The deterministic input consists of reported net peak areas; no measurement
uncertainty or physical cause is inferred.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import math
import re
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path

EXPECTED_SHA = "882b6799b2787041c86e07b36c7fe892ee1e7807756e05273227ac73b9411754"
DECIMAL_PLACES = 60
SCALE = 10 ** DECIMAL_PLACES
LOG_TERMS = 72
COSH_TERMS = 16
ROOT_STEPS = 160


def floor_grid(x, scale=SCALE):
    return F(x.numerator * scale // x.denominator, scale)


def ceil_grid(x, scale=SCALE):
    return F(-((-x.numerator * scale) // x.denominator), scale)


@dataclass(frozen=True)
class Interval:
    lo: F
    hi: F

    def __post_init__(self):
        if self.lo > self.hi:
            raise ValueError("invalid interval")

    @classmethod
    def enclosure(cls, lo, hi):
        return cls(floor_grid(F(lo)), ceil_grid(F(hi)))

    @classmethod
    def point(cls, x):
        return cls(F(x), F(x))

    def __add__(self, other):
        other = as_interval(other)
        return Interval.enclosure(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-as_interval(other))

    def __rsub__(self, other):
        return as_interval(other) - self

    def __mul__(self, other):
        other = as_interval(other)
        values = [a * b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Interval.enclosure(min(values), max(values))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = as_interval(other)
        if other.lo <= 0 <= other.hi:
            raise ZeroDivisionError("interval denominator includes zero")
        return self * Interval.enclosure(1 / other.hi, 1 / other.lo)

    def absolute(self):
        hi = max(abs(self.lo), abs(self.hi))
        lo = 0 if self.lo <= 0 <= self.hi else min(abs(self.lo), abs(self.hi))
        return Interval.enclosure(lo, hi)

    def power(self, exponent):
        if exponent == 0:
            return Interval.point(1)
        if exponent < 0:
            return Interval.point(1) / self.power(-exponent)
        values = [self.lo ** exponent, self.hi ** exponent]
        if exponent % 2 == 0 and self.lo <= 0 <= self.hi:
            values.append(F(0))
        return Interval.enclosure(min(values), max(values))

    def mid_float(self):
        return float((self.lo + self.hi) / 2)


def as_interval(x):
    return x if isinstance(x, Interval) else Interval.point(x)


def interval_mean(xs):
    xs = list(xs)
    return sum(xs, Interval.point(0)) / len(xs)


def interval_center(xs):
    average = interval_mean(xs)
    return [x - average for x in xs]


def interval_max(xs):
    xs = list(xs)
    return Interval.enclosure(max(x.lo for x in xs), max(x.hi for x in xs))


def log_series(x):
    """For 1<=x<=2, log x=2 sum t^(2k+1)/(2k+1), t=(x-1)/(x+1).

    The omitted positive tail is <= 2*t^(2K+1)/((2K+1)*(1-t^2)).
    All computations and this bound are rational.
    """
    if not F(1) <= x <= F(2):
        raise ValueError("log series requires range-reduced input in [1,2]")
    t = (x - 1) / (x + 1)
    square = t * t
    power, total = t, F(0)
    for k in range(LOG_TERMS):
        total += 2 * power / (2 * k + 1)
        power *= square
    tail = 2 * power / ((2 * LOG_TERMS + 1) * (1 - square))
    return Interval.enclosure(total, total + tail)


@lru_cache(maxsize=None)
def log_fraction(x):
    if x <= 0:
        raise ValueError("log requires a positive rational")
    if x == 2:
        return log_series(F(2))
    k = x.numerator.bit_length() - x.denominator.bit_length()
    power_two = F(2 ** k) if k >= 0 else F(1, 2 ** (-k))
    r = x / power_two
    while r < 1:
        k -= 1
        r *= 2
    while r >= 2:
        k += 1
        r /= 2
    return log_series(r) + k * log_fraction(F(2))


def log_interval(x):
    return Interval.enclosure(log_fraction(x.lo).lo, log_fraction(x.hi).hi)


def cosh_fraction(x):
    """Positive cosh series plus a geometric upper bound on its tail."""
    x = abs(x)
    square = x * x
    term, total = F(1), F(1)
    for k in range(1, COSH_TERMS):
        term *= square / ((2 * k - 1) * (2 * k))
        total += term
    first_omitted = term * square / ((2 * COSH_TERMS - 1) * (2 * COSH_TERMS))
    later_ratio_bound = square / ((2 * COSH_TERMS + 1) * (2 * COSH_TERMS + 2))
    if later_ratio_bound >= 1:
        raise ValueError("cosh series tail bound is not contractive")
    return Interval.enclosure(total, total + first_omitted / (1 - later_ratio_bound))


def cosh_interval(x):
    a = x.absolute()
    return Interval.enclosure(cosh_fraction(a.lo).lo, cosh_fraction(a.hi).hi)


def read_source(path):
    raw = path.read_bytes()
    sha = hashlib.sha256(raw).hexdigest()
    if sha != EXPECTED_SHA:
        raise ValueError("source hash does not match the recovered published data")
    match = re.search(r"```csv\s*\n(.*?)\n```", raw.decode(), re.S)
    if match is None:
        raise ValueError("source CSV missing")
    table = list(csv.reader(io.StringIO(match.group(1))))
    decays = [F(row[1]) for row in table if row and row[0] == "Rn-222 Decay Constant (lambda)"]
    if len(decays) != 1 or decays[0] <= 0:
        raise ValueError("unique positive decay constant required")
    records = [{"cartridge": int(row[0]), "elapsed_seconds": int(row[4]),
                "counts_352": int(row[6]), "counts_609": int(row[5]),
                "live_seconds": 60 * F(row[3])}
               for row in table if row and re.fullmatch(r"[1-9]", row[0])]
    records.sort(key=lambda row: row["cartridge"])
    if [row["cartridge"] for row in records] != list(range(1, 10)):
        raise ValueError("expected all nine source cartridges exactly once")
    if not all(row["counts_352"] > 0 and row["counts_609"] > 0 and row["live_seconds"] > 0
               for row in records):
        raise ValueError("positive counts and exposures required")
    return records, decays[0], {"name": path.name, "sha256": sha}


def rational_root(ratios):
    """Certify k by exact signs of sum rho/(rho+k)-n/2.

    This function is strictly decreasing for k>0. Its initial min/max-ratio
    bracket has opposite signs, and exact bisection preserves the bracket.
    """
    target = F(len(ratios), 2)
    def equation(k):
        return sum((rho / (rho + k) for rho in ratios), F(0)) - target
    lo, hi = min(ratios), max(ratios)
    if equation(lo) < 0 or equation(hi) > 0:
        raise ArithmeticError("initial root bracket is invalid")
    iterations = 0
    for _ in range(ROOT_STEPS):
        iterations += 1
        middle = (lo + hi) / 2
        sign = equation(middle)
        if sign > 0:
            lo = middle
        elif sign < 0:
            hi = middle
        else:
            lo = hi = middle
            break
    if equation(lo) < 0 or equation(hi) > 0:
        raise ArithmeticError("final root bracket does not certify the sign change")
    return Interval.enclosure(lo, hi), {"bisections": iterations,
                "lower_endpoint_equation_nonnegative": equation(lo) >= 0,
                "upper_endpoint_equation_nonpositive": equation(hi) <= 0,
                "equation": "sum_j rho_j/(rho_j+k) = n/2", "arithmetic": "exact fractions"}


def fixed_decimal(x, digits, upper=False):
    scale = 10 ** digits
    rounded = ceil_grid(x, scale) if upper else floor_grid(x, scale)
    units = rounded.numerator * scale // rounded.denominator
    sign = "-" if units < 0 else ""
    units = abs(units)
    whole, remainder = divmod(units, scale)
    return f"{sign}{whole}.{remainder:0{digits}d}"


def serialize_interval(x):
    return {"decimal_lower": fixed_decimal(x.lo, 45),
            "decimal_upper": fixed_decimal(x.hi, 45, upper=True),
            "display_midpoint_float": x.mid_float(),
            "decimal_strings_are_outward_rounded": True}


def fraction_record(x):
    return {"exact_rational": str(x), "display_float": float(x)}


def projection_example(shape, name):
    """Perturbation rows (a+b)s and (a-b)s, with a=.10 and b=.008."""
    a, b = F(1, 10), F(1, 125)
    n = len(shape)
    x = list(range(-3, 4))
    average = sum(shape, F(0)) / n
    centered = [s - average for s in shape]
    slope = sum((F(j) * s for j, s in zip(x, centered)), F(0)) / 28
    residual = [s - slope * j for j, s in zip(x, centered)]
    s2 = sum((s * s for s in centered), F(0))
    r2 = sum((r * r for r in residual), F(0))
    ev, ez, eh = 2 * a * a * s2, 2 * b * b * s2, 2 * a * a * r2
    return {"name": name, "shape_in_cartridge_order_2_to_8": [str(s) for s in shape],
            "centered_shape_squared_norm": fraction_record(s2),
            "spatial_residual_shape_squared_norm": fraction_record(r2),
            "common_column_energy_fraction_before_spatial_projection": fraction_record(ev / (ev + ez)),
            "fraction_of_common_column_energy_retained_in_h": fraction_record(eh / ev),
            "h_fraction_among_h_and_Z_after_projection": fraction_record(eh / (eh + ez)),
            "h_fraction_of_original_centered_column_and_Z_energy": fraction_record(eh / (ev + ez)),
            "common_column_matrix_squared_norm": fraction_record(ev),
            "interaction_matrix_squared_norm": fraction_record(ez),
            "common_spatial_residual_matrix_squared_norm": fraction_record(eh)}


def audit(source, orders_json, interior_json, intake, output):
    records, lam, provenance = read_source(source)
    old_orders = json.loads(orders_json.read_text())
    old_interior = json.loads(interior_json.read_text())
    if old_orders["source"]["sha256"] != provenance["sha256"] or old_interior["source"]["sha256"] != provenance["sha256"]:
        raise ValueError("audit source hashes differ")
    inside = records[1:8]
    ratios = [F(row["counts_352"], row["counts_609"]) for row in inside]
    d = [log_fraction(rho) for rho in ratios]
    dbar = interval_mean(d)
    z = [(value - dbar) / 2 for value in d]
    M = interval_max([value.absolute() for value in z])
    k, root_certificate = rational_root(ratios)
    delta = log_interval(k) - dbar
    absolute_delta = delta.absolute()
    cosh_squared = cosh_interval(2 * M).power(2)
    abs_cube_mean = interval_mean(value.absolute().power(3) for value in z)
    c3 = F(2, 3) * cosh_squared * abs_cube_mean
    cmax = F(2, 3) * cosh_squared * M.power(3)
    def remainder_bound(D):
        return D * M / 2 + (M + D / 2).power(4) / 12
    bounds = {"using_certified_observed_root": remainder_bound(absolute_delta),
              "using_mean_absolute_cubic_bound_C3": remainder_bound(c3),
              "using_maximum_only_cubic_bound_Cmax": remainder_bound(cmax)}
    if absolute_delta.hi > c3.lo or c3.hi > cmax.lo:
        raise ArithmeticError("certified delta/C3/Cmax ordering failed")
    if absolute_delta.hi > 2 * M.lo:
        raise ArithmeticError("certified root lies outside the simple theoretical bracket")
    logcosh = [log_interval(cosh_interval(value - delta / 2)) for value in z]
    actual_correction = interval_center(logcosh)
    quadratic = interval_center([value.power(2) / 2 for value in z])
    residuals = [a - b for a, b in zip(actual_correction, quadratic)]
    actual_max = interval_max([value.absolute() for value in residuals])
    short_bounds = {"delta_abs_le_4_503071e_8": (absolute_delta, F("4.503071e-8")),
                    "C3_le_1_459756e_7": (c3, F("1.459756e-7")),
                    "Cmax_le_6_288239e_7": (cmax, F("6.288239e-7")),
                    "root_remainder_bound_le_9_913e_10": (bounds["using_certified_observed_root"], F("9.913e-10")),
                    "C3_remainder_bound_le_1_486201e_9": (bounds["using_mean_absolute_cubic_bound_C3"], F("1.486201e-9")),
                    "Cmax_remainder_bound_le_3_853641e_9": (bounds["using_maximum_only_cubic_bound_Cmax"], F("3.853641e-9")),
                    "actual_remainder_le_3_992e_10": (actual_max, F("3.992e-10"))}
    certified_short_bounds = {label: {"exact_upper_rational": str(limit), "verified": value.hi <= limit}
                              for label, (value, limit) in short_bounds.items()}
    if not all(row["verified"] for row in certified_short_bounds.values()):
        raise ArithmeticError("a proposed short decimal upper bound was not certified")
    # The actual observed h uses the supplied point correction. A common live
    # time contributes only an intercept, but it is included here explicitly.
    g = [(log_fraction(F(row["counts_352"])) + log_fraction(F(row["counts_609"]))) / 2
         - log_fraction(row["live_seconds"]) + lam * row["elapsed_seconds"] for row in inside]
    v = interval_center(g)
    xs = list(range(-3, 4))
    slope = sum((x * value for x, value in zip(xs, v)), Interval.point(0)) / 28
    h = [value - slope * x for x, value in zip(xs, v)]
    ev = 2 * sum((value.power(2) for value in v), Interval.point(0))
    ez = 2 * sum((value.power(2) for value in z), Interval.point(0))
    eh = 2 * sum((value.power(2) for value in h), Interval.point(0))
    examples = [projection_example([F(int(j >= 4)) for j in range(2, 9)], "group step beginning at cartridge 4")]
    examples += [projection_example([F(int(j == chosen)) for j in range(2, 9)], f"localized at cartridge {chosen}")
                 for chosen in range(2, 9)]
    examples.append(projection_example([F(j - 5, 3) for j in range(2, 9)],
                                       "affine column perturbation, max absolute shape one"))
    result = {
        "source": provenance, "attachment": {"name": intake.name, "sha256": hashlib.sha256(intake.read_bytes()).hexdigest()},
        "method": {"certification": "exact Fraction arithmetic with outward rational lattice rounding; explicit analytic series tails; exact rational root signs",
                   "certification_scope": "Python interval certificate conditional on the documented series inequalities; not a Lean-checked proof or measurement uncertainty interval",
                   "lattice_decimal_places": DECIMAL_PLACES, "log_series_terms": LOG_TERMS,
                   "cosh_series_terms": COSH_TERMS, "root_bisections": ROOT_STEPS,
                   "log_series_tail": "2*t^(2K+1)/((2K+1)*(1-t^2)), t=(r-1)/(r+1), 1<=r<=2",
                   "cosh_series_tail": "first omitted positive term divided by 1 minus an upper bound on later term ratios",
                   "two_line_z": "z_j = (log(N352_j/N609_j) - mean log(N352/N609))/2; common exposure/decay column factors cancel exactly",
                   "centered_remainder_argument": "q(s)=logcosh(s)-s^2/2 is in [-a^4/12,0] for |s|<=a; center(q) has absolute value at most a^4/12. Centered linear term is -delta*z/2 because mean z=0.",
                   "energy_convention": "Frobenius squared norm of the two-row matrices: E_v=2||v||^2, E_h=2||h||^2, E_Z=2||z||^2"},
        "two_line_bounds": {"n": len(inside), "M": serialize_interval(M),
                            "mean_absolute_cubic_z": serialize_interval(abs_cube_mean),
                            "k": serialize_interval(k), "delta": serialize_interval(delta),
                            "absolute_delta": serialize_interval(absolute_delta),
                            "C3": serialize_interval(c3), "Cmax": serialize_interval(cmax),
                            "root_certificate": root_certificate,
                            "quadratic_remainder_upper_expressions": {label: serialize_interval(value) for label, value in bounds.items()},
                            "actual_max_absolute_quadratic_remainder": serialize_interval(actual_max),
                            "old_binary64_max_remainder": old_orders["interior_2_8"]["max_abs_column_second_order_remainder"],
                            "9_9e_10_is_below_root_based_bound_expression": F("9.9e-10") < bounds["using_certified_observed_root"].lo,
                            "certified_short_decimal_upper_bounds": certified_short_bounds,
                            "per_cartridge": [{"cartridge": row["cartridge"], "z": serialize_interval(value),
                                                "exact_sample_log_correction": serialize_interval(correction),
                                                "quadratic_prediction": serialize_interval(second),
                                                "quadratic_remainder": serialize_interval(residual)}
                                               for row, value, correction, second, residual in zip(inside, z, actual_correction, quadratic, residuals)]},
        "observed_spatial_energy": {"common_column_squared_norm": serialize_interval(ev),
                                    "common_spatial_residual_squared_norm": serialize_interval(eh),
                                    "interaction_squared_norm": serialize_interval(ez),
                                    "h_fraction_among_h_and_Z": serialize_interval(eh / (eh + ez)),
                                    "h_fraction_of_original_centered_column_and_Z_energy": serialize_interval(eh / (ev + ez)),
                                    "common_column_fraction_before_spatial_projection": serialize_interval(ev / (ev + ez))},
        "synthetic_energy_examples": {"status": "exact algebraic perturbation examples, not additional observations",
                                      "construction": "rows (a+b)*s and (a-b)*s, a=1/10, b=1/125; center s, then remove its affine spatial projection",
                                      "formula": "Let S=||center(s)||^2, H=||(I-Pi_affine)s||^2. E_v=2a^2S, E_Z=2b^2S, E_h=2a^2H. Residual fraction is a^2H/(a^2H+b^2S), not generally a^2/(a^2+b^2).",
                                      "examples": examples}}
    output.mkdir(parents=True, exist_ok=True)
    destination = output / "exact_two_line_bounds_audit.json"
    destination.write_text(json.dumps(result, indent=2, allow_nan=False) + "\n")
    summary = {"output": str(destination),
               "bounds": {label: result["two_line_bounds"][label] for label in
                           ("M", "delta", "C3", "Cmax", "quadratic_remainder_upper_expressions", "actual_max_absolute_quadratic_remainder")},
               "short_upper_certificates": certified_short_bounds,
               "observed_energy": result["observed_spatial_energy"],
               "synthetic_energy_examples": [{"name": row["name"],
                                               "h_retention": row["fraction_of_common_column_energy_retained_in_h"],
                                               "h_fraction_h_plus_Z": row["h_fraction_among_h_and_Z_after_projection"],
                                               "h_fraction_original_centered_energy": row["h_fraction_of_original_centered_column_and_Z_energy"]}
                                              for row in examples]}
    print(json.dumps(summary, indent=2, allow_nan=False))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--orders-audit", type=Path, required=True)
    parser.add_argument("--interior-audit", type=Path, required=True)
    parser.add_argument("--intake", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    audit(args.source, args.orders_audit, args.interior_audit, args.intake, args.output)
