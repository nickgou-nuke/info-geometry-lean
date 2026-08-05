"""Exact grade readout for the retained Cl(5,5) Witt packet."""

load("01_cl55_witt_generators.sage")
import json

grade_polynomial = {}
for k in range(-5, 6):
    grade_polynomial[str(k)] = int(sum(1 for g in grades if g == k))

retained_grade_dimensions = {str(k): int(sum(1 for g in grades if g == k))
                             for k in [-2, -1, 0, 1, 2]}

with open("../../../artifacts/cl55_five_grade/grades.json", "w") as stream:
    json.dump({
        "field": "QQ",
        "operator": "N=sum(c_i*a_i)-5/2",
        "retained_grades": retained_grade_dimensions,
        "full_End_S_grade_multiplicities": grade_polynomial,
        "retained_window": [-2, -1, 0, 1, 2],
        "outside_window_present": any(k not in [-2, -1, 0, 1, 2]
                                       for k in range(-5, 6)
                                       if grade_polynomial[str(k)] > 0)
    }, stream, indent=2, sort_keys=True, default=int)

print("SAGE:grade_report=artifacts/cl55_five_grade/grades.json")
