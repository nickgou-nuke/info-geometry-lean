#!/usr/bin/env python3
"""
GAP / Python Generator for Five-Graded Jacobi Orbit Decomposition.

Analyzes the 125 homogeneous grade triples from {-2, -1, 0, +1, +2}^3
(and the 216 lane triples from {-2, -1, 0s, 0h, +1, +2}^3)
under:
1. C3 cyclic permutation: (a, b, c) -> (b, c, a) [sign = +1]
2. Skew transposition: (a, b, c) -> (b, a, c) [sign = -1]
3. Chevalley duality: (a, b, c) -> (-a, -b, -c)
4. Grade vanishing condition: [g_i, g_j] = 0 when |g_i + g_j| > 2

Emits:
- Canonical orbit representatives
- Dispatch table mapping each triple to (representative, permutation, sign)
- Exportable JSON and Lean classification scaffolding
"""

import json

GRADES = [-2, -1, 0, 1, 2]

def grade_bracket_allowed(g1, g2):
    """Returns True if the bracket [g1, g2] is inside the 5-graded bounds [-2, 2]."""
    return abs(g1 + g2) <= 2

def jacobi_triple_nontrivial(g1, g2, g3):
    """
    Returns False if all three bracket terms [g1, [g2, g3]], [g2, [g3, g1]], [g3, [g1, g2]]
    vanish definitionally by grade truncation.
    """
    term1 = grade_bracket_allowed(g2, g3) and grade_bracket_allowed(g1, g2 + g3)
    term2 = grade_bracket_allowed(g3, g1) and grade_bracket_allowed(g2, g3 + g1)
    term3 = grade_bracket_allowed(g1, g2) and grade_bracket_allowed(g3, g1 + g2)
    return term1 or term2 or term3

def compute_orbit_decomposition():
    triples = [(g1, g2, g3) for g1 in GRADES for g2 in GRADES for g3 in GRADES]
    print(f"Total 5-grade triples: {len(triples)}")

    visited = set()
    orbits = []
    dispatch_table = {}

    for t in triples:
        if t in visited:
            continue
        g1, g2, g3 = t
        if not jacobi_triple_nontrivial(g1, g2, g3):
            # Trivial grade-forced zero
            visited.add(t)
            dispatch_table[t] = {
                "representative": "trivial_grade_zero",
                "orbit_type": "vanishes_by_grade_bounds",
                "sign": 0,
                "perm": [0, 1, 2]
            }
            continue

        # S3 orbit of t:
        s3_perms = [
            ([0, 1, 2], +1),
            ([1, 2, 0], +1),
            ([2, 0, 1], +1),
            ([1, 0, 2], -1),
            ([0, 2, 1], -1),
            ([2, 1, 0], -1),
        ]
        
        # Dual Chevalley orbit
        current_orbit = []
        for p, sgn in s3_perms:
            perm_t = (t[p[0]], t[p[1]], t[p[2]])
            dual_t = (-t[p[0]], -t[p[1]], -t[p[2]])
            current_orbit.append((perm_t, sgn, "direct", p))
            current_orbit.append((dual_t, sgn, "dual", p))

        # Select lexicographically minimal canonical representative
        valid_reps = [item[0] for item in current_orbit]
        rep = min(valid_reps)
        
        for ot, sgn, mode, p in current_orbit:
            if ot not in visited:
                visited.add(ot)
                dispatch_table[ot] = {
                    "representative": rep,
                    "mode": mode,
                    "sign": sgn,
                    "perm": p
                }
        
        orbits.append({
            "representative": rep,
            "size": len(set(valid_reps)),
            "sum": sum(rep)
        })

    print(f"Nontrivial canonical orbit representatives found: {len(orbits)}")
    for i, orb in enumerate(sorted(orbits, key=lambda x: (x['sum'], x['representative']))):
        print(f"  Orbit {i+1:2d}: Rep = {orb['representative']}, sum = {orb['sum']:+2d}, orbit size = {orb['size']}")

    return dispatch_table, orbits

if __name__ == "__main__":
    dispatch, orbits = compute_orbit_decomposition()
    with open("scratch/five_grade_jacobi_dispatch.json", "w") as f:
        json.dump({"orbits": orbits, "dispatch": {str(k): v for k, v in dispatch.items()}}, f, indent=2)
    print("\nSaved orbit dispatch ledger to scratch/five_grade_jacobi_dispatch.json")
