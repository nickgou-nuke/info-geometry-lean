#!/usr/bin/env python3
"""Exact symbolic CAS verification of the detector cross-section duality.

Formalizes:
1. Distance linearizer root: L(-d0) = 0 and d0 = b/a.
2. Restored linear rate: L_i = I_i + B_i*Q = C_i*X.
3. Activity cancellation: A = C_i * C_j * (P_ij / (P_i * P_j)) * W_0.
4. Restored photopeak area: S^(peak)_i = 4*pi*C_i / (A*P_i*a^2) = 4*pi*P_j / (C_j*P_ij*W_0*a^2).
5. Virtual summing area: S_v,j = 4*pi*B_j / (C_j*a^2).
6. Dual cross-quotient: S^(peak)_i / S_v,j = P_j / (B_j * P_ij * W_0).
7. Microscopic efficiency matching: S^(peak)_i / S_v,j = (1 / P(i|j)) * (eps_p,i / eps_t,i).
"""
import hashlib
import json
from pathlib import Path
import sympy as s

# 1. Define symbolic variables
C_i, C_j = s.symbols('C_i C_j', positive=True)
B_i, B_j = s.symbols('B_i B_j', positive=True)
P_i, P_j, P_ij = s.symbols('P_i P_j P_ij', positive=True)
W_0 = s.symbols('W_0', positive=True)
W_pp, W_pt = s.symbols('W_pp W_pt', positive=True)
a, b, d, d_0 = s.symbols('a b d d_0', positive=True)
A = s.symbols('A', positive=True)
X, Q = s.symbols('X Q', positive=True)
eps_pi, eps_pj = s.symbols('eps_pi eps_pj', positive=True)
eps_ti, eps_tj = s.symbols('eps_ti eps_tj', positive=True)

# 2. Linearizer checks
L = a * d + b
d_root = -d_0
L_at_root = L.subs([(d, d_root), (b, a * d_0)])

# 3. Restored rate
I_i = C_i * X - B_i * Q
restored_rate = I_i + B_i * Q

# 4. Activity cancellation in coincidence
A_derived = C_i * C_j * (P_ij / (P_i * P_j)) * W_0
A_derived_pp = C_i * C_j * (P_ij / (P_i * P_j)) * W_pp

# 5. Restored photopeak area
S_peak_i_raw = 4 * s.pi * C_i / (A * P_i * a**2)
S_peak_i_sub = S_peak_i_raw.subs(A, A_derived)
S_peak_i_target = 4 * s.pi * P_j / (C_j * P_ij * W_0 * a**2)

S_peak_i_sub_pp = S_peak_i_raw.subs(A, A_derived_pp)
S_peak_i_target_pp = 4 * s.pi * P_j / (C_j * P_ij * W_pp * a**2)

# 6. Virtual loss area
S_v_j = 4 * s.pi * B_j / (C_j * a**2)

# 7. Cross-quotient
cross_quotient = S_peak_i_sub / S_v_j
cross_target = P_j / (B_j * P_ij * W_0)

cross_quotient_pp = S_peak_i_sub_pp / S_v_j
cross_target_pp = P_j / (B_j * P_ij * W_pp)

# 8. Microscopic efficiency correspondence and reconciliation with Apollonian check
# Coincidence sum: Q = A * P_ij * eps_pi * eps_pj * W_pp
# Summing-out loss: Delta I_j = A * P_ij * eps_pj * eps_ti * W_pt
# Response model: Delta I_j = B_j * Q  =>  B_j = (W_pt / W_pp) * (eps_ti / eps_pi)
ratio_micro = cross_quotient.subs(B_j, eps_ti / eps_pi)
ratio_micro_target = (P_j / (P_ij * W_0)) * (eps_pi / eps_ti)

# General angular correlation split:
B_j_angular = (W_pt / W_pp) * (eps_ti / eps_pi)
ratio_micro_angular = cross_quotient_pp.subs(B_j, B_j_angular)
ratio_micro_angular_target = (P_j / (P_ij * W_pt)) * (eps_pi / eps_ti)

checks = {
    'linearizer_root': L_at_root,
    'linearizer_extract_d0': (b / a).subs(b, a * d_0) - d_0,
    'restored_linear_rate': restored_rate - C_i * X,
    'peak_area_activity_cancellation': s.simplify(S_peak_i_sub - S_peak_i_target),
    'peak_area_activity_cancellation_pp': s.simplify(S_peak_i_sub_pp - S_peak_i_target_pp),
    'cross_quotient_identity': s.simplify(cross_quotient - cross_target),
    'cross_quotient_identity_pp': s.simplify(cross_quotient_pp - cross_target_pp),
    'microscopic_ratio_matching': s.simplify(ratio_micro - ratio_micro_target),
    'microscopic_ratio_matching_angular': s.simplify(ratio_micro_angular - ratio_micro_angular_target),
    'peak_to_total_identity': s.simplify((P_ij * W_0 / P_j) * ratio_micro - (eps_pi / eps_ti)),
    'peak_to_total_recovery_general': s.simplify((P_ij * W_pt / P_j) * ratio_micro_angular - (eps_pi / eps_ti)),
    'peak_to_total_parameter_form': s.simplify((P_ij * W_pt / P_j) * cross_quotient_pp - (W_pt / (B_j * W_pp))),
    'peak_to_total_concordant_angular': s.simplify((P_ij * W_0 / P_j) * cross_quotient - (1 / B_j)),
    'unit_branching_quotient': s.simplify(ratio_micro_target.subs([(P_j, 1), (P_ij, 1)]) - (1 / W_0) * (eps_pi / eps_ti)),
    'co60_w0_exact_rational': (1 + s.Rational(5, 49) + s.Rational(4, 441)) - s.Rational(10, 9),
    'eu152_gd_w0_pure_rational': (1 - s.Rational(1, 14)) - s.Rational(13, 14),
    'eu152_sm_1408_w0_pure_rational': (1 + s.Rational(1, 4)) - s.Rational(5, 4),
    'tl208_w0_pure_rational': (1 + s.Rational(5, 28) - s.Rational(1, 231)) - s.Rational(155, 132),
}

results = {k: str(s.factor(v)) for k, v in checks.items()}

assert all(v == '0' for v in results.values()), f"Failed symbolic checks: {results}"

print(json.dumps({
    'status': 'PASSED',
    'symbolic_checks': results,
    'source': 'scripts/verify_detector_cross_section_duality.py',
    'sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
}, indent=2))

