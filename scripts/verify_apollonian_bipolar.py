#!/usr/bin/env python3
"""
Symbolic verification of the Apollonian Bipolar Field Theory
for the Virtual Point Detector (VPD) model in HPGe spectrometry.
"""

import sympy as sp

def main():
    print("=== Apollonian Bipolar Field Symbolic Verification ===")

    d, d0, a, b = sp.symbols('d d0 a b', positive=True)
    A_act, P_i, P_j, P_ij, W0 = sp.symbols('A P_i P_j P_ij W0', positive=True)
    eta_pi, eta_ti, S_geom = sp.symbols('eta_pi eta_ti S_geom', positive=True)
    eta_pj = sp.symbols('eta_pj', positive=True)
    pi = sp.pi

    # 1. Metric Inter-Polar Separation
    # Pole A at d, Pole B at -d0
    r_AB = d - (-d0)
    assert sp.simplify(r_AB - (d + d0)) == 0
    print("Check 1: r_AB = d + d0 verified.")

    # 2. Linearizer Proportionality
    # Lambda(d) = a * d + b with b = a * d0
    Lambda = a * d + a * d0
    assert sp.simplify(Lambda - a * r_AB) == 0
    print("Check 2: Lambda(d) = a * r_AB verified.")

    # 3. Inter-polar root
    # Lambda(-d0) = 0
    assert sp.simplify(Lambda.subs(d, -d0)) == 0
    print("Check 3: Lambda(-d0) = 0 (virtual pole root) verified.")

    # 4. Flux and Effective Area Identification
    # Flux J = A / (4 * pi * r_AB^2)
    # Phi = J * S_eff = A * X(d)
    # X(d) = 1 / (a^2 * (d + d0)^2) = 1 / (a^2 * r_AB^2)
    # Therefore S_eff / (4 * pi * r_AB^2) = 1 / (a^2 * r_AB^2) => S_eff = 4 * pi / a^2
    S_eff = 4 * pi / a**2
    X_d = S_eff / (4 * pi * r_AB**2)
    X_expected = 1 / (a**2 * (d + d0)**2)
    assert sp.simplify(X_d - X_expected) == 0
    print("Check 4: S_eff = 4*pi / a^2 yields exact geometric coupling X(d) verified.")

    # 5. Dual Apertures from Microscopic Transmittance
    C_i_micro = A_act * P_i * eta_pi * S_geom * a**2 / (4 * pi)
    Speak_calc = 4 * pi * C_i_micro / (A_act * P_i * a**2)
    assert sp.simplify(Speak_calc - eta_pi * S_geom) == 0
    print("Check 5: Photopeak aperture S^(peak)_i = eta_pi * S_geom verified.")

    # Total loss envelope of partner j:
    C_j_micro = A_act * P_j * eta_pj * S_geom * a**2 / (4 * pi)
    B_j_micro = A_act * P_ij * eta_pj * eta_ti * S_geom**2 * a**4 / ((4 * pi)**2) * W0
    Sv_calc = (4 * pi * B_j_micro) / (C_j_micro * a**2)
    q_ij = P_ij / P_j
    assert sp.simplify(Sv_calc - q_ij * eta_ti * S_geom * W0) == 0
    print("Check 6: Summing loss aperture S_v,j = (P_ij/P_j) * eta_ti * S_geom * W(0) verified.")

    # 6. Peak-to-Total Recovery through Apollonian Cross-Quotient
    cross_quot = Speak_calc / Sv_calc
    expected_quot = (1 / (q_ij * W0)) * (eta_pi / eta_ti)
    assert sp.simplify(cross_quot - expected_quot) == 0
    print("Check 7: Cross-quotient (S^(peak)_i / S_v,j) = (1 / (q * W0)) * (P/T)_i verified.")

    print("\nALL APOLLONIAN BIPOLAR IDENTITIES VERIFIED (Residual 0).")

if __name__ == "__main__":
    main()
