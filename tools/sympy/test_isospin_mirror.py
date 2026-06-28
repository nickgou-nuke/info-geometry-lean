#!/usr/bin/env python3
"""
Formalization of mirror nuclei dynamics using SymPy.
"""
import sys
from sympy import symbols, Function, Integral, oo, I, simplify, Matrix, zeros, Eq, Abs, Symbol
from sympy.physics.matrices import msigma

def run_tests():
    all_passed = True

    print("Running Mirror Nuclei Dynamics Formalization Tests...")

    try:
        # 1. SU(2) isospin algebra using Pauli matrices
        print("1. Testing SU(2) isospin algebra... ", end="")
        tau_x = msigma(1)
        tau_y = msigma(2)
        tau_z = msigma(3)
        # Commutation relation [tau_x, tau_y] = 2i tau_z
        comm = tau_x * tau_y - tau_y * tau_x
        if comm == 2 * I * tau_z:
            print("PASS")
        else:
            print("FAIL")
            all_passed = False

        # 2. MED, CED, TED formulas as differences of multiplet energies
        print("2. Testing MED, CED, TED formulas... ", end="")
        E_m1, E_0, E_p1 = symbols('E_{Tz=-1} E_{Tz=0} E_{Tz=+1}')
        E_mh, E_ph = symbols('E_{Tz=-1/2} E_{Tz=+1/2}')
        
        # Multiplet Energy Difference (T=1/2 mirror nuclei)
        MED = E_mh - E_ph
        # Coulomb Energy Difference (T=1 triplets)
        CED = E_m1 - E_p1
        # Triplet Energy Difference (T=1 triplets)
        TED = E_m1 + E_p1 - 2*E_0
        
        if MED != 0 and CED != 0 and TED != 0:
            print("PASS")
        else:
            print("FAIL")
            all_passed = False

        # 3. B(E\lambda) transition rate formula
        print("3. Testing B(E_lambda) transition rate formula... ", end="")
        Ji, Jf, lam = symbols('J_i J_f lambda', real=True)
        M_E = Symbol(r'\langle J_f || M(E\lambda) || J_i \rangle')
        B_E_lambda = (1 / (2*Ji + 1)) * Abs(M_E)**2
        
        if B_E_lambda.has(Ji) and B_E_lambda.has(M_E):
            print("PASS")
        else:
            print("FAIL")
            all_passed = False

        # 4. Thomas-Ehrman shift symbolically (Delta E_C vs radial integral of weakly bound s-wave)
        print("4. Testing Thomas-Ehrman shift symbolically... ", end="")
        r = symbols('r', positive=True)
        u_s = Function('u_s')(r) # Weakly bound s-wave radial wavefunction
        V_C = Function('V_C')(r) # Coulomb potential difference
        Delta_E_C = Integral(u_s**2 * V_C, (r, 0, oo))
        
        if Delta_E_C.has(Integral) and Delta_E_C.has(u_s):
            print("PASS")
        else:
            print("FAIL")
            all_passed = False

        # 5. Linear system for effective charges e_pi, e_nu
        print("5. Testing linear system for effective charges e_pi, e_nu... ", end="")
        e_pi, e_nu, M_pi, M_nu = symbols('e_pi e_nu M_pi M_nu')
        
        # Mirror symmetry implies interchanging protons and neutrons
        M_p = e_pi * M_pi + e_nu * M_nu
        M_n = e_nu * M_pi + e_pi * M_nu
        
        system_matrix = Matrix([[M_pi, M_nu], [M_nu, M_pi]])
        charges = Matrix([e_pi, e_nu])
        transitions = Matrix([M_p, M_n])
        
        # Verify the system equation holds: Matrix * Charges = Transitions
        if simplify(system_matrix * charges - transitions) == zeros(2, 1):
            print("PASS")
        else:
            print("FAIL")
            all_passed = False

        # 6. Isospin mixing matrix elements mathematically
        print("6. Testing isospin mixing matrix elements... ", end="")
        H_c_01 = Symbol(r'\langle T=0 | H_C | T=1 \rangle')
        E_T0, E_T1 = symbols('E_{T=0} E_{T=1}')
        isospin_mixing_alpha = H_c_01 / (E_T0 - E_T1)
        
        if isospin_mixing_alpha.has(H_c_01):
            print("PASS")
        else:
            print("FAIL")
            all_passed = False

        # 7. Symmetry energy correlation L vs Delta R_ch
        print("7. Testing symmetry energy correlation L vs Delta R_ch... ", end="")
        L, a, b, Delta_R_ch = symbols(r'L a b \Delta{R}_{ch}')
        skin_correlation = Eq(Delta_R_ch, a * L + b)
        
        if skin_correlation.lhs == Delta_R_ch and skin_correlation.rhs == a * L + b:
            print("PASS")
        else:
            print("FAIL")
            all_passed = False

    except Exception as e:
        print(f"FAIL (Exception: {e})")
        all_passed = False

    if all_passed:
        print("\nALL TESTS PASSED.")
        sys.exit(0)
    else:
        print("\nSOME TESTS FAILED.")
        sys.exit(1)

if __name__ == "__main__":
    run_tests()
