import sys

def test_su2_isospin():
    try:
        # Using standard Pauli-matrix based representation over QQ
        t_plus = Matrix(QQ, [[0, 1], [0, 0]])
        t_minus = Matrix(QQ, [[0, 0], [1, 0]])
        t_z = Matrix(QQ, [[1/2, 0], [0, -1/2]])
        
        # Check standard isospin algebra commutation relations
        assert t_plus * t_minus - t_minus * t_plus == 2 * t_z
        assert t_z * t_plus - t_plus * t_z == t_plus
        assert t_z * t_minus - t_minus * t_z == -t_minus
        print("PASS: SU(2) isospin Lie Algebra constructed")
    except Exception as ex:
        print(f"FAIL: SU(2) isospin Lie Algebra - {ex}")

def test_med():
    try:
        # T_z = -T and T_z = +T energies for a state J
        E_J_minus = 1.25 # MeV
        E_J_plus = 1.10 # MeV
        MED = E_J_minus - E_J_plus
        assert abs(MED - 0.15) < 1e-5
        print("PASS: Mirror Energy Differences (MED) computed")
    except Exception as ex:
        print(f"FAIL: Mirror Energy Differences (MED) - {ex}")

def test_transition_rates():
    try:
        # B(E1) and B(E2) transition rates (Weisskopf estimates)
        A = 16
        B_E1 = 6.446e-4 * A**(2.0/3.0) 
        B_E2 = 5.94e-6 * A**(4.0/3.0) 
        assert B_E1 > 0
        assert B_E2 > 0
        print("PASS: Theoretical B(E1) and B(E2) transition rates evaluated")
    except Exception as ex:
        print(f"FAIL: Theoretical B(E1) and B(E2) transition rates - {ex}")

def test_thomas_ehrman_shift():
    try:
        # A=17: 17O vs 17F (1s1/2 vs 1d5/2)
        # Shift in Coulomb energy
        delta_Ec_d52 = 3.54 # MeV
        delta_Ec_s12 = 2.77 # MeV
        TES = delta_Ec_d52 - delta_Ec_s12
        assert abs(TES - 0.77) < 1e-5
        print("PASS: Thomas-Ehrman shift for A=17 toy model computed")
    except Exception as ex:
        print(f"FAIL: Thomas-Ehrman shift for A=17 toy model - {ex}")

def test_effective_charges():
    try:
        # Solve exact linear system for effective charges (e_pi, e_nu)
        # A=54 mirror pairs example:
        # M * [e_pi, e_nu]^T = B
        M = Matrix(QQ, [[3, 1], [1, 3]])
        B = vector(QQ, [4, 2])
        e = M.solve_right(B)
        assert e[0] == 5/4
        assert e[1] == 1/4
        print("PASS: Exact linear system for effective charges solved")
    except Exception as ex:
        print(f"FAIL: Exact linear system for effective charges - {ex}")

def test_isospin_mixing():
    try:
        # A=35 system (T=1/2 and T=3/2 mixing)
        # 2x2 isospin mixing matrix H
        H = Matrix(RDF, [[0.0, 0.1], [0.1, 2.0]])
        vals = H.eigenvalues()
        assert len(vals) == 2
        print("PASS: 2x2 isospin mixing matrix for A=35 system computed")
    except Exception as ex:
        print(f"FAIL: 2x2 isospin mixing matrix for A=35 system - {ex}")

def test_linear_correlation():
    try:
        # Linear correlation L = a * Delta R_ch + b
        delta_R_ch = 0.05
        a = 1.2
        b = -0.1
        L = a * delta_R_ch + b
        assert abs(L - (-0.04)) < 1e-5
        print("PASS: Linear correlation L computed")
    except Exception as ex:
        print(f"FAIL: Linear correlation L - {ex}")

if __name__ == "__main__":
    test_su2_isospin()
    test_med()
    test_transition_rates()
    test_thomas_ehrman_shift()
    test_effective_charges()
    test_isospin_mixing()
    test_linear_correlation()
