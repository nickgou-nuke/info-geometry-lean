import sympy as sp
import sys

def burau_matrix(n, i, t, reduced=False):
    """
    Constructs the Burau representation matrix for the i-th generator of B_n.
    If reduced is False, returns the unreduced n x n matrix.
    """
    if reduced:
        # Reduced Burau is (n-1) x (n-1)
        M = sp.eye(n - 1)
        if i == 1:
            M[0, 0] = -t
            M[0, 1] = 1
        elif i == n - 1:
            M[n - 2, n - 2] = -t
            M[n - 2, n - 3] = t
        else:
            M[i - 1, i - 1] = -t
            M[i - 1, i - 2] = t
            M[i - 1, i] = 1
        return M
    else:
        # Unreduced Burau is n x n
        M = sp.eye(n)
        M[i - 1, i - 1] = 1 - t
        M[i - 1, i] = t
        M[i, i - 1] = 1
        M[i, i] = 0
        return M

def main():
    print("Point 3: Burau/Lawrence/Krammer/Bigelow representations.")
    q, t = sp.symbols('q t')
    
    print("\n--- Unreduced Burau Representation for B_4 (4x4 matrix) ---")
    s1 = burau_matrix(4, 1, t, reduced=False)
    s2 = burau_matrix(4, 2, t, reduced=False)
    s3 = burau_matrix(4, 3, t, reduced=False)
    
    print("Matrix for generator s_1:")
    sp.pprint(s1)
    
    print("\nChecking Braid Relation s1 * s2 * s1 == s2 * s1 * s2:")
    lhs = sp.simplify(s1 * s2 * s1)
    rhs = sp.simplify(s2 * s1 * s2)
    print("LHS == RHS:", lhs == rhs)
    if lhs == rhs:
        print("Fidelity demonstrated: The braid relation holds exactly.")

    print("\nComputing a trace polynomial for s1 * s2:")
    trace_val = sp.simplify((s1 * s2).trace())
    print(trace_val)

    print("\n--- Reduced Burau Representation for B_5 (4x4 matrix) ---")
    s1_r = burau_matrix(5, 1, t, reduced=True)
    s2_r = burau_matrix(5, 2, t, reduced=True)
    print("Matrix for reduced s_1:")
    sp.pprint(s1_r)
    print("Checking Braid Relation s1 * s2 * s1 == s2 * s1 * s2:", 
          sp.simplify(s1_r * s2_r * s1_r) == sp.simplify(s2_r * s1_r * s2_r))

if __name__ == "__main__":
    main()
