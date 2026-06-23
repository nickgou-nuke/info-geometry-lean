#!/usr/bin/env python3
"""
Verify Hodge-Trifactor operator algebra and partition functions using SymPy.
"""
import sympy as sp
import clifford
from galgebra.ga import Ga

def verify_operator_algebra():
    print("====================================================")
    print("Verifying Hodge-Trifactor operator algebra...")
    
    # 1. Define symbolic projector variables
    # P_ex, P_co, P_har satisfy orthog-projector axioms
    # P_ex^2 = P_ex, P_co^2 = P_co, P_har^2 = P_har
    # P_ex*P_co = 0, P_ex*P_har = 0, etc.
    # P_ex + P_co + P_har = I
    
    P_ex = sp.Symbol('P_ex', commutative=False)
    P_co = sp.Symbol('P_co', commutative=False)
    
    # T = P_ex - P_co
    T = P_ex - P_co
    print(f"Operator T = {T}")
    
    # We compute T^3.
    # T^2 = (P_ex - P_co)^2 = P_ex^2 - P_ex*P_co - P_co*P_ex + P_co^2
    # Substituting projectiveness: P_ex^2 -> P_ex, P_co^2 -> P_co
    # Substituting orthogonality: P_ex*P_co -> 0, P_co*P_ex -> 0
    # Thus T^2 = P_ex + P_co.
    # T^3 = T * T^2 = (P_ex - P_co) * (P_ex + P_co) = P_ex^2 + P_ex*P_co - P_co*P_ex - P_co^2
    # = P_ex - P_co = T.
    
    # Let's perform this algebraic reduction explicitly using substitution rules
    rules = {
        P_ex * P_ex: P_ex,
        P_co * P_co: P_co,
        P_ex * P_co: 0,
        P_co * P_ex: 0
    }
    
    T2 = (T * T).expand().subs(rules).subs(rules)
    print(f"T^2 expanded = {T2}")
    assert T2 == P_ex + P_co, "T^2 verification failed!"
    
    T3 = (T * T2).expand().subs(rules).subs(rules)
    print(f"T^3 expanded = {T3}")
    assert T3 == T, "T^3 verification failed!"
    print("SymPy: T^3 = T tripotent relation verified successfully.")

def verify_partition_functions():
    print("\nVerifying partition function Euler factor mappings...")
    x = sp.Symbol('x') # x = p^-beta
    
    # Exact (Bosonic): 1 / (1 - x)
    B = 1 / (1 - x)
    # Coexact (Fermionic): 1 + x
    F = 1 + x
    # Harmonic (Möbius): 1 - x
    H = 1 - x
    
    # Cancelation relations
    BH = sp.simplify(B * H)
    FH = sp.simplify(F * H)
    
    print(f"B(x) * H(x) = {BH}")
    print(f"F(x) * H(x) = {FH}")
    
    assert BH == 1, "B(x) * H(x) is not 1!"
    assert FH == 1 - x**2, "F(x) * H(x) is not 1 - x^2!"
    print("SymPy: Partition function relationships verified successfully.")

def verify_with_clifford():
    print("\nVerifying Hodge-Trifactor components in Clifford algebra...")
    # In Cl(1,1), we can define projector matrices and verify T = P_ex - P_co
    # and T^3 = T.
    # The matrix representations for the projectors are:
    # P_ex = [[1, 0], [0, 0]]
    # P_co = [[0, 0], [0, 1]]
    # P_har = [[0, 0], [0, 0]] (fully exact and coexact, empty harmonic sector)
    
    P_ex_mat = sp.Matrix([[1, 0], [0, 0]])
    P_co_mat = sp.Matrix([[0, 0], [0, 1]])
    
    T_mat = P_ex_mat - P_co_mat
    print(f"T matrix:\n{T_mat}")
    
    T3_mat = T_mat * T_mat * T_mat
    assert T3_mat == T_mat, "T^3 = T failed in Clifford matrix model!"
    print("Clifford matrix model: T^3 = T verified.")
    print("====================================================")

if __name__ == "__main__":
    verify_operator_algebra()
    verify_partition_functions()
    verify_with_clifford()
