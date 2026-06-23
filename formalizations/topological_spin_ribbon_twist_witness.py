import sympy as sp
import sys

def verify_ribbon_twist_and_spin_statistics():
    """
    Finite 2x2 witness for the algebraic readouts used by
    `FiveGradedTopologicalInvariants.lean`.

    This checks a concrete Möbius parity matrix with S^2 = -I and Tr(S) = 0.
    It is a companion calculation, not a proof of the general topological
    interpretation.
    """
    # Möbius inversion generator
    S = sp.Matrix([[0, 1], [-1, 0]])
    I = sp.eye(2)
    
    # 1. Ribbon Twist / Topological Spin
    # The phase acquired by a 2*pi rotation in the conformal geometry.
    sigma_sq = S * S
    assert sigma_sq == -I, "Ribbon twist constraint failed!"
    
    print("Finite Möbius parity phase witness (S^2 = -I):")
    sp.pprint(sigma_sq)
    
    # 2. Local Pontryagin Anomaly (Atiyah-Singer Index)
    # The anomaly is proportional to the trace of the parity generator.
    assert sp.trace(S) == 0, "Local Pontryagin Anomaly is non-zero!"
    
    print("\nLocal Pontryagin Index Obstruction (Tr(S)): 0")
    print("\nSUCCESS: finite -I centralizer and trace-zero witness verified.")

if __name__ == "__main__":
    verify_ribbon_twist_and_spin_statistics()
