#!/usr/bin/env python3
import sympy as sp

def main():
    # Define Cuntz algebra dimension (truncated for matrix analysis)
    N = 4 
    
    # Define the left shift operator S_L
    # S_L |n> = |n-1> for n > 0, S_L |0> = 0
    S_L = sp.zeros(N)
    for i in range(N-1):
        S_L[i, i+1] = 1

    print("Cuntz Left Shift Operator (S_L):")
    sp.pprint(S_L)

    # Define the modular conjugation J (exchange between physical and ghost)
    # On a doubled space 2N x 2N
    I = sp.eye(N)
    J = sp.Matrix(sp.BlockMatrix([[sp.zeros(N), I], [I, sp.zeros(N)]]))
    
    print("\nModular Conjugation J (Doubled Space):")
    sp.pprint(J)

    # Extend S_L to the doubled space acting on the physical sector
    S_L_doubled = sp.Matrix(sp.BlockMatrix([[S_L, sp.zeros(N)], [sp.zeros(N), sp.zeros(N)]]))
    
    # Calculate J * S_L * J
    J_SL_J = J * S_L_doubled * J

    print("\nAdjoint Left Shift (J S_L J):")
    sp.pprint(J_SL_J)

    # Define the discrete Dirac-Hodge gradient D = S_L + J S_L J
    D = S_L_doubled + J_SL_J

    print("\nDiscrete Dirac-Hodge Gradient D = S_L + J S_L J:")
    sp.pprint(D)

    # Prove the discrete conservation law D * rho = 0 for a constant density rho
    # Let rho be a state vector in the doubled space
    c = sp.symbols('c')
    rho = sp.Matrix([c]*2*N)
    
    D_rho = D * rho
    print("\nD * rho for constant density (vacuum symmetry):")
    sp.pprint(D_rho)
    
    # Notice that D * rho is NOT 0 at the boundaries!
    # The true vacuum state on the Cuntz algebra must balance the shifts.

if __name__ == "__main__":
    main()
