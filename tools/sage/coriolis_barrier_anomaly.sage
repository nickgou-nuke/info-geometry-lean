#!/usr/bin/env sage
import json

def verify_drazin_algebra():
    print("=== SageMath: Drazin Inverse and Projector Verification ===")
    # Define a singular matrix A over QQ
    A = matrix(QQ, [[1, 1, 0], [0, 1, 0], [0, 0, 0]])
    
    # Jordan form decomposition to compute the Drazin inverse
    # A has eigenvalue 1 (mult 2) and 0 (mult 1)
    # The Drazin inverse of Jordan block of 1 is the inverse, and of 0 is 0
    # A^D should be the same as the inverse on the invertible subspace, and 0 on ker(A)
    # Here A has index 1 (since the nilpotency index of the 0 block is 1)
    # Let's verify the Drazin inverse conditions for AD = matrix([[1, -1, 0], [0, 1, 0], [0, 0, 0]])
    AD = matrix(QQ, [[1, -1, 0], [0, 1, 0], [0, 0, 0]])
    
    # 1. A * AD == AD * A
    assert A * AD == AD * A
    # 2. AD * A * AD == AD
    assert AD * A * AD == AD
    # 3. A^2 * AD == A
    assert A^2 * AD == A
    
    # Compute the Drazin spectral projector P_D = A * A^D
    PD = A * AD
    print(f"Drazin Projector P_D:\n{PD}")
    
    # Verify it is a projector (P_D^2 == P_D)
    assert PD * PD == PD
    print("Drazin relations verified successfully!")

def verify_self_concordance():
    print("=== SageMath: Self-Concordance Verification ===")
    x = var('x')
    assume(x > 0)
    f = x - log(x) - 1
    
    f1 = diff(f, x)
    f2 = diff(f1, x)
    f3 = diff(f2, x)
    
    # For x > 0, |f'''(x)| is -f'''(x)
    lhs = -f3
    rhs = 2 * (f2)^(3/2)
    
    diff_val = simplify(lhs - rhs)
    print(f"Self-concordance difference in Sage: {diff_val}")
    assert diff_val == 0
    print("Self-concordance verified successfully!")

def main():
    verify_drazin_algebra()
    verify_self_concordance()
    print("All SageMath formalizations verified successfully!")

main()
