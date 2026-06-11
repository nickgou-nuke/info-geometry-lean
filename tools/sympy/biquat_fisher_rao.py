import sympy as sp

def main():
    print("--- Computing Fisher-Rao Metric via Hessian of Massieu Potential ---")
    
    # 1. Define Quaternionic Coordinates
    q0, q1, q2, q3 = sp.symbols('q0 q1 q2 q3', real=True)
    q = sp.Matrix([q0, q1, q2, q3])
    
    # 2. Define the Thermodynamic Potential Psi(q)
    # Psi(q) = 1/2 * (q0^2 + q1^2 + q2^2 + q3^2)
    Psi = sp.Rational(1, 2) * (q0**2 + q1**2 + q2**2 + q3**2)
    
    print(f"Thermodynamic Potential Psi(q) = {Psi}")
    
    # 3. Compute the Hessian Matrix
    # g_{ij} = d^2 Psi / (dq_i dq_j)
    Hessian = sp.hessian(Psi, q)
    
    print("\nFisher-Rao Information Metric (Hessian of Psi):")
    sp.pprint(Hessian)
    
    # Verify it is exactly the 4x4 Identity Matrix
    Identity4x4 = sp.eye(4)
    if Hessian == Identity4x4:
        print("\nVerification SUCCESS: The evaluated Fisher-Rao metric is exactly the 4x4 Identity Matrix.")
    else:
        print("\nVerification FAILED.")

if __name__ == "__main__":
    main()
