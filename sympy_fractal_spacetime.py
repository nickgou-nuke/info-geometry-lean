import sympy as sp

def fibonacci(n):
    """Return the nth Fibonacci number, with F(0)=0, F(1)=1, F(2)=1, F(3)=2, etc."""
    if n < 0:
        # Standard extension to negative indices: F(-n) = (-1)^(n+1) F(n)
        return (-1)**(-n + 1) * fibonacci(-n)
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a

def main():
    print("=== SymPy Formalization & Verification of hep-th/0203086 ===")
    print("Paper: 'Fractal Strings as the Basis of Cantorian-Fractal Spacetime and the Fine Structure Constant'\n")

    # 1. Define Golden Mean (phi) and Golden Ratio (tau)
    phi = (sp.sqrt(5) - 1) / 2
    tau = 1 + phi

    print("1. Core Constants & Defining Relations:")
    print(f"   Golden Mean phi = {phi}")
    print(f"   Golden Ratio tau = {tau}")
    print(f"   Verify phi * tau == 1: {sp.simplify(phi * tau) == 1}")
    print(f"   Verify phi^2 + phi == 1: {sp.simplify(phi**2 + phi) == 1}")
    print(f"   Verify tau^2 - tau == 1: {sp.simplify(tau**2 - tau) == 1}")
    print()

    # 2. Verify Ring Generator Identity (Equation 25):
    # (1 + phi)^n = F_(n+1) + phi * F_n for both positive and negative indices
    print("2. Ring Generator Theorem Verification (Eq 25):")
    success_ring = True
    for n in range(-5, 10):
        lhs = tau**n
        rhs = fibonacci(n+1) + phi * fibonacci(n)
        diff = sp.simplify(lhs - rhs)
        if diff != 0:
            success_ring = False
            print(f"   Fail at n={n}: {lhs} != {rhs}")
            break
    print(f"   Ring generator identity (tau^n = F_(n+1) + phi*F_n) verified for n in [-5, 9]: {success_ring}")
    print()

    # 3. Geometric Counting Function Poles Verification (Eq 38 & 39)
    # The zeta function is: \zeta_L(s) = 1 / (1 - 2 * 2^(-phi^(j-1) * s))
    # Zeros of denominator: 1 - 2 * 2^(-phi^(j-1) * s) = 0
    # Let's verify that s_n = tau^(j-1) * (1 + 2 * pi * i * n / ln(2)) is a solution.
    print("3. Complex Dimension Poles Verification (Eq 38 & 39):")
    
    # We choose concrete values for j and n to verify the pole equation
    all_poles_valid = True
    for j_val in [1, 2, 3, 4]:
        for n_val in [-2, -1, 0, 1, 2]:
            # s_n = tau^(j-1) * (1 + 2 * pi * i * n / ln(2))
            # Note: phi^(j-1) = tau^(-(j-1))
            phi_power = phi**(j_val - 1)
            # Proposed pole
            pole_s = (tau**(j_val - 1)) * (1 + 2 * sp.pi * sp.I * n_val / sp.log(2))
            # Denominator: 1 - 2 * 2^(-phi^(j-1) * s)
            # In base e, 2^(-phi^(j-1) * s) is exp(-phi^(j-1) * s * log(2))
            expr = 1 - 2 * sp.exp(-phi_power * pole_s * sp.log(2))
            simplified_expr = sp.simplify(expr)
            if simplified_expr != 0:
                all_poles_valid = False
                print(f"   Fail for j={j_val}, n={n_val}: Denominator = {simplified_expr}")
    print(f"   Denominator 1 - 2 * 2^(-phi^(j-1) * s) vanishes at all test poles: {all_poles_valid}")
    print()

    # 4. Fine Structure Constant Transfinite Sum (Eq 56)
    # \alpha^-1 = 1 + tau^2 + tau^4 + tau^8 + tau^3 + tau^9
    print("4. Fine Structure Constant Sum Verification (Eq 56):")
    alpha_inv_terms = [1, tau**2, tau**4, tau**8, tau**3, tau**9]
    alpha_inv_sum = sum(alpha_inv_terms)
    alpha_inv_simplified = sp.simplify(alpha_inv_sum)
    expected_sum = 100 + 61 * phi
    
    print(f"   Sum of terms: {alpha_inv_sum}")
    print(f"   Simplified Sum: {alpha_inv_simplified}")
    print(f"   Is sum exactly 100 + 61*phi? {alpha_inv_simplified == expected_sum}")
    print(f"   Numerical value: {alpha_inv_simplified.evalf()}")
    print()

    # 5. El Naschie / Selvam-Fadnavis Fine Structure Constant (Eq 55)
    # \alpha^-1 = 20 * tau^4
    print("5. El Naschie / Selvam-Fadnavis Fine Structure Constant (Eq 55):")
    alpha_inv_en = 20 * tau**4
    alpha_inv_en_simplified = sp.simplify(alpha_inv_en)
    expected_en = 100 + 60 * phi
    
    print(f"   Formula: 20 * tau^4")
    print(f"   Simplified: {alpha_inv_en_simplified}")
    print(f"   Is formula exactly 100 + 60*phi? {alpha_inv_en_simplified == expected_en}")
    print(f"   Numerical value: {alpha_inv_en_simplified.evalf()}")
    print()

    # 6. Logarithmic Periodicity Resonance (Section 4)
    # d_y = 2 * pi * m * phi^(j-1) / ln(2)
    # Product should be 2 * pi * m * n
    print("6. Log-Periodicity Resonance Verification:")
    m_val, n_val, j_val = 3, 5, 2
    d_y = 2 * sp.pi * m_val * (phi**(j_val - 1)) / sp.log(2)
    # ratio = epsilon_0 / epsilon = 2^(n_val * tau^(j-1))
    ratio = 2**(n_val * (tau**(j_val - 1)))
    arg = d_y * sp.log(ratio)
    arg_simplified = sp.simplify(arg)
    expected_arg = 2 * sp.pi * m_val * n_val
    print(f"   For j={j_val}, m={m_val}, n={n_val}:")
    print(f"   d_y = {d_y}")
    print(f"   ln(ratio) = {sp.log(ratio)}")
    print(f"   Product = {arg_simplified}")
    print(f"   Is product exactly 2 * pi * m * n (mod 2*pi resonance)? {arg_simplified == expected_arg}")
    print()

if __name__ == "__main__":
    main()
