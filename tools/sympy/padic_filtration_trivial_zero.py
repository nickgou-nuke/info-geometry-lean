import sympy as sp

def verify_padic_filtration():
    print("=== p-adic L functions and trivial zeroes (Perrin-Riou) ===")
    
    # We define the basis of D_p(V)
    e0, e_minus1, e_minus2 = sp.symbols('e_0 e_{-1} e_{-2}')
    lam = sp.symbols('lambda')
    
    # Define omega_e
    omega_e = (lam / 2) * e_minus2 + e_minus1 + (1 / (2 * lam)) * e0
    print(f"omega_e = {omega_e}")
    
    # Define the filtration spaces (symbolically represented by their basis vectors)
    Fil_0_basis = [omega_e]
    Fil_minus1_basis = [omega_e, e_minus1 + lam * e_minus2]
    
    print("\nFiltration Fil^0 D_p(V) basis:")
    print(Fil_0_basis)
    
    print("\nFiltration Fil^{-1} D_p(V) basis:")
    print(Fil_minus1_basis)
    
    # Check if e0 is in Fil^{-1} by seeing if it can be spanned by the basis
    # c1 * omega_e + c2 * (e_minus1 + lam * e_minus2) = e0 ?
    # From omega_e, the e0 term is c1 * (1 / (2*lam)) = 1 => c1 = 2*lam
    # Then the e_minus1 term is c1 + c2 = 0 => c2 = -2*lam
    # Let's check the e_minus2 term: c1 * (lam / 2) + c2 * lam = (2*lam)*(lam/2) + (-2*lam)*lam = lam^2 - 2*lam^2 = -lam^2 != 0.
    # So e0 is NOT solely in Fil^{-1}, which makes sense, it requires the full space to span.
    
    c1 = 2 * lam
    c2 = -2 * lam
    span_check = sp.simplify(c1 * Fil_minus1_basis[0] + c2 * Fil_minus1_basis[1])
    print(f"\nLinear combination 2*lambda*omega_e - 2*lambda*(e_{{-1}} + lambda*e_{{-2}}) =")
    print(span_check)

def verify_trivial_zero_derivative():
    print("\n=== Trivial Zero Derivative Formula ===")
    # L'_p(M, 0) = l_p(M) * L(M, 0) / Omega_inf
    L_p_prime_M_0, l_p_M, L_M_0, Omega_inf = sp.symbols('L_p^\'(M\\,0) \ell_p(M) L(M\\,0) Omega_\\infty')
    
    conjecture_eq = sp.Eq(L_p_prime_M_0, l_p_M * L_M_0 / Omega_inf)
    print(f"Greenberg-Tilouine Conjecture: {conjecture_eq}")

if __name__ == "__main__":
    verify_padic_filtration()
    verify_trivial_zero_derivative()
