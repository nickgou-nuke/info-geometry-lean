import sympy as sp

def verify_dirichlet_mode_factorization():
    print("DIRICHLET MODE FACTORIZATION — SymPy VERIFICATION")
    n, u, v = sp.symbols('n u v', real=True, positive=True)
    # s = 1/2 + u + i*v
    s = sp.Rational(1, 2) + u + sp.I * v
    
    # Left hand side: n^(-s) rewritten as exp(-s * log(n))
    lhs = sp.exp(-s * sp.log(n))
    
    # Right hand side components
    L = sp.log(n)
    critical_weight = sp.exp(-sp.Rational(1, 2) * L)
    scale_envelope = sp.exp(-u * L)
    phase_wave = sp.exp(-sp.I * v * L)
    
    rhs = critical_weight * scale_envelope * phase_wave
    
    # Simplify the ratio
    diff = sp.simplify(lhs / rhs) - 1
    
    print(f"LHS: exp(-s * log(n)) = {lhs}")
    print(f"RHS: exp(-1/2 log n) * exp(-u log n) * exp(-i v log n) = {rhs}")
    
    if diff == 0:
        print("SUCCESS: Dirichlet Mode Factorization is algebraically exact.\n")
    else:
        print("FAILURE.\n")

def verify_J_even_projection():
    print("J-EVEN PROJECTION OF THE COMPLETED ZETA FUNCTION — SymPy VERIFICATION")
    # Let J be the parity/reflection operator J[f(z)] = f(-z)
    z = sp.Symbol('z')
    xi = sp.Function('xi')
    
    # Define P_minus_J projection: P_minus_J[f] = 1/2 (f(z) - f(-z))
    def P_minus_J(f_z):
        f_minus_z = f_z.subs(z, -z)
        return sp.Rational(1, 2) * (f_z - f_minus_z)
    
    # We know xi(z) = xi(-z) due to Riemann functional equation
    xi_z = xi(z)
    xi_minus_z = xi(-z)
    
    # Substitute the symmetry property
    projection = P_minus_J(xi(z)).subs(xi(-z), xi(z))
    
    print(f"P^-_J [xi(z)] = 1/2 * (xi(z) - xi(-z))")
    print(f"Applying Xi(z) = Xi(-z) gives: {projection}")
    
    if projection == 0:
        print("SUCCESS: P^-_J(xi) = 0 verified.\n")
    else:
        print("FAILURE.\n")

if __name__ == "__main__":
    verify_dirichlet_mode_factorization()
    verify_J_even_projection()
