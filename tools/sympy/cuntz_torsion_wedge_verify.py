import sympy as sp

def verify_quaternionic_torsion():
    print("Verifying Quaternionic Torsion Wedge Commutator")
    
    i, j, k = sp.symbols('i j k', commutative=False)
    
    def q_mult(expr):
        expr = expr.expand()
        expr = expr.subs(i*i, -1).subs(j*j, -1).subs(k*k, -1)
        expr = expr.subs(i*j, k).subs(j*i, -k)
        expr = expr.subs(j*k, i).subs(k*j, -i)
        expr = expr.subs(k*i, j).subs(i*k, -j)
        return expr
        
    O_mu_1, O_mu_2, O_mu_3 = sp.symbols('O_mu_1 O_mu_2 O_mu_3', real=True)
    e_nu_1, e_nu_2, e_nu_3 = sp.symbols('e_nu_1 e_nu_2 e_nu_3', real=True)
    O_nu_1, O_nu_2, O_nu_3 = sp.symbols('O_nu_1 O_nu_2 O_nu_3', real=True)
    e_mu_1, e_mu_2, e_mu_3 = sp.symbols('e_mu_1 e_mu_2 e_mu_3', real=True)
    
    O_mu = O_mu_1*i + O_mu_2*j + O_mu_3*k
    e_nu = e_nu_1*i + e_nu_2*j + e_nu_3*k
    
    O_nu = O_nu_1*i + O_nu_2*j + O_nu_3*k
    e_mu = e_mu_1*i + e_mu_2*j + e_mu_3*k
    
    omega_wedge_e = q_mult(O_mu * e_nu - O_nu * e_mu)
    
    # Commutator [Omega, e]_wedge = Omega \wedge e + e \wedge Omega
    # (Because for 1-forms A, B: [A, B]_wedge = A \wedge B + B \wedge A)
    # (e \wedge Omega)_{mu nu} = e_mu Omega_nu - e_nu Omega_mu
    e_wedge_omega = q_mult(e_mu * O_nu - e_nu * O_mu)
    comm_wedge = sp.simplify(omega_wedge_e + e_wedge_omega)
    
    O_bar_mu = -O_mu
    O_bar_nu = -O_nu
    e_wedge_O_bar = q_mult(e_mu * O_bar_nu - e_nu * O_bar_mu)
    
    term_plus = sp.simplify(omega_wedge_e + e_wedge_O_bar)
    term_minus = sp.simplify(omega_wedge_e - e_wedge_O_bar)
    
    print("\nOmega ^ e + e ^ bar{Omega} =")
    print(term_plus)
    print("\nOmega ^ e - e ^ bar{Omega} =")
    print(term_minus)
    print("\n[Omega, e]_wedge (which is Omega ^ e + e ^ Omega) =")
    print(comm_wedge)
    
    if sp.simplify(term_minus - comm_wedge) == 0:
        print("\nSUCCESS: Omega ^ e - e ^ bar{Omega} exactly equals the commutator wedge [Omega, e]_wedge.")
    else:
        print("\nFAILURE.")

if __name__ == "__main__":
    verify_quaternionic_torsion()
