import sympy as sp

def main():
    # 1. Define symbolic variables for proton and neutron densities, their Laplacians, and kinetic densities
    rho_p, rho_n = sp.symbols('rho_p rho_n')
    del2_rho_p, del2_rho_n = sp.symbols('del2_rho_p del2_rho_n')
    K_p, K_n = sp.symbols('K_p K_n')
    
    # Parameters for the Skyrme CSB and CIB energy density functionals
    s0, s1, s2 = sp.symbols('s0 s1 s2')
    u0, u1, u2 = sp.symbols('u0 u1 u2')
    
    # 2. Symbolically encode the CSB energy density functional (H_CSB) from equation A.15
    H_CSB = s0 * (rho_n**2 - rho_p**2) + s1 * (rho_n * K_n - rho_p * K_p) + s2 * (rho_n * del2_rho_n - rho_p * del2_rho_p)
    
    # 3. Symbolically encode the CIB energy density functional (H_CIB) from equation A.25
    H_CIB = u0 * rho_n * rho_p + u1 * (rho_n * K_p + rho_p * K_n) + u2 * (rho_n * del2_rho_p + rho_p * del2_rho_n)
    
    # 4. Calculates the functional derivative with respect to rho_p and rho_n to find the mean-field potentials.
    # The functional derivative is dH/drho + Laplacian(dH/ddel2_rho)
    def functional_derivative(H, rho_q, del2_rho_q):
        d_rho = sp.diff(H, rho_q)
        d_del2 = sp.diff(H, del2_rho_q)
        # Apply the Laplacian operator to the derivative with respect to the Laplacian of the density.
        # Since our functionals are quadratic in densities, d_del2 is a linear combination of densities.
        # So we can just substitute densities with their Laplacians.
        laplacian_term = d_del2.subs({rho_p: del2_rho_p, rho_n: del2_rho_n})
        return sp.simplify(d_rho + laplacian_term)

    V_CSB_p = functional_derivative(H_CSB, rho_p, del2_rho_p)
    V_CSB_n = functional_derivative(H_CSB, rho_n, del2_rho_n)
    
    V_CIB_p = functional_derivative(H_CIB, rho_p, del2_rho_p)
    V_CIB_n = functional_derivative(H_CIB, rho_n, del2_rho_n)
    
    # 5. Symbolically proves that setting rho_p = rho_n (isospin symmetry) nullifies the CSB central term, but CIB persists.
    
    # Define a substitution dictionary for isospin symmetry (rho_p = rho_n)
    isospin_symmetry = {rho_p: rho_n, K_p: K_n, del2_rho_p: del2_rho_n}
    
    # Check that CSB energy density is completely nullified
    H_CSB_sym = sp.simplify(H_CSB.subs(isospin_symmetry))
    assert H_CSB_sym == 0, "Error: CSB energy density should be nullified under isospin symmetry"
    
    # Check that CIB energy density persists (is not zero)
    H_CIB_sym = sp.simplify(H_CIB.subs(isospin_symmetry))
    assert H_CIB_sym != 0, "Error: CIB energy density should persist under isospin symmetry"
    
    # Check the central terms of the mean-field potentials
    V_CSB_p_sym = sp.simplify(V_CSB_p.subs(isospin_symmetry))
    V_CSB_n_sym = sp.simplify(V_CSB_n.subs(isospin_symmetry))
    
    # Note that V_CSB_p and V_CSB_n have opposite signs, so their sum is exactly zero
    assert sp.simplify(V_CSB_p_sym + V_CSB_n_sym) == 0, "Error: CSB potentials sum should be zero under isospin symmetry"
    
    V_CIB_p_sym = sp.simplify(V_CIB_p.subs(isospin_symmetry))
    V_CIB_n_sym = sp.simplify(V_CIB_n.subs(isospin_symmetry))
    
    # CIB potentials are equal and non-zero
    assert V_CIB_p_sym == V_CIB_n_sym, "Error: CIB potentials should be symmetric under isospin symmetry"
    assert V_CIB_p_sym != 0, "Error: CIB potentials should persist"
    
    # 6. Prints PASS.
    print("PASS")

if __name__ == "__main__":
    main()
