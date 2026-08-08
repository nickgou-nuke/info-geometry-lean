import sympy as sp

def tRS_lax_matrix(n):
    hbar = sp.Symbol('hbar')
    chi = sp.symbols(f'chi1:{n+1}')
    p = sp.symbols(f'p1:{n+1}')
    T = sp.zeros(n, n)
    for i in range(n):
        for j in range(n):
            if i == j:
                T[i, j] = p[i]
            else:
                prod_term = sp.prod([(chi[j] - chi[k]*hbar)/(chi[j] - chi[k]) for k in range(n) if k != j])
                T[i, j] = (chi[j]*(1 - hbar) / (chi[j] - chi[i]*hbar)) * p[j] * prod_term
    return T

def qq_system_relation(z, hbar, xi_i, xi_ip1, Q_plus_i, Q_minus_i, Lambda_i, Q_plus_im1, Q_plus_ip1):
    lhs = xi_i * Q_plus_i.subs(z, hbar*z) * Q_minus_i - xi_ip1 * Q_plus_i * Q_minus_i.subs(z, hbar*z)
    rhs = Lambda_i * Q_plus_im1.subs(z, hbar*z) * Q_plus_ip1
    return sp.Eq(lhs, rhs)

def quiver_X_kl_magnetic_frame(k, l):
    """
    Magnetic frame relations for the X_{k,l} quiver variety.
    Generates the characteristic polynomial of the tRS system.
    """
    T = tRS_lax_matrix(k+l)
    u = sp.Symbol('u')
    return T.charpoly(u)

def quiver_M_Nk_adhm(N, k):
    """
    ADHM quiver M_{N,k} moduli space of rank-N sheaves.
    """
    return {"vertices": [k], "framing": [N]}
