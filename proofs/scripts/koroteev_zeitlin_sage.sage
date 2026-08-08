# SageMath formalization of tRS spectral curves
R.<hbar, z> = PolynomialRing(QQ)
chi = var('chi1 chi2 chi3')
p = var('p1 p2 p3')

def tRS_Hamiltonians(chi_vars, p_vars, hbar):
    n = len(chi_vars)
    T = matrix(SR, n, n)
    for i in range(n):
        for j in range(n):
            if i == j:
                T[i,j] = p_vars[i]
            else:
                T[i,j] = (chi_vars[j]*(1-hbar)/(chi_vars[j] - chi_vars[i]*hbar)) * p_vars[j]
    return T.charpoly('u')

char_poly = tRS_Hamiltonians([chi1, chi2, chi3], [p1, p2, p3], hbar)
print(char_poly)
