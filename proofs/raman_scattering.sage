# raman_scattering.sage
# Non-linear algebraic invariants of Raman scattering

R.<w_I, w_S, w_A, P_I, P_S, P_A> = PolynomialRing(QQ, 6)

# Energy conservation: w_A - w_I = w_I - w_S
energy_inv = w_A - 2*w_I + w_S

# Phase conjugation matrices and non-linear susceptibility relation
# P_S = chi_3 * |E_I|^2 * E_S
# Simply representing algebraic invariants
I = Ideal([energy_inv, P_S - P_I*w_S^2, P_A - P_I*w_A^2])

print("Ideal of Raman Scattering Invariants:")
print(I)
print("Groebner basis:")
print(I.groebner_basis())
