import sympy as sp

q = sp.Symbol('q')

# Degrees of G2: d1 = 2, d2 = 6
# Poincare polynomial:
P_G2 = (1 + q) * (1 + q + q**2 + q**3 + q**4 + q**5)

# Cyclotomic polynomials:
phi1 = q - 1
phi2 = q + 1
phi3 = q**2 + q + 1
phi6 = q**2 - q + 1

P_cyclo = (phi2**2) * phi3 * phi6

diff = sp.simplify(P_G2 - P_cyclo)
print(f"P_G2(q) expanded: {sp.expand(P_G2)}")
print(f"Phi_2(q)^2 * Phi_3(q) * Phi_6(q) expanded: {sp.expand(P_cyclo)}")
print(f"Difference: {diff}")
assert diff == 0

eval_q2 = int(P_cyclo.subs(q, 2))
print(f"Evaluation at q=2: {eval_q2} (matches 189 Borel subgroups)")
assert eval_q2 == 189

# Full G2(q) order:
order_cyclo = (q**6) * (phi1**2) * (phi2**2) * phi3 * phi6
order_q2 = int(order_cyclo.subs(q, 2))
print(f"Order |G2(2)|: {order_q2} (matches 12096)")
assert order_q2 == 12096

# Cross-section maximal tori (6 conjugacy classes in W(G2)):
tori = [
    ("T_1 (split torus)", phi1**2, int((phi1**2).subs(q, 2))),
    ("T_2 (Coxeter anisotropic)", phi2**2, int((phi2**2).subs(q, 2))),
    ("T_3 (order 3 cyclic)", phi3, int(phi3.subs(q, 2))),
    ("T_6 (order 6 regular)", phi6, int(phi6.subs(q, 2))),
    ("T_s (short reflection)", phi1 * phi2, int((phi1 * phi2).subs(q, 2))),
    ("T_l (long reflection)", phi1 * phi2, int((phi1 * phi2).subs(q, 2)))
]

print("\nMaximal Tori Cross-Sections in G2(2):")
for name, form, val in tori:
    print(f"  {name:25s}: {str(form):20s} -> size at q=2: {val}")

