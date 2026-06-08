import sympy as sp

phi = (1 + sp.sqrt(5)) / 2
tau_conjugate = (1 - sp.sqrt(5)) / 2
N_tau = sp.Matrix([[0, 1], [1, 1]])
lam = sp.Symbol("lambda")

checks = {
    "phi_minpoly": sp.simplify(phi**2 - phi - 1),
    "tau_conjugate_minpoly": sp.simplify(tau_conjugate**2 - tau_conjugate - 1),
    "tau_conjugate_times_phi": sp.simplify(tau_conjugate * phi + 1),
    "fusion_matrix_charpoly": sp.factor(N_tau.charpoly(lam).as_expr() - (lam**2 - lam - 1)),
}

for name, value in checks.items():
    print(f"{name} = {value}")
    assert value == 0, (name, value)

print("strict_fibonacci_fusion_witness = ok")
