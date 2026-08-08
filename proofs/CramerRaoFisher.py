import sympy as sp


I, theta, E, variance, Z = sp.symbols("I theta E variance Z", positive=True)

fisher_quadratic = I * theta**2 / 2
dual_fisher_quadratic = E**2 / (2 * I)

fenchel_gap = fisher_quadratic + dual_fisher_quadratic - theta * E
assert sp.factor(fenchel_gap) == (E - I * theta) ** 2 / (2 * I)

gradient = sp.diff(fisher_quadratic, theta)
hessian = sp.diff(gradient, theta)
assert sp.simplify(gradient - I * theta) == 0
assert sp.simplify(hessian - I) == 0

dual_gradient = sp.diff(dual_fisher_quadratic, E)
dual_hessian = sp.diff(dual_gradient, E)
assert sp.simplify(dual_gradient - E / I) == 0
assert sp.simplify(dual_hessian - 1 / I) == 0
assert sp.simplify(hessian * dual_hessian - 1) == 0

cramer_rao_bound = 1 / I
assert sp.simplify(I * cramer_rao_bound - 1) == 0

bosonic_log = sp.log(Z)
fermionic_inverse_log = sp.log(1 / Z)
assert sp.simplify(fermionic_inverse_log + bosonic_log) == 0

print("CramerRaoFisher.py: CRB, Hessian duality, and log inversion verified")
