import sympy as sp
from galgebra.ga import Ga

print("--- SymPy / GAlgebra: Wigner Quasiprobability & Symplectic Phase Space ---")

q, p = sp.symbols('q p', real=True)
ps = Ga('PhaseSpace', g=[1, 1], coords=(q, p))
e_q, e_p = ps.mv()

W_func = sp.Function('W')(q, p)
H_func = sp.Function('H')(q, p)
W = ps.mv(W_func)
H = ps.mv(H_func)

grad = ps.grad
print("Phase Space Gradient:", grad)

# Symplectic form omega = e_q ^ e_p
omega = e_q ^ e_p
print("Symplectic Form (omega):", omega)

# Poisson bracket in GA
dH = grad * H
dW = grad * W

# Projection to components
dH_q = dH | e_q
dH_p = dH | e_p
dW_q = dW | e_q
dW_p = dW | e_p

poisson_bracket = dH_q * dW_p - dH_p * dW_q
print("Poisson Bracket {H, W}:", poisson_bracket)

print("Moyal bracket geometrically expands upon the Poisson bracket using the symplectic gradient.")
