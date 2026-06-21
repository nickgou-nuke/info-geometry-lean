import sympy as sp

# Define symbols
d = sp.Symbol('d', positive=True) # embedding dimension
beta = 1 / sp.sqrt(d)             # Inverse temperature
i, j = sp.symbols('i j', cls=sp.Idx)
N = sp.Symbol('N', integer=True)  # Number of tokens / spin states

# Define energy states / query-key dot products
x = sp.IndexedBase('x') # x_i = Q K^T
E = sp.IndexedBase('E') # E_i = -x_i

# Define the Partition Function Z
Z_transformer = sp.Sum(sp.exp(x[j] / sp.sqrt(d)), (j, 1, N))
Z_boltzmann = sp.Sum(sp.exp(-beta * E[j]), (j, 1, N))

print("1. The Partition Function (Z):")
print("Transformer Denominator: ", sp.pretty(Z_transformer))
print("Boltzmann Partition Z:   ", sp.pretty(Z_boltzmann))
# Substitute E_i = -x_i
print("Isomorphism Verified:    ", Z_boltzmann.subs(E[j], -x[j]) == Z_transformer)

# Define the Probability Distribution / Softmax
p_i_transformer = sp.exp(x[i] / sp.sqrt(d)) / Z_transformer
p_i_boltzmann = sp.exp(-beta * E[i]) / Z_boltzmann

print("\n2. The Probability Distribution (Softmax):")
print("Transformer Attention Weights: ", sp.pretty(p_i_transformer))
print("Boltzmann Probability p_i:   ", sp.pretty(p_i_boltzmann))
print("Isomorphism Verified:          ", p_i_boltzmann.subs({E[i]: -x[i], E[j]: -x[j]}) == p_i_transformer)

# Define the Free Energy (F)
F = -(1 / beta) * sp.log(Z_boltzmann)
print("\n3. The Free Energy (F):")
print(sp.pretty(F))

# The gradient of Free Energy gives the expectation value (magnetization)
# For the discrete case, dF / dE_i = p_i
dF_dEi = sp.simplify(sp.diff(F, E[i]))
print("\n4. Derivative of Free Energy (dF / dE_i):")
print(sp.pretty(dF_dEi))
print("Notice this is exactly p_i_boltzmann!")

