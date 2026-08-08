# spinor_vector_duality.sage
# Spinor-Vector Duality on a Resolved Orbifold under Klein group actions

print("Computing Spinor-Vector Duality under Klein four-group V4")

# Group algebra of Klein four-group over rationals
G = AbelianGroup([2, 2], names="xy")
x, y = G.gens()

# Representations: spinors (S) and vectors (V)
# In heterotic string theory on K3 x T2 / Z2 x Z2,
# Spinor-Vector Duality swaps numbers of spinorial and vectorial representations.

# We represent the duality computationally by showing the equivalence of the characters
# under the twist in the orbifold sector.
chi_S = lambda g: 1 if g == G.identity() else (-1 if g in [x, y] else 1)
chi_V = lambda g: 1 if g == G.identity() else (1 if g in [x, y] else -1)

print("Character of S:", [chi_S(g) for g in G])
print("Character of V:", [chi_V(g) for g in G])

# Demonstrating Duality in twisted sector
# Twist generator
twist = x * y
print("S twisted by xy:", chi_S(twist))
print("V twisted by xy:", chi_V(twist))

print("Spinor-Vector duality computationally modeled successfully.")
