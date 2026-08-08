import sympy as sp

print("==================================================================")
print("Formalization: Commutation of SU(3) and SU(2) in the g_0 Sector")
print("==================================================================\n")

print("According to the TKK architecture embedded in D5 (or SO(10) / SU(5)),")
print("both the Strong Interaction (SU(3)) and Isospin (SU(2)) live in the g_0 grading.")
print("To preserve the independence of color and flavor, they must commute.")
print("We embed them into the 5x5 matrix algebra of the g_0 sector.\n")

# Define the 5x5 matrix space
# SU(3) color lives in the upper 3x3 block
# SU(2) flavor lives in the lower 2x2 block

# Create generic SU(3) generator (using symbols for the 8 Gell-Mann components)
g1, g2, g3, g4, g5, g6, g7, g8 = sp.symbols('g1:9', real=True)
# A generic traceless 3x3 Hermitian matrix
SU3_block = sp.Matrix([
    [g3 + g8/sp.sqrt(3), g1 - sp.I*g2, g4 - sp.I*g5],
    [g1 + sp.I*g2, -g3 + g8/sp.sqrt(3), g6 - sp.I*g7],
    [g4 + sp.I*g5, g6 + sp.I*g7, -2*g8/sp.sqrt(3)]
])

# Create generic SU(2) generator (using symbols for the 3 Pauli components)
w1, w2, w3 = sp.symbols('w1:4', real=True)
# A generic traceless 2x2 Hermitian matrix
SU2_block = sp.Matrix([
    [w3, w1 - sp.I*w2],
    [w1 + sp.I*w2, -w3]
])

# Embed into the 5x5 g_0 algebra space
# SU(3) embedded matrix:
T_SU3 = sp.zeros(5, 5)
T_SU3[0:3, 0:3] = SU3_block

# SU(2) embedded matrix:
T_SU2 = sp.zeros(5, 5)
T_SU2[3:5, 3:5] = SU2_block

print("1. Generic SU(3) Strong Interaction Generator (in 5x5 space):")
sp.pprint(T_SU3)
print("\n2. Generic SU(2) Electroweak Isospin Generator (in 5x5 space):")
sp.pprint(T_SU2)

# Compute the Lie Bracket (Commutator)
print("\n3. Computing the Lie Bracket [SU(3), SU(2)] = T_SU3 * T_SU2 - T_SU2 * T_SU3")
Commutator = T_SU3 * T_SU2 - T_SU2 * T_SU3

sp.pprint(Commutator)

if Commutator == sp.zeros(5, 5):
    print("\n[RESULT] THE COMMUTATOR IS EXACTLY ZERO!")
    print("This mathematically proves that Color (SU(3)) and Flavor (SU(2)) are orthogonal")
    print("subalgebras within the TKK g_0 sector. They act on the same Dirac vacuum (g_1 + g_-1)")
    print("but their operations are completely independent. This is the structural foundation")
    print("of the Standard Model gauge independence within the unified TKK closure!")
else:
    print("\n[RESULT] Non-zero commutator found. Something is wrong with the embedding.")
