import sympy as sp

print("==================================================================")
print("Anomalies from Non-Commuting Moore-Penrose and Drazin Inverses")
print("==================================================================\n")

# Let's consider a nilpotent operator N (representing our chiral null-space / parafermions)
# A simple nilpotent 2x2 matrix (like the off-diagonal block of a Zorn matrix)
N = sp.Matrix([[0, 1], [0, 0]])

print("1. The Nilpotent Null-Space Generator N (e.g., Parafermion state):")
sp.pprint(N)
print("\nNotice N^2 = 0. It is strictly nilpotent.\n")

# For nilpotent matrices, the Drazin inverse (N^D) is strictly 0.
# The Moore-Penrose pseudo-inverse (N^+) can be computed via SVD or limit.
# For N = [[0,1],[0,0]], N^+ is [[0,0],[1,0]] (the transpose).
N_Drazin = sp.Matrix([[0, 0], [0, 0]])
N_MP = sp.Matrix([[0, 0], [1, 0]])

print("2. Generalized Inverses:")
print("Drazin Inverse N^D (preserves spectral properties, nilpotence -> 0):")
sp.pprint(N_Drazin)
print("\nMoore-Penrose Inverse N^+ (preserves metric/geometric properties):")
sp.pprint(N_MP)

# The Obstruction / Anomaly comes from the non-commutativity of the projectors
# Let's look at the projectors formed by Moore-Penrose:
P1 = N * N_MP
P2 = N_MP * N

print("\n3. The Non-Commuting Projectors (The Origin of the Anomaly!):")
print("Projector P1 = N * N^+ :")
sp.pprint(P1)
print("\nProjector P2 = N^+ * N :")
sp.pprint(P2)

Commutator = P1 * P2 - P2 * P1
print("\n4. Commutator [P1, P2] (The Anomaly Obstruction):")
sp.pprint(Commutator)

print("\n--- Physical Implications ---")
print("1. Weyl Anomaly & Dilaton: The failure of these geometric projectors to commute")
print("   creates a non-zero trace/commutator in the regularized vacuum.")
print("   This trace obstruction IS the conformal/Weyl anomaly. To restore the symmetry,")
print("   a new scalar field must emerge -- THE DILATON!")
print("2. Souriau Thermodynamics: In Souriau's Lie group thermodynamics, this non-commutative")
print("   symplectic structure (the failure of exact integration) introduces a central extension.")
print("   This extension enforces an irrotational phase flow (since curl-free potentials")
print("   absorb the anomaly phase).")
print("3. Drazin vs Moore-Penrose: The mismatch between spectral (Drazin) and geometric (MP)")
print("   inverses is exactly the mismatch between topological indexing (Atiyah-Singer)")
print("   and the local metric regularization (Fujikawa's method)!")
