import numpy as np

# Define Pauli matrices
I = np.eye(2, dtype=np.complex128)
sigma_1 = np.array([[0, 1], [1, 0]], dtype=np.complex128)
sigma_2 = np.array([[0, -1j], [1j, 0]], dtype=np.complex128)
sigma_3 = np.array([[1, 0], [0, -1]], dtype=np.complex128)

def tensor_product(*matrices):
    res = matrices[0]
    for m in matrices[1:]:
        res = np.kron(res, m)
    return res

# Construct 10 Gamma matrices for Cl(10)
# Gamma_1 to Gamma_10
G = []
G.append(tensor_product(sigma_1, I, I, I, I))
G.append(tensor_product(sigma_2, I, I, I, I))
G.append(tensor_product(sigma_3, sigma_1, I, I, I))
G.append(tensor_product(sigma_3, sigma_2, I, I, I))
G.append(tensor_product(sigma_3, sigma_3, sigma_1, I, I))
G.append(tensor_product(sigma_3, sigma_3, sigma_2, I, I))
G.append(tensor_product(sigma_3, sigma_3, sigma_3, sigma_1, I))
G.append(tensor_product(sigma_3, sigma_3, sigma_3, sigma_2, I))
G.append(tensor_product(sigma_3, sigma_3, sigma_3, sigma_3, sigma_1))
G.append(tensor_product(sigma_3, sigma_3, sigma_3, sigma_3, sigma_2))

# Adjust signatures for Cl(5,5)
# We want 5 to square to +I and 5 to square to -I.
# Currently all square to +I.
# Let's multiply the even indexed ones by 1j.
eta = np.zeros(10)
Gamma = []
for i in range(10):
    if i % 2 == 0:
        Gamma.append(G[i])
        eta[i] = 1.0
    else:
        Gamma.append(1j * G[i])
        eta[i] = -1.0

# Lie algebra generators M_{ab} = 1/4 [Gamma_a, Gamma_b]
M = np.zeros((10, 10, 32, 32), dtype=np.complex128)
for a in range(10):
    for b in range(10):
        if a != b:
            M[a, b] = 0.25 * (Gamma[a] @ Gamma[b] - Gamma[b] @ Gamma[a])

# Casimir C2 = 1/2 sum_{a<b} eta^{aa} eta^{bb} M_{ab}^2 (or similar)
# Since eta is diagonal and eta_{aa} = 1/eta^{aa}
C2 = np.zeros((32, 32), dtype=np.complex128)
for a in range(10):
    for b in range(a+1, 10):
        # M_{ab} M^{ab} = M_{ab} (eta^{aa} eta^{bb} M_{ab})
        # Wait, M^{ab} = eta^{ac} eta^{bd} M_{cd} = eta^{aa} eta^{bb} M_{ab}
        term = eta[a] * eta[b] * (M[a, b] @ M[a, b])
        C2 += term

# Non-Hermitian defect
# M_ab is not necessarily anti-Hermitian because of the metric.
# Let's compute the trace of the non-Hermitian part of the Casimir or generators
defect_traces = []
for a in range(10):
    for b in range(a+1, 10):
        H = M[a, b]
        # Non-Hermitian part: N = (H - H.conj().T) / 2i (wait, anti-Hermitian is usual, H + H^\dagger)
        # Let's just look at H + H^\dagger
        defect = H + H.conj().T
        defect_traces.append(np.trace(defect @ defect))

with open("/home/goutev/.gemini/antigravity-cli/brain/2194c6ce-46ff-464a-a7c0-64b262badc39/O55_Explicit_Coordinates.md", "w") as f:
    f.write("# O(5,5) Explicit Coordinates\n\n")
    f.write("## 10-Dimensional Minkowski Spacetime Metric\n")
    f.write("Signature: (5 positive, 5 negative)\n")
    f.write(f"`eta = {list(eta)}`\n\n")
    f.write("## Quadratic Casimir $C_2$\n")
    f.write(f"The Casimir operator is a multiple of the identity:\n")
    f.write(f"Value: {np.trace(C2)/32}\n\n")
    f.write("## Non-Hermitian Defect Traces\n")
    f.write(f"Total defect trace sum: {sum(defect_traces)}\n")

print("Done")
