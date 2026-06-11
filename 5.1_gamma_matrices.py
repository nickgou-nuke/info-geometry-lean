import numpy as np

# Pauli matrices
sigma1 = np.array([[0, 1], [1, 0]])
sigma2 = np.array([[0, -1j], [1j, 0]])
sigma3 = np.array([[1, 0], [0, -1]])
identity_2x2 = np.eye(2)

# Gamma matrices
gamma0 = np.kron(np.array([[1, 0], [0, -1]]), identity_2x2)  # Block diagonal
gamma1 = np.kron(np.array([[0, 1], [-1, 0]]), sigma1)
gamma2 = np.kron(np.array([[0, 1], [-1, 0]]), sigma2)
gamma3 = np.kron(np.array([[0, 1], [-1, 0]]), sigma3)
gamma5 = 1j * gamma0 @ gamma1 @ gamma2 @ gamma3

# Alternative, explicit form for gamma0, gamma1, gamma2, gamma3, and gamma5
gamma0_explicit = np.array([[1, 0, 0, 0],
                            [0, 1, 0, 0],
                            [0, 0, -1, 0],
                            [0, 0, 0, -1]])

gamma1_explicit = np.array([[0, 0, 0, 1],
                            [0, 0, 1, 0],
                            [0, -1, 0, 0],
                            [-1, 0, 0, 0]])

gamma2_explicit = np.array([[0, 0, 0, -1j],
                            [0, 0, 1j, 0],
                            [0, 1j, 0, 0],
                            [-1j, 0, 0, 0]])

gamma3_explicit = np.array([[0, 0, 1, 0],
                            [0, 0, 0, -1],
                            [-1, 0, 0, 0],
                            [0, 1, 0, 0]])
gamma5_explicit = np.array([[0, 0, 1, 0],
                            [0, 0, 0, 1],
                            [1, 0, 0, 0],
                            [0, 1, 0, 0]])

#Verification
print(f"Gamma 0 equal to explicit definition: {np.array_equal(gamma0, gamma0_explicit)}")
print(f"Gamma 1 equal to explicit definition: {np.array_equal(gamma1, gamma1_explicit)}")
print(f"Gamma 2 equal to explicit definition: {np.array_equal(gamma2, gamma2_explicit)}")
print(f"Gamma 3 equal to explicit definition: {np.array_equal(gamma3, gamma3_explicit)}")
print(f"Gamma 5 equal to explicit definition: {np.array_equal(gamma5, gamma5_explicit)}")
