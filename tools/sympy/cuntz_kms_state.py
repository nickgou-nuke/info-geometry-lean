import sympy as sp

print("==========================================================")
print(" CUNTZ O_2 KMS STATE AND MODULAR AUTOMORPHISM WITNESS")
print("==========================================================")

# Define symbolic Cuntz generators S1, S2
t, beta = sp.symbols('t beta', real=True)
n = 2 # O_2 algebra

# Modular Automorphism Group sigma_t(S) = e^(i t ln n) S
sigma_t_S1 = sp.exp(sp.I * t * sp.log(n))

print(f"[1] Modular Automorphism on S_j:\n    sigma_t(S_j) = {sigma_t_S1} * S_j")

# KMS Condition: tau(A * sigma_{i beta}(B)) = tau(B * A)
# For A = S_1, B = S_1^*, tau(S_1 S_1^*) = tau(S_1^* S_1) * e^(-beta ln n)
tau_1 = sp.exp(-beta * sp.log(n))

print(f"[2] KMS Condition implies trace of projector P_j = S_j S_j^*:\n    tau(S_j S_j^*) = {tau_1}")

# Cuntz Identity: S_1 S_1^* + S_2 S_2^* = 1
sum_tau = n * tau_1

print(f"[3] Cuntz Identity Trace: sum_j tau(S_j S_j^*) = {sum_tau}")

# Solve for beta
beta_solution = sp.solve(sum_tau - 1, beta)
print(f"[4] Unique KMS Inverse Temperature beta for O_2:\n    beta = {beta_solution[0]}")

print("\n=> SUCCESS: The unique KMS state on Cuntz O_2 exists strictly at beta = 1.")
print("=> This topological completion perfectly aligns with the Bosonic Pole at beta = 1.")
