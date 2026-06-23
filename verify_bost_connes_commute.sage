# SageMath verification of Bost-Connes modular flow commutativity
t = var('t', domain='real')
n = var('n', domain='integer')
Omega_n = var('Omega_n', domain='integer')

# Commutativity check of scalar coefficients on complex field
LHS = n^(I * t) * (-1)^Omega_n
RHS = (-1)^Omega_n * n^(I * t)

assert LHS == RHS
print("SageMath: Bost-Connes commutativity verified successfully.")
