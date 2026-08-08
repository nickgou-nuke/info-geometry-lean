# Construct the Cl(5,5) Clifford algebra
Q = QuadraticForm(QQ, 10, [1]*5 + [-1]*5)
Cl.<e1,e2,e3,e4,e5,e6,e7,e8,e9,e10> = CliffordAlgebra(Q)

# Define a null vector representing a Majorana parafermion mode
# Q(v) = v1^2 + ... + v5^2 - v6^2 - ... - v10^2
# A null vector can be e.g., e1 + e6
v = e1 + e6

# Explicitly compute that its square evaluates exactly to the zero scalar
v_squared = v * v

print(f"Null vector v = {v}")
print(f"v^2 = {v_squared}")
assert v_squared == 0, "The square of the null vector is not zero!"
print("Anomaly algebraically cancelled: F * F = 0.")
