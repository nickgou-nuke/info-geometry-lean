# SageMath verification of Zorn projectors & sandwich formulas
OP1 = Matrix([[1, 0], [0, 0]])
OP2 = Matrix([[0, 0], [0, 1]])
I = Matrix([[1, 0], [0, 1]])

assert OP1^2 == OP1
assert OP2^2 == OP2
assert OP1*OP2 == 0

T = OP1 - OP2
assert T^3 == T

# Reconstruct
assert (T^2 + T)/2 == OP1
assert (T^2 - T)/2 == OP2
assert I - T^2 == 0

# Sandwich
x, y = var('x y')
a, b = var('a b')
X = Matrix([[a, x], [y, b]])
assert OP1 * X * OP2 == Matrix([[0, x], [0, 0]])
assert OP2 * X * OP1 == Matrix([[0, 0], [y, 0]])

print("SageMath: Zorn projector and sandwich verification successful.")
