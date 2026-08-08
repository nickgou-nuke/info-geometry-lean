# pin55_cartan.sage
# Cartan involution matrix on the split-signature Pin(5,5) Lie algebra.
# The Lie algebra of Pin(5,5) is so(5,5) which is the split real form of type D5.

print("Pin(5,5) Cartan involution matrix on split-signature Lie algebra SO(5,5)")

# Quadratic form for split signature so(5,5)
Q = block_matrix([[matrix.zero(5), matrix.identity(5)], [matrix.identity(5), matrix.zero(5)]])

# Lie algebra elements satisfy X^T Q + Q X = 0
# The Cartan involution is typically given by theta(X) = -X^T
def cartan_involution(X):
    return -X.transpose()
