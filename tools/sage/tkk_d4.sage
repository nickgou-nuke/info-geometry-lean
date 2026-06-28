# tools/sage/tkk_d4.sage
# Minimal test for D4 Lie algebra

R = QQ
L = lie_algebras.so(QQ, 8)  # so(8) of type D4

print("Lie algebra L =", L)
print("Dimension of L:", L.dimension())
# If we can get the Cartan subalgebra dimension (rank) via a different method:
# Try to get the Lie algebra's Cartan subalgebra via the `cartan_subalgebra` attribute if exists.
# We'll just try and catch.
try:
    rank = L.rank()
    print("Rank (via L.rank()):", rank)
except AttributeError:
    pass
try:
    # Maybe the Cartan subalgebra is a Lie algebra itself
    C = L.cartan_subalgebra()
    print("Cartan subalgebra:", C)
    print("Dimension of Cartan subalgebra:", C.dimension())
except AttributeError:
    pass
print("Success: basic construction works.")