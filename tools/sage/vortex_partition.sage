# Vortex partition function for U(1) gauge theory with N_f=2 flavors.
# Z_vec = sum_{k=0}^\infty q^k Z_{1-loop}^{(k)} where
# Z_{1-loop}^{(k)} = prod_{i=1}^k 1/((i*epsilon1)*(i*epsilon2)) * 1/((i*epsilon1 + m1)*(i*epsilon2 + m2)) * 1/((i*epsilon1 - m1)*(i*epsilon2 - m2))
# We'll set masses m1=m2=0 for simplicity, then Z_{1-loop}^{(k)} = 1/( (epsilon1*epsilon2)^k * (k!)^2 )
# So Z = sum_{k=0}^\infty (q/(epsilon1*epsilon2))^k / (k!)^2 = I_0(2*sqrt(q/(epsilon1*epsilon2))) where I_0 is modified Bessel.
# This is symmetric under exchange epsilon1 <-> epsilon2.
# We'll compute series up to order 3 and verify symmetry.

epsilon1, epsilon2, q = var('epsilon1 epsilon2 q')
# Define series up to kmax
kmax = 3
z = 0
for k in range(0, kmax+1):
    term = (q/(epsilon1*epsilon2))^k / (factorial(k))^2
    z += taylor(term, epsilon1, 0, 2)  # expand to see symmetry? Actually term is symmetric already.
# Let's just show term is symmetric.
print("Term for k=", k, ":", term)
print("Is symmetric in epsilon1, epsilon2?", bool((epsilon1*epsilon2)^k == (epsilon2*epsilon1)^k))
# Actually we need to see if expression is unchanged under swap.
def is_symmetric(expr):
    return bool(simplify(expr.subs({epsilon1:epsilon2, epsilon2:epsilon1}) - expr) == 0)
for k in range(0, kmax+1):
    term = (q/(epsilon1*epsilon2))^k / (factorial(k))^2
    print(f"k={k}: term symmetric? {is_symmetric(term)}")
# Sum
Z = sum((q/(epsilon1*epsilon2))^k / (factorial(k))^2 for k in range(0, kmax+1))
print("\nTruncated series Z =", Z)
print("Z symmetric?", is_symmetric(Z))
# Also show that swapping epsilon1 and epsilon2 leaves Z unchanged.
Zsw = Z.subs({epsilon1:epsilon2, epsilon2:epsilon1})
print("Z after swap:", Zsw)
print("Equal?", bool(simplify(Z - Zsw) == 0))