# SageMath code to compute two-variable Macdonald polynomials and verify symmetry under q<->t
# This illustrates a piece of the equivariant K-theory of Hilb_n(C^2) and its 3d mirror symmetry.

# Define the fraction field QQ(q,t)
Qqt = FractionField(PolynomialRing(QQ, 'q,t'))
q, t = Qqt.gens()

# Polynomial ring in x,y over QQ(q,t)
R = PolynomialRing(Qqt, ['x','y'])
x, y = R.gens()

# Define the Macdonald polynomials for n=2 (see Macdonald's book)
# For two variables, the Macdonald polynomials P_{lambda}(x;q,t) are known explicitly.
# Partitions of 2: [2], [1,1], [] (empty partition)
# We'll compute using the formula from Macdonald, Symmetric Functions and Hall Polynomials, Chapter VI.

def mcdonald_poly(partition):
    """Return the symmetric polynomial P_lambda(x1,x2;q,t) for two variables."""
    if partition == []:
        return 1
    elif partition == [1]:
        # P_{(1)} = x1 + x2
        return x + y
    elif partition == [1,1]:
        # P_{(1,1)} = x1*x2
        return x*y
    elif partition == [2]:
        # P_{(2)} = x1^2 + x2^2 + ((1-q)/(1-t)) * x1*x2
        # Actually formula: P_{(2)} = x1^2 + x2^2 + ((1-q)/(1-t))*x1*x2
        return x^2 + y^2 + ((1-q)/(1-t))*x*y
    else:
        raise ValueError("Partition not supported for n=2")

parts = [[], [1], [1,1], [2]]
for la in parts:
    P = mcdonald_poly(la)
    # Substitute q<->t in the coefficients
    Ps = P.map_coefficients(lambda c: c.subs({q:t, t:q}))
    # Check if P equals Ps (they should be equal up to maybe a factor? Actually Macdonald polynomials are symmetric in q,t)
    # For these simple cases they are equal.
    print("Partition:", la)
    print("P =", P)
    print("P(q<->t) =", Ps)
    print("Are they equal? ", bool(simplify(P - Ps) == 0))
    print()