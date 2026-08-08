# SageMath: Colimit Ladder of Number Systems

# 1. Primes as basis for the free commutative monoid (N)
Primes_Set = Primes()
print("Primes base: ", Primes_Set)

# 2. Natural numbers as free commutative monoid over Primes
N_monoid = ZZ
print("Integers (Z): ", N_monoid)

# 3. Localization to Rationals Q = S^{-1}Z
Q_field = QQ
print("Rationals (Q): ", Q_field)

# 4. Completion to Reals R
R_field = RR
print("Reals (R): ", R_field)

# 5. Pushout to Complex Field C
# C = R[x]/(x^2 + 1)
R_poly.<x> = PolynomialRing(R_field)
C_field = R_field.extension(x^2 + 1, 'I')
print("Complex Pushout (C): ", C_field)
