# SageMath: D4 Triality to SU(3) Origin
L = RootSystem("D4").ambient_space()
W = L.weyl_group()

# Triality outer automorphism on simple roots
# α1 (8_v), α2 (central), α3 (8_s), α4 (8_c)
triality_perm = Permutation((1, 3, 4))

print("D4 Roots mapped under S3 Triality:")
print(f"Vector (8_v): α1 -> α{triality_perm(1)}")
print(f"Central: α2 -> α{triality_perm(2)}")
print(f"Semispinor (8_s): α3 -> α{triality_perm(3)}")
print(f"Conj Semispinor (8_c): α4 -> α{triality_perm(4)}")

# G2 stabilizer condition
# The invariant subspace under the triality permutation yields G2.
# Restricting to the tripotent T^3 = T stabilizes SU(3).
print("Algebraic breaking cascade: SO(8) -> G2 -> SU(3)")
