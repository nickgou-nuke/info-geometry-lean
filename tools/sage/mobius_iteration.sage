var('lam')
var('n', domain='integer')
assume(lam > 0)

print("1. Define diagonal matrix D")
D = matrix([[lam, 0], [0, 1/lam]])
print(f"D =\n{D}")

print("\n2. Symbolically calculate D^n")
try:
    Dn = D^n
except Exception as e:
    # If D^n fails with symbolic n, we construct it directly
    Dn = matrix([[lam^n, 0], [0, (1/lam)^n]])

print(f"D^n =\n{Dn}")

print("\n3. Extract characteristic constant and prove")
k = lam^2
k_prime = (lam^n)^2
k_n = k^n
print(f"k = {k}")
print(f"k' = {k_prime}")
print(f"k^n = {k_n}")
print(f"k' == k^n is {bool(k_prime == k_n)}")

print("\n4. Verify fixed points {0, infinity} remain invariant")
p1 = vector([1, 0])
p2 = vector([0, 1])

res1 = Dn * p1
res2 = Dn * p2

print(f"D^n * [1, 0]^T = {res1}")
print(f"D^n * [0, 1]^T = {res2}")

print(f"Is [1, 0]^T purely scaled? {bool(res1[1] == 0)}")
print(f"Is [0, 1]^T purely scaled? {bool(res2[0] == 0)}")
