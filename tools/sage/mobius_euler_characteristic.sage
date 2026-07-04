print("Computing Euler characteristics...")
CP1 = simplicial_complexes.Sphere(2)
euler_cp1 = CP1.euler_characteristic()
print(f"Euler characteristic of CP^1 (S^2): {euler_cp1}")

RP1 = simplicial_complexes.Sphere(1)
euler_rp1 = RP1.euler_characteristic()
print(f"Euler characteristic of RP^1 (S^1): {euler_rp1}")

assert euler_cp1 == 2
assert euler_rp1 == 0

print("\nAnalyzing Mobius transformation f(x) = (1+x)/(1-x)")
var('x')
f = (1+x)/(1-x)

# Find fixed points
fixed_pts = solve(x == f, x)
print(f"Fixed points equations: {fixed_pts}")

# Extract roots and check domains
R.<y> = QQ[]
poly = y^2 + 1
roots_CC = poly.roots(ring=CC)
roots_RR = poly.roots(ring=RR)

print(f"Fixed points over CC: {roots_CC}")
print(f"Fixed points over RR: {roots_RR}")

assert len(roots_CC) == 2
assert len(roots_RR) == 0

print("Verification complete!")
