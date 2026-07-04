var('a, b, c, d, z1, z2, z')
M = matrix([[a, b], [c, d]])
v = vector([z1, z2])
w = M * v
ratio = w[0] / w[1]
sub_ratio = ratio.subs(z1 == z * z2)
sim_ratio = sub_ratio.simplify_full()
expected = (a * z + b) / (c * z + d)
diff = sim_ratio - expected
diff_sim = diff.simplify_full()

print("Matrix:\n", M)
print("Vector:", v)
print("Ratio w1/w2:", ratio)
print("Substituted:", sub_ratio)
print("Simplified:", sim_ratio)
print("Expected:", expected)

if diff_sim == 0:
    print("Verification successful!")
else:
    print("Verification failed! Difference:", diff_sim)
    import sys
    sys.exit(1)
