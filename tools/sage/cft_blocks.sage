# tools/sage/cft_blocks.sage
var('z1 z2 z3 z4 a b c d')

# Define the cross ratio
def cross_ratio(p1, p2, p3, p4):
    return ((p1 - p2) * (p3 - p4)) / ((p1 - p3) * (p2 - p4))

x = cross_ratio(z1, z2, z3, z4)

# Define the Moebius transformation
def f(z):
    return (a * z + b) / (c * z + d)

# Apply transformation to the coordinates
fz1 = f(z1)
fz2 = f(z2)
fz3 = f(z3)
fz4 = f(z4)

# Compute the transformed cross ratio
x_transformed = cross_ratio(fz1, fz2, fz3, fz4)

# Simplify the difference to prove equality
# We use rational_simplify() to handle rational functions
difference = (x_transformed - x).rational_simplify()

print("Original cross ratio x:")
print(x)
print("\nDifference after simplification (x_transformed - x):")
print(difference)

if difference == 0:
    print("\nProof successful: The cross ratio is strictly invariant under Moebius transformations.")
else:
    print("\nProof failed: The cross ratio is not invariant.")
