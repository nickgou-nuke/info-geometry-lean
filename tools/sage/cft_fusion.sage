from sage.all import *

alpha, b = var('alpha b')

def compute_fusion_rules(r, s):
    fusion_set = set()
    for i in range(r):
        for j in range(s):
            val = alpha + (i - (r - 1)/2)*b + (j - (s - 1)/2)/b
            fusion_set.add(val)
    return fusion_set

res = compute_fusion_rules(2, 1)
print(f"Computed Set: {res}")

expected = {alpha - b/2, alpha + b/2}
print(f"Expected Set: {expected}")

if res == expected:
    print("Verification Successful!")
else:
    print("Verification Failed.")
