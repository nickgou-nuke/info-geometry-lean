var('alpha, b')

def conformal_dimension(a):
    return a * (b + 1/b - a)

def fusion_product(r, s, a):
    result = []
    for i in range(r):
        for j in range(s):
            momentum = a + (i - (r - 1)/2)*b + (j - (s - 1)/2)/b
            result.append(momentum.expand())
    return result

print(f"V_1,1 x V_alpha = {fusion_product(1, 1, alpha)}")
print(f"V_2,1 x V_alpha = {fusion_product(2, 1, alpha)}")
print(f"V_1,2 x V_alpha = {fusion_product(1, 2, alpha)}")
