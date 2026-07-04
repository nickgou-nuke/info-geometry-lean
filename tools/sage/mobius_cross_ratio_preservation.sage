var('z1 z2 z3 z4 a b c d')
assume(a*d - b*c != 0)

def f(z):
    return (a*z + b)/(c*z + d)

def cross_ratio(w1, w2, w3, w4):
    return ((w1 - w3)*(w2 - w4)) / ((w2 - w3)*(w1 - w4))

print("--- Standard Case ---")
cr_original = cross_ratio(z1, z2, z3, z4)
cr_transformed = cross_ratio(f(z1), f(z2), f(z3), f(z4))

diff = (cr_transformed - cr_original).full_simplify()
print("Is the cross-ratio invariant for finite points?", bool(diff == 0))

print("\n--- Limit Case: z4 -> Infinity ---")
cr_inf = limit(cr_original, z4=oo)
print("Original cross ratio limit as z4 -> oo:", cr_inf)

cr_transformed_inf = limit(cr_transformed, z4=oo).full_simplify()
print("Transformed cross ratio limit as z4 -> oo:", cr_transformed_inf)

diff_inf = (cr_transformed_inf - cr_inf).full_simplify()
print("Is the cross-ratio invariant when z4 -> oo?", bool(diff_inf == 0))
