var('z')
f(z) = (z + I) / (I*z + 1)

print("Evaluations:")
print("f(0) =", f(0))
print("f(1) =", f(1).simplify_full())
print("f(-1) =", f(-1).simplify_full())
try:
    print("f(-i) =", f(-I))
except Exception as e:
    print("f(-i) error:", e)

print("\nVerifying boundary map:")
var('theta', domain='real')
z_circ = exp(I*theta)
fz_circ = f(z_circ)

im_part = fz_circ.imag().simplify_full()
print("Imaginary part of f(exp(i*theta)):", im_part)

if im_part == 0:
    print("Verification successful: Imaginary part is exactly 0.")
else:
    print("Attempting trig expand:")
    # Rewrite exp(I*theta) as cos(theta) + I*sin(theta)
    fz_circ_trig = f(cos(theta) + I*sin(theta))
    im_part_trig = fz_circ_trig.imag().simplify_full()
    print("Imaginary part with trig:", im_part_trig)
    if im_part_trig == 0:
        print("Verification successful after trig expansion: Imaginary part is exactly 0.")
