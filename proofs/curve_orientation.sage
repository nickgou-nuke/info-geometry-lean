# curve_orientation.sage
var('t', 'x', 'y')
# Parameterized circle
x(t) = cos(t)
y(t) = sin(t)
dx_dt = diff(x(t), t)
dy_dt = diff(y(t), t)

# Complex contour integral for winding number around origin
# 1/(2*pi*I) * int (1/z) dz
# dz = dx + I * dy
# z = x + I * y
# dz/z = (dx + I * dy) / (x + I * y) = (x*dx + y*dy)/(x^2+y^2) + I*(x*dy - y*dx)/(x^2+y^2)
# Imaginary part integrated gives the winding number
integrand = (x(t)*dy_dt - y(t)*dx_dt) / (x(t)^2 + y(t)^2)

winding_number = 1/(2*pi) * integral(integrand, t, 0, 2*pi)
print(f"Winding number: {winding_number}")
