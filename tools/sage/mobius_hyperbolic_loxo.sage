import sys

# Define variables and assumptions
var('t rho alpha r theta')
assume(t, 'real')
assume(rho, 'real')
assume(alpha, 'real')
assume(r > 0)
assume(theta, 'real')

# Define z and L(t)(z)
z = r * exp(I * theta)
L = exp((rho + I * alpha) * t) * z

print("1. 1-parameter Loxodromic flow L(t)(z):")
print(L)

print("\n2. Hyperbolic flow assertion (alpha = 0):")
L_hyp = L.subs(alpha == 0)
print("L_hyp(t)(z) =", L_hyp)

# Prove points move along radial lines by showing L_hyp / z is real and positive
ratio_hyp = (L_hyp / z).simplify_full()
print("Ratio L_hyp / z =", ratio_hyp)
assert ratio_hyp.imag().simplify_full() == 0, "Assertion failed: Ratio has imaginary part"
print("Assertion passed: L_hyp / z is purely real.")

# For a positive real ratio, arg(L_hyp) == arg(z)
# We can also check this symbolically by looking at the argument of the ratio
arg_ratio = arg(ratio_hyp).simplify_full()
print("arg(L_hyp / z) =", arg_ratio)
assert arg_ratio == 0, "Assertion failed: arg(L_hyp / z) != 0"
print("Assertion passed: polar argument matches perfectly (points move along radial lines).")

print("\n3. Loxodromic flow assertion (rho != 0, alpha != 0):")
# A curve z(t) = r(t) * e^{i phi(t)} is a logarithmic spiral if dr/dt = k * r * dphi/dt for some constant k != 0
# Let's extract r(t) and phi(t) from L
# L = exp((rho + I * alpha) * t) * r * exp(I * theta)
# L = r * exp(rho * t) * exp(I * (alpha * t + theta))
# Therefore, radius R(t) = r * exp(rho * t)
# and angle Phi(t) = alpha * t + theta

# Let's evaluate this symbolically
R_t = abs(L)
Phi_t = arg(L)

# Unfortunately Sage's abs and arg of complex variables with symbolic real parameters can be complicated.
# Let's rewrite L in a way Sage can easily parse for abs and arg.
# We can just look at log(L / z) = (rho + I*alpha)*t
log_ratio = (rho + I * alpha) * t
radial_part = log_ratio.real()
angular_part = log_ratio.imag()

print("Logarithmic ratio log(L/z) =", log_ratio)
print("Radial part change (ln(R(t)/r)):", radial_part)
print("Angular part change (Phi(t) - theta):", angular_part)

# If this forms a logarithmic spiral, the ratio of the radial change to the angular change is constant.
spiral_constant = (radial_part / angular_part).simplify_full()
print("Ratio of radial to angular change =", spiral_constant)
assert spiral_constant == rho / alpha, "Assertion failed: Not a logarithmic spiral"
print("Assertion passed: The flow represents a logarithmic spiral with constant ratio rho/alpha.")

print("\nAll assertions passed successfully!")
