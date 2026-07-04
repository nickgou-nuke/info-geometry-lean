var('rho alpha', domain='real')
assume(alpha > -pi, alpha <= pi)
k = exp(rho + I*alpha)

mag = abs(k).simplify_full()
print(f"Magnitude: {mag}")
if mag != exp(rho):
    print("Magnitude is not exp(rho)!")

phase = arg(k).simplify_full()
print(f"Phase: {phase}")
if phase != alpha:
    print("Phase is not alpha!")
