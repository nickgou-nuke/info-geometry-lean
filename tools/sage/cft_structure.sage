print("CFT Structure - Spin and Phase computation")

var('A B z z_bar')

phase_A = exp(2*pi*I*A)
phase_B = exp(-2*pi*I*B)

total_phase = (phase_A * phase_B).simplify()
print(f"Total phase: {total_phase}")

var('S')
total_phase_S = total_phase.subs(A == S + B).simplify()
print(f"Phase in terms of S = A - B: {total_phase_S}")

print("For the state to be single-valued (phase = 1) or fermions (phase = -1):")
print(r"exp(2*I*pi*S) = \pm 1")
print("This implies 2*S is an integer.")

print("Solving for phase = 1:")
sol1 = solve(exp(2*I*pi*S) == 1, S, to_poly_solve=True)
print(sol1)

print("Solving for phase = -1:")
sol2 = solve(exp(2*I*pi*S) == -1, S, to_poly_solve=True)
print(sol2)
