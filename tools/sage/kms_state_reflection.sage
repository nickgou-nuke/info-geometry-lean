import sys

var('t, beta, E1, E2')
H = matrix([[E1, 0], [0, E2]])
rho = matrix([[exp(-beta*E1), 0], [0, exp(-beta*E2)]])
U_t = matrix([[exp(I*E1*t), 0], [0, exp(I*E2*t)]])
U_minus_t = matrix([[exp(-I*E1*t), 0], [0, exp(-I*E2*t)]])

var('A11, A12, A21, A22')
var('B11, B12, B21, B22')
A = matrix([[A11, A12], [A21, A22]])
B = matrix([[B11, B12], [B21, B22]])

A_t = U_t * A * U_minus_t
F_t = (rho * A_t * B).trace()
G_t = (rho * B * A_t).trace()

F_t_shifted = F_t.subs(t == t - I*beta)

F_t_shifted_simp = F_t_shifted.simplify_full()
G_t_simp = G_t.simplify_full()

diff = (F_t_shifted_simp - G_t_simp).simplify_full()

print("KMS Verification:")
print(f"F(t - i*beta) - G(t) = {diff}")
if diff == 0:
    print("SUCCESS: KMS boundary condition verified symbolically.")
else:
    print("FAILURE: KMS condition not met.")
    sys.exit(1)
