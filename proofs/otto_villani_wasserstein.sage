# Otto-Villani Calculus: Wasserstein gradient flow of entropy
# We model a discrete probability manifold and its Riemannian metric (Wasserstein metric).

var('p1 p2 p3 v1 v2')
# Entropy functional H(p) = \sum p_i log(p_i)
H = p1*log(p1) + p2*log(p2) + p3*log(p3)

# Wasserstein metric: G(v, v) = \sum p_{i, i+1} v_i^2
# Gradient flow equation: v = - grad(\delta H / \delta p)
# grad(phi)_i = phi_{i+1} - phi_i
# delta H / delta p_i = log(p_i) + 1

dH_dp1 = diff(H, p1)
dH_dp2 = diff(H, p2)
dH_dp3 = diff(H, p3)

v1_flow = -(dH_dp2 - dH_dp1)
v2_flow = -(dH_dp3 - dH_dp2)

print("Wasserstein Gradient Flow Velocity:")
print("v1 =", v1_flow)
print("v2 =", v2_flow)

# Bregman divergence map (Discrete Bayesian update)
# D_H(p || q) = H(p) - H(q) - <grad H(q), p - q>
var('q1 q2 q3')
H_q = q1*log(q1) + q2*log(q2) + q3*log(q3)
grad_H_q1 = diff(H_q, q1)
grad_H_q2 = diff(H_q, q2)
grad_H_q3 = diff(H_q, q3)

Bregman_Div = H - H_q - (grad_H_q1*(p1-q1) + grad_H_q2*(p2-q2) + grad_H_q3*(p3-q3))
print("Bregman Divergence:")
print(Bregman_Div)
