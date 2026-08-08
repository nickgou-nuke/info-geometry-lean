# SageMath script for Itakura-Saito Bregman Divergence and RG Flow
# d_IS(p, q) = p/q - ln(p/q) - 1

var('p, q')
# Define the Itakura-Saito divergence
d_IS = p/q - log(p/q) - 1
print("Itakura-Saito Divergence d_IS(p,q):", d_IS)

# The convex function generating this is F(p) = -ln(p)
var('p_var, q_var')
F(p_var) = -log(p_var)

# Fenchel-Legendre transform of F(p)
# F*(y) = sup_p (p*y - F(p))
# d/dp (p*y + log(p)) = y + 1/p = 0 => p = -1/y
var('y')
F_star(y) = (p_var*y - F(p_var)).subs(p_var == -1/y).simplify_full()
print("Fenchel-Legendre transform F*(y):", F_star(y))

# RG Flow mapping driven by d_IS
# Flow of state p with respect to scale tau
var('tau')
p_tau = function('p_tau')(tau)
# Gradient flow equation based on d_IS
flow_eq = diff(p_tau, tau) == -diff(d_IS.subs(p==p_tau, q==q_var), p_tau)
print("RG Flow Equation:", flow_eq)
