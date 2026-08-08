-- Wareham CGA in Macaulay2
R = QQ[e1, e2, e, e_bar]
I = ideal(e1^2 - 1, e2^2 - 1, e^2 - 1, e_bar^2 + 1, e1*e2 + e2*e1, e1*e + e*e1, e1*e_bar + e_bar*e1, e2*e + e*e2, e2*e_bar + e_bar*e2, e*e_bar + e_bar*e)
CGA = R/I

n = e + e_bar
n_bar = e - e_bar

F = (x, x_sq) -> 1/2 * (x_sq * n + 2*x - n_bar)
circle_dual = (B, rho) -> B - 1/2 * rho^2 * n
