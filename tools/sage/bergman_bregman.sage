print("Initializing SageMath for Bergman-Bregman divergence...")

var('z z_bar')
B = function('B')(z, z_bar)

# Complex potential
phi = log(B)

# Complex Hessian form: i \partial \bar{\partial} \log B
hessian_form = I * diff(diff(phi, z), z_bar)
print(r"Complex Hessian form (i \partial \bar{\partial} \log B):")
print(hessian_form)

# Statistical divergence algebraically
var('z1 z1_bar z2 z2_bar')

phi_1 = log(function('B')(z1, z1_bar))
phi_2 = log(function('B')(z2, z2_bar))

dphi_dz = diff(log(function('B')(z, z_bar)), z)
dphi_dz_bar = diff(log(function('B')(z, z_bar)), z_bar)

dphi_dz_2 = dphi_dz.subs({z: z2, z_bar: z2_bar})
dphi_dz_bar_2 = dphi_dz_bar.subs({z: z2, z_bar: z2_bar})

D = phi_1 - phi_2 - dphi_dz_2 * (z1 - z2) - dphi_dz_bar_2 * (z1_bar - z2_bar)

print("\nBregman Divergence D(z1, z2):")
print(D)
