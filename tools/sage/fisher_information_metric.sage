from sage.all import *

# Define complex variables as independent formal variables for Wirtinger derivatives
z, zbar = var('z zbar')

# Example 1: Generic Bergman Kernel
# We can declare B as a formal function
B_gen = function('B')(z, zbar)
Phi_gen = log(B_gen)

# The metric is given by the Hessian: \partial^2 \Phi / \partial z \partial \bar{z}
omega_gen = diff(Phi_gen, z, zbar)
print("Generic Fisher Information Metric (Hessian of log B):")
print(omega_gen)
print()

# Example 2: Unit Disk (Poincare metric)
# B(z, zbar) = 1 / (1 - z*zbar)^2  (up to a constant factor like 1/pi)
B_disk = 1 / (1 - z*zbar)^2
Phi_disk = log(B_disk)

omega_disk = diff(Phi_disk, z, zbar)
omega_disk = omega_disk.full_simplify()

print("Bergman Kernel for Unit Disk:")
print(B_disk)
print("Logarithmic Potential (Phi):")
print(Phi_disk)
print("Fisher Information Metric (omega) for Unit Disk:")
print(omega_disk)
