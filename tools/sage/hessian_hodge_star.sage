print("Initializing Riemannian Manifold...")
M = Manifold(2, 'M', structure='Riemannian')
X.<x, y> = M.chart()

print("Defining generic thermodynamic potential Q...")
Q = function('Q')(x, y)
F = ln(Q)

print("Deriving Hessian metric g_ij = d_i d_j ln Q...")
g = M.metric('g')
g[0,0] = diff(F, x, 2)
g[1,1] = diff(F, y, 2)
g[0,1] = diff(F, x, y)
g[1,0] = diff(F, x, y)

print("Setting orientation...")
# The first chart is automatically the default orientation
# For hodge_dual, we might just need volume form

print("Defining 2-form omega...")
omega = M.diff_form(2, 'omega')
A = function('A')(x, y)
omega[0,1] = A


print("Computing parameterized Hodge star operator...")
star_omega = omega.hodge_dual()

print("Hodge star of omega (0-form / scalar field):")
print(star_omega.display())

print("Computing exterior derivative d(star omega) to generate dynamic equations of motion...")
d_star_omega = star_omega.differential()
print(d_star_omega.display())
