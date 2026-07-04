from sage.all import *

print("Setting up Manifold and Chart...")
M = Manifold(3, 'M', latex_name=r'\mathcal{M}')
X.<x,y,z> = M.chart()
t = var('t')

# Neck model metric: g = A(t,z) dx^2 + A(t,z) dy^2 + B(t,z) dz^2
g = M.metric('g')
A = function('A')(t, z)
B = function('B')(t, z)

g[0,0] = A
g[1,1] = A
g[2,2] = B

print("Computing Ricci tensor...")
Ric = g.ricci()

print("\n--- Ricci Flow Equations (dg/dt = -2 Ric(g)) ---")
print(f"dA/dt = -2 * [{Ric[0,0].expr()}]")
print(f"dB/dt = -2 * [{Ric[2,2].expr()}]")

print("\nComputing Scalar Curvature R...")
R = g.ricci_scalar()
print("Scalar Curvature R =")
print(R.expr())

print("\nComputing Evolution of Scalar Curvature (dR/dt)...")
dR_dt = diff(R.expr(), t)
print("dR/dt =")
print(dR_dt)
print("\nDone.")
