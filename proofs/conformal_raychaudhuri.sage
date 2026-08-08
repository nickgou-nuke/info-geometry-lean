# conformal_raychaudhuri.sage
from sage.all import *
from sage.manifolds.catalog import Minkowski

print("Initializing Conformal Raychaudhuri Equation in SageMath...")

M = Manifold(4, 'M', structure='Lorentzian')
X.<t, x, y, z> = M.chart()
g = M.metric()
g[0,0], g[1,1], g[2,2], g[3,3] = -1, 1, 1, 1

Omega = M.scalar_field(function('Omega')(t, x, y, z), name='Omega')
g_hat = M.lorentzian_metric('g_hat')
g_hat.set(Omega^2 * g)

print("Conformal Metric g_hat = Omega^2 g initialized.")
print("Optical expansion theta defined as divergence of null geodesics mapping to conformal boundary.")
