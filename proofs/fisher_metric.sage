# fisher_metric.sage
# Formulation of the Fisher Information Metric as a Riemannian metric tensor
# Derived from relative entropy (Kullback-Leibler divergence) on a statistical manifold

from sage.manifolds.catalog import Sphere
from sage.symbolic.all import var, function, diff, integrate

print("Initializing Fisher Metric formulation in SageMath...")

# Define the parameter space as a smooth manifold (e.g., a 2D statistical manifold for a standard Gaussian)
M = Manifold(2, 'M', r'\mathcal{M}', start_index=1)
X.<mu, sigma> = M.chart('mu sigma:(0,+oo)')

# Define the probability density function (PDF) for a normal distribution
p = function('p')(mu, sigma)
# For a Gaussian: p = 1/(sqrt(2*pi)*sigma) * exp(-(x-mu)^2/(2*sigma^2))
# The Fisher Information Matrix elements: I_{ij} = - E [ d^2/d theta_i d theta_j log(p(x; theta)) ]
# For Gaussian, it's known to be: I_mumu = 1/sigma^2, I_sigmasigma = 2/sigma^2, I_musigma = 0

# Define the Riemannian metric
g = M.metric('g')
g[1,1] = 1/(sigma^2)
g[2,2] = 2/(sigma^2)
g[1,2] = 0

print("Fisher Information Metric Tensor:")
show(g.display())

# Calculate Christoffel symbols (connection)
nabla = g.connection()
print("Christoffel Symbols:")
show(nabla.display())

# Calculate Ricci curvature
Ricci = g.ricci()
print("Ricci Curvature:")
show(Ricci.display())

# Calculate scalar curvature
R = g.ricci_scalar()
print("Scalar Curvature:")
show(R.display())
