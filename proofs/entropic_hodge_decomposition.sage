# SageMath Script for Entropic Hodge Decomposition
# Decomposing a phase space flow into an exact (scalar, Bregman) and co-exact (vector, Berry) part.

# Define a 3D manifold (phase space)
M = Manifold(3, 'M', field='real')
X.<x,y,z> = M.chart()

# Define the metric (Euclidean for simplicity)
g = M.metric('g')
g[0,0], g[1,1], g[2,2] = 1, 1, 1

# Define a scalar field B (Bregman potential related)
B = M.scalar_field(function('B')(x, y, z), name='B')

# The exact scalar part is d(ln B)
lnB = M.scalar_field(ln(B.expr()), name='lnB')
exact_part = lnB.differential()

# Define a 2-form A (Vector potential / Berry connection related)
A = M.diff_form(2, name='A')
A[0,1] = function('Axy')(x,y,z)
A[0,2] = function('Axz')(x,y,z)
A[1,2] = function('Ayz')(x,y,z)

# The co-exact vector part is delta A (codifferential of A)
# In 3D, delta on 2-forms gives a 1-form.
def codifferential(form):
    k = form.degree()
    n = form.domain().dim()
    sgn = (-1)**(n*(k-1) + 1)
    return sgn * form.hodge_dual(g).exterior_derivative().hodge_dual(g)

coexact_part = codifferential(A)

# General flow is the sum of exact and co-exact parts
F = exact_part + coexact_part

print("Entropic Hodge Decomposition formulated.")
print("Exact Part (Bregman flow): d(ln B) =", exact_part.display())
print("Co-exact Part (Berry phase flow): delta A =", coexact_part.display())
print("General Flow =", F.display())
