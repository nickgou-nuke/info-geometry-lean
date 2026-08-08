import sympy as sp


u, v, w = sp.symbols("u v w", real=True)

sigma1 = sp.Matrix(
    [
        [0, 1, 0],
        [1, 0, 0],
        [0, 0, 1],
    ]
)
sigma2 = sp.Matrix(
    [
        [1, 0, 0],
        [0, 0, 1],
        [0, 1, 0],
    ]
)
I3 = sp.eye(3)

assert sigma1 * sigma1 == I3
assert sigma2 * sigma2 == I3
assert sigma1 * sigma2 * sigma1 == sigma2 * sigma1 * sigma2

spectral_parameter = lambda a, b: a - b
cpt_invert_scale = lambda a: -a

assert sp.simplify(spectral_parameter(v, u) + spectral_parameter(u, v)) == 0
assert (
    sp.simplify(
        spectral_parameter(cpt_invert_scale(u), cpt_invert_scale(v))
        + spectral_parameter(u, v)
    )
    == 0
)
assert (
    sp.simplify(
        spectral_parameter(u, w)
        - spectral_parameter(u, v)
        - spectral_parameter(v, w)
    )
    == 0
)

field = sp.Matrix(sp.symbols("x0 x1 x2"))
braid_torsion = sigma1 * sigma2 * sigma1 * field - sigma2 * sigma1 * sigma2 * field
assert braid_torsion == sp.zeros(3, 1)

print("SpectralYangBaxter.py: braid/YBE and spectral parameter identities verified")
