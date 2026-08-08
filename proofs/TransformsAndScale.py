import sympy as sp


z, omega, t, u, x, y, n = sp.symbols("z omega t u x y n")
x_real = sp.symbols("x_real", real=True)
lam_pos, x_pos = sp.symbols("lam_pos x_pos", positive=True)
I = sp.I

cayley = (z - I) / (z + I)
inv_cayley = I * (1 + cayley) / (1 - cayley)
assert sp.simplify(inv_cayley - z) == 0

log_mellin_arg = sp.expand((I * omega + 1 - 1) * t)
fourier_arg = sp.expand(I * omega * t)
assert sp.simplify(log_mellin_arg - fourier_arg) == 0

fourier_add_lhs = sp.expand(-I * omega * (x + y))
fourier_add_rhs = sp.expand(-I * omega * x + -I * omega * y)
assert sp.simplify(fourier_add_lhs - fourier_add_rhs) == 0

log_mellin_add_lhs = sp.expand((z - 1) * (t + u))
log_mellin_add_rhs = sp.expand((z - 1) * t + (z - 1) * u)
assert sp.simplify(log_mellin_add_lhs - log_mellin_add_rhs) == 0

assert (
    sp.simplify(
        sp.expand_log(sp.log(lam_pos * x_pos), force=True)
        - (sp.log(x_pos) + sp.log(lam_pos))
    )
    == 0
)

sqrt5 = sp.sqrt(5)
phi = (1 + sqrt5) / 2
golden_tick = sp.log(phi)
resonance_lhs = sp.expand((I * omega) * (t + n * golden_tick))
resonance_rhs = sp.expand(I * omega * t + I * omega * n * golden_tick)
assert sp.simplify(resonance_lhs - resonance_rhs) == 0

real_cayley = (x_real - I) / (x_real + I)
unit_circle_norm_sq = sp.simplify(real_cayley * sp.conjugate(real_cayley))
assert sp.simplify(unit_circle_norm_sq - 1) == 0

print("TransformsAndScale.py: Fourier/Mellin/Cayley dictionary verified")
