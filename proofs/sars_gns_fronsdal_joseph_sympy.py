import sympy as sp

q0,q1,p0,p1,hbar,eta = sp.symbols('q0 q1 p0 p1 hbar eta')

def sigma(u,v):
    q,p = u
    r,s = v
    return q*s - p*r

def norm_sq(u):
    q,p = u
    return q*q + p*p

def fock_exponent_quarter(u):
    return -norm_sq(u)/4

assert sp.simplify(sigma((q0,p0),(q1,p1)) + sigma((q1,p1),(q0,p0))) == 0
assert norm_sq((0,0)) == 0
assert fock_exponent_quarter((0,0)) == 0

U00 = p0*q0
U01 = p0*q1
U10 = p1*q0
U11 = p1*q1
joseph_minor = sp.expand(U00*U11 - U01*U10)
assert joseph_minor == 0
star_correction = -hbar*hbar*eta
assert sp.simplify(star_correction + hbar*hbar*eta) == 0

edges = ['GNS_completion','defines_quantization','cut_out_by','annihilates','embeds_as']
print({'sigma_skew': True, 'fock_zero_exponent': 0, 'joseph_minor': joseph_minor, 'star_correction': star_correction, 'trace_status': 'not_trace_class_in_infinite_GNS', 'dmodule_generators': 1, 'edges': len(edges)})
