#!/usr/bin/env sage -python
r"""
sl(2,C) Infinitesimal/Exponential Packet in SageMath
Pure-math verification of trace-zero 2x2 matrices, discriminant, and exponential flows
"""

from sage.all import QQ, CC, I, Matrix, var, exp, cos, sin, simplify, solve
from sage.matrix.constructor import identity_matrix


def sl2_matrix(a, b, c):
    """Construct a 2x2 trace-zero matrix [[a,b],[c,-a]]"""
    return Matrix([[a, b], [c, -a]])


def matrix_det(M):
    """Compute determinant of 2x2 matrix"""
    return M[0, 0] * M[1, 1] - M[0, 1] * M[1, 0]


def vector_field(M, z):
    """Compute the quadratic vector field V(z) = -c*z^2 + 2*a*z + b"""
    a, b, c = M[0, 0], M[0, 1], M[1, 0]
    return -c * z**2 + 2 * a * z + b


def discriminant(M):
    """Compute the discriminant of the quadratic vector field"""
    a, b, c = M[0, 0], M[0, 1], M[1, 0]
    return 4 * a**2 + 4 * b * c


def discriminant_eq_neg_four_det(M):
    """Verify the exact identity: Delta = -4 * det"""
    delta = discriminant(M)
    detM = matrix_det(M)
    return delta.spec() == (-4 * detM).simplify()


def verify_symbolic_identity():
    """Verify the symbolic identity with generic parameters"""
    a, b, c = var('a b c')
    M = sl2_matrix(a, b, c)
    delta = discriminant(M)
    detM = matrix_det(M)
    assert simplify(delta - (-4 * detM)) == 0
    return simplify(delta), simplify(detM)


def verify_packets():
    """Verify the four concrete packet representatives"""
    z = var('z')
    
    packets = {
        'parabolic': sl2_matrix(1, 1, -1),
        'hyperbolic': sl2_matrix(1, 0, -1),
        'elliptic': sl2_matrix(0, 1, -1),
        'loxodromic': sl2_matrix(1, 1, I),
    }
    
    reports = {}
    for name, M in packets.items():
        delta = discriminant(M)
        detM = matrix_det(M)
        vf = vector_field(M, z)
        roots = solve(vf == 0, z)
        reports[name] = {
            'matrix': M,
            'determinant': detM,
            'vector_field': vf,
            'discriminant': delta,
            'roots': [r.rhs() for r in roots],
        }
    
    # Verify classification by discriminant shape
    assert reports['parabolic']['discriminant'] == 0
    assert reports['hyperbolic']['discriminant'] == 4
    assert reports['elliptic']['discriminant'] == -4
    assert reports['loxodromic']['discriminant'].imag() != 0
    
    return reports


def matrix_exp_2x2(M, t):
    """Compute matrix exponential exp(t*M) for 2x2 trace-zero matrix using closed form.
    
    For trace-zero 2x2 matrices, we have:
    - If det(M) > 0: exp(tM) = cos(sqrt(det)*t)*I + sin(sqrt(det)*t)/sqrt(det) * M
    - If det(M) < 0: exp(tM) = cosh(sqrt(-det)*t)*I + sinh(sqrt(-det)*t)/sqrt(-det) * M
    - If det(M) = 0 (nilpotent): exp(tM) = I + t*M
    """
    from sage.all import sqrt, cos, sin, cosh, sinh, zero_matrix
    detM = matrix_det(M)
    I2 = identity_matrix(2)
    
    if detM == 0:
        # Nilpotent case: M^2 = 0, so exp(tM) = I + tM
        return I2 + t * M
    elif detM > 0:
        # Elliptic case
        omega = sqrt(detM)
        return cos(omega * t) * I2 + sin(omega * t) / omega * M
    else:
        # Hyperbolic case (detM < 0)
        omega = sqrt(-detM)
        return cosh(omega * t) * I2 + sinh(omega * t) / omega * M


def matrix_exp(M):
    """Wrapper for matrix exponential - uses closed form for 2x2 trace-zero"""
    t = var('t')
    return matrix_exp_2x2(M, t)


def verify_exponential_flows():
    """Verify the exponential bridge for one-parameter flows"""
    t = var('t')
    
    # Parabolic (nilpotent): M^2 = 0, so exp(tM) = I + tM
    para = sl2_matrix(1, 1, -1)
    assert (para * para).is_zero()
    para_exp = matrix_exp(t * para)
    assert simplify(para_exp.det() - 1) == 0
    assert simplify(para_exp.trace() - 2) == 0
    
    # Hyperbolic: diagonal-like
    hyper = sl2_matrix(1, 0, -1)
    hyper_exp = matrix_exp(t * hyper)
    assert simplify(hyper_exp.det() - 1) == 0
    
    # Elliptic: rotation-like
    ell = sl2_matrix(0, 1, -1)
    ell_exp = matrix_exp(t * ell)
    assert simplify(ell_exp.det() - 1) == 0
    
    return {
        'parabolic_exp': para_exp,
        'hyperbolic_exp_00': simplify(hyper_exp[0, 0]),
        'elliptic_exp_00': simplify(ell_exp[0, 0]),
        'elliptic_exp_01': simplify(ell_exp[0, 1]),
    }


def main():
    print("=== SAGE: sl(2,C) Infinitesimal/Exponential Packet ===")
    print()
    
    # 1. Symbolic identity
    delta, detM = verify_symbolic_identity()
    print(f"Symbolic identity: Delta = {delta}, det(M) = {detM}")
    assert simplify(delta + 4 * detM) == 0
    print("Symbolic identity verified: Delta = -4 * det")
    print()
    
    # 2. Packet verification
    reports = verify_packets()
    for name, report in reports.items():
        print(f"[{name}]")
        print(f"  Matrix = {report['matrix']}")
        print(f"  Determinant = {report['determinant']}")
        print(f"  Vector field = {report['vector_field']}")
        print(f"  Discriminant = {report['discriminant']}")
        print(f"  Roots = {report['roots']}")
        print()
    
    # 3. Exponential bridge
    exp_reports = verify_exponential_flows()
    print("[Exponential Flows]")
    print(f"  Parabolic exp(0,0) = {exp_reports['parabolic_exp'][0, 0]}")
    print(f"  Hyperbolic exp(0,0) = {exp_reports['hyperbolic_exp_00']}")
    print(f"  Elliptic exp(0,0) = {exp_reports['elliptic_exp_00']}")
    print(f"  Elliptic exp(0,1) = {exp_reports['elliptic_exp_01']}")
    print()
    
    print("MOBIUS_INFINITESIMAL_SAGE_OK")


if __name__ == "__main__":
    main()