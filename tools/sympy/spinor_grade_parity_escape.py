import sympy as sp
from sympy.physics.matrices import msigma


def gamma_matrices():
    i2 = sp.eye(2)
    z2 = sp.zeros(2)
    s1, s2, s3 = msigma(1), msigma(2), msigma(3)

    g0 = sp.Matrix(sp.BlockMatrix([[i2, z2], [z2, -i2]]))
    g1 = sp.Matrix(sp.BlockMatrix([[z2, s1], [-s1, z2]]))
    g2 = sp.Matrix(sp.BlockMatrix([[z2, s2], [-s2, z2]]))
    g3 = sp.Matrix(sp.BlockMatrix([[z2, s3], [-s3, z2]]))
    g5 = sp.I * g0 * g1 * g2 * g3
    return g0, g1, g2, g3, g5


def dirac_adjoint(psi: sp.Matrix, gamma0: sp.Matrix) -> sp.Matrix:
    return psi.conjugate().T * gamma0


def bilinear(psi: sp.Matrix, matrix: sp.Matrix, phi: sp.Matrix, gamma0: sp.Matrix):
    return sp.simplify((dirac_adjoint(psi, gamma0) * matrix * phi)[0])


def verify_spinor_escape():
    gamma0, gamma1, _gamma2, _gamma3, gamma5 = gamma_matrices()

    p0, p1, p2, p3 = sp.symbols("p0 p1 p2 p3", complex=True)
    d0, d1, d2, d3 = sp.symbols("d0 d1 d2 d3", complex=True)
    psi = sp.Matrix([p0, p1, p2, p3])
    dpsi = sp.Matrix([d0, d1, d2, d3])

    expected_vielbein = (
        sp.conjugate(p0) * d0
        + sp.conjugate(p1) * d1
        + sp.conjugate(p2) * d2
        + sp.conjugate(p3) * d3
    )
    assert sp.simplify(bilinear(psi, gamma0, dpsi, gamma0) - expected_vielbein) == 0

    expected_axial_temporal = (
        -sp.conjugate(p0) * p2
        - sp.conjugate(p1) * p3
        - sp.conjugate(p2) * p0
        - sp.conjugate(p3) * p1
    )
    assert sp.simplify(bilinear(psi, gamma5 * gamma0, psi, gamma0) - expected_axial_temporal) == 0

    expected_axial_spatial = (
        -sp.conjugate(p0) * p1
        - sp.conjugate(p1) * p0
        - sp.conjugate(p2) * p3
        - sp.conjugate(p3) * p2
    )
    assert sp.simplify(bilinear(psi, gamma5 * gamma1, psi, gamma0) - expected_axial_spatial) == 0

    gravity_witness = sp.Matrix([1, 0, 0, 0])
    temporal_witness = sp.Matrix([1, 0, 1, 0])
    spatial_witness = sp.Matrix([1, 1, 0, 0])

    assert bilinear(gravity_witness, gamma0, gravity_witness, gamma0) == 1
    assert bilinear(temporal_witness, gamma5 * gamma0, temporal_witness, gamma0) == -2
    assert bilinear(spatial_witness, gamma5 * gamma1, spatial_witness, gamma0) == -2

    ta = sp.symbols("Ta", complex=True)
    inserted = bilinear(psi, gamma5 * gamma0, ta * psi, gamma0)
    assert sp.simplify(inserted - ta * bilinear(psi, gamma5 * gamma0, psi, gamma0)) == 0


def main():
    verify_spinor_escape()
    print("Spinor grade-parity escape finite bilinear checks passed.")


if __name__ == "__main__":
    main()
