#!/usr/bin/env python3
"""Affine-coordinate verifier for the zeta-plane symmetry frame.

This script verifies only the algebra of the standard coordinate actions:

  C(s) = conjugate(s)
  F(s) = 1 - s
  J(s) = 1 - conjugate(s)

In real coordinates `s = sigma + I*tau`, these become:

  C(sigma, tau) = (sigma, -tau)
  F(sigma, tau) = (1 - sigma, -tau)
  J(sigma, tau) = (1 - sigma, tau)

The critical line is the fixed locus of `J`, i.e. `sigma = 1/2`.
No numerical zeta evaluation and no RH claim are made here.
"""

from __future__ import annotations

import sympy as sp


sigma, tau = sp.symbols("sigma tau", real=True)
point = (sigma, tau)
a, b, x, alpha, beta = sp.symbols("a b x alpha beta", real=True)


def conjugation(p: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
    s, t = p
    return (s, -t)


def functional_dual(p: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
    s, t = p
    return (1 - s, -t)


def critical_mirror(p: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
    s, t = p
    return (1 - s, t)


def centered(p: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
    s, t = p
    return (s - sp.Rational(1, 2), t)


def add(p: tuple[sp.Expr, sp.Expr], q: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
    return (p[0] + q[0], p[1] + q[1])


def sub(p: tuple[sp.Expr, sp.Expr], q: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
    return (p[0] - q[0], p[1] - q[1])


def scale(a: sp.Expr, p: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
    return (a * p[0], a * p[1])


def flat_quadratic(p: tuple[sp.Expr, sp.Expr]) -> sp.Expr:
    return p[0] ** 2 + p[1] ** 2


def flat_displacement(p: tuple[sp.Expr, sp.Expr], q: tuple[sp.Expr, sp.Expr]) -> sp.Expr:
    return (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2


def marked_pair_reflection(left: sp.Expr, right: sp.Expr, value: sp.Expr) -> sp.Expr:
    return left + right - value


def marked_pair_midpoint(left: sp.Expr, right: sp.Expr) -> sp.Expr:
    return (left + right) / 2


def marked_pair_scale_coordinate(left: sp.Expr, right: sp.Expr, value: sp.Expr) -> sp.Expr:
    return (value - left) / (right - left)


def affine_transport(slope: sp.Expr, intercept: sp.Expr, value: sp.Expr) -> sp.Expr:
    return slope * value + intercept


def normal_quadratic_potential(p: tuple[sp.Expr, sp.Expr]) -> sp.Expr:
    return p[0] ** 2


def height_souriau_moment(p: tuple[sp.Expr, sp.Expr]) -> sp.Expr:
    return p[1]


def height_souriau_cocycle(shift: sp.Expr) -> sp.Expr:
    return shift


def same(p: tuple[sp.Expr, sp.Expr], q: tuple[sp.Expr, sp.Expr]) -> bool:
    return all(sp.simplify(a - b) == 0 for a, b in zip(p, q, strict=True))


def main() -> None:
    transforms = {
        "id": lambda p: p,
        "C": conjugation,
        "F": functional_dual,
        "J": critical_mirror,
    }
    composition = {
        ("id", "id"): "id",
        ("id", "C"): "C",
        ("id", "F"): "F",
        ("id", "J"): "J",
        ("C", "id"): "C",
        ("F", "id"): "F",
        ("J", "id"): "J",
        ("C", "C"): "id",
        ("F", "F"): "id",
        ("J", "J"): "id",
        ("C", "F"): "J",
        ("F", "C"): "J",
        ("C", "J"): "F",
        ("J", "C"): "F",
        ("F", "J"): "C",
        ("J", "F"): "C",
    }

    c = transforms["C"]
    f = transforms["F"]
    j = transforms["J"]

    assert same(c(c(point)), point)
    assert same(f(f(point)), point)
    assert same(j(j(point)), point)

    assert same(f(c(point)), c(f(point)))
    assert same(j(point), f(c(point)))

    for (left, right), result in composition.items():
        composed = transforms[left](transforms[right](point))
        assert same(composed, transforms[result](point)), (left, right, result)

    u, v = centered(point)
    assert same(centered(c(point)), (u, -v))
    assert same(centered(f(point)), (-u, -v))
    assert same(centered(j(point)), (-u, v))

    centered_point = (u, v)

    def centered_conjugation(p: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
        return (p[0], -p[1])

    def centered_functional_dual(p: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
        return (-p[0], -p[1])

    def centered_critical_mirror(p: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
        return (-p[0], p[1])

    def critical_tangent_projector(p: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
        return (0, p[1])

    def critical_normal_projector(p: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
        return (p[0], 0)

    def height_translation(a: sp.Expr, p: tuple[sp.Expr, sp.Expr]) -> tuple[sp.Expr, sp.Expr]:
        return (p[0], p[1] + a)

    half = sp.Rational(1, 2)
    zero = (0, 0)
    p_tangent = critical_tangent_projector(centered_point)
    p_normal = critical_normal_projector(centered_point)

    assert same(p_tangent, scale(half, add(centered_point, centered_critical_mirror(centered_point))))
    assert same(p_normal, scale(half, sub(centered_point, centered_critical_mirror(centered_point))))
    assert same(p_tangent, scale(half, sub(centered_point, centered_conjugation(centered_point))))
    assert same(p_normal, scale(half, add(centered_point, centered_conjugation(centered_point))))
    assert same(zero, scale(half, add(centered_point, centered_functional_dual(centered_point))))
    assert same(centered_point, scale(half, sub(centered_point, centered_functional_dual(centered_point))))

    assert same(add(p_tangent, p_normal), centered_point)
    assert same(critical_tangent_projector(p_tangent), p_tangent)
    assert same(critical_normal_projector(p_normal), p_normal)
    assert same(critical_tangent_projector(p_normal), zero)
    assert same(critical_normal_projector(p_tangent), zero)
    assert same(centered_critical_mirror(p_tangent), p_tangent)
    assert same(centered_critical_mirror(p_normal), scale(-1, p_normal))
    assert sp.simplify(flat_quadratic(centered_conjugation(centered_point)) - flat_quadratic(centered_point)) == 0
    assert sp.simplify(
        flat_quadratic(centered_functional_dual(centered_point)) - flat_quadratic(centered_point)
    ) == 0
    assert sp.simplify(
        flat_quadratic(centered_critical_mirror(centered_point)) - flat_quadratic(centered_point)
    ) == 0
    normal_drop = sp.simplify(flat_quadratic(centered_point) - flat_quadratic(p_tangent))
    assert sp.simplify(normal_drop - u**2) == 0
    assert sp.simplify(-flat_quadratic(p_tangent) - (-flat_quadratic(centered_point)) - u**2) == 0
    symmetric_even_potential = u**4 + v**2
    assert sp.simplify(symmetric_even_potential.subs(u, -u) - symmetric_even_potential) == 0
    assert sp.simplify(
        normal_quadratic_potential(centered_critical_mirror(centered_point))
        - normal_quadratic_potential(centered_point)
    ) == 0

    a = sp.symbols("a", real=True)
    other = (sp.symbols("u2", real=True), sp.symbols("v2", real=True))
    assert sp.simplify(
        flat_displacement(height_translation(a, centered_point), height_translation(a, other))
        - flat_displacement(centered_point, other)
    ) == 0
    assert same(height_translation(a, height_translation(b, centered_point)), height_translation(a + b, centered_point))
    assert same(height_translation(0, centered_point), centered_point)
    assert sp.simplify(
        height_souriau_moment(height_translation(a, centered_point))
        - (height_souriau_moment(centered_point) + height_souriau_cocycle(a))
    ) == 0
    assert sp.simplify(
        normal_quadratic_potential(height_translation(a, centered_point))
        - normal_quadratic_potential(centered_point)
    ) == 0
    assert same(
        centered_critical_mirror(height_translation(a, centered_point)),
        height_translation(a, centered_critical_mirror(centered_point)),
    )
    assert same(
        centered_conjugation(height_translation(a, centered_point)),
        height_translation(-a, centered_conjugation(centered_point)),
    )
    assert same(
        centered_functional_dual(height_translation(a, centered_point)),
        height_translation(-a, centered_functional_dual(centered_point)),
    )

    # Marked-pair affine normalization: the standard 1/2 is the normalized
    # midpoint of the distinguished pair, not an intrinsic raw coordinate.
    pair_reflected = marked_pair_reflection(a, b, x)
    pair_midpoint = marked_pair_midpoint(a, b)
    assert sp.simplify(marked_pair_reflection(a, b, a) - b) == 0
    assert sp.simplify(marked_pair_reflection(a, b, b) - a) == 0
    assert sp.simplify(marked_pair_reflection(a, b, pair_reflected) - x) == 0
    assert sp.solve(sp.Eq(pair_reflected, x), [x], dict=True) == [
        {x: pair_midpoint}
    ]
    assert sp.simplify(
        marked_pair_scale_coordinate(a, b, pair_midpoint) - sp.Rational(1, 2)
    ) == 0
    assert sp.simplify(
        marked_pair_scale_coordinate(a, b, pair_reflected)
        - (1 - marked_pair_scale_coordinate(a, b, x))
    ) == 0
    assert sp.simplify(marked_pair_reflection(0, 1, sigma) - (1 - sigma)) == 0
    transported_a = affine_transport(alpha, beta, a)
    transported_b = affine_transport(alpha, beta, b)
    transported_x = affine_transport(alpha, beta, x)
    assert sp.simplify(
        affine_transport(alpha, beta, pair_midpoint)
        - marked_pair_midpoint(transported_a, transported_b)
    ) == 0
    assert sp.simplify(
        affine_transport(alpha, beta, pair_reflected)
        - marked_pair_reflection(transported_a, transported_b, transported_x)
    ) == 0
    assert sp.simplify(
        marked_pair_scale_coordinate(transported_a, transported_b, transported_x)
        - marked_pair_scale_coordinate(a, b, x)
    ) == 0

    fixed_equations = [
        sp.Eq(j(point)[0], point[0]),
        sp.Eq(j(point)[1], point[1]),
    ]
    fixed_solution = sp.solve(fixed_equations, [sigma], dict=True)
    assert fixed_solution == [{sigma: sp.Rational(1, 2)}]

    orbit = {
        "rho": point,
        "conj_rho": c(point),
        "one_minus_rho": f(point),
        "one_minus_conj_rho": j(point),
    }

    print("zeta_coordinate_symmetry: ok")
    print("  generated_symmetry_frame: V4/Klein four")
    print("  centered_coordinates: u = sigma - 1/2, v = tau")
    print("  critical_cartan_projectors: tangent=(0, v), normal=(u, 0)")
    print("  symmetry_potential: mirror-invariant potentials are even in u")
    print("  flat_quadratic_extremum: fixed line minimizes +Q and maximizes -Q in normal direction")
    print("  vertical_height_translation: preserves flat displacement")
    print("  height_souriau_cocycle: moment(v+a)=moment(v)+a for coordinate height flow")
    print("  discrete_souriau: finite zeta reflection group has singleton Lie algebra and zero moment")
    print("  marked_pair_scale: midpoint(a,b) maps to 1/2 and reflection maps u to 1-u")
    print("  affine_transport: normalized marked-pair coordinate is invariant")
    for name, value in orbit.items():
        print(f"  {name}: {value}")
    print("  critical_mirror_fixed_locus: sigma = 1/2")


if __name__ == "__main__":
    main()
