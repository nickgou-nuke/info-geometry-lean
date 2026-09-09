#!/usr/bin/env python3
"""Independent symbolic and quadrature checks. These do not verify Lean proofs."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
import sympy as sp
from scipy.integrate import quad, dblquad

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    d, r, z, x, y, mu, t = sp.symbols("d r z x y mu t", positive=True)
    s2 = x*x + y*y + (d+z)**2
    path2 = z*z*s2/(d+z)**2
    entrance_distance2 = (x-d*x/(d+z))**2 + (y-d*y/(d+z))**2 + z*z
    checks = {
        "material_path_geometry": sp.factor(path2-entrance_distance2) == 0,
        "beer_lambert_derivative": sp.simplify(sp.diff(-sp.exp(-mu*t), t)-mu*sp.exp(-mu*t)) == 0,
        "disk_primitive_derivative": sp.simplify(
            sp.diff(-d/(2*sp.sqrt(d*d+r*r)), r)-d*r/(2*(d*d+r*r)**sp.Rational(3, 2))) == 0,
        "disk_rationalization": sp.simplify((1-d/sp.sqrt(d*d+r*r))/2-
            r*r/(2*sp.sqrt(d*d+r*r)*(sp.sqrt(d*d+r*r)+d))) == 0,
    }
    if not all(checks.values()):
        raise AssertionError(checks)
    results = []
    for d0, radius, length, attenuation in [(2., 1., 3., .4), (.5, 1.2, 2.5, .7), (5., .8, 1.5, .2), (2., 1., 3., 0.)]:
        def integrand(rho: float, depth: float) -> float:
            sq = (d0+depth)**2 + rho*rho
            path = depth*np.sqrt(sq)/(d0+depth)
            return attenuation*rho*np.exp(-attenuation*path)/(2*sq)
        volume, volume_error = dblquad(integrand, 0., length, lambda _: 0., lambda _: radius,
                                      epsabs=2e-11, epsrel=2e-11)
        u0 = d0/np.hypot(d0, radius)
        u1 = (d0+length)/np.hypot(d0+length, radius)
        side = quad(lambda u: -np.expm1(-attenuation*(radius/np.sqrt(1-u*u)-d0/u)),
                    u0, u1, epsabs=2e-11, epsrel=2e-11)[0]
        back = quad(lambda u: -np.expm1(-attenuation*length/u), u1, 1.,
                    epsabs=2e-11, epsrel=2e-11)[0]
        ray = (side+back)/2
        aperture, _ = quad(lambda rho: d0*rho/(2*np.hypot(d0, rho)**3), 0., radius,
                           epsabs=2e-11, epsrel=2e-11)
        expected_aperture = (1-u0)/2
        if not np.isclose(volume, ray, atol=2e-10, rtol=2e-10):
            raise AssertionError((volume, ray))
        if not np.isclose(aperture, expected_aperture, atol=2e-12, rtol=2e-12):
            raise AssertionError((aperture, expected_aperture))
        if not (-2e-12 <= volume <= aperture+2e-12):
            raise AssertionError("Transport normalization check failed")
        results.append({"synthetic_parameters": {"d": d0, "R": radius, "L": length, "mu": attenuation},
                        "volume_integral": volume, "independent_ray_integral": ray,
                        "difference": volume-ray, "quadrature_error_estimate": volume_error,
                        "disk_integral": aperture, "disk_closed_form": expected_aperture})
    report = {"status": "passed_non_kernel_checks", "symbolic": checks,
              "synthetic_quadrature": results,
              "limitation": "No measured HPGe efficiency, VPD fit, or Lean kernel proof is validated by these checks."}
    (ROOT / "validation" / "mathematical_checks.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
