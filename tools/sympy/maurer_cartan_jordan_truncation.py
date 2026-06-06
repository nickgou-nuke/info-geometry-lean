#!/usr/bin/env python3
"""Finite SymPy witness for the nilpotent/Jordan truncation corridor.

This script checks the exact finite matrix pattern behind the Maurer-Cartan
truncation discussion:

- a square-zero nilpotent correction `N`;
- a Jordan cell at a root of unity `J = zeta I + N`;
- exact collapse of all higher powers beyond the first nilpotent order;
- the finite power law for a unipotent perturbation.

It is a witness surface only. Lean owns the abstract theorem statements.
"""

import sympy as sp


def main() -> int:
    I2 = sp.eye(2)
    N = sp.Matrix([[0, 1], [0, 0]])
    zeta = sp.exp(2 * sp.pi * sp.I / 5)
    J = zeta * I2 + N

    t = sp.symbols("t")
    U = I2 + t * N

    ok = {}
    ok["N^2 = 0"] = (N**2 == sp.zeros(2))
    ok["Jordan shift squares to 0"] = ((J - zeta * I2) ** 2 == sp.zeros(2))
    ok["N J N = 0"] = (N * J * N == sp.zeros(2))
    ok["unipotent collapse"] = sp.simplify(U**6 - (I2 + 6 * t * N)) == sp.zeros(2)

    # Concrete root-of-unity witness checks for a few powers.
    root_power_checks = {}
    for n in range(0, 8):
        lhs = sp.expand(J**n)
        rhs = sp.expand(zeta**n * (I2 + (sp.Integer(n) / zeta) * N))
        root_power_checks[n] = sp.simplify(lhs - rhs) == sp.zeros(2)

    print("Maurer-Cartan / Jordan truncation witness")
    print("========================================")
    print(f"root of unity zeta = exp(2*pi*I/5)")
    print(f"J = zeta*I + N = {sp.Matrix(J)}")
    print()
    print("Nilpotent truncation:")
    for k, v in ok.items():
      print(f"  {k}: {v}")
    print()
    print("Jordan powers at the root of unity:")
    for n, v in root_power_checks.items():
        print(f"  J^{n} formula: {v}")
    print()
    print("Lean bridge table:")
    bridge = [
        ("square-zero Jordan power", "InfoGeometry.QuantumMonodromy.nilpotent_jordan_power"),
        ("real rotor/binomial collapse", "InfoGeometry.Quantum.RealKCategory.monodromy_power_binomial"),
        ("Hadjiivanov monodromy winding law", "InfoGeometry.Clifford.LogCftMonodromy.hadjiivanovMonodromy_pow_winding"),
        ("lower exchange nilpotent corridor", "InfoGeometry.OperatorAlgebra.LogExchangeMonodromy.lowerHadjiivanovMonodromy_pow_eq_phase_conj_componentN"),
    ]
    for label, lean_name in bridge:
        print(f"  - {label}: {lean_name}")

    overall = all(ok.values()) and all(root_power_checks.values())
    print()
    print(f"OVERALL: {overall}")
    return 0 if overall else 1


if __name__ == "__main__":
    raise SystemExit(main())
