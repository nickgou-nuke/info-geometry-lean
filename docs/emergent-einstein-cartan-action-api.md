# Emergent Einstein-Cartan Action API

> Owner: `lean/InfoGeometry/Canonical/EmergentEinsteinCartanAction.lean`
> Mirrors: `tools/sympy/emergent_einstein_cartan_action.py`

This owner surface is finite and algebraic.

It proves:

- the finite action density splits into Dirac, mass, curvature, and torsion
  slots;
- zero torsion removes the torsion term from the finite action density;
- a symmetric stress plus a symmetric torsion-quadratic source gives a
  symmetric total source;
- a scaled spin source satisfies the finite torsion equation;
- the finite Einstein-Cartan field-equation readout is definitionally
  equivalent to its expanded algebraic proposition; and
- with torsion fixed to `κ * Spin`, the finite Einstein-Cartan system is
  equivalent to the finite field equation.

It does not prove:

- continuum variational calculus;
- Bianchi identities or diffeomorphism invariance;
- covariant conservation laws;
- propagating torsion;
- a physical Einstein-Cartan theory.
