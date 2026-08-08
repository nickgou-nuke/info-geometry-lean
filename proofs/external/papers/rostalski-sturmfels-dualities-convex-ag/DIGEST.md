# Digest: Rostalski--Sturmfels, “Dualities in Convex Algebraic Geometry”

Source: arXiv `1006.4894`, Philipp Rostalski and Bernd Sturmfels, 2010.

## Core theme

The paper compares three dualities that meet in polynomial optimization and semidefinite programming:

1. **Convex duality** of convex bodies.
2. **Projective duality** of algebraic varieties/tangent hyperplanes.
3. **Lagrange/KKT duality** in constrained optimization.

The central message is that optimal values of polynomial programs are algebraic functions whose equations are controlled by projective dual hypersurfaces of the constraint varieties.

## Spectrahedra

A spectrahedron is an affine slice of the positive semidefinite cone, e.g.

\[
P=\{x\in\mathbb R^m \mid A_0+x_1A_1+\cdots+x_mA_m\succeq 0\}.
\]

The algebraic boundary is often a determinant hypersurface. Its dual convex body is generally not itself a spectrahedron, but is a spectrahedral shadow.

## Relation to this repository

This paper supplies the conceptual bridge between:

- projective/PGA incidence and cross-ratio layers;
- positive state spaces/traces of operator algebras;
- optimization/KMS/MaxCaliber conditions;
- determinant boundaries of Jordan/Clifford/Freudenthal state spaces.

In the code we formalize finite algebraic anchors:

- a toy spectrahedron/simplex as a PSD diagonal slice;
- convex closure of the feasible set;
- projective conic dual map via the gradient/tangent hyperplane;
- scalar KKT stationarity;
- sockets for full spectrahedral shadows, SDP duality, and projective-dual boundary theorems.
