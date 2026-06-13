# Finite Matrix Witness Index

> Status: `current authority`
> Audited: 2026-06-11
> Scope: finite, matrix-level readouts only
> Boundary: this index summarizes owner-backed finite witnesses; it does not claim analytic APS, Seiberg-Witten, or infinite-dimensional Virasoro closure.

This document is the compact matrix index for the finite supercharge, grading,
and Drazin lanes currently owned by the repo.  It keeps the concrete matrices
visible while treating the theorem files as the source of truth.

## 1. Supercharge lane

Owner files:

- [lean/InfoGeometry/GrandUnification/VirasoroDrazinWittenUnification.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/GrandUnification/VirasoroDrazinWittenUnification.lean)
- [lean/InfoGeometry/Canonical/DrazinSupercharge.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/DrazinSupercharge.lean)
- [lean/InfoGeometry/Arithmetic/KudinoorWittenIndexBridge.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Arithmetic/KudinoorWittenIndexBridge.lean)

Finite witness script:

- [tools/sympy/virasoro_drazin_witten_unification.py](/home/goutev/repos/info-geometry-lean/tools/sympy/virasoro_drazin_witten_unification.py)

Matrix components:

$$
Q = \begin{pmatrix}0 & 1 \\ 0 & 0\end{pmatrix}, \qquad
R = \begin{pmatrix}0 & 0 \\ 1 & 0\end{pmatrix}, \qquad
H = Q R + R Q
$$

Finite theorem-backed facts:

- `Q^2 = 0`
- `R^2 = 0`
- `(Q + R)^2 = H`
- the finite Witten supertrace collapses to the zero-sector index under the explicit paired-level hypothesis

Repo meaning:

- `Q` and `R` are the finite odd generators used in the combined witness.
- The operator identity is a finite Dirac-square closure, not a continuum SUSY theorem.

## 2. Grading lane

Owner files:

- [lean/InfoGeometry/Canonical/HaugManiYinYangBridge.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/HaugManiYinYangBridge.lean)
- [lean/InfoGeometry/Canonical/SpacetimeGeometricAlgebraBridge.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SpacetimeGeometricAlgebraBridge.lean)
- [lean/InfoGeometry/Arithmetic/KudinoorWittenIndexBridge.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Arithmetic/KudinoorWittenIndexBridge.lean)

Finite witness scripts:

- [tools/sympy/haug_mani_yin_yang_bridge.py](/home/goutev/repos/info-geometry-lean/tools/sympy/haug_mani_yin_yang_bridge.py)
- [tools/sympy/gull_doran_pseudoscalar_bridge.py](/home/goutev/repos/info-geometry-lean/tools/sympy/gull_doran_pseudoscalar_bridge.py)

Matrix components:

$$
K = J \circ \varepsilon, \qquad
K^2 = -I, \qquad
J K J = -K
$$

Finite theorem-backed facts:

- the real doubled phase axis squares to `-1`
- Tomita conjugation flips the phase axis sign
- the finite grading readout agrees with the parity split used in the Witten-index lane

Repo meaning:

- `K` is the finite real phase-axis witness for the doubled Hestenes/Krein lane.
- This is a finite real-linear model; it is not a claim that complex numbers are removed from mathematics.

## 3. Drazin lane

Owner files:

- [lean/InfoGeometry/Canonical/DrazinTripotentTrifactorBridge.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/DrazinTripotentTrifactorBridge.lean)
- [lean/InfoGeometry/Canonical/DikinDrazinBridge.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/DikinDrazinBridge.lean)
- [lean/InfoGeometry/GrandUnification/VirasoroDrazinWittenUnification.lean](/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/GrandUnification/VirasoroDrazinWittenUnification.lean)

Finite witness scripts:

- [tools/sympy/drazin_tripotent_trifactor_bridge.py](/home/goutev/repos/info-geometry-lean/tools/sympy/drazin_tripotent_trifactor_bridge.py)
- [tools/sympy/dikin_drazin_bridge.py](/home/goutev/repos/info-geometry-lean/tools/sympy/dikin_drazin_bridge.py)

Matrix components:

$$
O^3 = O, \qquad
P_D = O^2, \qquad
P_0 = I - O^2
$$

Finite theorem-backed facts:

- a tripotent operator is its own Drazin inverse at index `1`
- the active Drazin support is `P_D = O^2`
- the null projector is `P_0 = I - O^2`
- the Dikin/Drazin bridge keeps the Hessian readout positive on the nonzero core projection under the explicit positivity premise

Repo meaning:

- `P_D` is the active core projector.
- `P_0` is the null/boundary projector.
- the Dikin theorem here is a finite core-positivity statement, not an analytic ellipsoid theorem.

## 4. Unified finite readout

The repo’s finite matrix witnesses line up as follows:

$$
\text{supercharge} \;\Rightarrow\; (Q,R,H)
\qquad
\text{grading} \;\Rightarrow\; (J,\varepsilon,K)
\qquad
\text{Drazin} \;\Rightarrow\; (O,P_D,P_0)
$$

The common pattern is:

1. a concrete finite matrix witness;
2. a theorem file that owns the identities;
3. an explicit boundary statement about what is not proved.

That is the repository’s finite matrix discipline.
