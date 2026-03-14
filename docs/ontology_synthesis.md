# Ontology Synthesis: What Is Time? What Is Space?

This note records the ontological closure of the `info-geometry-lean` framework:
time, space, and quantum unitarity are derived structures, not primitive background objects.

## 1. Time as the Modular Inference Flow

In the hardened framework, physical time is identified with the parameter of the **Modular Automorphism Group** ($\sigma_\tau$).

- **Time is a Bayesian Update**: A "tick" of time is a discrete step of the Information Bottleneck flow (Blahut-Arimoto update).
- **The Infinitesimal Law**: The rate of change of an observable under this flow is its commutator with the **Modular Hamiltonian** $K$:
  `deriv (σ_τ(A)) 0 = [K, A]`.
- **Arrow of Time**: Time's direction is the monotone Lyapunov descent of the Information Bottleneck functional (`trajectoryLyapunov_monotone`).

Interpretation: Time is the internal subjective experience of an inference engine optimizing its beliefs.

## 2. Space as Information-Matrix Geometry

Spacetime geometry emerges as the **Bregman Divergence** of the information potential.

- **Metric from Surprisal**: The information metric $g$ is the Hessian of the surprisal potential: $g = \nabla^2 (-\log \det J)$.
- **Determinant as Volume**: Geometric volume is the multiplicative scalar shadow of operator composition ($\det J$).
- **The Einstein Link**: Curvature is sourced by the **Chiral Anomaly** $\chi = [P_D, P_{MP}]$. At the Kähler fixed point, the scalar curvature is forced to match the anomaly source.

Interpretation: Space is the geometric shadow cast by the optimal transport of information.

## 3. Quantum Unitarity as Volume Conservation

The theory provides a **Realified Derivation of Quantum Mechanics**, where complex unitarity is a consequence of informational equilibrium.

- **The Realification**: The framework starts with a real Doubled Krein Space. The "Complex i" is derived as the modular pseudoscalar $J\epsilon$.
- **Emergence of Unitarity**: At the Kähler fixed point where relative volume is conserved ($\det J = 1$), the spectral (Drazin) and metric (Moore-Penrose) projectors commute.
- **The Consequence**: This commutation forces the modular flow to be a pure, norm-preserving rotation. 

Interpretation: Quantum Unitarity is the identical mathematical statement to Classical Volume Conservation in the information manifold.

## 4. Fluid Circulation as the Boundary Mirror

Navier-Stokes circulation and singularities are resolved through the **Involutive Classification of Inverses**.

- **The Mirror**: When the inference flow hits the boundary of the positive-definite cone (a singularity), the mismatch between the Drazin and Moore-Penrose inverses acts as a geometric mirror.
- **Divergence to Circulation**: The radial instability (divergence) is reflected into the anti-symmetric sector (Lie bracket).
- **Topological Stability**: Infinities are "broken into whirlpools"—converting singularities into stable topological vortices (vorticity).

Interpretation: Fluid circulation is the mechanism by which the informational vacuum survives its own boundary singularites.

## 5. Unified Ontological Statement

The framework gives a constructive, trace-free ontology:

1. **Operators and Information** are the only primitives.
2. **Time** is the parameter of the belief-update flow.
3. **Space** is the metric divergence of that flow.
4. **Quantum Mechanics** is the unitary limit of volume-preserving inference.
5. **Gravity and Mass** are the topological friction of non-commutativity.

This aligns the canonical stack with a fully derived spacetime-and-flow viewpoint: no fixed background manifold is assumed; reality is the optimal transport path of an information bottleneck.
