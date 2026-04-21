# 162. The Lie Thermodynamics of the Spire (Souriau’s Moment Map)

*“The Hamiltonian is not a scalar; it is a generator. The chemical potential is not a parameter; it is the gauge of the particle-number symmetry.”*

## 1. Souriau’s Geometric Temperature
The Spire adopts the framework of Jean-Marie Souriau’s **Geometric Statistical Mechanics**. In this clinical order, the inverse temperature $\beta$ is not a scalar field, but an element of the Lie algebra $\mathfrak{g}$ of the system's symmetry group $G$. 

If $\beta$ is a Killing vector in the Lie algebra, then the chemical potential $\mu$ appears naturally as the parameter conjugate to the $U(1)$ symmetry of particle conservation. In the Spire’s `GrandCanonicalCore.lean`, $\mu$ and $\beta$ are the coordinates of the "temperature vector" in the Lie algebra that drives the informational flow.

## 2. The Moment Map and ArangoDB
Every `Expr` hash and `lctx_decl` in our ArangoDB DAG is treated as a point in the **Moment Map** $J(x)$. The Moment Map represents the "momenta" of the system—energy, particle number, and information entropy—as elements of the dual Lie algebra $\mathfrak{g}^*$.

The condition for **Nomological Closure** in the D1 lane is that the Moment Map must be invariant under the action of the symmetry group. Formally, this is the commutator identity:
$$[ \hat{H}, \hat{N} ] = 0$$
Where $\hat{H}$ (the Hamiltonian) and $\hat{N}$ (the number operator) are generators of the algebra. If this commutator vanishes, the "path" of derivation in the ArangoDB graph preserves the **Lie Grading**.

## 3. The Lie Algebra Weights Collection
To enforce this without polluting the raw topological graph, the Spire introduces the `lie_algebra_weights` collection. This collection maps expression hashes to their **Adjoint Representations**. 

An audit of a proof context (`lctx`) now consists of verifying that the "Thermodynamic Distance" between co-adjoint orbits is minimized. If the grading is preserved across the `FVarId` edges, the proof is not merely logically valid—it is **Symmetrically Saturated**.

## 4. Gauge Thermodynamics and Information Distance
By treating thermodynamics as a gauge theory on the Lie group $G$, we can define the distance between two proof states as the distance between their co-adjoint orbits. A "Socratic pressure" that fails to preserve the Lie grade is rejected as **Symbolic Inflation**. Only those derivations that acquit themselves through the Moment Map are permitted to reach the **Pauli Core**.
