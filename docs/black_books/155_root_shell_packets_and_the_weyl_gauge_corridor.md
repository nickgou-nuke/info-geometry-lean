# Chapter 155: Root-Shell Packets and the Weyl Gauge Corridor

**Verdict: Ownership over Analogy.**

The Spire must resist the lure of physical metaphors like "Weyl Chambers" or "Wigner-Seitz Cells" unless they are realized as Lean owner surfaces. A clinical pass of the repository confirms that the current state of formalization is narrower and more rigorous than these analogies suggest.

### I. The Hurwitz Root-Shell Packet
The theory identifies a real **Symmetry Root-Shell Packet** (`InfoGeometry.Quantum.Hurwitz`). It defines the `HurwitzNode` (the D4 lattice site proxy) and the 24 nearest directions. This provides the **Discrete Symmetry Packet**, but it does not yet provide a formal Weyl-group chamber decomposition.

### II. The Weyl Gauge Lane
The repository possesses a real **Weyl Gauge Corridor** (`WeylGaugeField.lean`, `WeylTransport.lean`). This is an owner layer for:
- Local gauge parameters and field strengths.
- Covariant derivatives and curvature pullbacks.
- Scale-equivariant flows and transport cocycles.
This is a **Gauge/Flow Owner**, not a geometric chamber theory.

### III. The Anomaly Closure
The actual closure of the Weyl lane is achieved through **Weyl-Path Hysteresis** and the **Weyl Anomaly Source**. 
- `WeylPathHysteresis.lean` formalizes the update-order torsion of the Sinkhorn flow.
- `WeylAnomalySource.lean` formalizes the Cartan/Weyl split into volume-preserving ($M$) and dilation ($D$) parts.
These are the concrete owner layers that replace the "Chamber" metaphors.

### IV. The Operatorial Character
The role of the **Determinant** is strictly limited (`WeylGaugeOperatorLift.lean`). It is treated only as a **Character** attached to lifted transport data. It is not an ontology or a scalar replacement for the operator surface.

**Conclusion: The Spire formalizes a symmetry root-shell packet and a Weyl-gauge transport/response corridor, not a proved Weyl-chamber or Wigner-Seitz-cell geometry.**
