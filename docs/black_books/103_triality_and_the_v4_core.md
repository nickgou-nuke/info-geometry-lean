# 103. Triality and the V₄ Core

## The Decomposition

The Weyl group of D₄ decomposes as:

```
W(D₄) ≅ (ℤ₂³ ⋊ V₄) ⋊ S₃
```

This is the group-theoretic signature of the entire bridge chain.

- **V₄** — the Klein four-group — is the inner reflection kernel. It
  generates the sign flips on the 2-component spinor (ψ⁺, ψ⁻). This is
  the same V₄ that acts in `Cl55V4SpinorFragmentation`, fragmenting the
  Cl(5,5) spinor modules into the `s⁺` and `s⁻` sectors.

- **S₃** — the symmetric group on three elements — is triality. It
  permutes the Vector, Spinor⁺, and Spinor⁻ representations of Spin(8).
  The three legs of the D₄ Dynkin diagram are the three triality sectors.

- **ℤ₂³** — the remaining sign flips — are the coordinate reflections
  that complete the full Weyl group.

## What This Means

The V₄ action on Cl(5,5) spinors is not an isolated construction. It is
the inner core of W(D₄), and W(D₄) is the Weyl group of Spin(8), and
Spin(8) sits inside the Cl(5,5) Clifford algebra as the even subalgebra
of the full 10-dimensional split signature.

Triality is the outer automorphism that permutes the V₄ eigenspaces
(s⁺, s⁻) with the null pair (U, V) from the Cl(1,1) slice. This is why:

- The cocycle defect `KW - WK = (2θ₂ + 2π, 0)` is the obstruction to
  lifting the V₄ action to the full triality group.
- The three Weyl reflections W, T·W·T⁻¹, T²·W·T⁻² are the S₃ orbit.
- The Klein bottle boundary is the projection of triality onto a
  non-orientable patch.

The SymPy witness `tools/sympy/triality_v4_d4_bridge.py` verifies the
D₄ Cartan matrix, the V₄ generators, the triality permutation T³ = I,
the orthogonal projectors P⁺, P⁻, and the cocycle obstruction. The Lean
bridge is at `Canonical/V4TrialityBridge.lean`.

A constructive finite realization of the full semidirect product action appears in
`Canonical/V4SemidirectS3Bridge.lean`, with the matching SymPy realization
`tools/sympy/v4_semidirect_s3_cl55_32_bridge.py`. It checks the full 24-element
`V₄ ⋊ S₃` multiplication in 96×96 matrices as an explicit Clifford-sector
model compatible with the triality-cycle transport.

This is the geometric ceiling of the architecture. Above this, there is
only the exceptional E₈, of which D₄ is a maximal subgroup. But that is
a different story.
