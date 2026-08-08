# Index of the Conformal-to-Noncommutative Topological Transition

This document maps the finite proof anchors and theorem-honest sockets connecting
Peirce subspaces, trifactor operators, Klein-bottle momentum topology,
Super-Berezinian regularization, and braid-ideal descent.

## 1. Trifactor and Peirce Algebra

Files:

- `proofs/SuperBerezinianKlein.lean`
- `proofs/CubicJordanPeirceDecomposition.lean`

Lean anchors:

- `trifactor_partition_of_unity`
- `trifactor_plus_minus_orthogonal`
- `Pcanonical_is_tripotent`
- `L_P_E1_eigen`
- `L_P_E2_eigen`
- `L_P_E3_zero`

The scalar trifactor decomposition proves that an operator satisfying `P³=P`
yields three algebraic sheets.  The Peirce anchor proves that for two-sided
orthogonal idempotents `E₁,E₂,E₃`, the canonical difference `P=E₁-E₂` is
tripotent and has diagonal eigenvalues `+1,-1,0` under left multiplication.

## 2. Non-Orientable Momentum Boundary

Files:

- `proofs/SuperBerezinianKlein.lean`
- `proofs/GlideSymmetricInvariant.lean`
- `proofs/klein_metriplectic_flow.py`

Lean anchors:

- `pgGlide_sq`
- `hamiltonian_preserves_plus_eigenspace`
- `hamiltonian_preserves_minus_eigenspace`

The `pg` glide relation is represented by `(x,y) ↦ (x+1,-y)`, with the square
of the glide equal to translation by two units.  A Hamiltonian commuting with an
involutive glide preserves the `+1` and `-1` eigensectors.

## 3. Super-Berezinian / Painlevé-like Cutoff

Files:

- `proofs/SuperBerezinianKlein.lean`
- `proofs/super_berezinian_klein.py`
- `proofs/klein_metriplectic_flow.py`

Lean anchors:

- `superBerezinian1_no_mixing`
- `superBerezinian1_even_scale_no_mixing`
- `palPoly2_self_reciprocal`
- `palPoly2_reciprocal_ratio`

The scalar Super-Berezinian toy model verifies the expected no-mixing reduction
and even-scale cancellation.  Python witnesses show finite stabilization in a
Painlevé-like asymptotic toy regime when a bosonic determinant collapses.

## 4. Braid Ideal Descent and q-Cross Map

File:

- `proofs/BraidIdealDescent.lean`

Lean anchors:

- `tauL`
- `tauR`
- `IsLeftTauIdeal`
- `IsRightTauIdeal`
- `qCrossMap`
- `qCrossMap_tmul`
- `YangBaxterIdealDescentSocket`

The maps `tauL` and `tauR` are constructed from `TensorProduct.assoc`,
`TensorProduct.comm`, and `TensorProduct.map`; they replace informal braid
strings by concrete linear maps.  The q-cross map is the scaled swap
`C_q(η⊗x)=q • (x⊗η)`.  Full Yang--Baxter/PBW ideal inheritance remains an
explicit socket requiring the braid relation and its ideal-stability data.

## Theorem-Honesty Boundary

The following are sockets, not proved anchors:

- full Pin/O(5,5) characteristic-polynomial classification;
- Painlevé III/V asymptotic theorem;
- Gohberg--Krein spectral-flow index;
- full TKK/Albert Peirce classification beyond finite associative anchors;
- Yang--Baxter implying the `τ`-ideal conditions for arbitrary quadratic ideals.
