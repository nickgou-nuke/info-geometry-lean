# Emergent Non-Abelian Gauge API

> Owner: `lean/InfoGeometry/Canonical/EmergentNonAbelianGauge.lean`
> Mirrors: `tools/sympy/emergent_nonabelian_gauge.py`

This owner surface is finite and matrix-level.

It proves:

- the Pauli generators close cyclically as
  `[τ₁, τ₂] = 2 i τ₃`, `[τ₂, τ₃] = 2 i τ₁`, and `[τ₃, τ₁] = 2 i τ₂`;
- the first Gell-Mann generators close cyclically as
  `[λ₁, λ₂] = 2 i λ₃`, `[λ₂, λ₃] = 2 i λ₁`, and `[λ₃, λ₁] = 2 i λ₂`;
- the first Pauli and Gell-Mann generators are nonzero;
- scalar insertion factors out of the right spinor argument for the
  `γ₅ γ₀` bilinear;
- explicit spinor witnesses give nonzero axial bilinears after scalar
  insertion.

It does not prove:

- gauge bundles;
- Yang-Mills curvature;
- physical `SU(2)` or `SU(3)` gauge dynamics;
- any continuum weak/strong-force theorem.
