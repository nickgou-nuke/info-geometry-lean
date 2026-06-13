# Non-Commutative Index Theorem Milestone

> Status: `architecture milestone`
> Audited: 2026-06-10
> Scope: finite Lean/SymPy proof surfaces only
> Boundary: this document is a dependency map, not a proof certificate for RH,
> analytic Hodge theory, KMS theory, CFT, or infinite UHF completion.

This note preserves the current coordinate-transition milestone: the finite
tripotent sector algebra now has an explicit Hodge-style dictionary, a finite
Tomita/Dirac-Hodge atom, a centered zeta-coordinate layer, a finite Witten
parity layer, and a finite diagonal-UHF cylinder skeleton.

The repository now has a clean finite corridor for the slogan:

```text
Hodge labels          Tripotent labels          Centered coordinate reading
exact                 P_plus                    u > 0 interpretation target
coexact               P_minus                   u < 0 interpretation target
harmonic              P_zero                    u = 0 interpretation target
```

Only the algebraic dictionary is proved. The geometric and physical readings are
interpretive targets unless separately formalized in Lean with their analytic
premises.

## Live Module Graph

```text
InfoGeometry.Canonical.TrifactorDecomposition
  -> InfoGeometry.GrandUnification.HodgeTrifactorBridge

InfoGeometry.Krein.TomitaMatrixAtom
  -> finite 2x2 J / eps / Pplus / Pminus / ladder atom
  -> mirrored by tools/sympy/hodge_trifactor_bridge.py

InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions
  -> centered coordinates s = 1/2 + u + iv
  -> finite Dirichlet mode factorization
  -> completed-xi reflection consequences from explicit hypotheses
  -> finite Bernoulli readouts for zeta(3), zeta(5), zeta(7), zeta(9)

InfoGeometry.Arithmetic.WittenParityIndex
  -> explicit finite parity polynomials D1, D2, D3, D4
  -> +1, -1, +1, -1 parity sequence

InfoGeometry.Canonical.UHFInductiveColimitBoundary
  -> finite binary-prefix diagonal algebra
  -> successor embeddings and cylinder compatibility

InfoGeometry.Canonical.CuntzCantorBoundaryShift
  -> binary branch prepend maps on CantorBoundary
  -> disjoint branch cover
  -> finite-cylinder pullback along branch maps
```

For the exact theorem names behind the centered coordinate transition, see
[centered-zeta-coordinate-api.md](centered-zeta-coordinate-api.md).

## Kernel-Checked Layer

The current closed finite layer consists of:

- `HodgeTrifactorBridge.lean`
  - `HodgeSector`, `TrifactorSector`, and `hodgeTrifactorEquiv`;
  - `hodge_trifactor_decomposition`;
  - `T_annihilates_harmonicSector`;
  - `T_on_exactSector`;
  - `T_on_coexactSector`;
  - linear-map preservation of the three sector components.
- `TomitaMatrixAtom.lean`
  - `J_sq`, `eps_sq`, and `J_mul_eps_eq_neg_eps_mul_J`;
  - `Pplus` / `Pminus` idempotence and orthogonality;
  - ladder nilpotence and support laws;
  - `diracHodgeAtom_eq_J`;
  - `diracHodgeAtom_anticommutes_eps`;
  - conjugation and intertwining laws swapping `Pplus` and `Pminus`.
- `ZetaSymmetryAdaptedDefinitions.lean`
  - centered coordinate chart and critical mirror fixed locus;
  - Dirichlet mode split into baseline, scale-normal, and phase factors;
  - finite Dirichlet and Euler readouts;
  - xi-evenness consequences from supplied reflection hypotheses;
  - finite Bernoulli defect layers for the first four odd zeta levels.
- `WittenParityIndex.lean`
  - polynomial parity checks for `D1`, `D2`, `D3`, `D4`;
  - the explicit `+1, -1, +1, -1` readout.
- `UHFInductiveColimitBoundary.lean`
  - `BitWord n`, `DiagAlg n`, and `CantorBoundary`;
  - algebra-preserving successor embedding;
  - injectivity of the successor embedding;
  - finite-cylinder compatibility and finite colimit membership.
- `CuntzCantorBoundaryShift.lean`
  - binary branch maps `prependBit false` and `prependBit true`;
  - branch injectivity, disjointness, and cover of the Cantor carrier;
  - finite-cylinder pullback closure under each branch.

## SymPy Witness Layer

The SymPy scripts are verification companions, not Lean proof inputs:

- `tools/sympy/hodge_trifactor_bridge.py`
  checks the tripotent projector identities, finite sector functoriality, and
  the 2x2 chiral anticommutation atom.
- `tools/sympy/zeta_symmetry_adapted_definitions.py`
  checks centered-coordinate algebra and numerical samples for the analytic
  zeta-side readouts.
- `tools/sympy/witten_parity_index.py`
  checks the four explicit Witten parity polynomials.
- `tools/sympy/uhf_inductive_colimit_boundary.py`
  checks the finite binary-prefix/cylinder skeleton.

## Proof Boundary

The following are intentionally not claimed by this milestone:

- a proof of the Riemann Hypothesis;
- a theorem that non-trivial zeta zeros are harmonic zero-modes;
- analytic Hodge decomposition for an infinite non-commutative space;
- full Tomita-Takesaki modular theory;
- KMS/CFT/AdS or physical thermodynamic equivalence;
- C*-completion of the UHF inductive limit;
- full Cuntz `O₂` Hilbert-space partial-isometry relations;
- Cantor topology, Cantor measure, or spectral theorem for the diagonal MASA.

The accepted statement is narrower and kernel-checkable:

> The finite tripotent algebra `T ^ 3 = T` has a proved three-sector
> decomposition.  That decomposition now has a Hodge-style label equivalence,
> a finite 2x2 Tomita atom that swaps the active signs, finite zeta-centered
> coordinate readouts, and finite Witten parity polynomials.

## Practical Entry Points

Use this order when extending the milestone:

1. Start from `InfoGeometry.Canonical.TrifactorDecomposition`.
2. Add sector-language consequences in
   `InfoGeometry.GrandUnification.HodgeTrifactorBridge`.
3. Add finite 2x2 Tomita/CPT checks in
   `InfoGeometry.Krein.TomitaMatrixAtom`.
4. Add centered arithmetic readouts in
   `InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions`.
5. Keep analytic series, topology, KMS, and RH-level statements as explicit
   theorem debt or conditional sockets with real hypotheses.

## Verification Commands

```bash
lake build InfoGeometry.GrandUnification.HodgeTrifactorBridge
lake build InfoGeometry.Krein.TomitaMatrixAtom
lake build InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions
lake build InfoGeometry.Arithmetic.WittenParityIndex
lake build InfoGeometry.Canonical.UHFInductiveColimitBoundary
lake build InfoGeometry.All
python3 tools/sympy/hodge_trifactor_bridge.py
python3 tools/sympy/zeta_symmetry_adapted_definitions.py
python3 tools/sympy/witten_parity_index.py
python3 tools/sympy/uhf_inductive_colimit_boundary.py
```
