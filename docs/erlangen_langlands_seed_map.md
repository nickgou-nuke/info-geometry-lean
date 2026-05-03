# Erlangen / Langlands Geometry Seed Map

This is a compact start file for the operator-Erlangen + Langlands research lane.

## Legend

- **Theorem-safe**: statements proved directly inside the file.
- **Witness-gated / Socket**: structure that composes supplied certificates, not proved from first principles.
- **Conservative / Non-assertive**: explicit notes that major global conjectural claims are not asserted here.

## Top Priority Kernels (ordered for dependency-first reading)

1. `lean/InfoGeometry/Geometry/BilingualUpperHalfPlane.lean`
   - Imports: `Mathlib`, `InfoGeometry.Krein.DoubledSpace`, `InfoGeometry.Canonical.TomitaTakesaki`, `InfoGeometry.Quantum.HestenesKahler`.
- Status: Theorem-safe core geometry on doubled-space upper-half-plane carrier.
- Use: base geometric language for Klein-style operator/Krein encoding.

2. `lean/InfoGeometry/OperatorAlgebra/FiniteJonesOptics.lean`
   - Imports: `Mathlib`, `InfoGeometry.OperatorAlgebra.JonesCalibration`.
   - Status: Theorem-safe finite-dimensional optics facts (rank collapse, invariants in explicit matrices).
   - Use: concrete finite example for noncommutative Erlangen invariance in channels.

3. `lean/InfoGeometry/OperatorAlgebra/FiniteJonesErlangerBridge.lean`
   - Imports: `Mathlib`, `InfoGeometry.OperatorAlgebra.FiniteJonesOptics`.
   - Status: Theorem-safe + owned target; explicit gauge covariance and diagonal invariance theorems.
   - Use: first concrete `Erlanger`-style bridge node.

4. `lean/InfoGeometry/Automorphic/AutomorphicKreinBridge.lean`
   - Imports: `InfoGeometry.Automorphic.SiegelResonance`, `InfoGeometry.Quantum.HestenesKahler`, `InfoGeometry.Krein.DoubledSpace`.
   - Status: Theorem-safe bridge theorems with monogenic/cuspidal identification.
   - Use: critical bridge between automorphic boundary and Krein/hestenes geometry.

5. `lean/InfoGeometry/Automorphic/LFunctionResonance.lean`
   - Imports: `Mathlib`, `InfoGeometry.Automorphic.SiegelResonance`.
   - Status: Socket+theorem-safe split operators, with future Langlands/zero-free/functional claims deferred as witness layers.
   - Use: base arithmetic resonance layer.

6. `lean/InfoGeometry/Automorphic/ProjectedLFunction.lean`
   - Imports: `Mathlib`, `InfoGeometry.Automorphic.SiegelResonance`, `InfoGeometry.OperatorAlgebra.AffineVirasoroExceptionalBridge`.
   - Status: Theorem-safe projector algebra and L-function projection statements; Euler/functional equation kept as supplied witness.
   - Use: explicit "projector to arithmetic readout" API for later bridges.

7. `lean/InfoGeometry/Automorphic/RoelckeSelbergSpectral.lean`
   - Imports: `Mathlib`, `InfoGeometry.Automorphic.SiegelResonance`.
   - Status: Spectral theorem and decomposition are packaged as assumptions/witnesses, not derived.
   - Use: central spectral interface for joint Hecke/Laplace eigenspaces.

8. `lean/InfoGeometry/Automorphic/LanglandsSugawaraBridge.lean`
   - Imports: `Mathlib`, `InfoGeometry.Automorphic.ProjectedLFunction`, `InfoGeometry.OperatorAlgebra.AffineVirasoroExceptionalBridge`.
   - Status: Explicitly witness-gated; does not assert full Langlands/functoriality/Euler claims.
   - Use: bridge node between Virasoro/Sugawara readout and completed L-data.

9. `lean/InfoGeometry/Automorphic/HeckePurification.lean`
   - Imports: `InfoGeometry.Automorphic.RoelckeSelbergSpectral`, `InfoGeometry.Automorphic.LFunctionResonance`, `InfoGeometry.Automorphic.LanglandsSugawaraBridge`, and auxiliary exceptional/Vir/VKM modules.
   - Status: Theorem-safe Hecke-Sugawara purification only under supplied compatibility certificates.
   - Use: structured purification layer for arithmetic–automorphic compatibility.

10. `lean/InfoGeometry/Automorphic/LanglandsPrimeResonance.lean`
    - Imports: `Mathlib`, `InfoGeometry.Automorphic.SiegelResonance`, `InfoGeometry.Automorphic.LFunctionResonance`.
    - Status: Theorem-safe equivalences inside witness context; explicitly not proving E9, geometric Langlands, or full functional equations.
    - Use: central "Langlands prime resonance" schema (central-zero ↔ resonance).

11. `lean/InfoGeometry/OperatorAlgebra/KapustinWittenDualitySocket.lean`
    - Imports: `Mathlib`.
    - Status: Operator-level S-duality skeleton + geometric-langlands interpretation as separate witness-gated socket.
    - Use: physical duality formalization entry before geometric categorification.

12. `lean/InfoGeometry/OperatorAlgebra/PhysicalLanglandsHolonomy.lean`
    - Imports: `Mathlib`.
    - Status: Noncommutative/KMS-compatible physical Langlands holonomy transport plus witness-gated geometric interpretation.
    - Use: most concrete physical-KW lane for dual holonomy readouts.

## Secondary (high-value) nodes

- `lean/InfoGeometry/Canonical/KleinBottleOrientifold.lean` — kernel-safe carrier for orientation/fermion-parity hypotheses.
- `lean/InfoGeometry/Canonical/ZetaTraceBridge.lean` — exact bridge to mathlib Euler product/zeta identities.
- `lean/InfoGeometry/Arithmetic/LFunctionPotential.lean` — conservative Jordan/L-function horizon abstraction.
- `lean/InfoGeometry/OperatorAlgebra/ConformalCyclicCosmology.lean` — boundary memory/crossover formalization with explicit residue-witness requirements.
- `lean/InfoGeometry/OperatorAlgebra/VerifiedCasimir.lean` — foundational invariant-core theorem.
- `lean/InfoGeometry/OperatorAlgebra/KleinianReturn.lean` and `SelfDualChiralConeBoundary.lean` — non-orientable/projective return and chiral boundary predicates.
- `lean/InfoGeometry/Canonical/BerryRotorBridge.lean` — modular Berry/Klein-Hestenes bridge stack.

## Implementation suggestion

1. Start from `BilingualUpperHalfPlane`, `FiniteJonesErlangerBridge`, and `AutomorphicKreinBridge`.
2. Build arithmetic readouts through `LFunctionResonance → ProjectedLFunction → LanglandsSugawaraBridge`.
3. Compose Langlands lane via `RoelckeSelbergSpectral`, `HeckePurification`, `LanglandsPrimeResonance`.
4. Add physical interpretation last via `KapustinWittenDualitySocket` and `PhysicalLanglandsHolonomy`.

You can now import the dependency spine from:
- `lean/InfoGeometry/ErlangenLanglandsLane.lean`

And use the theorem surface index:
- `docs/erlangen_langlands_surface_api.md`

For automation/integration, also use:
- `docs/erlangen_langlands_dependency_registry.json`
- `lean/InfoGeometry/ErlangenLanglandsChecks.lean`
- `lean/InfoGeometry/ErlangenLanglandsRoadmap.lean`
- `lean/InfoGeometry/ErlangenLanglandsEntry.lean` (single import entrypoint)
