# Real single-mode Kerr–Unruh algebra: theorem contract

## Provenance and intended scope

Source: the user's 2026-11-25 message headed “Coupling the 4D Loxodromic
Flow to the Fermionic Massieu Potential & Pauli CAR”, including the proposed
`KerrUnruhFermionicHorizonBridge.lean` and umbrella import list.
Baseline: `fe24e350b08fdea04f74c0748ef9fd9417c47529` in
`nickgou-nuke/info-geometry-lean`.

The requested exact algebra uses real matrices, `Real.exp`, `Real.log`, and
the co-rotating exponent `x = β * (E - Ω * m)`. The occupied basis vector is
first, the vacuum second. This is one finite fermionic mode.

## Owner search and reuse

- `InfoGeometry.Krein.TomitaMatrixAtom` owns the exact real matrices
  `ellPlus`, `ellMinus`, `Pplus`, `Pminus`, their CAR, projector products,
  and the real swap `J`. Its normalized `thermalPolarization` supplies a
  positive semidefinite matrix owner.
- `InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry` owns
  `fermiOccupation`, `fermiSimplexCoordinate`, and `occupationOdds`.
  Its scalar block is moved to `Clifford.FermiDiracAnalytic` without changing
  declaration names, definitions, or existing statements. The original module
  imports that focused owner. This avoids reproducing its Fermi API and lets
  the new finite theorem be checked without unrelated operator imports.
- Mathlib `Real.binEntropy` supplies binary entropy and its sharp maximum.
- The Amari/Bernoulli and finite complex CAR owners were inspected. Their
  scalar identities or complex wavefunction carriers do not replace the
  requested real operator calculation.
- Exact and related-name searches in `lean/`, `src/`, and relevant `proofs/`
  found no owner of the submitted six-coordinate Lorentz Poisson matrix.
  `Lie.LorentzCartanKernel` therefore introduces its coordinate formula.

## Exact targets and dependency order

1. Reuse the real CAR and complementary number/hole projectors.
2. Define `G(x) = exp(-x) • Pplus + Pminus`, prove its positive trace
   `Z(x) = 1 + exp(-x)` and normalized occupied trace `1/(1+exp x)`.
3. Define `ρ = (trace G)⁻¹ • G`; prove trace one, positive semidefiniteness,
   its existing thermal-polarization representation, and `J ρ(x) J = ρ(-x)`.
4. Prove the existing Fermi occupation is strictly between zero and one,
   its particle–hole symmetry, and its exact threshold at `x = 0`.
5. Prove actual `HasDerivAt` statements for `Ψ = log(1+exp(-x))` and the
   occupation; derive `Ψ'' = n(1-n)`, its sharp bound `1/4`, and equality
   precisely at zero.
6. Reuse native binary entropy to prove `S = Ψ + x*n`, `0 < S ≤ log 2`,
   equality precisely at zero, and its derivative `-x*n(1-n)`.
7. Substitute `x = β*(E-Ω*m)`. Positivity `β > 0` is required for translating
   signs and equality into comparisons of `E` with `Ω*m`.
8. Define `Q(E,m)=(0,0,m,0,0,E)` and
   `B(β,Ω)=(0,0,-β*Ω,0,0,β)`. Prove the Euclidean coordinate dual pairing
   is `β*(E-Ω*m)`, and separately prove `Π(Q) B = 0`.
9. Exhibit `β=1, Ω=0, E=1, m=0`: kernel membership with pairing one and
   occupation strictly less than one half.

## Corrections to the intake

| Intake claim | Disposition |
|---|---|
| CAR, Gibbs trace, Fermi occupation, scalar sign regimes | Exact finite targets |
| Hole idempotence and positive partition function promised in prose | Explicitly covered, unlike the supplied conjunction |
| Susceptibility and entropy peaks | Proved with native calculus and binary entropy |
| `P₀ = ker Π` identifies the half-occupation threshold | Refuted by an explicit real coordinate counterexample |
| Particle–hole equality is a CPT theorem | Only the real matrix involution and scalar symmetry are targets |
| Negative inverse temperature is another positive Hawking temperature | Algebraic sign reversal only; positive-domain hypothesis stays explicit |
| `n > 1/2` locates a spacetime interior/ergosphere or proves condensation | No such geometric or many-body conclusion follows from this scalar theorem |
| CAR bound proves absence of Kerr scattering instability | Scattering and stability require further field equations and boundary data |
| Fermi factor is the full Hawking emission spectrum | No greybody/absorption factors or asymptotic flux are constructed |
| All 18 umbrella modules verified | Supplied list contains 21 imports; their claimed root package is not present in the inspected checkout |

The Lorentz matrix is treated with its explicit coordinate and sign convention.
No identification of boost charge with stationary Killing energy is assumed
to have been proved. No new spacetime, KMS state, loxodromic flow, Tomita
operator, or spectral-projector identification is smuggled into these types.

## Acceptance

Use the unchanged Lean 4.34.1 / Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` pins. Compile through the shared
build lock; audit the complete new declaration namespaces; scan for proof
holes and unsafe proof bypasses; independently review the types and physical
scope. Record focused-build coverage separately from root-workspace coverage.
The proposed 21-import umbrella is not installed as a certificate for modules
that are not present. New owners are exposed through the existing library.
