# Ground-truth theorem contract: chiral zitterbewegung velocity and two-connection curvature

## Claim (after epistemic dissolution of the raw stream)

The raw stream (`GOEDEL.md` Stage D₅₇, `WHAT-IS-TIME.md`, `The_Core_Paradigm_Shift.md`)
confabulates a "Dirac spectral triple" on a noncommutative ring. Stripped of its
physics prose, the surviving mathematical content on `[Ring B]` with an
idempotent `P * P = P` and grading `S = P - (1 - P)` is:

1. **Owned already** (deep-searched; do not duplicate):
   - `S² = 1`, `{S, Φ} = 0`, `D_mass² = 1 + V`, `D_chiral² = 1 - V`, and the
     quartic decomposition `D⁴ - D² = 2V + δ(V)`, `δ(V) = δ(Q₊) + δ(Q₋)`:
     `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/DiracPolynomialAction.lean`
     (`peirceMassDirac`, `peirceChiralDirac`, `diracQuarticPolynomial`).
   - Grading conjugation anatomy `S Φ = J`, `Φ S = -J`, `S V S = V`:
     `lean/InfoGeometry/Physics/CobaltAsymmetryDependency.lean`,
     `lean/InfoGeometry/Physics/SolovievInterferenceDependency.lean`.
   - Gödel open-chain nilpotency and closed-cycle 4-sector holonomy:
     `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/FiniteCycleHolonomy.lean`.
   - Radical letters `(S ± 2Φ)² = 1 ± 4V`:
     `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/PositroidClusterTwistPoset.lean`
     (`operator_square_root_symbol_letters`).
   - Five faces of operator time (modular, Page–Wootters clock, retarded arrow,
     star parity, epoch tower): `TelegrapherTwoStateMasterPoset.lean`
     archetypes A115–A119.

2. **Genuinely missing (this task, kernel-checked here):** the chiral
   zitterbewegung velocity block
   `comm (peirceMassDirac P A C) (invS P) = -(2:ℤ) • genJ P A C`, its square
   `-(4:ℤ) • genV P A C`, the chiral-partner velocity `-(2:ℤ) • genPhi`,
   and the second-order oscillation
   `comm D (comm D J) = 4 • (D * D * J)`.

3. **Socratic aporia (raw claim falsified, downgraded):** the raw Stage D₅₇
   "Lichnerowicz–Weitzenböck" identity
   `(Φ₁ + J₂)² = (V₁ - V₂) - F₁₂` with
   `F₁₂ = [N₊₁, N₋₂] - [N₊₂, N₋₁]` is **not** a general ring identity. The true
   identity is
   `(Φ₁ + J₂)² = (V₁ - V₂) + {Φ₁, J₂}` with the cross anticommutator central
   under the cut: `comm P {Φ₁, J₂} = 0`. The falsifying witness lives in
   `M₂(ℚ)`: `P = E₁₁`, `A₁ = C₂ = 0`, `C₁ = E₂₁`, `A₂ = E₁₂` gives
   `(Φ₁ + J₂)² = 1` while the raw right side is `E₁₁ - E₂₂ ≠ 1`.

4. **Diagnosis of the falsification (glide reflection / Möbius twist).**
   The counterexamples arise by ignoring the grading; the anomalies are the
   generators.  On the witness both metric slots vanish (`V₁ = V₂ = 0`) and
   the entire discrepancy sits in the cross-term of the two odd (corner)
   generators: there `{Φ₁, J₂} = E₂₁E₁₂ + E₁₂E₂₁ = 1` (the even, cut-central
   slot) while the substituted commutator slot carries the unmatched
   cross-products `E₁₂E₂₁ = E₁₁` vs `E₂₁E₁₂ = E₂₂` — the plain commutator
   `E₁₁ - E₂₂` records the sheet swap instead of cancelling it.  The sheet
   swap `cut ↔ 1 - cut` is the Möbius half-twist of the glide reflection:
   the generator pair is σ-related (`invS P * Φ = J`, `Φ * invS P = -J`,
   owned in `InfoGeometry.Physics.CobaltAsymmetryDependency`), so crossing
   the reflection flips the chiral sign, and ring-level this says
   `{Φ, J} = 2 • (N₊² - N₋²)` — the anticommutator is the even
   (glide-even) slot, not a commutator slot.  Kernel-checked row:
   `glide_pair_reflection` in `ZitterbewegungVelocity.lean`.

## Carrier and conventions

Carrier: `[Ring B]`, multiplication in displayed order, `comm X Y = X * Y - Y * X`,
`anticomm X Y = X * Y + Y * X`. Vocabulary imported from
`InfoGeometry.OperatorAlgebra.PeirceSpine` (`invS`, `conePlus`, `coneMinus`,
`genPhi`, `genJ`, `genV`, `genSig`, `peirce_nf`) and
`InfoGeometry.OperatorAlgebra.PeirceSpine.DiracPolynomialAction`
(`peirceMassDirac`, `peirceChiralDirac`). The counterexample carrier is
`Matrix (Fin 2) (Fin 2) ℚ` following the idiom of
`lean/InfoGeometry/OperatorAlgebra/PeirceDefectMatrixWitness.lean`.

## Causal order (poset)

```text
cut P² = P (owned: Basic)
  → corner cones N±, square-zero sheets (owned: Basic)
  → grading anatomy S² = 1, S Φ = J, Φ S = -J (owned: Cobalt/Soloviev)
  → dispersion peirceMassDirac² = 1 + V (owned: DiracPolynomialAction)
  → zitterbewegung velocity -2J, square -4V, oscillation 4(1+V)J (NEW)
  → two-connection square = (V₁ - V₂) + {Φ₁, J₂} (NEW, corrected)
  → cross anticommutator central: comm P {Φ₁, J₂} = 0 (NEW)
  → synthesis theorem
```

## Proof obligations discharged

All new statements are proved with `peirce_nf hP` (path-algebra normal form for
the two-vertex Peirce quiver) or by entrywise finite matrix evaluation. No new
carrier, no scalar/diagonal/commuting Reductionen; the counterexample keeps
`ℚ` matrices noncommutative (products changed shape: `E₂₁E₁₂ = E₂₂`,
`E₁₂E₂₁ = E₁₁`).

## Explicitly unproved adjacent claims

No analytic Hamiltonian, no ODE flow, no spectral-triple analytic axioms, no
physical mass gap, no spacetime Lorentzian structure, no claim that the
quantity 4(1+V) is a frequency in any analytic sense. The oscillation
statement is the exact ring identity `comm D (comm D J) = 4 • (D² J)`; the
Canonical analytic-lane zitterbewegung files
(`MassiveDoubledZitterbewegung`, `RindlerZitterbewegung`, `ZbwDarwinDemodulation`
…) remain separate carriers with no proved ring-map edge to this module.
