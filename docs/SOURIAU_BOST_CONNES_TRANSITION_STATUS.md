# Souriau-Bost-Connes Transition Status

> Status: `theorem-honesty authority`
> Owner module:
> `lean/InfoGeometry/Canonical/SouriauBostConnesTransition.lean`
> Rule: do not describe this lane as an analytic zero-temperature
> Bost-Connes crystallization theorem until the open closure debt in the owner
> module is proved in Lean.

## What Is Verified

The owner module currently verifies a finite/local transition matrix. It is a
capstone readout over existing owner theorems, not a proof of the full analytic
physics narrative.

The exported theorem-safe capstone is:

```lean
InfoGeometry.Canonical.SouriauBostConnesTransition
  .souriau_bost_connes_transition_verified
```

It packages these kernel-checked components:

- finite Boolean prime Weyl denominator identity;
- Cayley critical-line/unit-circle readout;
- Riemann reflection as Cayley fugacity inversion;
- conditional RH readout from supplied prime Lee-Yang witnesses;
- finite Yang-Baxter matrix parameters;
- finite Fibonacci golden-ratio and phase readouts;
- combinatorial Dirac-sea vacuum and interface-step nilpotence.

The module also defines:

```lean
InfoGeometry.Canonical.SouriauBostConnesTransition.openClosureDebt
InfoGeometry.Canonical.SouriauBostConnesTransition.openClosureDebt_ne_nil
```

The second theorem proves that the capstone has explicit open debt.

## What Is Not Verified

Do not claim the repository has proved any of the following unconditionally:

- analytic Bost-Connes partition function construction;
- equality of the Bost-Connes partition function with `Real.riemannZeta`;
- zero-temperature limit `beta -> infinity`;
- Fisher-Souriau metric blow-up and inverse-metric collapse;
- phase-space shattering onto the Cantor boundary as an analytic convergence
  theorem;
- full Cuntz-to-Fibonacci boundary functor;
- categorical Fibonacci pentagon and hexagon coherence;
- full braided-category instance from the finite matrix readout;
- unconditional RH/Lee-Yang theorem;
- anomaly cancellation derived from the full analytic Bost-Connes system.

Those are mathematical targets, not current kernel facts.

## Forbidden Phrases

Do not write these phrases in maintained docs, paper nodes, or theorem names
unless the owner theorem has been proved:

- "the Souriau-Bost-Connes Transition Theorem is verified";
- "the compilation loop is officially closed";
- "zero-temperature crystallization is proved";
- "the Bost-Connes partition function is formalized";
- "the Cantor boundary crystallization theorem is axiom-free";
- "Fibonacci pentagon/hexagon coherence is closed";
- "RH follows from the prime Lee-Yang route" without saying `conditional`.

## Safe Wording

Use this wording instead:

```text
The repository currently contains a verified finite/local
Souriau-Bost-Connes transition matrix. It packages owner-backed facts about
finite prime Weyl denominators, Cayley critical-line readouts, finite
Yang-Baxter parameters, finite Fibonacci matrix readouts, and the combinatorial
Dirac-sea interface. The analytic Bost-Connes partition function,
zero-temperature convergence, categorical Fibonacci coherence, and full
boundary crystallization theorem remain explicit closure debt.
```

## Current Build Gate

Validate the owner module with:

```bash
lake env lean lean/InfoGeometry/Canonical/SouriauBostConnesTransition.lean
lake build InfoGeometry.Canonical.SouriauBostConnesTransition
```

After edits, scan the touched file for fake closure markers:

```bash
rg -n "sorry|admit|axiom|unsafe|: True|by\s+trivial|:=\s*trivial" \
  lean/InfoGeometry/Canonical/SouriauBostConnesTransition.lean
```

## Closure Debt Owners

The current open debt should be closed in owner lanes, not by adding wrapper
theorems:

- Bost-Connes partition function owner lane: construct the analytic object.
- Euler product owner lane: prove the reciprocal partition relation separately
  from the finite Weyl denominator.
- Thermodynamic analysis owner lane: prove the `beta -> infinity` convergence.
- Categorical owner lane: construct the Cuntz-to-Fibonacci boundary functor.
- `Categorical/FibonacciBraiding.lean`: prove pentagon and hexagon coherence.
- Boundary/anomaly owner lane: construct the boundary state required for a
  non-placeholder anomaly theorem.
