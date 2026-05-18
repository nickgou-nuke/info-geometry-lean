# Root Socket Proof Packets

This note records the current root-first proof search for the open sockets in
`InfoGeometry.Arithmetic.PrimonFreeEnergyRelativeTrace`.

It is not proof authority. It is a routing packet for the next native Lean
closure step.

## 1. `MellinInversionParitySocket`

### Sources

- Keith Ball, *The functional equation for ζ*.
  - arXiv: https://arxiv.org/abs/2201.05822
  - archive copy: https://warwick.ac.uk/fac/sci/maths/people/staff/keith_ball/functeq.pdf
- E. Elizalde, S. Leseduarte, S. Zerbini, *Mellin Transform Techniques for Zeta-Function Resummations*.
  - arXiv: https://arxiv.org/abs/hep-th/9303126

### Extracted claims

- The Riemann zeta functional equation has a short proof via contour/Mellin
  methods.
- Inverse Mellin techniques can derive zeta regularization identities and
  split the result into zeta, power, and exponentially decaying pieces.

### Repo symbol map

- `InfoGeometry.Arithmetic.PrimonFreeEnergyRelativeTrace.MellinInversionParitySocket`
- `InfoGeometry.Canonical.PrimeCl11MellinHurwitzBridge.PrimeCl11MellinHurwitzOwnerTarget`
- `InfoGeometry.Canonical.DiscreteMellinModularBridge`

### Lean candidates

- A narrow theorem packet for the discrete log-parity channel.
- A bridge theorem that only reexports the already proved finite scale-step
  and `Cl(1,1)` parity facts.

### Required assumptions

- A concrete Mellin inversion theorem in Lean, or a paper-backed import packet.
- A precise statement of the parity/channel equivalence.

### Debt

- The full `MellinInversionParitySocket` remains open.
- The repo currently only carries theorem reexports for the socket fields.

## 2. `KLEquilibriumSocket`

### Sources

- David Dereudre, *Variational principle for Gibbs point processes with finite
  range interaction*.
  - arXiv: https://arxiv.org/abs/1506.05000
- Younghak Kwon, Georg Menz, *Strict convexity of the free energy of the
  canonical ensemble under decay of correlations*.
  - arXiv: https://arxiv.org/abs/1710.08974

### Extracted claims

- Gibbs point processes are minimizers of free excess energy.
- Under finite-range/decay assumptions, free energy becomes strictly convex
  in the large-system limit.

### Repo symbol map

- `InfoGeometry.Arithmetic.PrimonFreeEnergyRelativeTrace.KLEquilibriumSocket`
- `InfoGeometry.Arithmetic.PrimonFreeEnergyRelativeTrace.StableUnstableGibbsChartSocket`
- `InfoGeometry.Canonical.GrandCanonicalThermodynamicEngine`

### Lean candidates

- A theorem packet for the finite-range variational principle.
- A theorem packet for strict convexity of the finite-volume free-energy
  readout.

### Required assumptions

- A concrete Gibbs/entropy/free-energy model in Lean.
- Decay or finite-range hypotheses stated explicitly.

### Debt

- The full `KLEquilibriumSocket` remains open.
- No repo-native theorem currently discharges its convexity/equilibrium fields.

## 3. `RelativeTraceSignatureSocket`

### Current state

- No direct repo theorem found beyond the witness reexports in
  `PrimonFreeEnergyRelativeTrace.lean`.
- No paper source has yet been pinned down with a theorem statement close enough
  to the exact socket fields.

### Debt

- Needs a primary source for the sign of the relative/prime-orbit trace term.
- Needs a theorem packet before any Lean bridge can be justified.

## 4. `MobiusFreeEnergyInversionSocket`

### Current state

- The file has theorem reexports, but no native closure.
- It remains a witness socket until a source-backed proof packet is found.

### Debt

- Needs a literature proof packet for the inverse-zeta/free-energy channel.

## 5. `FiveGradedMobiusBalanceSocket`

### Current state

- No root theorem found yet.

### Debt

- Needs a real representation theorem or a source-backed proof packet.

