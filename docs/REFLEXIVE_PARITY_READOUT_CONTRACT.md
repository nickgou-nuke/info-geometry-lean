# Reflexive parity/readout contract

## Ground truth

Reuse `DeBruijnRotorAlternationCycle.IsDualSeedPair d B` over an arbitrary
`[Ring A]`; its laws are `d*d=0`, `B*B=0`, `d*B*d=d`, `B*d*B=B`.
Keep its actual `polePlus=d*B`, `poleMinus=B*d`, `carrierSupport`,
`transitionVelocity=d+B`, and `wheelGenerator=d-B` definitions.

Use the already constructed
`GrassmannianBundleCyclotomicOrientability.ambientReflectionUnit`
with value and inverse `d+B+(1-(d*B+B*d))`. Its square is the ambient one;
the uncompleted `d+B` only squares to the active support. Use the existing
`unitOrbitMap X u = u*X*u⁻¹` for actual conjugation.

Target `Canonical/ReflexiveParityReadout.lean`:

1. On elements supported on both sides by the active carrier, ambient-unit
   conjugation agrees with the supported `(d+B)` sandwich.
2. The ambient unit exchanges `d` and `B`; thus for `[CommRing R] [Algebra R A]`
   it sends `α • (d+B) + β • (d-B)` to `α • (d+B) - β • (d-B)`.
3. The defect is `-((2*β) • (d-B))`; fixedness is equivalent to this coefficient
   annihilating `d-B`. Do not infer nonzero defect from nonzero coefficients.
4. On an arbitrary left `A`-module, a vector fixed by `d+B` and by `d*B` is zero;
   likewise for `B*d`. These are pointwise algebraic obstructions, not claims
   about Dirac spectra or descended spinor sections.
5. Reuse `Core.PeirceDensityIntertwining.density d B b a = b • (B*d)+a • (d*B)`.
   Multiplication by `phasePolarization` gives `a • (d*B)-b • (B*d)`.
   For the existing `NCG.TracialFunctional`, its readout is
   `(a-b)*τ(d*B)` by cyclicity. No positivity, normalization or nonzero trace
   hypothesis is inferred.

Owner reuse inspected: `GrassmannianBundleCyclotomicOrientability` reflection,
active-support and unit laws; `DeBruijnRotorAlternationCycle` Peirce table;
`Core/DiracSuperalgebra` and `Core/MajoranaSupportSwap` star/MP reflection facts;
`Core/PeirceDensityIntertwining`; `OperatorAlgebra/TracialCARDensity`.
The star/MP APIs remain owners for their stronger hypotheses; the proposed
bridge does not recreate their star symmetry or Clifford square theorems.

## Regressions and scope

Use native integral matrix seeds for a nonzero conjugation defect; characteristic
 two noncommuting seeds to show why the annihilation criterion is necessary;
and a self-adjoint scalar whose square is not one. Matrix checks are regression
instances of the arbitrary-ring statements, never replacement carriers.

No new `IsDualSeedPair`, putative condensate structure, Pin classification,
physical CP action, brane, particle-production or baryogenesis theorem.

## Authenticated external context (not Lean hypotheses)

Retrieved `https://arxiv.org/html/2511.23447` and
`https://arxiv.org/html/2510.05270` successfully. In 2511.23447, equations
(1), (10)–(12) use negative-square `Gamma^4` and positive-square chirality;
`R4=Gamma^4*chirality` squares to one, while `i R4` squares to minus one.
Equation (31) gives the massless periodic coincident condensate proportional to
`i W(x4) chirality`, not the proposed odd combination. Equations (59)–(60)
distinguish the fermionic plus-sign normalization from the scalar minus-sign
normalization. These formulas do not supply a representation/descent map into
our algebra. No podcast claims were authenticated.
