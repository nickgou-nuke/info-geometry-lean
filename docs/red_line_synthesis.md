# Red Line Synthesis

This note summarizes the "Red Thread of Free Energy" formalized in the
InfoGeometry Lean codebase.

## Chain Overview

1. Volume deformation:
   Jacobian or Radon-Nikodym scaling.
2. Negative logarithm:
   barrier / modular Hamiltonian potential.
3. Bregman lift:
   energy cost induced by the potential.
4. Partition and log-sum-exp:
   thermodynamic normalization.
5. Free energy:
   `F = -T log Z`, and `F = U - T S`.
6. Tomita-Takesaki realization:
   modular structures acting on doubled/Krein carriers.

## Formal Route In Code

1. `Jordan/LogDet.lean`:
   `logDetBarrier`, `logDetBregman`.
2. `Canonical/GrandUnification.lean` and `Canonical/GrandSynthesis.lean`:
   barrier/Kahler and RN-relative-volume bridges.
3. `Thermo/FromLogDet.lean`:
   `energyFromLogDet`, `partitionFromLogDet`, `freeEnergyFromLogDet`.
4. `ExponentialFamily/Analytic/LogSumExp.lean`:
   log-sum-exp generating potentials.
5. `MaxEnt/JaynesRNMaxEnt.lean`:
   RN derivative and Jaynes variational interfaces.
6. `Canonical/TomitaTakesaki.lean`:
   modular conjugation/sign and split-Clifford realization.

## Canonical Entry Points

Use canonical facades for publication/audit imports:

- `InfoGeometry.Canonical.RedLine`
- `InfoGeometry.Canonical.LogDet`
- `InfoGeometry.Canonical.ThermoFromLogDet`
- `InfoGeometry.Canonical.LogSumExp`
- `InfoGeometry.Canonical.JaynesRNMaxEnt`

